//! Lua parser plugin — full-parse mode.
//!
//! Handles `.lua` files.
//! The plugin parses source with Tree-sitter inside Rust/Wasm.

use intentumdiff_plugin_sdk::{
    cst::CstNode,
    hash::structural_hash_with_memo,
    tree::{SemanticNode, SemanticNodeBuilder},
};

wit_bindgen::generate!({
    path: "wit/plugin.wit",
    world: "parser-plugin",
});

use crate::exports::intentdiff::plugin::parser::ExamplePair;
use crate::exports::intentdiff::plugin::parser::Guest;
use crate::exports::intentdiff::plugin::parser::LanguageInfoRecord;
use crate::exports::intentdiff::plugin::parser::ParserMode;

const PLUGIN_METADATA: &str = include_str!("../plugin_metadata.info");

fn language_info_for(ids: Vec<String>) -> Vec<LanguageInfoRecord> {
    let metadata = intentumdiff_plugin_sdk::metadata::parse_plugin_metadata(PLUGIN_METADATA);
    ids.into_iter()
        .map(|language_id| {
            let info = metadata.language_or_default(&language_id);
            LanguageInfoRecord {
                language_id: info.language_id,
                language_name: info.language_name,
                language_short_name: info.language_short_name,
                monaco_language: info.monaco_language,
                default_filename: info.default_filename,
                language_file_extensions: info.language_file_extensions,
                author: metadata.author().to_string(),
                plugin_version: metadata.plugin_version().to_string(),
                last_updated: metadata.last_updated().to_string(),
            }
        })
        .collect()
}
struct LuaParser;

const TRIVIA: &[&str] = &["comment", "whitespace"];

const SEMANTIC_TYPES: &[&str] = &[
    // Root
    "chunk",
    // Function definitions
    "function_declaration",
    "local_function",
    "function_definition",
    "method_index_expression",
    // Variables / assignments
    "variable_list",
    "assignment_statement",
    "local_variable_declaration",
    // Statements
    "if_statement",
    "elseif_clause",
    "else_clause",
    "while_statement",
    "repeat_statement",
    "for_statement",
    "for_in_statement",
    "return_statement",
    "break_statement",
    "goto_statement",
    "label_statement",
    // Expressions
    "function_call",
    "method_call",
    "dot_index_expression",
    "bracket_index_expression",
    "binary_expression",
    "unary_expression",
    "vararg_expression",
    "table_constructor",
    "string",
    "number",
    "true",
    "false",
    "nil",
    "identifier",
];

fn is_semantic(node_type: &str) -> bool {
    SEMANTIC_TYPES.contains(&node_type)
}

fn source_span<'a>(source: &'a str, node: &CstNode) -> &'a str {
    let Some(line) = source.lines().nth(node.start_line as usize) else {
        return "";
    };
    let start = node.start_col as usize;
    let end = if node.start_line == node.end_line {
        node.end_col as usize
    } else {
        line.len()
    };
    line.get(start..end).unwrap_or("")
}

fn label_for(node: &CstNode, source: &str) -> String {
    if node.is_leaf() {
        return node.text_or_empty().to_string();
    }
    // Literal containers label with their captured source text (SDK-shared, issue #47).
    if let Some(label) = intentumdiff_plugin_sdk::ts_convert::literal_label(node) {
        return label;
    }
    match node.node_type.as_str() {
        "function_declaration" | "local_function" => {
            // tree-sitter-lua aliases local/global declarations to the same named
            // node and does not expose the anonymous `local` token as a CST child.
            // Use the declaration's source span to retain that semantic modifier.
            let is_local = source_span(source, node).trim_start().starts_with("local function");
            for child in &node.children {
                if child.node_type == "identifier" || child.node_type == "name" {
                    let name = child.text_or_empty();
                    return if is_local {
                        format!("local {name}")
                    } else {
                        name.to_string()
                    };
                }
            }
        }
        "assignment_statement" => {
            // First variable in the variable list
            for child in &node.children {
                if child.node_type == "variable_list" {
                    if let Some(first) = child.children.first() {
                        return first.text_or_empty().to_string();
                    }
                }
                if child.node_type == "identifier" {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "local_variable_declaration" => {
            for child in &node.children {
                if child.node_type == "identifier" || child.node_type == "name_list" {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "function_call" | "method_call" => {
            for child in &node.children {
                if child.node_type == "identifier"
                    || child.node_type == "dot_index_expression"
                    || child.node_type == "method_index_expression"
                {
                    return child.text_or_empty().to_string();
                }
            }
        }
        "dot_index_expression" | "method_index_expression" => {
            // table.field — use last identifier
            let ids: Vec<&CstNode> = node
                .children
                .iter()
                .filter(|c| c.node_type == "identifier")
                .collect();
            if let Some(last) = ids.last() {
                return last.text_or_empty().to_string();
            }
        }
        _ => {}
    }
    for child in &node.children {
        if child.node_type == "identifier" {
            return child.text_or_empty().to_string();
        }
    }
    node.node_type.clone()
}

fn is_class_like(_node_type: &str) -> bool {
    false // Lua has no built-in class syntax
}

fn is_method_like(node_type: &str) -> bool {
    matches!(
        node_type,
        "function_declaration" | "local_function" | "function_definition"
    )
}

/// Separate a Lua function's declared name from its lexical `local` modifier.
/// The grammar aliases local and global declarations to function_declaration,
/// without exposing the anonymous modifier token as a CST child. Keeping
/// "local add" in the function label breaks stable entity anchoring and makes
/// scoped parameter edits look like unrelated function deletion/addition.
/// An explicit modifier child preserves this meaningful source change with
/// its own precise span, while the callable label remains "add".
///
/// Rehash affected ancestors: the synthetic child was not in the CST hashes
/// returned by the shared converter and must not be silently style-only.
fn retain_local_function_modifier(node: &mut SemanticNode) -> bool {
    let mut changed = false;
    for child in &mut node.children {
        changed |= retain_local_function_modifier(child);
    }

    if matches!(node.node_type.as_str(), "function_declaration" | "local_function") {
        if let Some(name) = node.label.strip_prefix("local ") {
            let name = name.to_string();
            let modifier = SemanticNodeBuilder::new(
                format!("{}.{}", node.id, node.children.len()),
                "declaration_modifier",
                "local",
                node.position.start_line,
                node.position.start_col,
                node.position.start_line,
                node.position.start_col + 5,
                "",
            )
            .build();
            node.label = name;
            node.children.push(modifier);
            changed = true;
        }
    }

    if changed {
        // Keep the ORIGINAL full-CST digest in the new hash input. Computing
        // only from pruned semantic children could erase operator/keyword
        // changes that the CST preserved, incorrectly reporting style-only.
        // This also incorporates the explicit scope modifier and child hashes.
        let source_cst_hash = node.structural_hash.clone();
        node.structural_hash = SemanticNodeBuilder::new(
            node.id.clone(),
            node.node_type.clone(),
            format!("{}|source_cst_hash={source_cst_hash}", node.label),
            node.position.start_line,
            node.position.start_col,
            node.position.end_line,
            node.position.end_col,
            "",
        )
        .children(node.children.clone())
        .build()
        .structural_hash;
    }
    changed
}

fn convert(
    node: &CstNode,
    source: &str,
    id_prefix: &str,
    parent_class: Option<&str>,
    memo: &mut std::collections::HashMap<usize, String>,
) -> Option<SemanticNode> {
    // Lua threads no class context and sets no parent_type.
    let mut semantic = convert_semantic_classed(
        node,
        id_prefix,
        parent_class,
        memo,
        &|t| TRIVIA.contains(&t),
        &is_semantic,
        &|_| false,
        &|_| false,
        &|node| label_for(node, source),
    )?;
    retain_local_function_modifier(&mut semantic);
    Some(semantic)
}



use intentumdiff_plugin_sdk::ts_convert::{convert_semantic_classed, node_to_cst};

fn parse_source(source: &str) -> Result<CstNode, String> {
    let mut parser = tree_sitter::Parser::new();
    let lang = tree_sitter_lua::LANGUAGE.into();
    parser
        .set_language(&lang)
        .map_err(|_| "Failed to load lua grammar".to_string())?;
    let tree = parser
        .parse(source, None)
        .ok_or_else(|| "Parse failed".to_string())?;
    Ok(node_to_cst(tree.root_node(), source.as_bytes()))
}

fn process_impl(source: &str) -> String {
    let root: CstNode = match parse_source(source) {
        Ok(n) => n,
        Err(e) => return format!(r#"{{\"error\":\"{}\"}}"#, e),
    };
    let mut memo: std::collections::HashMap<usize, String> = std::collections::HashMap::new();
    let sem = match convert(&root, source, "0", None, &mut memo) {
        Some(n) => n,
        None => return r#"{"error":"Empty semantic tree"}"#.to_string(),
    };
    match serde_json::to_string(&sem) {
        Ok(s) => s,
        Err(e) => format!(r#"{{"error":"Serialisation error: {}"}}"#, e),
    }
}

impl Guest for LuaParser {
    fn get_parser_mode() -> ParserMode {
        ParserMode::FullParse
    }
    fn grammar_id() -> String {
        "lua".to_string()
    }
    fn detect_language(filename: String, _content: String) -> String {
        if filename.to_lowercase().ends_with(".lua") {
            return "lua".to_string();
        }
        String::new()
    }
    fn preprocess_source(source: String) -> String {
        source
    }
    fn example(_language: String) -> ExamplePair {
        ExamplePair {
            old: "function greet(name)\n    print(\"Hello, \" .. name)\nend\n\nfunction add(a, b)\n    return a + b\nend\n".to_string(),
            new: "local function greet(name)\n    print(string.format(\"Hello, %s!\", name))\nend\n\nlocal function add(x, y)\n    return x + y\nend\n\nlocal function multiply(x, y)\n    return x * y\nend\n".to_string(),
        }
    }
    fn process(input: String, _language: String, _filename: String) -> String {
        process_impl(&input)
    }
    fn trivia_node_types() -> Vec<String> {
        TRIVIA.iter().map(|s| s.to_string()).collect()
    }
    fn language_ids() -> Vec<String> {
        vec!["lua".to_string()]
    }
    fn language_info() -> Vec<LanguageInfoRecord> {
        language_info_for(Self::language_ids())
    }
    fn priority() -> i32 {
        0
    }
}

export!(LuaParser);

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exports::intentdiff::plugin::parser::Guest;
    use intentumdiff_plugin_sdk::testing as t;

    #[test]
    fn grammar_id_nonempty() {
        assert!(!LuaParser::grammar_id().is_empty());
    }

    #[test]
    fn language_ids_contain_grammar_id() {
        let gid = LuaParser::grammar_id();
        let ids = LuaParser::language_ids();
        assert!(
            ids.contains(&gid),
            "language_ids {:?} must contain {:?}",
            ids,
            gid
        );
    }

    #[test]
    fn detect_language_known_ext() {
        let r = LuaParser::detect_language("test.lua".to_string(), "".to_string());
        assert_eq!(r.as_str(), "lua");
    }

    #[test]
    fn detect_language_unknown_ext() {
        let r =
            LuaParser::detect_language("test.xyz_notareal_ext_9z8y".to_string(), "".to_string());
        assert_eq!(r.as_str(), "");
    }

    #[test]
    fn parser_mode_is_full_parse() {
        assert!(matches!(
            LuaParser::get_parser_mode(),
            ParserMode::FullParse
        ));
    }

    #[test]
    fn process_impl_accepts_raw_example_source() {
        let example = LuaParser::example(LuaParser::grammar_id());
        let out = process_impl(&example.old);
        t::assert_valid_json(&out, "process(raw example)");
        assert!(!out.contains("\"error\""), "{out}");
    }
    #[test]
    fn local_function_modifier_changes_semantic_tree() {
        let before = "function greet(name)\n    print(\"Hello, \" .. name)\nend\n";
        let after = "local function greet(name)\n    print(\"Hello, \" .. name)\nend\n";

        let before_tree = process_impl(before);
        let after_tree = process_impl(after);

        t::assert_valid_json(&before_tree, "global function");
        t::assert_valid_json(&after_tree, "local function");
        assert_ne!(before_tree, after_tree, "local modifier must be semantic");

        fn declaration<'a>(tree: &'a serde_json::Value, label: &str) -> Option<&'a serde_json::Value> {
            if matches!(
                tree.get("node_type").and_then(|v| v.as_str()),
                Some("function_declaration" | "local_function")
            ) && tree.get("label").and_then(|v| v.as_str()) == Some(label)
            {
                return Some(tree);
            }
            tree.get("children")
                .and_then(|v| v.as_array())
                .and_then(|children| children.iter().find_map(|child| declaration(child, label)))
        }

        let global: serde_json::Value = serde_json::from_str(&before_tree).unwrap();
        let local: serde_json::Value = serde_json::from_str(&after_tree).unwrap();
        let global_fn = declaration(&global, "greet").expect("global callable name");
        let local_fn = declaration(&local, "greet").expect("local callable has SAME name");

        let modifiers: Vec<&serde_json::Value> = local_fn["children"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|child| child["node_type"] == "declaration_modifier")
            .collect();
        assert_eq!(modifiers.len(), 1, "local scope must not be discarded");
        assert_eq!(modifiers[0]["label"], "local");
        assert_eq!(modifiers[0]["position"]["start_line"], 0);
        assert_eq!(modifiers[0]["position"]["start_col"], 0);
        assert_eq!(modifiers[0]["position"]["end_line"], 0);
        assert_eq!(modifiers[0]["position"]["end_col"], 5);
        assert!(
            global_fn["children"].as_array().unwrap().iter()
                .all(|child| child["node_type"] != "declaration_modifier"),
            "global form must not acquire local scope"
        );
        assert_ne!(
            global_fn["structural_hash"], local_fn["structural_hash"],
            "scope modifier must affect semantic structural hash"
        );
    }

    #[test]
    fn param_rename_and_local_scope_keep_stable_callable_name() {
        let before = process_impl("function add(a, b)\n    return a + b\nend\n");
        let after = process_impl("local function add(x, y)\n    return x + y\nend\n");
        t::assert_valid_json(&before, "global add");
        t::assert_valid_json(&after, "local add with renamed parameters");
        let old: serde_json::Value = serde_json::from_str(&before).unwrap();
        let new: serde_json::Value = serde_json::from_str(&after).unwrap();
        fn callable(tree: &serde_json::Value) -> Option<&serde_json::Value> {
            if tree["node_type"] == "function_declaration" && tree["label"] == "add" {
                return Some(tree);
            }
            tree.get("children").and_then(|v| v.as_array())
                .and_then(|children| children.iter().find_map(callable))
        }
        let old_fn = callable(&old).expect("original callable add");
        let new_fn = callable(&new).expect("continuing callable add");
        assert_ne!(old_fn["structural_hash"], new_fn["structural_hash"]);
        assert!(new_fn["children"].as_array().unwrap().iter().any(
            |child| child["node_type"] == "declaration_modifier" && child["label"] == "local"
        ));
    }

    #[test]
    fn local_function_operator_only_edit_preserves_full_cst_hash_evidence() {
        let plus = process_impl("local function add(a, b)\n    return a + b\nend\n");
        let minus = process_impl("local function add(a, b)\n    return a - b\nend\n");
        t::assert_valid_json(&plus, "local addition");
        t::assert_valid_json(&minus, "local subtraction");
        let before: serde_json::Value = serde_json::from_str(&plus).unwrap();
        let after: serde_json::Value = serde_json::from_str(&minus).unwrap();
        assert_ne!(
            before["structural_hash"], after["structural_hash"],
            "a meaningful operator-only edit under a local declaration must not hash as style"
        );
    }

    #[test]
    fn process_impl_empty_returns_valid_json() {
        let out = process_impl("");
        t::assert_valid_json(&out, "process(empty)");
    }

    #[test]
    fn process_impl_whitespace_returns_valid_json() {
        let out = process_impl("   \n  ");
        t::assert_valid_json(&out, "process(whitespace)");
    }
}
