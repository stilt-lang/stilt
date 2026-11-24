//! The files that other parts of the repository take from the Reference's lexical, syntax and
//! facts chapters: the tables of words and tokens of both lexers, the editors' grammars and the
//! manifest's schema. `sources` writes them, and with `--check` fails if one isn't what the
//! Reference gives; either way it fails if a list that the guide or the design documents restate
//! in their prose isn't the Reference's ([`copies`]).

use std::fs;
use std::path::Path;

use crate::lexical::{self, Lexical};
use crate::{copies, facts, textmate, treesitter, treesitter_queries, treesitter_scanner};

/// The lexical chapter, whose lists the files restate.
pub(crate) const LEXICAL: &str = "reference/02-lexical.md";

/// The chapter whose table of precedence the tree-sitter grammar follows.
pub(crate) const EXPRESSIONS: &str = "reference/08-expressions.md";

/// The chapters' lists, read from the repository at `root`.
pub(crate) fn read(root: &Path) -> Result<Lexical, String> {
    let text = |path: &str| fs::read_to_string(root.join(path)).map_err(|e| format!("{path}: {e}"));
    lexical::read(&text(LEXICAL)?, &text(crate::GRAMMAR)?)
}

/// Each file, as its path from the repository's root and its text, with the editor grammar's
/// template read from `root`.
pub(crate) fn files(root: &Path, lexical: &Lexical) -> Result<Vec<(&'static str, String)>, String> {
    let template = fs::read_to_string(root.join(textmate::TEMPLATE))
        .map_err(|e| format!("{}: {e}", textmate::TEMPLATE))?;
    let text = |path: &str| fs::read_to_string(root.join(path)).map_err(|e| format!("{path}: {e}"));
    let tree_sitter = treesitter::emit(&text(crate::GRAMMAR)?, lexical, &text(EXPRESSIONS)?)?;
    let lists = copies::read(root, lexical)?;
    Ok(vec![
        (crate::rust::PATH, crate::rust::emit(lexical)?),
        (crate::ocaml::PATH, crate::ocaml::emit(lexical)?),
        (textmate::PATH, textmate::emit(&template, lexical)?),
        (textmate::CONTROL_PATH, textmate::control()?),
        (
            treesitter_queries::PATH,
            treesitter_queries::emit(&tree_sitter),
        ),
        (
            treesitter_queries::ZED_PATH,
            treesitter_queries::emit_zed(&tree_sitter),
        ),
        (treesitter::GRAMMAR, tree_sitter),
        (treesitter_scanner::PATH, treesitter_scanner::emit(lexical)),
        (
            facts::PATH,
            facts::emit(&facts::read(&text(facts::CHAPTER)?)?),
        ),
        (
            copies::SCHEMA,
            copies::schema(&text(copies::SCHEMA)?, &lists)?,
        ),
    ])
}

/// Writes the files under `root`, or with `check` fails at the first that differs.
pub(crate) fn write(root: &Path, check: bool) -> Result<(), String> {
    let lexical = read(root)?;
    copies::check(root, &copies::read(root, &lexical)?)?;
    for (path, text) in files(root, &lexical)? {
        let file = root.join(path);
        if fs::read_to_string(&file).ok().as_deref() == Some(&text) {
            continue;
        }
        if check {
            return Err(format!(
                "{path} is not what the Reference gives; run `just grammar-generate`"
            ));
        }
        if let Some(dir) = file.parent() {
            fs::create_dir_all(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        }
        fs::write(&file, text).map_err(|e| format!("{path}: {e}"))?;
    }
    Ok(())
}

/// The tokens, longest first, each length in the order given, as maximal munch tries them.
pub(crate) fn longest_first<'a>(tokens: &[&'a str]) -> Vec<&'a str> {
    let mut sorted = tokens.to_vec();
    sorted.sort_by_key(|t| std::cmp::Reverse(t.len()));
    sorted
}
