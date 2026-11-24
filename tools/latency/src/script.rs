//! The edit script: edits of a project's files that a person makes while working, each
//! followed by the edit that undoes it, so that the project ends as it began.

use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::{SyntaxKind, SyntaxNode};

/// What an edit changes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Kind {
    /// A statement added to a function's body, or taken away.
    Body,
    /// A statement that can panic added to a body, or taken away, which changes the body's
    /// implicit effects (facts.implicit-effects) and nothing else of the program.
    Panic,
    /// A statement with a type error added to a body, or taken away.
    BodyError,
    /// A parameter added to a function, or taken away, which its callers must give.
    Signature,
    /// A variant added to the variant type of the module that the most modules import, or
    /// taken away, which every `match` over it must cover: the edit with the most dependents.
    Type,
    /// A function added to a module, or taken away.
    Item,
}

impl Kind {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::Body => "body",
            Self::Panic => "panic",
            Self::BodyError => "body error",
            Self::Signature => "signature",
            Self::Type => "type",
            Self::Item => "item",
        }
    }

    /// Whether the edit changes only one body, which then is the only one checked again (goal
    /// body-edits-recheck-one-body).
    pub(crate) fn in_body(self) -> bool {
        matches!(self, Self::Body | Self::Panic | Self::BodyError)
    }
}

/// An edit: the whole new text of one of the project's files.
#[derive(Clone, Debug)]
pub(crate) struct Edit {
    pub(crate) kind: Kind,
    pub(crate) file: usize,
    pub(crate) text: String,
}

/// A deterministic generator of numbers (splitmix64), so that a seed names one script.
struct Random(u64);

impl Random {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        let n = u64::try_from(n).expect("a count fits in 64 bits");
        usize::try_from(self.next() % n).expect("below a count")
    }
}

/// The functions of a file that have a block, with their parameter lists.
fn functions(text: &str) -> Vec<ast::Fn> {
    let tree = stilt_syntax::parse(text).tree();
    tree.items()
        .filter_map(|item| match item {
            ast::Item::Fn(f) if matches!(f.body(), Some(ast::FnBody::Block(_))) => Some(f),
            _ => None,
        })
        .filter(|f| f.name().is_none_or(|n| n.syntax().text() != "main"))
        .collect()
}

fn token_offset(node: &SyntaxNode, kind: SyntaxKind, last: bool) -> Option<usize> {
    let mut tokens = node
        .descendants_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|t| t.kind() == kind);
    let token = if last { tokens.last() } else { tokens.next() }?;
    let range = token.text_range();
    Some(usize::from(if last { range.start() } else { range.end() }))
}

fn insert(text: &str, at: usize, inserted: &str) -> String {
    format!("{}{inserted}{}", &text[..at], &text[at..])
}

/// The text of `f`'s file with `statement` first in its body.
fn with_statement(text: &str, f: &ast::Fn, statement: &str) -> Option<String> {
    let Some(ast::FnBody::Block(block)) = f.body() else {
        return None;
    };
    let at = token_offset(block.syntax(), SyntaxKind::L_CURLY, false)?;
    Some(insert(text, at, &format!("\n  {statement}\n")))
}

/// The text of `f`'s file with a parameter added to it.
fn with_parameter(text: &str, f: &ast::Fn) -> Option<String> {
    let list = f.param_list()?;
    let at = token_offset(list.syntax(), SyntaxKind::R_PAREN, true)?;
    let empty = list.self_param().is_none() && list.params().next().is_none();
    Some(insert(
        text,
        at,
        if empty { "extra: i64" } else { ", extra: i64" },
    ))
}

/// The text of a file with a variant added to its first variant type.
fn with_variant(text: &str) -> Option<String> {
    let tree = stilt_syntax::parse(text).tree();
    let list = tree.items().find_map(|item| match item {
        ast::Item::TypeDecl(t) => match t.def()? {
            ast::TypeDef::VariantList(list) => Some(list),
            ast::TypeDef::RecordDef(_) => None,
        },
        _ => None,
    })?;
    let at = usize::from(list.syntax().text_range().end());
    Some(insert(text, at, " | Extra"))
}

/// The file whose module the most `use` declarations import, among those `edit` accepts.
fn most_imported(
    texts: &[String],
    modules: &[String],
    edit: impl Fn(&str) -> Option<String>,
) -> Option<(usize, String)> {
    let imports = |module: &str| {
        let line = format!("use {module}");
        texts
            .iter()
            .flat_map(|t| t.lines())
            .filter(|l| l.trim() == line)
            .count()
    };
    (0..texts.len())
        .filter_map(|i| edit(&texts[i]).map(|t| (imports(&modules[i]), i, t)))
        .max_by_key(|(n, i, _)| (*n, std::cmp::Reverse(*i)))
        .map(|(_, i, t)| (i, t))
}

/// An edit of `kind` to the file `text`, at a function the generator picks.
fn edit(kind: Kind, text: &str, random: &mut Random) -> Option<String> {
    match kind {
        Kind::Item => return Some(format!("{text}\nfn added() -> i64 {{\n  1\n}}\n")),
        Kind::Type => return with_variant(text),
        _ => {}
    }
    let fns = functions(text);
    if fns.is_empty() {
        return None;
    }
    let f = &fns[random.below(fns.len())];
    match kind {
        Kind::Body => with_statement(text, f, "let _ = 0"),
        Kind::Panic => with_statement(text, f, "assert true"),
        Kind::BodyError => with_statement(text, f, "let _: bool = 0"),
        Kind::Signature => with_parameter(text, f),
        Kind::Item | Kind::Type => unreachable!("they are edited above"),
    }
}

/// A script of `pairs` edits to the files `texts`, whose modules have the dotted names
/// `modules`, each edit followed by its undoing. The kinds of edit take turns.
pub(crate) fn script(texts: &[String], modules: &[String], pairs: usize, seed: u64) -> Vec<Edit> {
    const KINDS: [Kind; 6] = [
        Kind::Body,
        Kind::Signature,
        Kind::Panic,
        Kind::BodyError,
        Kind::Item,
        Kind::Type,
    ];
    let mut random = Random(seed);
    let mut edits = Vec::new();
    let mut tries = 0;
    while edits.len() < 2 * pairs && tries < 100 * pairs {
        tries += 1;
        let kind = KINDS[(edits.len() / 2) % KINDS.len()];
        let picked = if kind == Kind::Type {
            most_imported(texts, modules, with_variant)
        } else {
            let file = random.below(texts.len());
            edit(kind, &texts[file], &mut random).map(|text| (file, text))
        };
        if let Some((file, text)) = picked {
            edits.push(Edit { kind, file, text });
            let undo = texts[file].clone();
            edits.push(Edit {
                kind,
                file,
                text: undo,
            });
        }
    }
    edits
}
