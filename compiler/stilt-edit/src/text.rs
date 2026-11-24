//! Whether a new text is the part it replaces (edits.new-text).

use stilt_syntax::{LineIndex, SyntaxKind, SyntaxNode, TextSize, parse};

use crate::canon::{Wrapper, body, declaration};
use crate::parts::{Kind, Part, Place, parts};

/// The first syntax error of a new text, as errors.syntax-errors finds it, counted within the text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Syntax {
    /// The code of the error.
    pub code: String,
    /// What the error says, which the JSON form of an edit leaves out.
    pub message: String,
    /// The line of the error, from 1.
    pub line: u32,
    /// The column of the error, from 1.
    pub col: u32,
}

/// Checks that `text` parses as exactly one instance of the part `part` stands for, with
/// nothing else around it but blank lines.
///
/// # Errors
///
/// `Err(Some(error))` with the text's first syntax error, and `Err(None)` when the text parses
/// but is not the part.
pub fn check_text(part: &Part, text: &str) -> Result<(), Option<Syntax>> {
    let wrapper = wrapper(part);
    let whole = format!("{}{text}{}", wrapper.before, wrapper.after);
    let tree = parse(&whole);
    if let Some(error) = tree.error() {
        let at = usize::from(error.range.start())
            .saturating_sub(wrapper.before.len())
            .min(text.len());
        let position = LineIndex::new(text).position(text, offset(text, at));
        return Err(Some(Syntax {
            code: error.code.as_str().to_owned(),
            message: error.message.clone(),
            line: position.line,
            col: position.col,
        }));
    }
    if !one_item(&tree.syntax(), part) {
        return Err(None);
    }
    let found = parts("m", &tree, &whole);
    let Some(wanted) = found
        .iter()
        .find(|p| p.body == part.body && p.kind == part.kind)
    else {
        return Err(None);
    };
    let end = whole.len() - wrapper.after.len();
    let at = &wanted.extent;
    let blank = |s: &str| s.chars().all(char::is_whitespace);
    let around = at.start >= wrapper.before.len()
        && at.end <= end
        && blank(&whole[wrapper.before.len()..at.start])
        && blank(&whole[at.end..end]);
    if around { Ok(()) } else { Err(None) }
}

/// Whether the tree holds one item, or one member in the impl or trait that the wrapper makes,
/// of the kind of `part`'s declaration, and no more.
fn one_item(root: &SyntaxNode, part: &Part) -> bool {
    let mut items = root.children();
    let (Some(item), None) = (items.next(), items.next()) else {
        return false;
    };
    let kind_ok = |n: &SyntaxNode| match part.kind {
        Kind::Fn => n.kind() == SyntaxKind::FN,
        Kind::Type => n.kind() == SyntaxKind::TYPE_DECL,
        Kind::Trait => n.kind() == SyntaxKind::TRAIT,
        Kind::Const => n.kind() == SyntaxKind::CONST,
        Kind::Test => n.kind() == SyntaxKind::TEST,
        Kind::Macro => n.kind() == SyntaxKind::SYNTAX,
        Kind::Effect => n.kind() == SyntaxKind::EFFECT,
    };
    if part.body || part.place == Place::Item {
        return kind_ok(&item);
    }
    let mut members = item
        .children()
        .filter(|n| matches!(n.kind(), SyntaxKind::FN | SyntaxKind::CONST));
    matches!((members.next(), members.next()), (Some(m), None) if kind_ok(&m))
}

fn wrapper(part: &Part) -> Wrapper {
    if part.body {
        body(part.kind)
    } else {
        declaration(&part.place)
    }
}

fn offset(text: &str, at: usize) -> TextSize {
    debug_assert!(at <= text.len());
    TextSize::from(u32::try_from(at).unwrap_or(u32::MAX))
}
