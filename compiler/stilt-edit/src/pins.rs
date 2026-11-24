//! Pinned docs (docs.pins, docs.lock-file and docs.stale): the hashes of each declaration's
//! signature and doc, and the lines of `docs.lock` that pin them.

use std::fmt::Write as _;
use std::ops::Range;

use stilt_syntax::ast::{self, AstNode as _};
use stilt_syntax::{Parse, SyntaxKind, SyntaxNode};

use crate::canon::{canonical, hash};
use crate::parts::{Part, parts};

/// A declaration's doc as it is now: its path, the hashes of its signature and of its doc, and
/// where its first line is in its file, which W0002 is reported at.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Doc {
    /// The path of the declaration.
    pub path: String,
    /// The hash of the declaration's signature.
    pub signature: String,
    /// The hash of the declaration's doc.
    pub doc: String,
    /// The bytes of the doc's first line in its file.
    pub first: Range<usize>,
}

/// A line of `docs.lock`: a path and the hashes its doc was pinned with (docs.pins).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Pin {
    /// The path of the declaration.
    pub path: String,
    /// The hash of the signature when the doc was pinned.
    pub signature: String,
    /// The hash of the doc when it was pinned.
    pub doc: String,
}

impl Pin {
    /// The pin of a doc as it is now.
    #[must_use]
    pub fn of(doc: &Doc) -> Self {
        Self {
            path: doc.path.clone(),
            signature: doc.signature.clone(),
            doc: doc.doc.clone(),
        }
    }
}

/// The docs of the declarations of a file whose module is `module`, in its order. A declaration
/// with a syntax error has none (docs.pins).
#[must_use]
pub fn docs(module: &str, parse: &Parse, text: &str) -> Vec<Doc> {
    let root = parse.syntax();
    parts(module, parse, text)
        .iter()
        .filter(|p| !p.body && !p.broken && text[p.extent.clone()].starts_with("///"))
        .filter_map(|part| {
            let node = declaration(&root, part)?;
            let source = &text[part.extent.clone()];
            let whole = canonical(part, source);
            let doc = whole
                .lines()
                .take_while(|l| l.starts_with("///"))
                .collect::<Vec<_>>()
                .join("\n");
            let line = source.find('\n').unwrap_or(source.len());
            Some(Doc {
                path: part.path.clone(),
                signature: hash(&signature(part, &node, text)),
                doc: hash(&doc),
                first: part.extent.start..part.extent.start + line,
            })
        })
        .collect()
}

/// The node of a declaration: the innermost one around its name.
fn declaration(root: &SyntaxNode, part: &Part) -> Option<SyntaxNode> {
    use SyntaxKind as K;
    let at = stilt_syntax::TextSize::try_from(part.name.start).ok()?;
    let token = root.token_at_offset(at).right_biased()?;
    token.parent_ancestors().find(|n| {
        matches!(
            n.kind(),
            K::FN | K::TYPE_DECL | K::TRAIT | K::CONST | K::TEST | K::SYNTAX | K::EFFECT
        )
    })
}

/// The text of a declaration's signature (docs.pinned-texts): its canonical text with no doc, its
/// own or its methods', and with each body it holds written `{}`.
fn signature(part: &Part, node: &SyntaxNode, text: &str) -> String {
    let mut edits: Vec<(Range<usize>, &str)> = Vec::new();
    for token in node
        .descendants_with_tokens()
        .filter_map(stilt_syntax::SyntaxElement::into_token)
        .filter(|t| t.kind() == SyntaxKind::DOC_COMMENT)
    {
        let start = usize::from(token.text_range().start());
        let end = usize::from(token.text_range().end());
        let rest = &text[end..];
        let through = rest.find('\n').map_or(rest.len(), |i| i + 1);
        let blanks = rest[through..]
            .bytes()
            .take_while(|b| matches!(b, b' ' | b'\t'))
            .count();
        edits.push((start..end + through + blanks, ""));
    }
    for body in bodies(node) {
        let range = body.text_range();
        edits.push((usize::from(range.start())..usize::from(range.end()), "{}"));
    }
    edits.sort_by_key(|(range, _)| std::cmp::Reverse(range.start));
    let mut source = text[part.extent.clone()].to_owned();
    for (range, with) in edits {
        let start = range.start.max(part.extent.start) - part.extent.start;
        let end = range.end.min(part.extent.end) - part.extent.start;
        source.replace_range(start..end, with);
    }
    canonical(part, source.trim_start())
}

/// The bodies a declaration holds: its own, the default bodies of a trait's functions and the
/// default values of its constants (traits.trait-constants), or a macro's templates, while its
/// patterns are its signature (macros.syntax-declarations).
fn bodies(node: &SyntaxNode) -> Vec<SyntaxNode> {
    if let Some(s) = ast::Syntax::cast(node.clone()) {
        return s
            .arms()
            .filter_map(|arm| Some(arm.template()?.syntax().clone()))
            .collect();
    }
    let own = |n: &SyntaxNode| -> Option<SyntaxNode> {
        match n.kind() {
            SyntaxKind::FN => Some(ast::Fn::cast(n.clone())?.body()?.syntax().clone()),
            SyntaxKind::TEST => Some(ast::Test::cast(n.clone())?.body()?.syntax().clone()),
            SyntaxKind::CONST => Some(ast::Const::cast(n.clone())?.value()?.syntax().clone()),
            _ => None,
        }
    };
    match ast::Trait::cast(node.clone()) {
        Some(tr) => tr.members().filter_map(|m| own(m.syntax())).collect(),
        None => own(node).into_iter().collect(),
    }
}

/// The pins that the text of a `docs.lock` holds. A line of another form pins nothing
/// (docs.lock-file).
#[must_use]
pub fn read_lock(text: &str) -> Vec<Pin> {
    let hash = |s: &str| {
        let digits = s.strip_prefix('#')?;
        let valid = digits.len() == 4
            && digits
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b));
        valid.then(|| digits.to_owned())
    };
    text.lines()
        .filter_map(|line| {
            let mut fields = line.rsplitn(3, ' ');
            let doc = hash(fields.next()?)?;
            let signature = hash(fields.next()?)?;
            let path = fields.next().filter(|p| !p.is_empty())?;
            Some(Pin {
                path: path.to_owned(),
                signature,
                doc,
            })
        })
        .collect()
}

/// The text of a `docs.lock` that holds `pins`: a line for each, sorted by the bytes of their
/// paths (docs.lock-file).
#[must_use]
pub fn write_lock(pins: &[Pin]) -> String {
    let mut sorted = pins.to_vec();
    sorted.sort();
    let mut text = String::new();
    for p in sorted {
        let _ = writeln!(text, "{} #{} #{}", p.path, p.signature, p.doc);
    }
    text
}

/// Whether a doc is stale, as its pin gives it: its signature changed and its doc didn't
/// (docs.stale).
#[must_use]
pub fn is_stale(doc: &Doc, pin: &Pin) -> bool {
    pin.signature != doc.signature && pin.doc == doc.doc
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The signature's text and the doc's of each declaration with a doc.
    fn texts(text: &str) -> Vec<String> {
        let parse = stilt_syntax::parse(text);
        let root = parse.syntax();
        parts("main", &parse, text)
            .iter()
            .filter(|p| !p.body && text[p.extent.clone()].starts_with("///"))
            .map(|p| signature(p, &declaration(&root, p).expect("a declaration"), text))
            .collect()
    }

    #[test]
    fn signatures_leave_out_docs_and_bodies() {
        let text = "/// The weight.\n/// ex: weight(1) == 2\nfn weight(o: i64) -> i64 { o * 2 }\n\n\
            /// A shape.\ntrait Shape {\n  /// Its area.\n  fn area(self) -> f64 { 0.0 }\n  \
            fn name(self) -> str\n}\n\n/// A limit.\nconst LIMIT: i64 = 10\n\n/// A test.\n\
            test \"adds\" { assert 1 + 1 == 2 }\n";
        assert_eq!(
            texts(text),
            [
                "fn weight(o: i64) -> i64 {}",
                "trait Shape {\n  fn area(self) -> f64 {}\n  fn name(self) -> str\n}",
                "fn area(self) -> f64 {}",
                "const LIMIT: i64 = {}",
                "test \"adds\" {}",
            ]
        );
    }

    /// A macro's signature is its arms' patterns: its templates are its bodies
    /// (macros.syntax-declarations).
    #[test]
    fn a_macro_signature_leaves_out_its_templates() {
        let text = "/// Swaps two places.\nsyntax swap {\n  ($a: name, $b: name) => \
            { let t = $a; $a = $b; $b = t }\n}\n";
        assert_eq!(
            texts(text),
            ["syntax swap {\n  ($a: name, $b: name) => {}\n}"]
        );
    }

    #[test]
    fn docs_hash_their_lines() {
        let text = "/// The weight.\nfn weight(o: i64) -> i64 { o * 2 }\n";
        let found = docs("main", &stilt_syntax::parse(text), text);
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].path, "main.weight");
        assert_eq!(found[0].doc, hash("/// The weight."));
        assert_eq!(found[0].signature, hash("fn weight(o: i64) -> i64 {}"));
        assert_eq!(found[0].first, 0..15);
    }

    #[test]
    fn locks_round_trip() {
        let text =
            "main.weight #3c2e #a91f\nmain.\"a b\" #0000 #ffff\nnot a pin\nmain.x #12 #3456\n";
        let pins = read_lock(text);
        assert_eq!(pins.len(), 2);
        assert_eq!(pins[1].path, "main.\"a b\"");
        assert_eq!(
            write_lock(&pins),
            "main.\"a b\" #0000 #ffff\nmain.weight #3c2e #a91f\n"
        );
    }
}
