//! The parts of a file: its declarations and their bodies, each with a path (edits.parts and
//! edits.paths) and the span of its source text.

use std::ops::Range;

use stilt_syntax::ast::{self, AstNode as _, Item};
use stilt_syntax::{Parse, SyntaxKind, SyntaxNode, sexp, text::string_value};

/// What a declaration is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    /// A function.
    Fn,
    /// A type.
    Type,
    /// A trait.
    Trait,
    /// A constant.
    Const,
    /// A test.
    Test,
    /// A macro (macros.syntax-declarations), whose templates are inside it, and which has no body
    /// part.
    Macro,
    /// An effect (handlers.declaring-effect), whose operations are inside it, and which has no body
    /// part.
    Effect,
}

/// Where a declaration stands, which decides the grammar its text is read in (edits.new-text).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Place {
    /// At module level: an `item`.
    Item,
    /// In an inherent impl for the type constructor `T`: an `inherent_member`.
    Inherent(String),
    /// In the impl of the trait `Tr` for `T`: a `trait_impl_member`.
    TraitImpl {
        /// The trait.
        tr: String,
        /// The type it is implemented for.
        ty: String,
    },
    /// In the trait `Tr`: a `trait_member`, a function or a constant.
    TraitMember(String),
}

/// A declaration of a module, or the body of one (edits.parts).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Part {
    /// The declaration's path (edits.paths), the body's too.
    pub path: String,
    /// Whether the part is the declaration's body.
    pub body: bool,
    /// The kind of the declaration.
    pub kind: Kind,
    /// Where the declaration stands.
    pub place: Place,
    /// The part's source text: its extent in the file, bytes (edits.extents).
    pub extent: Range<usize>,
    /// Where the declaration writes its name, in the file.
    pub name: Range<usize>,
    /// Whether the declaration has a syntax error, so that its hash covers its source text
    /// exactly as written and it has no body (edits.files-with-syntax-errors).
    pub broken: bool,
    /// The index, among the parts, of the declaration: this part's own index for a declaration.
    pub decl: usize,
}

impl Part {
    /// The address of the part without a hash: its path, with `/body` for a body.
    #[must_use]
    pub fn address(&self) -> String {
        if self.body {
            format!("{}/body", self.path)
        } else {
            self.path.clone()
        }
    }
}

/// The parts of a file whose module is `module`, in the order of the file: each declaration
/// before its body, and a trait before its methods. `text` is the text that `parse` parsed.
#[must_use]
pub fn parts(module: &str, parse: &Parse, text: &str) -> Vec<Part> {
    let mut found = Vec::new();
    for item in parse.tree().items() {
        match item {
            Item::Fn(n) => declare(&mut found, module, n.syntax(), Place::Item, text),
            Item::TypeDecl(n) => declare(&mut found, module, n.syntax(), Place::Item, text),
            Item::Const(n) => declare(&mut found, module, n.syntax(), Place::Item, text),
            Item::Test(n) => declare(&mut found, module, n.syntax(), Place::Item, text),
            Item::Syntax(n) => declare(&mut found, module, n.syntax(), Place::Item, text),
            Item::Effect(n) => declare(&mut found, module, n.syntax(), Place::Item, text),
            Item::Trait(n) => {
                declare(&mut found, module, n.syntax(), Place::Item, text);
                let name = n.name().map(|n| n.text());
                // A trait's functions and constants (traits.trait-constants).
                for member in n.members() {
                    let place = Place::TraitMember(name.clone().unwrap_or_default());
                    declare(&mut found, module, member.syntax(), place, text);
                }
            }
            Item::Impl(n) => {
                let ty = n.self_ty().and_then(|t| constructor(&t));
                let tr = n.trait_ty().and_then(|t| constructor(&t));
                let place = match (ty, tr) {
                    (Some(ty), Some(tr)) => Place::TraitImpl { tr, ty },
                    (Some(ty), None) => Place::Inherent(ty),
                    _ => continue,
                };
                for member in n.members() {
                    declare(&mut found, module, member.syntax(), place.clone(), text);
                }
            }
            Item::Use(_) => {}
        }
    }
    for held in parse.held() {
        let held = usize::from(held.start())..usize::from(held.end());
        reach_past_errors(&mut found, &held, text);
    }
    found
}

/// The part that a part of the file with a syntax error (`held`) declares, which runs to the
/// end of that text, its blank lines and lines that are only a comment left out, so that a
/// lexical error's tokens, which the tree doesn't hold, are in it too
/// (edits.files-with-syntax-errors). It is broken, and has no body.
fn reach_past_errors(found: &mut Vec<Part>, held: &Range<usize>, text: &str) {
    // The declaration that the text begins with: another one inside it, as a member of an impl
    // whose header has the error, is left as it is.
    let begins = |p: &Part| {
        !p.body
            && held.contains(&p.extent.start)
            && text[held.start..p.extent.start].trim().is_empty()
    };
    let Some(i) = found.iter().position(begins) else {
        return;
    };
    let end = last_line_end(text, held);
    let part = &mut found[i];
    part.broken = true;
    part.extent.end = part.extent.end.max(end);
    if found.get(i + 1).is_some_and(|p| p.body && p.decl == i) {
        found.remove(i + 1);
        for p in &mut found[i + 1..] {
            p.decl -= usize::from(p.decl > i);
        }
    }
}

/// The end of the last line of `range` that isn't blank or only a comment, without its blanks.
fn last_line_end(text: &str, range: &Range<usize>) -> usize {
    let mut end = range.start;
    let mut at = range.start;
    for line in text[range.clone()].split_inclusive('\n') {
        let kept = line.trim_end();
        let alone = kept.trim_start();
        let comment = alone.starts_with("//") && !alone.starts_with("///");
        if !alone.is_empty() && !comment {
            end = at + kept.len();
        }
        at += line.len();
    }
    end
}

/// The last name of a type constructor or trait as an impl writes it (edits.paths).
fn constructor(ty: &ast::Type) -> Option<String> {
    let ast::Type::NamedType(named) = ty else {
        return None;
    };
    named.path()?.segments().last().map(|t| t.text().to_owned())
}

/// Adds the declaration `node` and its body.
fn declare(found: &mut Vec<Part>, module: &str, node: &SyntaxNode, place: Place, text: &str) {
    let Some((kind, name, at)) = identify(node) else {
        return;
    };
    let path = match &place {
        Place::Item => format!("{module}.{name}"),
        Place::Inherent(ty) => format!("{module}.{ty}.{name}"),
        Place::TraitImpl { tr, ty } => format!("{module}.{ty}.{tr}.{name}"),
        Place::TraitMember(tr) => format!("{module}.{tr}.{name}"),
    };
    let broken = node.descendants().any(|n| n.kind() == SyntaxKind::ERROR);
    let decl = found.len();
    found.push(Part {
        path: path.clone(),
        body: false,
        kind,
        place: place.clone(),
        extent: extent(node, text),
        name: at.clone(),
        broken,
        decl,
    });
    if let Some(body) = body_node(node).filter(|_| !broken) {
        found.push(Part {
            path,
            body: true,
            kind,
            place,
            extent: extent(&body, text),
            name: at,
            broken: false,
            decl,
        });
    }
}

/// The kind and name of a declaration, as its path writes the name, and where it is written.
fn identify(node: &SyntaxNode) -> Option<(Kind, String, Range<usize>)> {
    use SyntaxKind as K;
    let named = |n: Option<ast::Name>| {
        let n = n.filter(|n| !n.text().is_empty())?;
        Some((n.text(), span(n.syntax())))
    };
    let (kind, (name, at)) = match node.kind() {
        K::FN => (Kind::Fn, named(ast::Fn::cast(node.clone())?.name())?),
        K::TYPE_DECL => (
            Kind::Type,
            named(ast::TypeDecl::cast(node.clone())?.name())?,
        ),
        K::TRAIT => (Kind::Trait, named(ast::Trait::cast(node.clone())?.name())?),
        K::CONST => (Kind::Const, named(ast::Const::cast(node.clone())?.name())?),
        K::SYNTAX => (Kind::Macro, named(ast::Syntax::cast(node.clone())?.name())?),
        K::EFFECT => (
            Kind::Effect,
            named(ast::Effect::cast(node.clone())?.name())?,
        ),
        K::TEST => {
            let name = ast::Test::cast(node.clone())?.name()?;
            let at = usize::from(name.text_range().start())..usize::from(name.text_range().end());
            (Kind::Test, (sexp::quote(&string_value(&name)), at))
        }
        _ => return None,
    };
    Some((kind, name, at))
}

fn span(node: &SyntaxNode) -> Range<usize> {
    usize::from(node.text_range().start())..usize::from(node.text_range().end())
}

/// The node of a declaration's body.
fn body_node(node: &SyntaxNode) -> Option<SyntaxNode> {
    use SyntaxKind as K;
    match node.kind() {
        K::FN => Some(ast::Fn::cast(node.clone())?.body()?.syntax().clone()),
        K::TEST => Some(ast::Test::cast(node.clone())?.body()?.syntax().clone()),
        K::CONST => Some(ast::Const::cast(node.clone())?.value()?.syntax().clone()),
        _ => None,
    }
}

/// The extent of a node (edits.extents): from its first doc comment or token to its last token, and
/// the comment that follows the last token on its line.
fn extent(node: &SyntaxNode, text: &str) -> Range<usize> {
    let mut start = None;
    let mut end = 0;
    for token in node
        .descendants_with_tokens()
        .filter_map(rowan_token)
        .filter(|t| {
            !matches!(
                t.kind(),
                SyntaxKind::WHITESPACE | SyntaxKind::NEWLINE | SyntaxKind::COMMENT
            ) && !t.text().is_empty()
        })
    {
        start.get_or_insert(usize::from(token.text_range().start()));
        end = usize::from(token.text_range().end());
    }
    let start = start.unwrap_or(end);
    start..trailing_comment(text, end)
}

fn rowan_token(e: stilt_syntax::SyntaxElement) -> Option<stilt_syntax::SyntaxToken> {
    e.into_token()
}

/// The end of the comment that follows `end` on its line, or `end`.
fn trailing_comment(text: &str, end: usize) -> usize {
    let rest = &text[end..];
    let line = rest.find('\n').unwrap_or(rest.len());
    let line = &rest[..line];
    let after = line.trim_start_matches([' ', '\t']);
    if after.starts_with("//") && !after.starts_with("///") {
        end + line.len()
    } else {
        end
    }
}

/// The smallest part that holds the span `at` (edits.diagnostic-addresses): a body when the span
/// lies in one, and otherwise the innermost declaration. A span lies in a part when it starts
/// there.
#[must_use]
pub fn smallest(parts: &[Part], at: usize) -> Option<&Part> {
    parts
        .iter()
        .filter(|p| p.extent.start <= at && at < p.extent.end.max(p.extent.start + 1))
        .min_by_key(|p| p.extent.len())
}
