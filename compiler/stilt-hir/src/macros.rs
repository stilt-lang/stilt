//! Pattern macros (macros.syntax-declarations): each declaration read into arms of matchers and
//! templates, with the errors of its patterns and templates (macros.patterns and macros.templates),
//! which uses in any module read to match and expand (macros.uses and macros.matching).
//!
//! A module's macros are a query of their own, read from its syntax alone, so that an edit that
//! leaves them as they were leaves the modules that use them unresolved again.

mod checks;
pub(crate) mod matching;
pub(crate) mod substitute;

use std::sync::Arc;

use stilt_db::{Db, SourceFile};
use stilt_diag::Diagnostic;
use stilt_syntax::ast::{self, AstNode, Bracket, MacroElem, RepOp, SeparatorKind};
use stilt_syntax::{SyntaxKind, SyntaxToken, TextRange};

use crate::hir::Name;

/// The kind of a fragment (macros.patterns).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FragKind {
    /// `expr`.
    Expr,
    /// `block`.
    Block,
    /// `pattern`.
    Pattern,
    /// `type`.
    Type,
    /// `name`, a lowercase identifier.
    Lower,
    /// `Name`, an uppercase identifier.
    Upper,
}

impl FragKind {
    /// The kind a word names, if it names one.
    #[must_use]
    pub fn of(word: &str) -> Option<Self> {
        Some(match word {
            "expr" => Self::Expr,
            "block" => Self::Block,
            "pattern" => Self::Pattern,
            "type" => Self::Type,
            "name" => Self::Lower,
            "Name" => Self::Upper,
            _ => return None,
        })
    }

    /// Whether a fragment of the kind stands in parentheses in an expansion, so that it stays
    /// one form (macros.expansion).
    #[must_use]
    pub fn parenthesized(self) -> bool {
        matches!(self, Self::Expr | Self::Pattern | Self::Type)
    }
}

/// A repetition, of matchers or of a template's items.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rep<T> {
    /// The separator, `,` or `;`, as a token kind, if there is one.
    pub sep: Option<SyntaxKind>,
    /// Whether it is `+`, one or more, rather than `*`.
    pub plus: bool,
    /// The items it repeats.
    pub items: Vec<T>,
    /// Its `$`.
    pub at: TextRange,
}

/// A matcher of a pattern (macros.patterns).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Matcher {
    /// A token, matched by itself: its kind and text.
    Token(SyntaxKind, Name),
    /// A fragment: its name, its kind if the word names one, and where it is written.
    Frag(Name, Option<FragKind>, TextRange),
    /// A repetition.
    Rep(Rep<Matcher>),
    /// A group, with its bracket.
    Group(Bracket, Vec<Matcher>),
}

/// An item of a template (macros.templates).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TItem {
    /// A token written as it is, and where.
    Token(SyntaxKind, Name, TextRange),
    /// A fragment, `$name`, and where it is written.
    Frag(Name, TextRange),
    /// A repetition.
    Rep(Rep<TItem>),
    /// A group, with its brackets' places.
    Group(Bracket, Vec<TItem>, TextRange, TextRange),
}

/// An arm of a macro.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MacroArm {
    /// The bracket of the pattern's group.
    pub bracket: Bracket,
    /// The matchers inside the pattern's group.
    pub pattern: Vec<Matcher>,
    /// The trailing block's fragment, if the arm takes one: its name, its kind if the word
    /// names one, and where its name and its kind are written.
    pub trailing: Option<(Name, Option<FragKind>, (TextRange, TextRange))>,
    /// The template's items.
    pub template: Vec<TItem>,
    /// The template's place in its file, and its text on one line, which notes show.
    pub at: TextRange,
    /// The template's text on one line.
    pub text: String,
}

impl MacroArm {
    /// The kind of each fragment the pattern binds, by name, the trailing block's included.
    #[must_use]
    pub fn kinds(&self) -> Vec<(Name, FragKind)> {
        fn walk(ms: &[Matcher], out: &mut Vec<(Name, FragKind)>) {
            for m in ms {
                match m {
                    Matcher::Frag(name, Some(kind), _) => out.push((*name, *kind)),
                    Matcher::Rep(rep) => walk(&rep.items, out),
                    Matcher::Group(_, items) => walk(items, out),
                    Matcher::Token(..) | Matcher::Frag(..) => {}
                }
            }
        }
        let mut out = Vec::new();
        walk(&self.pattern, &mut out);
        if let Some((name, Some(kind), _)) = &self.trailing {
            out.push((*name, *kind));
        }
        out
    }
}

/// A macro: its arms, and what its templates are (macros.checked-templates).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MacroDef {
    /// Its name.
    pub name: Name,
    /// Its arms, in order.
    pub arms: Vec<MacroArm>,
    /// Whether every template is an expression, so that the macro stands where an expression
    /// does, and whether every one is a pattern.
    pub expr: bool,
    /// Whether every template is a pattern, so that it stands where a pattern does.
    pub pattern: bool,
    /// Whether its declaration has an error, so that its uses report nothing more
    /// (errors.declarations-with-errors).
    pub broken: bool,
}

impl MacroDef {
    /// Where a template first writes a token of this text, if one does.
    #[must_use]
    pub fn written(&self, text: &str) -> Option<TextRange> {
        fn find(items: &[TItem], text: &str) -> Option<TextRange> {
            items.iter().find_map(|item| match item {
                TItem::Token(_, t, at) if &**t == text => Some(*at),
                TItem::Rep(rep) => find(&rep.items, text),
                TItem::Group(_, inner, ..) => find(inner, text),
                TItem::Token(..) | TItem::Frag(..) => None,
            })
        }
        self.arms.iter().find_map(|arm| find(&arm.template, text))
    }
}

/// The macros a file declares, each with the errors of its declaration.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MacroDefs {
    /// Each macro, with the errors of its declaration, in source order.
    pub defs: Vec<(Arc<MacroDef>, Vec<Diagnostic>)>,
}

impl MacroDefs {
    /// The first macro of this name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&Arc<MacroDef>> {
        self.defs
            .iter()
            .map(|(def, _)| def)
            .find(|def| &*def.name == name)
    }
}

/// The macros of a file, read from its syntax.
#[salsa::tracked(returns(ref))]
pub fn macro_defs(db: &dyn Db, file: SourceFile) -> MacroDefs {
    let tree = stilt_db::parse(db, file).tree();
    let defs = tree
        .items()
        .filter_map(|item| match item {
            ast::Item::Syntax(s) => Some(read(&s)),
            _ => None,
        })
        .map(|(def, errors)| (Arc::new(def), errors))
        .collect();
    MacroDefs { defs }
}

/// A declaration's macro and the errors of its patterns and templates (macros.patterns,
/// macros.templates and macros.checked-templates).
pub(crate) fn read(s: &ast::Syntax) -> (MacroDef, Vec<Diagnostic>) {
    let arms: Vec<MacroArm> = s.arms().filter_map(|arm| read_arm(&arm)).collect();
    let mut errors = Vec::new();
    let (mut expr, mut pattern) = (true, true);
    for arm in &arms {
        let (is_expr, is_pattern) = checks::check_arm(arm, &mut errors);
        expr &= is_expr;
        pattern &= is_pattern;
    }
    let def = MacroDef {
        name: Name::from(s.name().map(|n| n.text()).unwrap_or_default()),
        arms,
        expr,
        pattern,
        broken: !errors.is_empty(),
    };
    (def, errors)
}

fn read_arm(arm: &ast::MacroArm) -> Option<MacroArm> {
    let group = arm.pattern()?;
    let template = arm.template()?;
    let trailing = arm.trailing().and_then(|f| {
        let name = f.name()?;
        let word = f.kind();
        let kind = word.as_ref().and_then(|k| FragKind::of(k.text()));
        let kind_at = word.map_or(name.text_range(), |k| k.text_range());
        Some((Name::from(name.text()), kind, (name.text_range(), kind_at)))
    });
    let items: Vec<TItem> = template.elements().iter().map(template_item).collect();
    let text = template
        .syntax()
        .text()
        .to_string()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    Some(MacroArm {
        bracket: group.bracket(),
        pattern: group.elements().iter().map(matcher).collect(),
        trailing,
        template: items,
        at: first_to_end(template.syntax()),
        text,
    })
}

/// The span of a node from its first token that isn't trivia.
fn first_to_end(node: &stilt_syntax::SyntaxNode) -> TextRange {
    let start = node
        .descendants_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .find(|t| !t.kind().is_trivia())
        .map_or(node.text_range().start(), |t| t.text_range().start());
    TextRange::new(start, node.text_range().end())
}

fn token(t: &SyntaxToken) -> (SyntaxKind, Name) {
    (t.kind(), Name::from(t.text()))
}

fn rep_of<T>(r: &ast::MacroRep, item: impl Fn(&MacroElem) -> T) -> Rep<T> {
    Rep {
        sep: r.separator().map(|s| match s {
            SeparatorKind::Comma => SyntaxKind::COMMA,
            SeparatorKind::Semicolon => SyntaxKind::SEP,
        }),
        plus: r.op() == RepOp::Plus,
        items: r
            .group()
            .map(|g| g.elements())
            .unwrap_or_default()
            .iter()
            .map(item)
            .collect(),
        at: r
            .dollar()
            .map_or(r.syntax().text_range(), |d| d.text_range()),
    }
}

fn matcher(e: &MacroElem) -> Matcher {
    match e {
        MacroElem::Token(t) => {
            let (kind, text) = token(t);
            Matcher::Token(kind, text)
        }
        MacroElem::Sep(_) => Matcher::Token(SyntaxKind::SEP, Name::from(";")),
        MacroElem::Group(g) => {
            Matcher::Group(g.bracket(), g.elements().iter().map(matcher).collect())
        }
        MacroElem::Frag(f) => Matcher::Frag(
            Name::from(f.name().map(|n| n.text().to_owned()).unwrap_or_default()),
            f.kind().and_then(|k| FragKind::of(k.text())),
            first_to_end(f.syntax()),
        ),
        MacroElem::Rep(r) => Matcher::Rep(rep_of(r, matcher)),
    }
}

fn template_item(e: &MacroElem) -> TItem {
    match e {
        MacroElem::Token(t) => {
            let (kind, text) = token(t);
            TItem::Token(kind, text, t.text_range())
        }
        MacroElem::Sep(s) => {
            TItem::Token(SyntaxKind::SEP, Name::from(";"), s.syntax().text_range())
        }
        MacroElem::Group(g) => {
            let open = g.open().map_or(g.syntax().text_range(), |t| t.text_range());
            let close = g.close().map_or(open, |t| t.text_range());
            TItem::Group(
                g.bracket(),
                g.elements().iter().map(template_item).collect(),
                open,
                close,
            )
        }
        MacroElem::Frag(f) => TItem::Frag(
            Name::from(f.name().map(|n| n.text().to_owned()).unwrap_or_default()),
            first_to_end(f.syntax()),
        ),
        MacroElem::Rep(r) => TItem::Rep(rep_of(r, template_item)),
    }
}

/// The text of a bracket, opening or closing.
#[must_use]
pub fn bracket_text(bracket: Bracket, open: bool) -> (SyntaxKind, &'static str) {
    use SyntaxKind::{L_BRACK, L_CURLY, L_PAREN, R_BRACK, R_CURLY, R_PAREN};
    match (bracket, open) {
        (Bracket::Paren, true) => (L_PAREN, "("),
        (Bracket::Paren, false) => (R_PAREN, ")"),
        (Bracket::Square, true) => (L_BRACK, "["),
        (Bracket::Square, false) => (R_BRACK, "]"),
        (Bracket::Curly, true) => (L_CURLY, "{"),
        (Bracket::Curly, false) => (R_CURLY, "}"),
    }
}
