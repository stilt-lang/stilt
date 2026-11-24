//! The views of macros (macros.syntax-declarations and macros.patterns): a declaration, its arms,
//! patterns and templates, and a use.

use super::{AstNode, Docs, Name, Path, child, children, has, token};
use crate::SyntaxKind::{self, *};
use crate::{SyntaxElement, SyntaxNode, SyntaxToken};

nodes! {
    /// A `syntax` declaration.
    Syntax = SYNTAX,
    /// An arm of a declaration: a pattern, an optional trailing block and a template.
    MacroArm = MACRO_ARM,
    /// A group, `( … )`, `[ … ]` or `{ … }`, of a pattern, a template or a use.
    MacroGroup = MACRO_GROUP,
    /// A fragment, `$name: kind` in a pattern and `$name` in a template.
    MacroFrag = MACRO_FRAG,
    /// A repetition, `$( … ) sep op`.
    MacroRep = MACRO_REP,
    /// A separator inside a group.
    MacroSep = MACRO_SEP,
    /// A template.
    Template = TEMPLATE,
    /// A use where an expression stands.
    MacroUse = MACRO_USE,
    /// A use where a pattern stands.
    MacroPat = MACRO_PAT,
}

impl Syntax {
    /// The doc comments before the declaration.
    #[must_use]
    pub fn docs(&self) -> Option<Docs> {
        child(&self.0)
    }

    /// Whether the declaration is written `pub`.
    #[must_use]
    pub fn is_pub(&self) -> bool {
        has(&self.0, PUB_KW)
    }

    /// The macro's name.
    #[must_use]
    pub fn name(&self) -> Option<Name> {
        child(&self.0)
    }

    /// The arms, in order.
    pub fn arms(&self) -> impl Iterator<Item = MacroArm> + use<> {
        children(&self.0)
    }
}

impl MacroArm {
    /// The pattern's group.
    #[must_use]
    pub fn pattern(&self) -> Option<MacroGroup> {
        child(&self.0)
    }

    /// The trailing block, `$name: block`, if the arm has one.
    #[must_use]
    pub fn trailing(&self) -> Option<MacroFrag> {
        child(&self.0)
    }

    /// The template after `=>`.
    #[must_use]
    pub fn template(&self) -> Option<Template> {
        child(&self.0)
    }
}

/// An element of a group, a repetition or a template.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MacroElem {
    /// A token matched by itself, or written as it is.
    Token(SyntaxToken),
    /// A separator: a `;`, or a newline that ends a statement.
    Sep(MacroSep),
    /// A group in brackets.
    Group(MacroGroup),
    /// A fragment, `$name: form`, or its use in a template.
    Frag(MacroFrag),
    /// A repetition, `$( … ) sep op`.
    Rep(MacroRep),
}

/// The elements of a node's children, without trivia and without the brackets of a group.
fn elements(node: &SyntaxNode, brackets: bool) -> Vec<MacroElem> {
    let mut out: Vec<MacroElem> = node
        .children_with_tokens()
        .filter_map(|element| match element {
            // A `;` that separates is in a `MACRO_SEP`: one standing alone is one the separator
            // rules drop (lexical.separators), and no token (syntax.token-classes).
            SyntaxElement::Token(t) if t.kind().is_trivia() || t.kind() == SEMICOLON => None,
            SyntaxElement::Token(t) => Some(MacroElem::Token(t)),
            SyntaxElement::Node(n) => match n.kind() {
                MACRO_SEP => Some(MacroElem::Sep(MacroSep(n))),
                MACRO_GROUP => Some(MacroElem::Group(MacroGroup(n))),
                MACRO_FRAG => Some(MacroElem::Frag(MacroFrag(n))),
                MACRO_REP => Some(MacroElem::Rep(MacroRep(n))),
                _ => None,
            },
        })
        .collect();
    if brackets {
        let is_bracket = |e: &MacroElem| {
            matches!(e, MacroElem::Token(t) if matches!(
                t.kind(),
                L_PAREN | R_PAREN | L_BRACK | R_BRACK | L_CURLY | R_CURLY
            ))
        };
        if out.first().is_some_and(is_bracket) {
            out.remove(0);
        }
        if out.last().is_some_and(is_bracket) {
            out.pop();
        }
    }
    out
}

/// The bracket a group is written with.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Bracket {
    /// `( … )`.
    Paren,
    /// `[ … ]`.
    Square,
    /// `{ … }`.
    Curly,
}

impl MacroGroup {
    /// The group's bracket.
    #[must_use]
    pub fn bracket(&self) -> Bracket {
        let open = self
            .0
            .children_with_tokens()
            .find_map(|e| e.into_token().filter(|t| !t.kind().is_trivia()));
        match open.map(|t| t.kind()) {
            Some(L_BRACK) => Bracket::Square,
            Some(L_CURLY) => Bracket::Curly,
            _ => Bracket::Paren,
        }
    }

    /// The opening bracket.
    #[must_use]
    pub fn open(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .find_map(|e| e.into_token().filter(|t| !t.kind().is_trivia()))
    }

    /// The closing bracket, absent from a group with a syntax error.
    #[must_use]
    pub fn close(&self) -> Option<SyntaxToken> {
        let last = self
            .0
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .filter(|t| !t.kind().is_trivia())
            .last()?;
        let open = self.open()?;
        (last != open && matches!(last.kind(), R_PAREN | R_BRACK | R_CURLY)).then_some(last)
    }

    /// The elements between the brackets.
    #[must_use]
    pub fn elements(&self) -> Vec<MacroElem> {
        elements(&self.0, true)
    }
}

impl MacroFrag {
    /// The `$`.
    #[must_use]
    pub fn dollar(&self) -> Option<SyntaxToken> {
        token(&self.0, DOLLAR)
    }

    /// The fragment's name.
    #[must_use]
    pub fn name(&self) -> Option<SyntaxToken> {
        token(&self.0, LOWER_IDENT)
    }

    /// The kind written after the `:`, in a pattern.
    #[must_use]
    pub fn kind(&self) -> Option<SyntaxToken> {
        self.0
            .children_with_tokens()
            .filter_map(rowan::NodeOrToken::into_token)
            .skip_while(|t| t.kind() != COLON)
            .find(|t| matches!(t.kind(), LOWER_IDENT | UPPER_IDENT | TYPE_KW))
    }
}

/// A repetition's operator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RepOp {
    /// `*`, zero or more.
    Star,
    /// `+`, one or more.
    Plus,
}

impl MacroRep {
    /// The `$`.
    #[must_use]
    pub fn dollar(&self) -> Option<SyntaxToken> {
        token(&self.0, DOLLAR)
    }

    /// The group it repeats.
    #[must_use]
    pub fn group(&self) -> Option<MacroGroup> {
        child(&self.0)
    }

    /// The separator, `,` or `;`, if there is one.
    #[must_use]
    pub fn separator(&self) -> Option<SeparatorKind> {
        if has(&self.0, COMMA) {
            Some(SeparatorKind::Comma)
        } else if child::<MacroSep>(&self.0).is_some() {
            Some(SeparatorKind::Semicolon)
        } else {
            None
        }
    }

    /// `+` or `*`.
    #[must_use]
    pub fn op(&self) -> RepOp {
        if has(&self.0, PLUS) {
            RepOp::Plus
        } else {
            RepOp::Star
        }
    }
}

/// A repetition's separator.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SeparatorKind {
    /// `,`.
    Comma,
    /// `;`.
    Semicolon,
}

impl Template {
    /// The template's items.
    #[must_use]
    pub fn elements(&self) -> Vec<MacroElem> {
        elements(&self.0, false)
    }
}

impl MacroUse {
    /// The macro's path.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }

    /// The group, and the trailing block if there is one.
    pub fn groups(&self) -> impl Iterator<Item = MacroGroup> + use<> {
        children(&self.0)
    }
}

impl MacroPat {
    /// The macro's path.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }

    /// Its tokens, in brackets.
    #[must_use]
    pub fn group(&self) -> Option<MacroGroup> {
        child(&self.0)
    }
}
