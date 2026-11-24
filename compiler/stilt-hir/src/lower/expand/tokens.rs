//! A use's tokens, each where the user sees it (macros.matching and macros.errors-in-expansions).

use stilt_syntax::ast::{self, AstNode, MacroElem};
use stilt_syntax::{SyntaxKind, SyntaxToken, TextRange};

use super::super::Resolver;
use crate::hir::Name;
use crate::macros::bracket_text;
use crate::macros::matching::UseTokens;
use crate::macros::substitute::Tok;

impl Resolver<'_> {
    /// The tokens of a use's groups, brackets included: its group's, then its trailing
    /// block's.
    pub(super) fn use_tokens(&self, groups: &[ast::MacroGroup]) -> UseTokens {
        let mut tokens = Vec::new();
        let mut group_end = 0;
        for (i, g) in groups.iter().enumerate() {
            self.group_tokens(g, &mut tokens);
            if i == 0 {
                group_end = tokens.len().saturating_sub(1);
            }
        }
        UseTokens::new(tokens, group_end)
    }

    fn group_tokens(&self, g: &ast::MacroGroup, out: &mut Vec<Tok>) {
        let fallback = self.in_file(g.syntax().text_range());
        let (open_kind, open_text) = bracket_text(g.bracket(), true);
        match g.open() {
            Some(t) => out.push(self.tok(&t)),
            None => out.push(self.made(open_kind, open_text, fallback)),
        }
        for e in g.elements() {
            match e {
                MacroElem::Token(t) => out.push(self.tok(&t)),
                MacroElem::Sep(s) => {
                    let at = self.in_file(s.syntax().text_range());
                    out.push(self.made(SyntaxKind::SEP, ";", at));
                }
                MacroElem::Group(inner) => self.group_tokens(&inner, out),
                // A use holds no fragment or repetition, which only a declaration's patterns
                // and templates write, and its file then has a syntax error.
                MacroElem::Frag(f) => out.push(self.made(
                    SyntaxKind::DOLLAR,
                    "$",
                    self.in_file(f.syntax().text_range()),
                )),
                MacroElem::Rep(r) => out.push(self.made(
                    SyntaxKind::DOLLAR,
                    "$",
                    self.in_file(r.syntax().text_range()),
                )),
            }
        }
        let (close_kind, close_text) = bracket_text(g.bracket(), false);
        if let Some(t) = g.close() {
            out.push(self.tok(&t));
        } else {
            let end = TextRange::empty(fallback.end());
            out.push(self.made(close_kind, close_text, end));
        }
    }

    pub(super) fn tok(&self, t: &SyntaxToken) -> Tok {
        self.made(t.kind(), t.text(), self.in_file(t.text_range()))
    }

    /// A token of the code being resolved, at `range` there.
    pub(super) fn made(&self, kind: SyntaxKind, text: &str, range: TextRange) -> Tok {
        let (at, user) = self.placed(range);
        Tok {
            kind,
            text: Name::from(text),
            at,
            user,
            mark: self.mark_of(range),
        }
    }
}
