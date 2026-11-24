//! The views of names and paths.

use super::{AstNode, tokens};
use crate::SyntaxKind::{self, *};
use crate::{SyntaxNode, SyntaxToken};

nodes! {
    /// A path: names separated by dots.
    Path = PATH,
    /// A name that a declaration or a binding introduces.
    Name = NAME,
    /// A name that refers to something declared elsewhere.
    NameRef = NAME_REF,
}

impl Path {
    /// The names of the path, `Self` included.
    pub fn segments(&self) -> impl Iterator<Item = SyntaxToken> + use<> {
        tokens(&self.0).filter(|t| matches!(t.kind(), LOWER_IDENT | UPPER_IDENT | SELF_TYPE_KW))
    }

    /// The names of the path joined by dots.
    #[must_use]
    pub fn text(&self) -> String {
        self.segments()
            .map(|t| t.text().to_owned())
            .collect::<Vec<_>>()
            .join(".")
    }
}

impl Name {
    /// The identifier.
    #[must_use]
    pub fn ident(&self) -> Option<SyntaxToken> {
        tokens(&self.0).find(|t| matches!(t.kind(), LOWER_IDENT | UPPER_IDENT))
    }

    /// The identifier's text, or the empty string.
    #[must_use]
    pub fn text(&self) -> String {
        self.ident()
            .map(|t| t.text().to_owned())
            .unwrap_or_default()
    }
}

impl NameRef {
    /// The identifier.
    #[must_use]
    pub fn ident(&self) -> Option<SyntaxToken> {
        tokens(&self.0).find(|t| matches!(t.kind(), LOWER_IDENT | UPPER_IDENT))
    }

    /// The identifier's text, or the empty string.
    #[must_use]
    pub fn text(&self) -> String {
        self.ident()
            .map(|t| t.text().to_owned())
            .unwrap_or_default()
    }
}
