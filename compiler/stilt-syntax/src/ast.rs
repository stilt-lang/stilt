//! Typed views of the syntax tree. Each node type wraps a node of one kind, and each enum
//! wraps a node of one of several kinds. Accessors return `None` where a tree with syntax
//! errors lacks a part.

use crate::SyntaxKind::{self, *};
use crate::{SyntaxNode, SyntaxToken};

/// A typed view of a node.
pub trait AstNode: Sized {
    /// The view of `node`, if it has the right kind.
    fn cast(node: SyntaxNode) -> Option<Self>;
    /// The node viewed.
    fn syntax(&self) -> &SyntaxNode;
}

macro_rules! nodes {
    ($($(#[$doc:meta])* $name:ident = $kind:ident,)*) => {$(
        $(#[$doc])*
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        // The node is visible to the views of every section, whose enums wrap one another's.
        pub struct $name(pub(super) SyntaxNode);

        impl $name {
            /// The kind of the nodes this type views.
            pub const KIND: SyntaxKind = $kind;
        }

        impl AstNode for $name {
            fn cast(node: SyntaxNode) -> Option<Self> {
                (node.kind() == $kind).then(|| Self(node))
            }

            fn syntax(&self) -> &SyntaxNode {
                &self.0
            }
        }
    )*};
}

macro_rules! enums {
    ($($(#[$doc:meta])* $name:ident { $($variant:ident,)* })*) => {$(
        $(#[$doc])*
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        pub enum $name {
            $(#[allow(missing_docs)] $variant($variant),)*
        }

        impl AstNode for $name {
            fn cast(node: SyntaxNode) -> Option<Self> {
                match node.kind() {
                    $(k if k == $variant::KIND => Some(Self::$variant($variant(node))),)*
                    _ => None,
                }
            }

            fn syntax(&self) -> &SyntaxNode {
                match self {
                    $(Self::$variant(n) => n.syntax(),)*
                }
            }
        }
    )*};
}

// The views of each section of the grammar, which the macros above declare.
mod control;
mod decls;
mod docs;
mod effects;
mod exprs;
mod generics;
mod macros;
mod module;
mod paths;
mod patterns;
mod quotes;
mod stmts;
mod types;

pub use self::control::*;
pub use self::decls::*;
pub use self::docs::*;
pub use self::effects::*;
pub use self::exprs::*;
pub use self::generics::*;
pub use self::macros::*;
pub use self::module::*;
pub use self::paths::*;
pub use self::patterns::*;
pub use self::quotes::*;
pub use self::stmts::*;
pub use self::types::*;

fn child<N: AstNode>(node: &SyntaxNode) -> Option<N> {
    node.children().find_map(N::cast)
}

fn children<N: AstNode>(node: &SyntaxNode) -> impl Iterator<Item = N> + use<N> {
    node.children().filter_map(N::cast)
}

fn nth<N: AstNode>(node: &SyntaxNode, n: usize) -> Option<N> {
    children(node).nth(n)
}

fn tokens(node: &SyntaxNode) -> impl Iterator<Item = SyntaxToken> + use<> {
    node.children_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
}

fn token(node: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxToken> {
    tokens(node).find(|t| t.kind() == kind)
}

fn has(node: &SyntaxNode, kind: SyntaxKind) -> bool {
    token(node, kind).is_some()
}

/// The first node after the token of kind `after` that `N` views.
fn after<N: AstNode>(node: &SyntaxNode, after: SyntaxKind) -> Option<N> {
    node.children_with_tokens()
        .skip_while(|e| e.kind() != after)
        .filter_map(rowan::NodeOrToken::into_node)
        .find_map(N::cast)
}

/// A parameter's mode (values.passing-values).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Mode {
    /// No mode written.
    Let,
    /// `inout`.
    Inout,
}

fn mode(node: &SyntaxNode) -> Mode {
    if has(node, INOUT_KW) {
        Mode::Inout
    } else {
        Mode::Let
    }
}
