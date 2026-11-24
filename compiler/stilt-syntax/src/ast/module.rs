//! The views of a module: its file, its header and its items, impl blocks among them.

use super::{
    AstNode, Const, Effect, Fn, GenericList, Path, Syntax, Test, Trait, Type, TypeDecl, after,
    child, children, has, token, tokens,
};
use crate::SyntaxKind::{self, *};
use crate::capability::Capability;
use crate::{SyntaxNode, SyntaxToken};

nodes! {
    /// A source file: a module.
    SourceFile = SOURCE_FILE,
    /// A module header: `module a.b`, with its `without` clauses.
    Header = HEADER,
    /// A `without` clause, of a module header or of a function: `without panic, alloc`.
    Limits = LIMITS,
    /// `use a.b`.
    Use = USE,
    /// An impl block.
    Impl = IMPL,
}

enums! {
    /// An item of a module.
    Item { Use, Fn, TypeDecl, Trait, Const, Test, Impl, Syntax, Effect, }
}

impl SourceFile {
    /// The view of the root of a file's tree.
    pub(crate) fn root(node: SyntaxNode) -> Self {
        debug_assert_eq!(node.kind(), SOURCE_FILE);
        Self(node)
    }

    /// The `module` header, if the file has one.
    #[must_use]
    pub fn header(&self) -> Option<Header> {
        child(&self.0)
    }

    /// The items, in order.
    pub fn items(&self) -> impl Iterator<Item = Item> + use<> {
        children(&self.0)
    }
}

impl Header {
    /// The module's dotted name.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }

    /// The header's `without` clauses, of which program.header-limits allows one.
    pub fn clauses(&self) -> impl Iterator<Item = Limits> + use<> {
        children(&self.0)
    }
}

/// A limit of a `without` clause (program.header-limits).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Limit {
    /// `panic`: no operation that adds the implicit `panic` effect.
    Panic,
    /// `overflow`: no operation that adds the implicit `overflow` effect
    /// (effects.without-overflow).
    Overflow,
    /// `alloc`: no operation that adds the implicit `alloc` effect.
    Alloc,
    /// `div`: no operation that may not end (facts.div).
    Div,
    /// `copy`: no write that copies shared data (facts.copy).
    Copy,
    /// `locks`: no `when`, nor a call of a function that runs one (shared.locks).
    Locks,
    /// A capability: no native that has it, nor a function that does (facts.without).
    Capability(Capability),
    /// `unsafe`: no `unsafe` block in the code it limits (c.without-unsafe).
    Unsafe,
}

impl Limit {
    /// The limit as it is written.
    #[must_use]
    pub fn text(self) -> &'static str {
        match self {
            Limit::Panic => "panic",
            Limit::Overflow => "overflow",
            Limit::Alloc => "alloc",
            Limit::Div => "div",
            Limit::Copy => "copy",
            Limit::Locks => "locks",
            Limit::Capability(c) => c.text(),
            Limit::Unsafe => "unsafe",
        }
    }
}

impl Limits {
    /// The `without` keyword.
    #[must_use]
    pub fn without_token(&self) -> Option<SyntaxToken> {
        token(&self.0, WITHOUT_KW)
    }

    /// The limits the clause names, in order, each with its token.
    pub fn limits(&self) -> impl Iterator<Item = (Limit, SyntaxToken)> + use<> {
        tokens(&self.0).filter_map(|t| {
            let limit = match t.kind() {
                PANIC_KW => Limit::Panic,
                OVERFLOW_KW => Limit::Overflow,
                ALLOC_KW => Limit::Alloc,
                DIV_KW => Limit::Div,
                COPY_KW => Limit::Copy,
                LOCKS_KW => Limit::Locks,
                UNSAFE_KW => Limit::Unsafe,
                kind => Limit::Capability(Capability::of_keyword(kind)?),
            };
            Some((limit, t))
        })
    }
}

impl Use {
    /// The path it imports.
    #[must_use]
    pub fn path(&self) -> Option<Path> {
        child(&self.0)
    }

    /// Whether it is written `meta use`, which imports a module's procedural macros
    /// (macros.meta-use).
    #[must_use]
    pub fn is_meta(&self) -> bool {
        has(&self.0, META_KW)
    }
}

impl Impl {
    /// Its generic parameters, in brackets.
    #[must_use]
    pub fn generic_list(&self) -> Option<GenericList> {
        child(&self.0)
    }

    /// The trait of a trait impl.
    #[must_use]
    pub fn trait_ty(&self) -> Option<Type> {
        if has(&self.0, FOR_KW) {
            child(&self.0)
        } else {
            None
        }
    }

    /// The type the impl is for.
    #[must_use]
    pub fn self_ty(&self) -> Option<Type> {
        if has(&self.0, FOR_KW) {
            after(&self.0, FOR_KW)
        } else {
            child(&self.0)
        }
    }

    /// The `where` clause, if the impl has one (traits.where).
    #[must_use]
    pub fn where_clause(&self) -> Option<super::WhereClause> {
        child(&self.0)
    }

    /// The functions and constants of the impl.
    pub fn members(&self) -> impl Iterator<Item = Item> + use<> {
        children(&self.0).filter(|item| matches!(item, Item::Fn(_) | Item::Const(_)))
    }
}
