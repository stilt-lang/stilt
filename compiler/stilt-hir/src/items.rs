//! What a module declares, without signatures, bodies or positions: all that its scope and
//! other modules' scopes need, so that an edit inside a declaration leaves it unchanged.

use stilt_db::{Db, SourceFile};
use stilt_syntax::ast::{self, AstNode};
use stilt_syntax::text::string_value;
use stilt_syntax::{SyntaxKind, SyntaxNode};

use crate::hir::Name;

/// The items of a module, in source order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ItemTree {
    /// The items, in source order.
    pub items: Vec<ItemSummary>,
}

/// An item of a module, as its scope reads it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ItemSummary {
    /// `use` with the names of its path.
    Use(Vec<Name>),
    /// `meta use` with the names of its path (macros.meta-use).
    MetaUse(Vec<Name>),
    /// A declaration.
    Decl {
        /// Whether it is written `pub`.
        is_pub: bool,
        /// What it declares.
        kind: DeclSummary,
        /// Whether a part with a syntax error declares only its name, so that every use of
        /// the name has the error type (errors.broken-parts).
        unknown: bool,
    },
    /// An impl block, which declares no name.
    Impl,
}

/// What a declaration declares, as its module's scope reads it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DeclSummary {
    /// A function.
    Fn(Name),
    /// A constant.
    Const(Name),
    /// A type, with its number of type parameters, whether the last is a pack (variadics.packs,
    /// variadics.packs), its variants, and its value parameters (generics.value-parameters).
    Type {
        /// Its name.
        name: Name,
        /// Its number of type parameters.
        arity: u32,
        /// Whether its last type parameter is a pack.
        pack: bool,
        /// Its variants' names.
        variants: Vec<Name>,
        /// Its value parameters.
        values: ValueParams,
    },
    /// A trait, with its shape.
    Trait(Name, TraitShape),
    /// A test, by its name.
    Test(String),
    /// A macro, in the value namespace (macros.syntax-declarations).
    Macro(Name),
    /// A procedural macro, in the value namespace (macros.procedural-declarations).
    Proc(Name),
    /// An effect, in the type namespace, with its number of type parameters
    /// (handlers.declaring-effect).
    Effect(Name, u32),
}

/// The value parameters of a type, which other modules need to read the arguments written for them
/// (generics.value-arguments): each one's place among the type's parameters and the type written
/// for it, as its name when it is a primitive type name, and otherwise empty, an error of the
/// declaration (generics.value-parameters).
pub type ValueParams = Vec<(u32, Name)>;

/// What other modules need of a trait to resolve the bounds and impls that name it, read from its
/// syntax alone (traits.trait-parameters and traits.constructor-traits): its parameters' names, and
/// the number of type arguments its `Self` takes, that of the first `Self` written with arguments,
/// or 0 for a trait over types.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct TraitShape {
    pub params: Vec<Name>,
    pub arity: u32,
}

impl TraitShape {
    /// The shape of a trait's declaration.
    #[must_use]
    pub fn of(t: &ast::Trait) -> Self {
        let arity = t
            .syntax()
            .descendants()
            .filter_map(ast::NamedType::cast)
            .find_map(|n| {
                let path = n.path()?;
                let mut segments = path.segments();
                let first = segments.next()?;
                let applied = first.kind() == SyntaxKind::SELF_TYPE_KW && segments.next().is_none();
                let args = n.args().count();
                (applied && args > 0).then(|| u32::try_from(args).unwrap_or(u32::MAX))
            })
            .unwrap_or(0);
        Self {
            params: t.params().map(|p| name(p.name())).collect(),
            arity,
        }
    }
}

/// The items of a file.
#[salsa::tracked(returns(ref))]
pub fn item_tree(db: &dyn Db, file: SourceFile) -> ItemTree {
    let tree = stilt_db::parse(db, file).tree();
    ItemTree {
        items: tree.items().map(|item| summary(&item)).collect(),
    }
}

fn summary(item: &ast::Item) -> ItemSummary {
    let unknown = only_named(item.syntax());
    let decl = |is_pub, kind| ItemSummary::Decl {
        is_pub,
        kind,
        unknown,
    };
    match item {
        ast::Item::Use(u) => {
            let path = u
                .path()
                .into_iter()
                .flat_map(|p| p.segments())
                .map(|t| Name::from(t.text()))
                .collect();
            if u.is_meta() {
                ItemSummary::MetaUse(path)
            } else {
                ItemSummary::Use(path)
            }
        }
        ast::Item::Impl(_) => ItemSummary::Impl,
        ast::Item::Fn(f) if f.is_macro() => decl(f.is_pub(), DeclSummary::Proc(name(f.name()))),
        ast::Item::Fn(f) => decl(f.is_pub(), DeclSummary::Fn(name(f.name()))),
        ast::Item::Const(c) => decl(c.is_pub(), DeclSummary::Const(name(c.name()))),
        ast::Item::Trait(t) => decl(
            t.is_pub(),
            DeclSummary::Trait(name(t.name()), TraitShape::of(t)),
        ),
        ast::Item::TypeDecl(t) => {
            let variants = match t.def() {
                Some(ast::TypeDef::VariantList(list)) => {
                    list.variants().map(|v| name(v.name())).collect()
                }
                Some(ast::TypeDef::RecordDef(_)) | None => Vec::new(),
            };
            let arity = u32::try_from(t.params().count()).unwrap_or(u32::MAX);
            decl(
                t.is_pub(),
                DeclSummary::Type {
                    name: name(t.name()),
                    arity,
                    pack: t.params().last().is_some_and(|p| p.is_pack()),
                    variants,
                    values: value_params(t),
                },
            )
        }
        ast::Item::Syntax(s) => decl(s.is_pub(), DeclSummary::Macro(name(s.name()))),
        ast::Item::Effect(e) => {
            let arity = u32::try_from(e.params().count()).unwrap_or(u32::MAX);
            decl(e.is_pub(), DeclSummary::Effect(name(e.name()), arity))
        }
        ast::Item::Test(t) => decl(
            false,
            DeclSummary::Test(t.name().map(|n| string_value(&n)).unwrap_or_default()),
        ),
    }
}

/// The value parameters of a type declaration, each with the primitive type name written for it.
fn value_params(t: &ast::TypeDecl) -> ValueParams {
    (0..)
        .zip(t.params())
        .filter_map(|(i, p)| match p {
            ast::Generic::ValueParam(v) => Some((i, primitive_name(v.ty()))),
            _ => None,
        })
        .collect()
}

/// The name of a type written as a bare primitive type name, and otherwise the empty name.
pub(crate) fn primitive_name(t: Option<ast::Type>) -> Name {
    let named = match t {
        Some(ast::Type::NamedType(n)) if n.args().next().is_none() => n.path(),
        _ => None,
    };
    let segments: Vec<_> = named.into_iter().flat_map(|p| p.segments()).collect();
    match segments.as_slice() {
        [one] if crate::scope::is_primitive(one.text()) => Name::from(one.text()),
        _ => Name::default(),
    }
}

/// Whether a part with a syntax error declares only the name of the declaration or member of `node`
/// (errors.broken-parts): a function without its parameters, a constant without its type, a type, a
/// trait without its block, or a macro (macros.syntax-declarations). Every use of the name has the
/// error type.
pub(crate) fn only_named(node: &SyntaxNode) -> bool {
    let recovered = node.children().any(|c| c.kind() == SyntaxKind::ERROR);
    match node.kind() {
        // A function whose head broke before its parameters' `(`, where the parser may still
        // leave an empty list, or inside its result, whose signature then isn't whole.
        SyntaxKind::FN => {
            recovered
                && ast::Fn::cast(node.clone()).is_some_and(|f| {
                    let no_params = f.param_list().is_none_or(|l| {
                        !l.syntax()
                            .children_with_tokens()
                            .any(|e| e.kind() == SyntaxKind::L_PAREN)
                    });
                    let broken_result = f.ret_type().is_some_and(|r| {
                        r.ty().is_none()
                            || r.syntax()
                                .descendants()
                                .any(|c| c.kind() == SyntaxKind::ERROR)
                    });
                    no_params || broken_result
                })
        }
        // A trait whose head broke before its block's `{`, so that the parser read no member.
        SyntaxKind::TRAIT
            if node
                .children_with_tokens()
                .take_while(|e| e.kind() != SyntaxKind::L_CURLY)
                .any(|e| e.kind() == SyntaxKind::ERROR) =>
        {
            true
        }
        _ => {
            recovered
                && match node.kind() {
                    SyntaxKind::CONST => {
                        ast::Const::cast(node.clone()).is_some_and(|c| c.ty().is_none())
                    }
                    SyntaxKind::TYPE_DECL | SyntaxKind::SYNTAX | SyntaxKind::EFFECT => true,
                    SyntaxKind::TRAIT => !node
                        .children_with_tokens()
                        .any(|e| e.kind() == SyntaxKind::L_CURLY),
                    _ => false,
                }
        }
    }
}

/// A declared name, empty where a tree with syntax errors lacks it.
pub(crate) fn name(name: Option<ast::Name>) -> Name {
    Name::from(name.map(|n| n.text()).unwrap_or_default())
}
