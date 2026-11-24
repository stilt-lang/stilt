//! The views of a module (views.std-view and views.show; projections.declaring-projection and
//! projections.show): whether it names a view type or declares or calls a projection, which puts it
//! in the advanced tier (program.tiers and program.module-tier), and for each function, the sources
//! that each binding of a view type reads, or writes for a writable binding, and the parameters
//! that its result views or writes, which `stilt show` prints.

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::body_starts;
use stilt_hir::decls::{TypeDefInfo, declarations};
use stilt_hir::hir::{self, Name};
use stilt_syntax::TextRange;

use crate::analyses::views::sources::Source;
use crate::analyses::views::{Place, Sources};
use crate::queries::{infer_body, module_info};
use crate::tast::walk::{self, Part};
use crate::tast::{Block, Code, Definition, Expr, ExprKind, StmtKind, TypedBody};
use crate::ty::{Ty, is_view_type};

/// A view that a function's body binds, or gives as its result, with what it reads, or writes
/// (projections.show).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Viewing {
    /// Where it is in its file: the pattern that binds it, or the expression returned.
    pub at: TextRange,
    /// The binding, or `None` for the function's result.
    pub binding: Option<Name>,
    /// The variables of the sources it reads, each once, in the order they are found: for the
    /// result, the parameters it views.
    pub sources: Vec<Name>,
    /// Whether it writes its sources: a writable binding, or a result that writes `inout`
    /// parameters (projections.what-view-writes and projections.results-that-write).
    pub writes: bool,
}

/// The views of the body `index` of a file's module that read a source, in the order of the
/// body: each binding of a view type, a closure that captures one among them (views.fixed), and
/// each expression that gives the function a result that views a parameter (views.across-calls). A
/// body with an error has none (facts.bodies-with-errors).
#[must_use]
pub fn views(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Vec<Viewing> {
    let body = &infer_body(db, program, file, index).body;
    let Definition::Code(Code::Block(block)) = &body.code else {
        return Vec::new();
    };
    let start = body_starts(db, program, file)[index as usize];
    let found = Sources::of(body, block);
    let named = |places: &[Place]| -> Vec<Name> {
        let mut names: Vec<Name> = Vec::new();
        for p in places {
            let name = &body.locals[p.root.0 as usize];
            if !names.contains(name) {
                names.push(*name);
            }
        }
        names
    };
    let places = |sources: &[Source]| -> Vec<Place> {
        sources.iter().filter_map(|s| s.place().cloned()).collect()
    };
    let mut views: Vec<Viewing> = found
        .bindings()
        .filter_map(|(v, at)| {
            let sources = named(&places(found.of_binding(v)?));
            (!sources.is_empty()).then(|| Viewing {
                at: at + start,
                binding: Some(body.locals[v.0 as usize]),
                sources,
                writes: found.is_writable(v),
            })
        })
        .collect();
    let mut returned = Vec::new();
    results(block, true, &mut returned);
    for e in returned {
        let params: Vec<Source> = found
            .sources(e)
            .into_iter()
            .filter(|p| found.allowed(p))
            .collect();
        for writes in [false, true] {
            let these: Vec<Source> = params
                .iter()
                .filter(|p| p.reads() != writes)
                .cloned()
                .collect();
            if !these.is_empty() {
                views.push(Viewing {
                    at: e.at + start,
                    binding: None,
                    sources: named(&places(&these)),
                    writes,
                });
            }
        }
    }
    views.sort_by_key(|v| v.at.start());
    views
}

/// The expressions that give a function its result: each `return`'s value, and the value of
/// its block's last statement when `tail`, through the blocks and branches that give it, not
/// counting those of closures, whose results are theirs. A projection's signature says what
/// it yields, and nothing more is shown for it (projections.show).
fn results<'a>(b: &'a Block, tail: bool, out: &mut Vec<&'a Expr>) {
    for (i, s) in b.iter().enumerate() {
        for e in walk::stmt_exprs(s) {
            returns(e, out);
        }
        if let StmtKind::Expr(e) = &s.kind
            && tail
            && i + 1 == b.len()
        {
            leaves(e, out);
        }
    }
}

/// The values of the `return`s inside an expression, outside its closures.
fn returns<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match &e.kind {
        ExprKind::Return(Some(v)) => leaves(v, out),
        ExprKind::Closure(..) => return,
        _ => {}
    }
    for part in walk::parts(e) {
        match part {
            Part::Expr(x) => returns(x, out),
            Part::Block(b) => results(b, false, out),
        }
    }
}

/// The expressions that give the value of `e`, through its blocks and branches.
fn leaves<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    let tail = |b: &'a Block, out: &mut Vec<&'a Expr>| {
        if let Some(StmtKind::Expr(x)) = b.last().map(|s| &s.kind) {
            leaves(x, out);
        }
    };
    match &e.kind {
        ExprKind::Block(b) => tail(b, out),
        ExprKind::If(_, b, alt) | ExprKind::IfLet(_, _, b, alt) => {
            tail(b, out);
            if let Some(a) = alt {
                leaves(a, out);
            }
        }
        ExprKind::Match(_, arms) => arms.iter().for_each(|a| leaves(&a.body, out)),
        ExprKind::Else(a, b) => {
            leaves(a, out);
            leaves(b, out);
        }
        _ => out.push(e),
    }
}

/// A file's module's tier: the first tier that allows every feature it uses (program.module-tier),
/// `advanced` for a module that names a view type (views.std-view), declares or calls a projection
/// (projections.declaring-projection), uses a trait with parameters, a trait function without
/// `self`, a trait constant or a constructor trait other than by calling its methods
/// (traits.advanced-tier), writes a polymorphic function type or names `Lazy`
/// (polymorphism.advanced-tier and polymorphism.lazy-values), or writes an anonymous or open
/// record's form or declares a pack (records.advanced-tier; variadics.advanced-tier), declares a
/// macro (macros.advanced-tier), or uses effects, handlers or tasks (handlers.advanced-tier;
/// tasks.advanced-tier), `meta` for a module that declares a value parameter (generics.meta-tier),
/// writes `comptime` (meta.staging-tier), names `std.meta` or writes a bound test
/// (meta.reflection-tier), or declares a procedural macro or writes a quote (macros.meta-tier), and
/// `core` for any other, since every other feature that the Reference defines is in the core tier. Using
/// a macro declared elsewhere is in every tier, whatever its expansion writes
/// (macros.advanced-tier; macros.meta-tier), and so is naming a type with value arguments or
/// calling a function with value parameters (generics.meta-tier). A module that declares a foreign
/// function, writes an `unsafe` block or names `std.c` with `use` is `systems` (c.systems-tier).
#[must_use]
pub fn tier(db: &dyn Db, program: Program, file: SourceFile) -> &'static str {
    let module = &module_info(db, program, file).name;
    if writes_systems(db, file) {
        "systems"
    } else if writes_meta(db, file) {
        "meta"
    } else if declares_macros(db, file)
        || names_views(db, program, file)
        || super::parameters::uses_parameters(db, program, module)
        || super::polymorphism::uses_polymorphism(db, program, file)
        || super::shapes::writes_shapes(db, file)
        || super::effects::uses_effects(db, program, file)
    {
        "advanced"
    } else {
        "core"
    }
}

/// Whether a file's module declares a value parameter (generics.meta-tier), writes `comptime`
/// (meta.staging-tier), names `std.meta` with `use` or writes a bound test (meta.reflection-tier),
/// or declares a procedural macro or writes a quote (macros.meta-tier), the features of the meta
/// tier.
fn writes_meta(db: &dyn Db, file: SourceFile) -> bool {
    use stilt_syntax::SyntaxKind::{BOUND_TEST, COMPTIME_KW, MACRO_KW, QUOTE_KW, USE, VALUE_PARAM};
    let tree = stilt_db::parse(db, file).tree();
    stilt_syntax::ast::AstNode::syntax(&tree)
        .descendants_with_tokens()
        .any(|e| match e.kind() {
            COMPTIME_KW | VALUE_PARAM | BOUND_TEST | MACRO_KW | QUOTE_KW => true,
            USE => e.as_node().is_some_and(names_meta),
            _ => false,
        })
}

/// Whether a file's module declares a foreign function, writes an `unsafe` block or names
/// `std.c` with `use`, the features of the systems tier (c.systems-tier).
fn writes_systems(db: &dyn Db, file: SourceFile) -> bool {
    use stilt_syntax::SyntaxKind::{UNSAFE_EXPR, USE};
    let tree = stilt_db::parse(db, file).tree();
    let foreign = tree
        .items()
        .any(|i| matches!(i, stilt_syntax::ast::Item::Fn(f) if f.is_foreign()));
    foreign
        || stilt_syntax::ast::AstNode::syntax(&tree)
            .descendants()
            .any(|n| match n.kind() {
                UNSAFE_EXPR => true,
                USE => names_module(&n, "std.c"),
                _ => false,
            })
}

/// Whether a `use` names `std.meta`.
fn names_meta(node: &stilt_syntax::SyntaxNode) -> bool {
    names_module(node, "std.meta")
}

/// Whether a `use` names the module `module`.
fn names_module(node: &stilt_syntax::SyntaxNode, module: &str) -> bool {
    use stilt_syntax::ast::AstNode as _;
    let path = stilt_syntax::ast::Use::cast(node.clone()).and_then(|u| u.path());
    path.is_some_and(|p| {
        let text: String = p
            .syntax()
            .descendants_with_tokens()
            .filter_map(stilt_syntax::SyntaxElement::into_token)
            .filter(|t| !t.kind().is_trivia())
            .map(|t| t.text().to_owned())
            .collect();
        text == module
    })
}

/// Whether a file's module declares a macro (macros.advanced-tier).
fn declares_macros(db: &dyn Db, file: SourceFile) -> bool {
    stilt_hir::item_tree(db, file).items.iter().any(|item| {
        matches!(
            item,
            stilt_hir::ItemSummary::Decl {
                kind: stilt_hir::DeclSummary::Macro(_),
                ..
            }
        )
    })
}

/// Whether a file's module names a view type, `View` or `Iter` (views.std-view), in a
/// declaration's types, or in a value its code makes or binds, or declares or calls a
/// projection (projections.declaring-projection).
///
/// # Panics
///
/// If the module has 4G bodies or more.
#[must_use]
pub fn names_views(db: &dyn Db, program: Program, file: SourceFile) -> bool {
    let module = &module_info(db, program, file).name;
    let bodies = u32::try_from(body_starts(db, program, file).len()).expect("under 4G bodies");
    declares_views(db, program, module)
        || (0..bodies).any(|i| {
            let expansions = &stilt_hir::module_body(db, program, file, i).expansions;
            holds_views(&infer_body(db, program, file, i).body, expansions)
        })
}

/// Whether the declarations of `module` name a view type in their types, or are projections.
fn declares_views(db: &dyn Db, program: Program, module: &str) -> bool {
    let decls = declarations(db, program);
    let sig = |s: &stilt_hir::decls::FnSig| {
        s.projection
            || s.params.iter().any(|(_, t)| names(t))
            || names(&s.ret)
            || s.row.raise.as_deref().is_some_and(names)
    };
    let types = decls.types.iter().any(|(item, info)| {
        &*item.home == module
            && match &info.def {
                TypeDefInfo::Record(fields) => fields.iter().any(|(_, t)| names(t)),
                TypeDefInfo::Variants(vs) => vs.iter().flat_map(|(_, ts)| ts).any(names),
                TypeDefInfo::Builtin => false,
            }
    });
    let functions = decls
        .functions
        .iter()
        .any(|(item, s)| &*item.home == module && sig(s));
    let members = decls
        .inherent
        .iter()
        .filter(|(owner, _)| &*owner.home == module)
        .any(|(_, ms)| ms.iter().any(|m| sig(&m.signature)));
    let impls = decls
        .trait_impls
        .values()
        .filter(|i| &*i.module == module)
        .any(|i| i.members.iter().any(|m| sig(&m.signature)));
    let traits = decls
        .traits
        .iter()
        .filter(|(item, _)| &*item.home == module)
        .any(|(_, t)| t.methods.iter().any(|m| sig(&m.signature)));
    types || functions || members || impls || traits
}

/// Whether a declaration's type names a view type.
fn names(t: &hir::Ty) -> bool {
    match t {
        hir::Ty::Con(item, ts) => {
            is_view_type(item, "View") || is_view_type(item, "Iter") || ts.iter().any(names)
        }
        hir::Ty::Tuple(ts) | hir::Ty::App(_, ts) => ts.iter().any(names),
        hir::Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| names(t))
                || f.ret.iter().chain(f.row.raise.as_deref()).any(names)
        }
        hir::Ty::Spread(_, t) => names(t),
        hir::Ty::Param(_)
        | hir::Ty::Handler(_)
        | hir::Ty::SelfTy
        | hir::Ty::Value(_)
        | hir::Ty::Error => false,
    }
}

/// Whether a typed body makes or binds a value whose type names a view type, or calls a
/// projection.
fn holds_views(body: &TypedBody, expansions: &[stilt_hir::hir::Expansion]) -> bool {
    // Nothing in a macro's expansion, fragments included, counts (macros.advanced-tier).
    let ours = |at| !super::in_expansion(expansions, at);
    let mut found = false;
    let mut stmt = |s: &crate::tast::Stmt| {
        if let StmtKind::Let(b) | StmtKind::Var(b) = &s.kind
            && ours(b.pattern.at)
        {
            found |= mentions(&b.pattern.ty);
        }
    };
    let mut expr_found = false;
    let mut expr = |e: &Expr| {
        expr_found |= ours(e.at) && (mentions(&e.ty) || matches!(e.kind, ExprKind::Project(..)));
    };
    match &body.code {
        Definition::Code(Code::Block(b)) => walk::iter_block(b, &mut stmt, &mut expr),
        Definition::Code(Code::Expr(e)) => walk::iter(e, &mut stmt, &mut expr),
        Definition::Native | Definition::Broken => {}
    }
    found || expr_found
}

/// Whether a type names a view type.
fn mentions(t: &Ty) -> bool {
    match t {
        Ty::Con(item, ts) => {
            is_view_type(item, "View") || is_view_type(item, "Iter") || ts.iter().any(mentions)
        }
        Ty::Tuple(ts) | Ty::App(_, ts) => ts.iter().any(mentions),
        Ty::Fn(f) => {
            f.params.iter().any(|(_, t)| mentions(t))
                || mentions(&f.ret)
                || f.row.raise.as_deref().is_some_and(mentions)
        }
        Ty::Spread(s) => mentions(&s.elem),
        Ty::Param(_) | Ty::Handler(_) | Ty::SelfTy | Ty::Var(_) | Ty::Value(_) | Ty::Error => false,
    }
}
