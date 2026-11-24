//! The context of each hole of a body, which `stilt show` reports (goal hole-context), in
//! the order Hazel measured (Agent syntax, "Typed holes as context"): the type its context
//! expects and the effects it may perform, the types they mention, the bindings in scope, and
//! the first functions whose result fits.

mod candidates;
mod fits;
mod scope;

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::body_starts;
use stilt_hir::decls::{Lookup, QueriedOnce};
use stilt_hir::hir::{Capability, GenericId, Item, Limits, Mode, Name};
use stilt_syntax::ast::{self, AstNode as _};
use stilt_syntax::{TextRange, TextSize};

pub use fits::MOST;
use scope::Binding;

use crate::owners::{BodyOwner, Place};
use crate::queries::{
    body_limits, body_owner, generic_name, implicit_effects, infer_body, module_info,
};
use crate::tast::{Code, Definition, TypedBody};
use crate::ty::{Row, Table, Ty};

/// The context of a hole.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hole {
    /// Where it is in its file.
    pub at: TextRange,
    /// The type its context expects, as a program writes it.
    pub expects: String,
    /// What it may perform, as a row writes each: `io`, a `raise`, and row variables.
    pub effects: Vec<String>,
    /// The implicit effects that a `without` rules out where it is: `panic`, `alloc`.
    pub without: Vec<&'static str>,
    /// The types that the expected type and the effects name, in the order they name them,
    /// each once, but for the prelude's and the built-in types, which have no declaration of
    /// the program's or the standard library's modules to show.
    pub types: Vec<Item>,
    /// The bindings in scope, each with its type, in the order they are bound; of two of one
    /// name, the later, which hides the other.
    pub in_scope: Vec<(Name, String)>,
    /// At most [`MOST`] functions whose result fits, in the order of [`candidates`].
    pub fits: Vec<Fit>,
}

/// A function whose result fits a hole.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fit {
    /// The path of its declaration (edits.paths), as `std.prelude.List.len`.
    pub path: String,
    /// What a program writes before its name, if anything: its type or trait for a member, as
    /// `List`, or its module for an imported module's function, as `io`.
    pub qualifier: Option<Name>,
}

/// What code at a hole may perform.
pub(crate) struct Allowed {
    io: bool,
    raise: Raise,
    limits: Limits,
}

/// What code at a hole may raise.
enum Raise {
    Nothing,
    Of(Ty),
    /// Any error whose type implements `Show`, as a test's or a doc example's (program.test-results
    /// and program.doc-examples).
    Showable,
}

/// The holes of the body `index` of a file's module, in the order they are written, each with its
/// context. A body with an error has none: what it expects isn't known (facts.bodies-with-errors).
#[must_use]
pub fn holes(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Vec<Hole> {
    let typed = &infer_body(db, program, file, index).body;
    let Definition::Code(code) = &typed.code else {
        return Vec::new();
    };
    let owner = body_owner(db, program, file, index);
    let module = module_info(db, program, file);
    let names = |id: &GenericId| *generic_name(db, program, id.clone());
    let table = Table::default();
    let decls = QueriedOnce::new(db, program);
    let mut sources = candidates::Sources::new(db, program, &decls, file);
    sources.enclosing = enclosing(owner, module.name);
    sources.bounds = bounds(owner);
    let judge = fits::Judge {
        decls: &decls,
        bounds: &sources.bounds,
        effects: implicit_effects(db, program),
    };
    let limits = body_limits(module, owner);
    let start = body_starts(db, program, file)[index as usize];
    let params = parameters(db, file, start, typed, owner);
    scope::sites(params, &typed.locals, code)
        .into_iter()
        .map(|site| {
            let (effects, allowed) = match &site.row {
                Some(row) => (table.row_elements(row, &names), allowed(row, limits)),
                None => own_effects(owner, limits, &table, &names),
            };
            let receivers = receivers(&site.scope);
            let candidates = sources.all(&site.ty, &receivers);
            Hole {
                at: site.at + start,
                expects: table.show(&site.ty, &names),
                effects,
                without: words(limits),
                types: mentioned(&decls, &site.ty, &allowed),
                in_scope: visible(&site.scope, &table, &names),
                fits: judge.select(&candidates, &site.ty, &allowed),
            }
        })
        .collect()
}

/// The body's parameters, each with its type, `self` first for a method. A function's `= ?`
/// binds none, its body being the hole alone, so its parameters' names are read from its
/// declaration, which is around the hole, `start` being where the body starts.
fn parameters(
    db: &dyn Db,
    file: SourceFile,
    start: TextSize,
    typed: &TypedBody,
    owner: &BodyOwner,
) -> Vec<Binding> {
    let BodyOwner::Fn {
        signature, hole, ..
    } = owner
    else {
        return Vec::new();
    };
    let names: Vec<Name> = if *hole {
        let hole = match &typed.code {
            Definition::Code(Code::Block(b)) => b.first().map(|s| s.at.start()),
            Definition::Code(Code::Expr(e)) => Some(e.at.start()),
            Definition::Native | Definition::Broken => None,
        };
        declared_params(db, file, start + hole.unwrap_or_default())
    } else {
        typed
            .params
            .iter()
            .filter_map(|(_, v)| typed.locals.get(v.0 as usize).copied())
            .collect()
    };
    names
        .into_iter()
        .zip(&signature.params)
        .map(|(name, (mode, t))| Binding {
            name,
            ty: Ty::from_hir(t, None),
            mutable: *mode == Mode::Inout,
        })
        .collect()
}

/// The names of the parameters of the function declared around `at`, `self` first.
fn declared_params(db: &dyn Db, file: SourceFile, at: TextSize) -> Vec<Name> {
    let tree = stilt_db::parse(db, file).syntax();
    let Some(f) = tree
        .token_at_offset(at)
        .right_biased()
        .and_then(|t| t.parent_ancestors().find_map(ast::Fn::cast))
    else {
        return Vec::new();
    };
    let Some(list) = f.param_list() else {
        return Vec::new();
    };
    let receiver = list.self_param().map(|_| Name::from("self"));
    let params = list
        .params()
        .filter_map(|p| p.name().map(|n| Name::from(n.text().as_str())));
    receiver.into_iter().chain(params).collect()
}

/// What the body's own code may perform, written and as a hole's search reads it: its
/// function's row, `{io, raise<E: Show>}` for a test or a doc example, and nothing for a
/// constant.
fn own_effects(
    owner: &BodyOwner,
    limits: Limits,
    table: &Table,
    names: &dyn Fn(&GenericId) -> Name,
) -> (Vec<String>, Allowed) {
    match owner {
        BodyOwner::Fn { signature, .. } => {
            let row = Row::from_hir(&signature.row, None);
            (table.row_elements(&row, names), allowed(&row, limits))
        }
        BodyOwner::Test | BodyOwner::Example => (
            vec!["io".to_owned(), "raise<E: Show>".to_owned()],
            Allowed {
                io: true,
                raise: Raise::Showable,
                limits,
            },
        ),
        BodyOwner::Const(..) => (Vec::new(), allowed(&Row::EMPTY, limits)),
    }
}

fn allowed(row: &Row, limits: Limits) -> Allowed {
    Allowed {
        io: row.io,
        raise: row
            .raise
            .as_ref()
            .map_or(Raise::Nothing, |t| Raise::Of((**t).clone())),
        limits,
    }
}

fn words(limits: Limits) -> Vec<&'static str> {
    let mut words: Vec<&'static str> = [
        ("panic", limits.panic),
        ("alloc", limits.alloc),
        ("div", limits.div),
        ("copy", limits.copy),
    ]
    .into_iter()
    .filter_map(|(word, on)| on.then_some(word))
    .collect();
    words.extend(limits.capabilities.iter().map(Capability::text));
    words
}

/// The path of the function whose body it is (edits.paths).
fn enclosing(owner: &BodyOwner, module: Name) -> Option<String> {
    let BodyOwner::Fn { name, place, .. } = owner else {
        return None;
    };
    Some(match place {
        Place::Module => format!("{module}.{name}"),
        Place::Impl {
            trait_item: None,
            owner: Some(o),
        } => format!("{module}.{}.{name}", o.name),
        Place::Impl {
            trait_item: Some(t),
            owner: Some(o),
        } => format!("{module}.{}.{}.{name}", o.name, t.name),
        Place::Impl { owner: None, .. } => return None,
        Place::Trait(t) => format!("{module}.{}.{name}", t.name),
    })
}

/// The type parameters of the body's function, each with the traits that bound it.
fn bounds(owner: &BodyOwner) -> crate::implements::Bounds {
    match owner {
        BodyOwner::Fn { signature, .. } => signature
            .type_params
            .iter()
            .map(|(g, traits)| (Ty::Param(g.clone()), traits.clone()))
            .collect(),
        BodyOwner::Const(..) | BodyOwner::Test | BodyOwner::Example => Vec::new(),
    }
}

/// The types of the bindings in scope, each once, with whether a binding of the type may be
/// passed `inout`.
fn receivers(scope: &[Binding]) -> Vec<(Ty, bool)> {
    let mut found: Vec<(Ty, bool)> = Vec::new();
    for b in scope {
        match found.iter_mut().find(|(t, _)| *t == b.ty) {
            Some((_, mutable)) => *mutable |= b.mutable,
            None => found.push((b.ty.clone(), b.mutable)),
        }
    }
    found
}

/// The bindings of `scope` that code at the hole can name, with their types: of two of one
/// name, the later.
fn visible(
    scope: &[Binding],
    table: &Table,
    names: &dyn Fn(&GenericId) -> Name,
) -> Vec<(Name, String)> {
    scope
        .iter()
        .enumerate()
        .filter(|(i, b)| !scope[i + 1..].iter().any(|c| c.name == b.name))
        .map(|(_, b)| (b.name, table.show(&b.ty, names)))
        .collect()
}

/// The declared types that `expected` and the error type the hole may raise name, outside the
/// prelude, in the order they name them, each once.
fn mentioned(decls: &dyn Lookup, expected: &Ty, allowed: &Allowed) -> Vec<Item> {
    fn walk(decls: &dyn Lookup, t: &Ty, found: &mut Vec<Item>) {
        match t {
            Ty::Con(item, args) => {
                let prelude = &*item.home == "std.prelude";
                if !prelude && decls.type_info(item).is_some() && !found.contains(item) {
                    found.push(item.clone());
                }
                for a in args {
                    walk(decls, a, found);
                }
            }
            Ty::Tuple(ts) | Ty::App(_, ts) => ts.iter().for_each(|a| walk(decls, a, found)),
            Ty::Fn(f) => {
                for (_, a) in &f.params {
                    walk(decls, a, found);
                }
                walk(decls, &f.ret, found);
                if let Some(e) = &f.row.raise {
                    walk(decls, e, found);
                }
            }
            Ty::Spread(s) => walk(decls, &s.elem, found),
            Ty::Param(_) | Ty::Handler(_) | Ty::SelfTy | Ty::Var(_) | Ty::Value(_) | Ty::Error => {}
        }
    }
    let mut found = Vec::new();
    walk(decls, expected, &mut found);
    if let Raise::Of(e) = &allowed.raise {
        walk(decls, e, &mut found);
    }
    found
}
