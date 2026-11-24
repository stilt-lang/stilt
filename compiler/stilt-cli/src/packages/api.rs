//! A package's API, as its check gives it when the package is the root of a program (versions.api):
//! its modules and their tiers, its `pub` items, members, trait methods and visible trait impls by
//! their addresses, each with a signature written without the names of its generics and parameters,
//! and its limitable facts, those of its inferred facts that a `without` can name; each `pub`
//! effect with its operations, and each `pub` macro with its patterns or its signature; whether the
//! package's own code performs `io`; and whether it holds an `unsafe` block (c.unsafe-in-api).

use std::collections::{HashMap, HashSet};

use stilt_db::{Database, Program, SourceFile};
use stilt_hir::decls::{Declarations, FnSig, TypeDefInfo};
use stilt_hir::hir::{Decl, DeclKind, FnTy, GenericId, Item, ItemHir, Name, Row, TraitRef, Ty};
use stilt_hir::scope::{Kind, Value};
use stilt_ide::show::facts::SHOWN;
use stilt_mir::{Code, FnRef};
use stilt_pkg::api::{self, Api, Entry};
use stilt_types::packages::Need;

/// The API of the root package of `program`, whose name is `name`, with each address as a program
/// that depends on the package names it: `name` for its module `main`, and `name.a.b` for its
/// module `a.b` (packages.modules-of-dependencies).
pub(crate) fn extract(db: &Database, program: Program, name: &str) -> Api {
    let files: Vec<SourceFile> = program
        .files(db)
        .iter()
        .copied()
        .filter(|&f| stilt_db::package_of(db, program, f) == 0)
        .collect();
    let decls = stilt_hir::decls::declarations(db, program);
    let facts = facts(db, program, &files);
    let fact = |f: &FnRef| facts.get(f).cloned().unwrap_or_default();
    let mut out = Api::default();
    let mut modules = HashSet::new();
    for &file in &files {
        let Some(module) = stilt_hir::def_map(db, program)
            .of_file(file)
            .filter(|m| m.valid)
        else {
            continue;
        };
        modules.insert(module.name);
        let home = if &*module.name == "main" {
            name.to_owned()
        } else {
            format!("{name}.{}", module.name)
        };
        out.entries.insert(
            home.clone(),
            item(
                api::Kind::Module,
                stilt_types::facts::tier(db, program, file).into(),
            ),
        );
        let scope = &stilt_hir::module_scope(db, program, file).scope;
        let at = |name: &Name| Item {
            home: module.name,
            name: *name,
        };
        for (name, e) in scope.types.iter().filter(|(_, e)| e.is_pub) {
            let it = at(name);
            types(&mut out, decls, (&home, &it), e.kind, &fact);
        }
        for (name, v) in &scope.values {
            let Value::Item(e) = v else { continue };
            let it = at(name);
            let shape = e
                .is_pub
                .then(|| value_shape(db, program, (file, &it), e.kind));
            if let Some(shape) = shape.flatten() {
                // A macro runs as the program is built, so no `without` of a caller limits it.
                let proc = e.kind == Kind::Proc;
                let facts = (!proc).then(|| fact(&FnRef::Function(it.clone())));
                let entry = with(item(api::Kind::Item, shape), facts.unwrap_or_default());
                out.entries.insert(format!("{home}.{name}"), entry);
            }
        }
    }
    impls(&mut out, decls, (&modules, name), &fact);
    own_code(db, program, &mut out);
    out
}

/// The shape of the `pub` value item `it` of `file`, of kind `kind`: a function's or a
/// constant's signature, a pattern macro's patterns, or a procedural macro's signature, what its
/// uses give it and what they make of its result, while what it expands to is its body
/// (macros.procedural-declarations).
fn value_shape(
    db: &Database,
    program: Program,
    (file, it): (SourceFile, &Item),
    kind: Kind,
) -> Option<String> {
    let decls = stilt_hir::decls::declarations(db, program);
    match kind {
        Kind::Fn => decls.functions.get(it).map(sig),
        Kind::Const => decls.constants.get(it).map(ty),
        Kind::Macro => patterns(db, program, file, it.name),
        Kind::Proc => decls.functions.get(it).map(|s| format!("macro {}", sig(s))),
        _ => None,
    }
}

/// Whether the package's own code performs `io` (packages.own-effects), and whether it holds an
/// `unsafe` block (c.unsafe-in-api).
fn own_code(db: &Database, program: Program, out: &mut Api) {
    let calls = stilt_types::packages::io_calls(db, program, 0);
    out.io = calls.iter().any(|c| c.need != Need::Unsafe);
    out.unsafe_code = calls.iter().any(|c| c.need == Need::Unsafe);
}

/// A `pub` macro's shape: its patterns, which are part of its module's API, while its
/// templates are its body (macros.syntax-declarations).
fn patterns(db: &Database, program: Program, file: SourceFile, name: Name) -> Option<String> {
    stilt_hir::module_hir(db, program, file)
        .items
        .iter()
        .find_map(|i| match i {
            ItemHir::Decl(Decl {
                kind: DeclKind::Macro(m),
                ..
            }) if m.name == *name => Some(format!("syntax {}", m.patterns)),
            _ => None,
        })
}

fn item(kind: api::Kind, shape: String) -> Entry {
    Entry {
        kind,
        shape,
        facts: Vec::new(),
        default: false,
    }
}

fn with(entry: Entry, facts: Vec<String>) -> Entry {
    Entry { facts, ..entry }
}

/// A type with its members, or a trait with its methods.
fn types(
    out: &mut Api,
    decls: &Declarations,
    (home, it): (&str, &Item),
    kind: Kind,
    fact: &dyn Fn(&FnRef) -> Vec<String>,
) {
    let address = format!("{home}.{}", it.name);
    if kind == Kind::Trait {
        out.entries
            .insert(address.clone(), item(api::Kind::Item, "trait".into()));
        for m in decls.traits.get(it).map_or(&[][..], |t| &t.methods) {
            let facts = fact(&FnRef::DefaultMethod(it.clone(), m.name));
            let entry = Entry {
                default: m.has_default,
                ..with(item(api::Kind::TraitMethod, sig(&m.signature)), facts)
            };
            out.entries.insert(format!("{address}.{}", m.name), entry);
        }
        return;
    }
    if kind == Kind::Effect {
        let shape = decls.effects.get(it).map_or_else(String::new, effect_shape);
        out.entries.insert(address, item(api::Kind::Item, shape));
        return;
    }
    let shape = decls.types.get(it).map_or_else(String::new, |t| {
        let params = t.params.len();
        match &t.def {
            TypeDefInfo::Record(fields) => format!(
                "<{params}> {{{}}}",
                list(fields.iter().map(|(n, t)| format!("{n}: {}", ty(t))))
            ),
            TypeDefInfo::Variants(vs) => format!(
                "<{params}> {}",
                list(
                    vs.iter()
                        .map(|(n, ts)| format!("{n}({})", list(ts.iter().map(ty))))
                )
            ),
            TypeDefInfo::Builtin => "builtin".to_owned(),
        }
    });
    out.entries
        .insert(address.clone(), item(api::Kind::Item, shape));
    for m in decls
        .inherent
        .get(it)
        .into_iter()
        .flatten()
        .filter(|m| m.is_pub)
    {
        let facts = fact(&FnRef::Member(it.clone(), m.name));
        let entry = with(item(api::Kind::Member, sig(&m.signature)), facts);
        out.entries.insert(format!("{address}.{}", m.name), entry);
    }
}

/// The trait impls of the package's modules, each with its methods' implicit effects.
fn impls(
    out: &mut Api,
    decls: &Declarations,
    (modules, name): (&HashSet<Name>, &str),
    fact: &dyn Fn(&FnRef) -> Vec<String>,
) {
    for ((tr, owner), info) in &decls.trait_impls {
        if !modules.contains(&info.module) {
            continue;
        }
        let home = if &*info.module == "main" {
            name.to_owned()
        } else {
            format!("{name}.{}", info.module)
        };
        let address = format!("{home}.{}.{}", owner.name, tr.name);
        let bounds = list(info.generics.iter().map(|(g, traits)| {
            format!(
                "{}: {}",
                g.index,
                list(traits.iter().map(|t| format!("{}.{}", t.home, t.name)))
            )
        }));
        let shape = format!(
            "impl<{bounds}> {}.{} for {}",
            tr.home,
            tr.name,
            ty(&info.self_ty)
        );
        out.entries
            .insert(address.clone(), item(api::Kind::Impl, shape));
        for m in &info.members {
            let f = FnRef::ImplMethod(tr.clone(), owner.clone(), m.name);
            let entry = with(item(api::Kind::Member, String::new()), fact(&f));
            out.entries.insert(format!("{address}.{}", m.name), entry);
        }
    }
}

/// The limitable facts of each function of the package's files, as `without` names them, in
/// the order that `stilt show` prints them: those that `stilt-types` infers as they are when
/// verification proves nothing (versions.limitable-facts; versions.facts-without-proofs), and the
/// `copy` and `alloc` of the writes to shared data (facts.copy).
pub(crate) fn facts(
    db: &Database,
    program: Program,
    files: &[SourceFile],
) -> HashMap<FnRef, Vec<String>> {
    let mut found = HashMap::new();
    // Only the standard library has natives, which only its documentation reads (docs.std).
    let std = program.std(db);
    let natives = if files.iter().any(|f| std.contains(f)) {
        stilt_mir::native_bodies(db, program)
    } else {
        HashMap::new()
    };
    for (f, code) in &stilt_mir::bodies(db, program).code {
        let (file, index) = match code {
            Code::Body(file, index) => (file, index),
            Code::Native => match natives.get(f) {
                Some((file, index)) => (file, index),
                None => continue,
            },
        };
        if !files.contains(file) {
            continue;
        }
        let mut has = stilt_types::facts::api_effects(db, program, *file, *index);
        has.extend(
            stilt_rc::copy_causes(db, program, *file, *index)
                .into_iter()
                .map(|c| c.0),
        );
        let shown = SHOWN.iter().filter(|e| has.contains(e));
        found.insert(f.clone(), shown.map(|e| e.word().to_owned()).collect());
    }
    found
}

/// An effect's type parameters and its operations, in order, each with its parameters, result
/// and row: a handler implements every operation, so adding one breaks the handlers of other
/// packages as changing one breaks their performances (handlers.declaring-effect and
/// handlers.handler-literals).
fn effect_shape(e: &stilt_hir::decls::EffectInfo) -> String {
    let ops = list(e.ops.iter().map(|o| {
        let params = list(
            o.params
                .iter()
                .map(|(mode, t)| format!("{mode:?} {}", ty(t))),
        );
        format!("{}({params}) -> {} / {}", o.name, ty(&o.ret), row(&o.row))
    }));
    format!("effect <{}> {{{ops}}}", e.params.len())
}

fn list(items: impl Iterator<Item = String>) -> String {
    items.collect::<Vec<_>>().join(", ")
}

/// A signature, without the names of its generics and parameters: each generic by its place.
fn sig(s: &FnSig) -> String {
    let bounds = list(s.type_params.iter().map(|(g, traits)| {
        format!(
            "{}: {}",
            g.index,
            list(traits.iter().map(|t| format!("{}.{}", t.home, t.name)))
        )
    }));
    let params = list(s.params.iter().zip(&s.passing).map(|((mode, t), passing)| {
        let escaping = if *passing { "" } else { "escaping " };
        format!("{escaping}{mode:?} {}", ty(t))
    }));
    // A projection's result is written `inout T`, which changes what type-checks at its callers
    // (projections.declaring-projection), and a foreign function's calls stand only in `unsafe`
    // blocks (c.unsafe-operations and c.unsafe-in-api).
    let inout = if s.projection { "inout " } else { "" };
    let foreign = if s.foreign { "extern " } else { "" };
    format!(
        "{foreign}<{bounds}; {}> ({params}) -> {inout}{} / {}",
        s.row_params.len(),
        ty(&s.ret),
        row(&s.row)
    )
}

fn row(r: &Row) -> String {
    let mut parts = Vec::new();
    if r.io {
        parts.push("io".to_owned());
    }
    if let Some(e) = &r.raise {
        parts.push(format!("raise<{}>", ty(e)));
    }
    for e in &r.effects {
        parts.push(effect(e));
    }
    if let Some(v) = &r.var {
        parts.push(format!("'{}", v.index));
    }
    parts.join(" ")
}

fn ty(t: &Ty) -> String {
    match t {
        Ty::Con(item, args) if args.is_empty() => format!("{}.{}", item.home, item.name),
        Ty::Con(item, args) => {
            format!("{}.{}<{}>", item.home, item.name, list(args.iter().map(ty)))
        }
        Ty::Param(g) if g.is_poly() => format!("'p{}", g.declared().index - GenericId::POLY),
        Ty::Param(g) => format!("'{}", g.index),
        Ty::SelfTy => "Self".to_owned(),
        Ty::App(head, args) => format!("{}<{}>", ty(head), list(args.iter().map(ty))),
        Ty::Tuple(ts) => format!("({})", list(ts.iter().map(ty))),
        Ty::Fn(f) => fn_ty(f),
        Ty::Spread(p, t) => format!("..'{}:{}", p.index, ty(t)),
        Ty::Handler(h) => {
            let answer = h.answer.as_ref().map(|t| format!(" -> {}", ty(t)));
            let answer = answer.unwrap_or_default();
            format!("handler {}{answer} / {}", effect(&h.effect), row(&h.row))
        }
        Ty::Value(v) => format!("#{v}"),
        Ty::Error => "{error}".to_owned(),
    }
}

/// An effect with its type arguments (handlers.effects-in-rows).
fn effect(e: &stilt_hir::hir::EffectInst) -> String {
    let (home, name) = (&e.effect.home, &e.effect.name);
    if e.args.is_empty() {
        format!("{home}.{name}")
    } else {
        format!("{home}.{name}<{}>", list(e.args.iter().map(ty)))
    }
}

fn fn_ty(f: &FnTy) -> String {
    // A polymorphic function type's parameters, with their bounds (polymorphism.function-types).
    let generics = if f.generics.is_empty() {
        String::new()
    } else {
        let each = f.generics.iter().map(|(g, bounds)| {
            let traits = bounds.iter().map(|b| match b {
                TraitRef::Trait(item, args) if args.is_empty() => {
                    format!("{}.{}", item.home, item.name)
                }
                TraitRef::Trait(item, args) => {
                    format!("{}.{}<{}>", item.home, item.name, list(args.iter().map(ty)))
                }
                TraitRef::Error => "{error}".to_owned(),
            });
            format!("{}: {}", ty(&Ty::Param(g.clone())), list(traits))
        });
        format!("<{}>", list(each))
    };
    let params = list(f.params.iter().map(|(m, t)| format!("{m:?} {}", ty(t))));
    let ret = f.ret.as_ref().map_or_else(|| "()".to_owned(), ty);
    format!("fn{generics}({params}) -> {ret} / {}", row(&f.row))
}
