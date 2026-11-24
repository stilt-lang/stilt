//! The fix of a duplicate body (docs.duplicate-body-fix): the later body replaced by a call of the
//! first, when the two have one signature but for their names and their parameters' names, and the
//! later's module can call the first without a new `use`.

use std::fmt::Write as _;

use stilt_db::{Db, Program};
use stilt_diag::{Edit, Fix};
use stilt_hir::decls::FnSig;
use stilt_hir::hir::{DeclKind, GenericId, Item, ItemHir, Mode, Name, Row, Ty};
use stilt_hir::{module_body, module_hir};

use super::{Body, block};
use crate::owners::{BodyOwner, Place};
use crate::queries::{body_owner, generic_name, module_info};

/// The fix that makes `later` call `first`, whose path is `first_path`, if there is one.
pub(super) fn call(
    db: &dyn Db,
    program: Program,
    first: Body,
    later: Body,
    first_path: &str,
) -> Option<Fix> {
    let BodyOwner::Fn {
        name,
        signature,
        place,
        ..
    } = body_owner(db, program, first.file, first.index)
    else {
        return None;
    };
    let BodyOwner::Fn {
        signature: later_signature,
        ..
    } = body_owner(db, program, later.file, later.index)
    else {
        return None;
    };
    let names = |id: &GenericId| *generic_name(db, program, id.clone());
    if signature_text(signature, &names) != signature_text(later_signature, &names) {
        return None;
    }
    let head = callee(db, program, first, later, *name, place)?;
    let hir = module_body(db, program, later.file, later.index);
    let params: Vec<&Name> = hir
        .params
        .iter()
        .map(|p| &hir.locals[p.0 as usize].name)
        .collect();
    let starts = head.split('.').next().unwrap_or_default();
    if params.iter().any(|p| &***p == starts) {
        return None;
    }
    let args: Vec<String> = params
        .iter()
        .zip(&later_signature.params)
        .map(|(name, (mode, _))| match mode {
            Mode::Inout => format!("inout {name}"),
            Mode::Let => name.to_string(),
        })
        .collect();
    let marked = if signature.row.raise.is_some() {
        "try "
    } else {
        ""
    };
    let text = format!("{{ {marked}{head}({}) }}", args.join(", "));
    let range = block(db, program, later)?;
    Some(Fix::new(
        format!("call `{first_path}`, whose body this is"),
        vec![Edit::replace(range, text)],
    ))
}

/// How the later's module names the first function, `name` of `place`: by its name, or its
/// type's, in its own module, and after the name of a module that it imports otherwise, when it
/// is `pub`, as its type is.
fn callee(
    db: &dyn Db,
    program: Program,
    first: Body,
    later: Body,
    name: Name,
    place: &Place,
) -> Option<String> {
    let home = &module_info(db, program, first.file).name;
    let here = module_info(db, program, later.file);
    let owner = match place {
        Place::Module => None,
        Place::Impl {
            trait_item: None,
            owner: Some(ty),
        } => Some(ty),
        _ => return None,
    };
    let local = match owner {
        Some(ty) => format!("{}.{name}", ty.name),
        None => name.to_string(),
    };
    if &here.name == home {
        return Some(local);
    }
    let public = match owner {
        Some(ty) => member_is_pub(db, program, first, name) && type_is_pub(db, program, first, ty),
        None => fn_is_pub(db, program, first, name),
    };
    let imported = here.imports.iter().any(|m| m == home);
    let binding = home.rsplit('.').next().unwrap_or(home);
    (public && imported).then(|| format!("{binding}.{local}"))
}

fn fn_is_pub(db: &dyn Db, program: Program, first: Body, name: Name) -> bool {
    module_hir(db, program, first.file)
        .items
        .iter()
        .any(|item| {
            matches!(item, ItemHir::Decl(d) if d.is_pub
            && matches!(&d.kind, DeclKind::Fn(f) if f.name == name))
        })
}

fn type_is_pub(db: &dyn Db, program: Program, first: Body, ty: &Item) -> bool {
    module_hir(db, program, first.file)
        .items
        .iter()
        .any(|item| {
            matches!(item, ItemHir::Decl(d) if d.is_pub
            && matches!(&d.kind, DeclKind::Type(t) if t.name == ty.name))
        })
}

fn member_is_pub(db: &dyn Db, program: Program, first: Body, name: Name) -> bool {
    module_hir(db, program, first.file)
        .items
        .iter()
        .any(|item| {
            matches!(item, ItemHir::Impl(imp) if imp.trait_ref.is_none()
            && imp.members.iter().any(|m| m.is_pub && *m.name() == name))
        })
}

/// A function's signature as a text, its generics named, without its name and its parameters'
/// names: what two functions must share for one to call the other in its place.
fn signature_text(sig: &FnSig, names: &dyn Fn(&GenericId) -> Name) -> String {
    let mut out = String::new();
    for (id, bounds) in &sig.type_params {
        let _ = write!(out, "<{}", names(id));
        for bound in bounds {
            let _ = write!(out, " {}.{}", bound.home, bound.name);
        }
        out.push('>');
    }
    for id in &sig.row_params {
        let _ = write!(out, "<row {}>", names(id));
    }
    for ((mode, ty), passes) in sig.params.iter().zip(&sig.passing) {
        let _ = write!(out, "({mode:?} {passes} ");
        hir_ty(&mut out, ty, names);
        out.push(')');
    }
    out.push_str("->");
    hir_ty(&mut out, &sig.ret, names);
    row(&mut out, &sig.row, names);
    out
}

fn hir_ty(out: &mut String, ty: &Ty, names: &dyn Fn(&GenericId) -> Name) {
    match ty {
        Ty::Con(item, args) => {
            let _ = write!(out, "{}.{}<", item.home, item.name);
            for arg in args {
                hir_ty(out, arg, names);
                out.push(',');
            }
            out.push('>');
        }
        Ty::Param(id) => {
            let _ = write!(out, "'{}", names(id));
        }
        Ty::SelfTy | Ty::Value(_) | Ty::Error => out.push_str(&leaf(ty)),
        Ty::App(head, args) => {
            hir_ty(out, head, names);
            out.push('<');
            for arg in args {
                hir_ty(out, arg, names);
                out.push(',');
            }
            out.push('>');
        }
        Ty::Tuple(items) => {
            out.push('(');
            for item in items {
                hir_ty(out, item, names);
                out.push(',');
            }
            out.push(')');
        }
        Ty::Fn(f) => {
            out.push_str("fn(");
            for (mode, param) in &f.params {
                let _ = write!(out, "{mode:?} ");
                hir_ty(out, param, names);
                out.push(',');
            }
            out.push_str(")->");
            if let Some(ret) = &f.ret {
                hir_ty(out, ret, names);
            }
            row(out, &f.row, names);
        }
        Ty::Spread(pack, elem) => {
            let _ = write!(out, "..'{}:", names(pack));
            hir_ty(out, elem, names);
        }
        Ty::Handler(h) => {
            out.push_str("handler ");
            effect(out, &h.effect, names);
            out.push_str("->");
            if let Some(answer) = &h.answer {
                hir_ty(out, answer, names);
            }
            row(out, &h.row, names);
        }
    }
}

/// The text of a type without parts: `Self`, a value argument and the error type.
fn leaf(ty: &Ty) -> String {
    match ty {
        Ty::SelfTy => "Self".to_owned(),
        Ty::Value(v) => format!("#{v}"),
        _ => "!".to_owned(),
    }
}

fn row(out: &mut String, row: &Row, names: &dyn Fn(&GenericId) -> Name) {
    let _ = write!(out, "/{}", row.io);
    if let Some(raise) = &row.raise {
        out.push_str(" raise ");
        hir_ty(out, raise, names);
    }
    for e in &row.effects {
        out.push(' ');
        effect(out, e, names);
    }
    if let Some(var) = &row.var {
        let _ = write!(out, " {}", names(var));
    }
}

/// An effect with its type arguments (handlers.effects-in-rows).
fn effect(out: &mut String, e: &stilt_hir::hir::EffectInst, names: &dyn Fn(&GenericId) -> Name) {
    let _ = write!(out, "{}.{}<", e.effect.home, e.effect.name);
    for arg in &e.args {
        hir_ty(out, arg, names);
        out.push(',');
    }
    out.push('>');
}
