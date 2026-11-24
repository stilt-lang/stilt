//! The foreign functions of a program, which C gives, written `extern fn` without a body
//! (c.foreign-functions): E0353 at each part of a signature that C can't take
//! (c.foreign-functions and c.types-c-takes). The parts that a foreign function has no place for
//! are read from the syntax, where they are written, and its types as they resolve, so that
//! `c.Ptr<u8>` is `std.c`'s however the module names it.

use stilt_db::{Db, Program, SourceFile};
use stilt_diag::{Diagnostic, codes};
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode};

use crate::hir::{DeclKind, FnDecl, ItemHir, Param, Ty};
use crate::lower::module_hir;

/// The types of a number, which C holds in its width, and `bool`, which it holds in a byte.
const SCALARS: [&str; 11] = [
    "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64", "bool",
];

/// Whether C holds a value of type `t` as Stilt does (c.element-types): a number, `bool`, or a
/// `c.Ptr` to one of these or to `()`. A type with an error holds, since its error is reported.
#[must_use]
pub fn c_holds(t: &Ty) -> bool {
    match t {
        Ty::Error => true,
        Ty::Con(item, args) if args.is_empty() => {
            item.home.as_str() == "std.prelude" && SCALARS.contains(&item.name.as_str())
        }
        Ty::Con(item, args) if is_c(item, "Ptr") && args.len() == 1 => {
            c_holds(&args[0]) || matches!(&args[0], Ty::Tuple(ts) if ts.is_empty())
        }
        _ => false,
    }
}

/// Whether `item` is the type `name` of `std.c`.
fn is_c(item: &crate::hir::Item, name: &str) -> bool {
    item.home.as_str() == "std.c" && item.name.as_str() == name
}

/// Whether a foreign function takes a value of type `t`, or gives one as its result
/// (c.types-c-takes): what C holds, a `c.Str`, and `()` as a result only.
fn c_takes(t: &Ty, result: bool) -> bool {
    match t {
        Ty::Tuple(ts) => result && ts.is_empty(),
        Ty::Con(item, args) if is_c(item, "Str") => args.is_empty(),
        _ => c_holds(t),
    }
}

/// The errors of the foreign functions of a file, in the order they are written.
#[salsa::tracked(returns(ref))]
pub fn foreign_errors(db: &dyn Db, program: Program, file: SourceFile) -> Vec<Diagnostic> {
    let module = module_hir(db, program, file);
    let resolved = |name: &str| {
        module.items.iter().find_map(|item| match item {
            ItemHir::Decl(d) => match &d.kind {
                DeclKind::Fn(f) if f.foreign && f.name.as_str() == name => Some(f),
                _ => None,
            },
            _ => None,
        })
    };
    let mut found = Vec::new();
    for item in stilt_db::parse(db, file).tree().items() {
        let ast::Item::Fn(f) = item else { continue };
        if f.is_foreign() {
            let decl = f.name().and_then(|n| resolved(&n.text()));
            found.extend(signature(&f, decl));
        }
    }
    found
}

fn error(range: TextRange, message: &str) -> Diagnostic {
    Diagnostic::new(codes::E0353, range, message)
}

/// c.foreign-functions's errors of `f`'s generics, receiver, modes and row, and c.types-c-takes's
/// of its types, which `decl` gives as they resolve.
fn signature(f: &ast::Fn, decl: Option<&FnDecl>) -> Vec<Diagnostic> {
    let mut found = Vec::new();
    for g in f.generic_list().iter().flat_map(ast::GenericList::generics) {
        if let Some(name) = g.name() {
            let message = "a foreign function takes no type, value or row parameter";
            found.push(error(name.syntax().text_range(), message));
        }
    }
    let declared = decl.map_or(&[][..], |d| &d.params[..]);
    if let Some(list) = f.param_list() {
        if let Some(token) = list.self_param().and_then(|s| s.self_token()) {
            found.push(error(
                token.text_range(),
                "a foreign function takes no receiver",
            ));
        }
        let own = declared.iter().filter(|p| matches!(p, Param::Param(..)));
        for (p, d) in list.params().zip(own) {
            found.extend(param(&p, d));
        }
    }
    if let (Some(ret), Some(Some(t))) = (f.ret_type(), decl.map(|d| d.ret.as_ref()))
        && let Some(ty) = ret.ty()
        && (ret.is_inout() || !c_takes(t, true))
    {
        let message = "C can't give this type: a foreign function returns an integer, a float, \
                       `bool`, a `c.Ptr`, a `c.Str` or `()`";
        found.push(error(ty.syntax().text_range(), message));
    }
    for e in f.row().iter().flat_map(ast::Row::elements) {
        if !matches!(e, ast::RowElem::RowIo(_)) {
            let message = "a foreign function may perform `io`, and no other effect";
            found.push(error(e.syntax().text_range(), message));
        }
    }
    found
}

/// A parameter's error: at its name for a mode C can't pass, and at its type for a type it
/// can't take.
fn param(p: &ast::Param, declared: &Param) -> Option<Diagnostic> {
    let at_name = |message: &str| p.name().map(|n| error(n.syntax().text_range(), message));
    if p.inout_token().is_some() {
        return at_name("C can't give back an `inout` parameter");
    }
    if p.is_escaping() {
        return at_name("C can't take an `escaping` parameter");
    }
    let Param::Param(_, t, _) = declared else {
        return None;
    };
    let ty = p.ty()?;
    (!c_takes(t, false)).then(|| {
        let message = "C can't take this type: a foreign function takes an integer, a float, \
                       `bool`, a `c.Ptr` or a `c.Str`";
        error(ty.syntax().text_range(), message)
    })
}
