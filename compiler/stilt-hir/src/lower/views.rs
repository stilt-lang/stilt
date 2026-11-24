//! The types of views where a declaration writes them (views.viewable-types and views.view-types):
//! a `View<T>` whose `T` isn't viewable is E0420, and a view type where a value would be stored, a
//! field, a payload, an error type or a constant's type, or nested in a list, a map, a tuple or a
//! type argument of a declared type other than `Option`, is E0421. Either part of the declaration
//! becomes the error type (errors.error-type). The standard library's own signatures name `View<T>`
//! for any `T`, which each use checks, so they aren't checked here; the types that bodies write are
//! checked with those they infer, after type checking.

use stilt_diag::{Code, Diagnostic, codes};
use stilt_syntax::TextRange;
use stilt_syntax::ast::{self, AstNode};

use super::{Resolver, bare};
use crate::hir::{FnTy, HandlerTy, Item, Row, Ty};
pub(super) use Holder::{Constant, Field, Free, Payload};

/// Whether an item is `std.view`'s `name`.
fn is_view_item(item: &Item, name: &str) -> bool {
    &*item.home == "std.view" && &*item.name == name
}

fn is_prelude(item: &Item, name: &str) -> bool {
    &*item.home == "std.prelude" && &*item.name == name
}

/// Whether a type is a view type: a `View`, an `Iter`, or an `Option` of one (views.view-types).
fn is_view(t: &Ty) -> bool {
    match t {
        Ty::Con(item, args) if is_prelude(item, "Option") => args.first().is_some_and(is_view),
        Ty::Con(item, _) => is_view_item(item, "View") || is_view_item(item, "Iter"),
        _ => false,
    }
}

/// Whether a type is viewable: `str` or a `List` (views.viewable-types). The error type is taken to
/// be.
fn viewable(t: &Ty) -> bool {
    match t {
        Ty::Con(item, _) => is_prelude(item, "str") || is_prelude(item, "List"),
        Ty::Error => true,
        _ => false,
    }
}

/// The written type that `node` holds where a type argument or component is written, if it
/// writes one there.
fn nth_part(node: Option<&ast::Type>, i: usize) -> Option<ast::Type> {
    match node.map(bare)? {
        ast::Type::NamedType(n) => n.args().nth(i),
        ast::Type::TupleType(t) => t.types().nth(i),
        // An anonymous record type's arguments are its fields' types, sorted by name.
        ast::Type::RecordType(r) => {
            let mut fields: Vec<ast::FieldDef> = r.fields().collect();
            fields.sort_by_key(|f| f.name().map(|n| n.text()));
            fields.get(i)?.ty()
        }
        _ => None,
    }
}

/// Where a declaration puts a type: where a view type may stand, a parameter's or a result's,
/// or where a value of it would be stored, named as E0421 names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Holder {
    Free,
    Field,
    Payload,
    Constant,
    Raised,
}

impl Holder {
    fn stores(self) -> bool {
        self != Self::Free
    }

    fn name(self) -> &'static str {
        match self {
            Self::Free => "this",
            Self::Field => "a field",
            Self::Payload => "a variant's payload",
            Self::Constant => "a constant",
            Self::Raised => "an error type",
        }
    }
}

/// An error of views.viewable-types or views.view-types: its code, the written type it is at, and
/// what it says.
struct Problem {
    code: Code,
    at: Option<ast::Type>,
    message: String,
}

impl Problem {
    fn stored(at: Option<ast::Type>, holder: &str) -> Self {
        let message = format!("{holder} can't hold a view, which must not outlive what it views");
        Self {
            code: codes::E0421,
            at,
            message,
        }
    }

    fn not_viewable(at: Option<ast::Type>) -> Self {
        let written = at.as_ref().map(|t| bare(t).syntax().text().to_string());
        let shown = written.map_or_else(|| "this type".to_owned(), |w| format!("`{w}`"));
        let message = format!("{shown} can't be viewed: only a `str` or a `List` can");
        Self {
            code: codes::E0420,
            at,
            message,
        }
    }
}

/// The errors of views.viewable-types and views.view-types in a type written as `node`, held
/// where `holder` says, each placed at its own written type, or at `node` where that isn't
/// written. Each is its own mistake, so each is reported (errors.root-causes): a stored view and
/// a type in it that can't be viewed are two.
fn problems(t: &Ty, node: Option<&ast::Type>, holder: &str, stored: bool, out: &mut Vec<Problem>) {
    let here = || node.cloned();
    let start = out.len();
    match t {
        _ if stored && is_view(t) => {
            out.push(Problem::stored(here(), holder));
            problems(t, node, holder, false, out);
        }
        Ty::Con(item, args) if is_view_item(item, "View") => {
            let Some(viewed) = args.first() else { return };
            let part = nth_part(node, 0);
            if viewable(viewed) {
                problems(viewed, part.as_ref(), holder, false, out);
            } else {
                out.push(Problem::not_viewable(part.or_else(here)));
            }
        }
        Ty::Con(item, args) => {
            // The payload of an `Option` and the elements of an `Iter` may be views.
            let free = is_prelude(item, "Option") || is_view_item(item, "Iter");
            let inner = format!("a `{}`", item.name);
            for (i, a) in args.iter().enumerate() {
                problems(a, nth_part(node, i).as_ref(), &inner, !free, out);
            }
        }
        Ty::Tuple(ts) => {
            for (i, a) in ts.iter().enumerate() {
                problems(a, nth_part(node, i).as_ref(), "a tuple", true, out);
            }
        }
        Ty::Fn(f) => fn_problems(f, node, holder, out),
        Ty::Handler(h) => handler_problems(h, node, out),
        Ty::App(_, args) => {
            for (i, a) in args.iter().enumerate() {
                problems(a, nth_part(node, i).as_ref(), "a constructor", true, out);
            }
        }
        Ty::Spread(_, t) => problems(t, None, "a tuple", true, out),
        Ty::Param(_) | Ty::SelfTy | Ty::Value(_) | Ty::Error => {}
    }
    for p in &mut out[start..] {
        if p.at.is_none() {
            p.at = here();
        }
    }
}

/// The error type that a row written as `row` raises, where it writes one.
fn raise_node(row: Option<ast::Row>) -> Option<ast::Type> {
    row.into_iter()
        .flat_map(|r| r.elements())
        .find_map(|e| match e {
            ast::RowElem::RowRaise(raise) => raise.ty(),
            _ => None,
        })
}

/// The errors in a function type written as `node`: its parameters and its result may be views,
/// its error type may not.
fn fn_problems(f: &FnTy, node: Option<&ast::Type>, holder: &str, out: &mut Vec<Problem>) {
    let written = match node.map(bare) {
        Some(ast::Type::FnType(w)) => Some(w),
        _ => None,
    };
    let params: Vec<Option<ast::Type>> = written
        .iter()
        .flat_map(|w| w.params().map(|p| p.ty()))
        .collect();
    let ret = written
        .as_ref()
        .and_then(ast::FnType::ret_type)
        .and_then(|r| r.ty());
    for (i, (_, p)) in f.params.iter().enumerate() {
        problems(
            p,
            params.get(i).cloned().flatten().as_ref(),
            holder,
            false,
            out,
        );
    }
    if let Some(t) = &f.ret {
        problems(t, ret.as_ref(), holder, false, out);
    }
    if let Some(t) = f.row.raise.as_deref() {
        let raise = raise_node(written.as_ref().and_then(ast::FnType::row));
        problems(t, raise.as_ref(), Holder::Raised.name(), true, out);
    }
}

/// The errors in a handler type written as `node`: its effect's type arguments and its error
/// type may not be views, its answer may, as a result may.
fn handler_problems(h: &HandlerTy, node: Option<&ast::Type>, out: &mut Vec<Problem>) {
    let written = match node.map(bare) {
        Some(ast::Type::HandlerType(w)) => Some(w),
        _ => None,
    };
    let effect = match written.as_ref().and_then(ast::HandlerType::effect) {
        Some(ast::EffectRef::Named(n)) => Some(n),
        _ => None,
    };
    for (i, t) in h.effect.args.iter().enumerate() {
        let at = effect.as_ref().and_then(|n| n.args().nth(i));
        problems(t, at.as_ref(), "an effect's type argument", true, out);
    }
    if let Some(t) = &h.answer {
        let answer = written
            .as_ref()
            .and_then(ast::HandlerType::answer)
            .and_then(|r| r.ty());
        problems(t, answer.as_ref(), "a handler's answer", false, out);
    }
    if let Some(t) = h.row.raise.as_deref() {
        let raise = raise_node(written.as_ref().and_then(ast::HandlerType::row));
        problems(t, raise.as_ref(), Holder::Raised.name(), true, out);
    }
}

impl Resolver<'_> {
    /// `t`, which a declaration writes as `node`, or the error type when it breaks
    /// views.viewable-types or views.view-types, which is reported. `holder` tells where the
    /// declaration puts a value of it.
    pub(super) fn checked_view(&mut self, t: Ty, node: Option<&ast::Type>, holder: Holder) -> Ty {
        if self.module.std {
            return t;
        }
        let mut found = Vec::new();
        problems(&t, node, holder.name(), holder.stores(), &mut found);
        if found.is_empty() {
            return t;
        }
        for p in found {
            // `problems` places each error at `node` where its own type isn't written.
            let at =
                p.at.map_or_else(TextRange::default, |n| self.at(bare(&n).syntax()));
            self.error(p.code, at, p.message);
        }
        Ty::Error
    }

    /// The error of views.viewable-types or views.view-types in a type that a body writes for a
    /// local, kept for the body's analyses, which report it when type checking finds no error
    /// (errors.root-causes).
    pub(super) fn check_written_view(&mut self, t: &Ty, node: &ast::Type) {
        if self.module.std {
            return;
        }
        let mut found = Vec::new();
        problems(t, Some(node), Holder::Free.name(), false, &mut found);
        for p in found {
            let at = self.at(bare(p.at.as_ref().unwrap_or(node)).syntax());
            self.analysed.push(Diagnostic::new(p.code, at, p.message));
        }
    }

    /// A function's row, whose error type, which is raised out of it and so stored, is checked
    /// as [`Resolver::checked_view`] checks a stored type.
    pub(super) fn checked_row(&mut self, mut row: Row, written: Option<ast::Row>) -> Row {
        let node = raise_node(written);
        if let Some(raise) = row.raise.take() {
            row.raise = Some(Box::new(self.checked_view(
                *raise,
                node.as_ref(),
                Holder::Raised,
            )));
        }
        row
    }
}
