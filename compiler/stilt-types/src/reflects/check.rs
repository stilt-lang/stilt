//! E0350 (meta.types-without-shape): where a function that reflects on a type parameter is
//! instantiated, the type given for it must have a shape, unless it has an impl of one of the
//! function's guards, and when the function reflects on its parts, so must each type its fields,
//! elements and payloads hold, at any depth, walked depth first in the order of meta.shapes, each
//! type once.

use stilt_diag::{Diagnostic, codes};
use stilt_hir::decls::Lookup;
use stilt_hir::hir::{GenericId, Name};
use stilt_syntax::TextRange;

use super::shapes::{Held, has_shape, parts};
use super::summary::{Use, params_of};
use super::{Key, Reflections, Reflects, Summary, own, root_param};
use crate::implements::implements_trait;
use crate::ty::{Table, Ty};

/// What names types and type parameters in messages, and the module a message is read in.
pub(crate) struct Names<'a> {
    pub(crate) generics: &'a dyn Fn(&GenericId) -> Name,
    pub(crate) module: &'a str,
}

impl Names<'_> {
    fn ty(&self, t: &Ty) -> String {
        Table::default().show(t, self.generics)
    }

    /// A function as the code of `module` names it.
    fn function(&self, key: &Key) -> String {
        let qualified = |home: &Name, name: &str| {
            if &**home == self.module {
                name.to_owned()
            } else {
                let last = home.rsplit('.').next().unwrap_or(home);
                format!("{last}.{name}")
            }
        };
        match key {
            Key::Function(item) => qualified(&item.home, &item.name),
            Key::Member(owner, name) | Key::ImplMethod(_, owner, name) => {
                format!("{}.{name}", owner.name)
            }
            Key::DefaultMethod(t, name) | Key::BuiltIn(t, name) => format!("{}.{name}", t.name),
        }
    }
}

/// A type without a shape that a walk found, with the types that hold it, outermost first.
struct Failure {
    ty: Ty,
    holders: Vec<(Ty, Held)>,
}

/// The walk of the types given for a type parameter that a function reflects on.
struct Walk<'a> {
    decls: &'a dyn Lookup,
    s: &'a Summary,
    with: &'a Reflects,
    seen: Vec<Ty>,
}

impl Walk<'_> {
    /// The first type in `t` that fails, depth first; `top` for the type given itself, whose
    /// parts are walked only when the function reflects on them.
    fn first(&mut self, t: &Ty, top: bool, holders: &mut Vec<(Ty, Held)>) -> Option<Failure> {
        match t {
            Ty::Param(g) if own(g) => return None,
            // A fresh type of a type given here stands for the types its shape's parts are.
            Ty::Param(g) => return self.fresh(g, holders),
            Ty::Var(_) | Ty::Error | Ty::SelfTy => return None,
            _ => {}
        }
        let guarded = self
            .with
            .guards
            .iter()
            .any(|tr| implements_trait(self.decls, (&Vec::new(), &[]), t, tr));
        if guarded {
            return None;
        }
        if !has_shape(self.decls, t) {
            return Some(Failure {
                ty: t.clone(),
                holders: holders.clone(),
            });
        }
        if top && !self.with.parts {
            return None;
        }
        for (part, held) in parts(self.decls, t) {
            if self.seen.contains(&part) {
                continue;
            }
            self.seen.push(part.clone());
            holders.push((t.clone(), held));
            let found = self.first(&part, false, holders);
            holders.pop();
            if found.is_some() {
                return found;
            }
        }
        None
    }

    /// A fresh type, or a rigid type of a closure given for `fields.build`: the parts of the
    /// type whose shape holds it, when that is no type parameter, which the body then reflects
    /// on instead.
    fn fresh(&mut self, g: &GenericId, holders: &mut Vec<(Ty, Held)>) -> Option<Failure> {
        if root_param(self.s, g).is_some() {
            return None;
        }
        let (_, of) = self.s.fresh_of.iter().find(|(f, _)| f == g)?;
        let of = of.clone();
        for (part, held) in parts(self.decls, &of) {
            holders.push((of.clone(), held));
            let found = self.first(&part, true, holders);
            holders.pop();
            if found.is_some() {
                return found;
            }
        }
        None
    }
}

/// The rigid types of polymorphic function types that a type holds and no shape gives, whose
/// instantiations can't be seen.
fn unseen(s: &Summary, t: &Ty) -> bool {
    let mut found = Vec::new();
    params_of(t, &mut found);
    found
        .iter()
        .any(|g| g.is_poly() && !s.fresh_of.iter().any(|(f, _)| f == g))
}

/// The errors of a body's summary, against the facts of the program.
pub(crate) fn errors(
    decls: &dyn Lookup,
    names: &Names<'_>,
    s: &Summary,
    facts: &Reflections,
) -> Vec<Diagnostic> {
    let mut errors = Vec::new();
    for u in &s.uses {
        if let Some(d) = use_error(decls, names, s, (u, facts)) {
            errors.push(d);
        }
    }
    for (t, at) in &s.shapes {
        let mut found = Vec::new();
        params_of(t, &mut found);
        if found
            .iter()
            .any(|g| g.is_poly() && !s.fresh_of.iter().any(|(f, _)| f == g))
        {
            errors.push(unseen_error(names, *at, t));
        } else if !matches!(t, Ty::Param(_)) && !has_shape(decls, t) {
            let message = format!(
                "`{}` has no shape, so its shape can't be named",
                names.ty(t)
            );
            errors.push(Diagnostic::new(codes::E0350, *at, message));
        }
    }
    errors.extend(method_errors(names, s, facts));
    // A bound met once uses each method of its impl, each of which may find the same type.
    let mut seen = Vec::new();
    errors.retain(|d| {
        let key = (d.range, d.message.clone());
        let new = !seen.contains(&key);
        seen.push(key);
        new
    });
    errors
}

/// E0350 at a use of a function that reflects, where a type given for one of its type
/// parameters fails, once, at the first argument whose type holds it, or at the use.
fn use_error(
    decls: &dyn Lookup,
    names: &Names<'_>,
    s: &Summary,
    (u, facts): (&Use, &Reflections),
) -> Option<Diagnostic> {
    let reflected = facts.of(&u.callee).iter().filter(|f| f.reflects.is_some());
    if u.poly && reflected.clone().next().is_some() {
        let message = format!(
            "`{}` reflects on its type, so it can't be given for a polymorphic function type, \
             whose type arguments each call picks where they can't be seen",
            names.function(&u.callee)
        );
        return Some(Diagnostic::new(codes::E0350, u.at, message));
    }
    for (cg, x) in &u.targs {
        let Some(with) = facts.param(&u.callee, cg).and_then(|f| f.reflects.as_ref()) else {
            continue;
        };
        if unseen(s, x) {
            return Some(unseen_error(names, u.at, x));
        }
        let mut walk = Walk {
            decls,
            s,
            with,
            seen: vec![x.clone()],
        };
        let Some(failure) = walk.first(x, true, &mut Vec::new()) else {
            continue;
        };
        let at = u
            .args
            .iter()
            .find(|(_, t)| holds_part(decls, t, &failure.ty, &mut Vec::new()))
            .map_or(u.at, |(at, _)| *at);
        let message = failed(names, (cg, with), &failure);
        return Some(Diagnostic::new(codes::E0350, at, message));
    }
    None
}

/// Whether a type holds another, as itself or in its shape's parts, at any depth.
fn holds_part(decls: &dyn Lookup, t: &Ty, inner: &Ty, seen: &mut Vec<Ty>) -> bool {
    if t == inner {
        return true;
    }
    if seen.contains(t) {
        return false;
    }
    seen.push(t.clone());
    parts(decls, t)
        .iter()
        .any(|(part, _)| holds_part(decls, part, inner, seen))
}

/// Whether a type holds another, as itself or among its arguments.
fn holds(t: &Ty, inner: &Ty) -> bool {
    t == inner
        || match t {
            Ty::Con(_, ts) | Ty::Tuple(ts) => ts.iter().any(|t| holds(t, inner)),
            _ => false,
        }
}

/// E0350's message: the type without a shape, the types that hold it, and the chain of
/// functions that reflect.
fn failed(names: &Names<'_>, (param, with): (&GenericId, &Reflects), f: &Failure) -> String {
    let mut held = String::new();
    for (holder, how) in f.holders.iter().rev() {
        held.push_str(if held.is_empty() { ": it is " } else { ", in " });
        held.push_str(&how.of(&names.ty(holder)));
    }
    let first = with
        .chain
        .first()
        .map(|k| names.function(k))
        .unwrap_or_default();
    let what = if with.parts {
        format!("the parts of its `{}`", (names.generics)(param))
    } else {
        format!("its `{}`", (names.generics)(param))
    };
    let through = match with.chain.get(1..) {
        Some(rest) if !rest.is_empty() => {
            let rest: Vec<String> = rest
                .iter()
                .map(|k| format!("`{}`", names.function(k)))
                .collect();
            format!(", through {}", rest.join(", "))
        }
        _ => String::new(),
    };
    let guards = if with.guards.is_empty() {
        String::new()
    } else {
        let traits: Vec<String> = with
            .guards
            .iter()
            .map(|t| format!("`{}`", t.name))
            .collect();
        format!(", nor an impl of {}", traits.join(" or "))
    };
    format!(
        "`{}` has no shape{guards}{held}, and `{first}` reflects on {what}{through}",
        names.ty(&f.ty)
    )
}

fn unseen_error(names: &Names<'_>, at: TextRange, t: &Ty) -> Diagnostic {
    let message = format!(
        "`{}` is a type of a polymorphic function type, which each call picks where it can't be \
         seen, so nothing can reflect on it",
        names.ty(t)
    );
    Diagnostic::new(codes::E0350, at, message)
}

/// E0350 where a trait's method, or an impl's, reflects on its own type parameters, or a trait's
/// default method on `Self`, whose callers reach it through a bound, at the first expression
/// that reflects on one. In an impl, `Self` is the impl's type, which is seen.
fn method_errors(names: &Names<'_>, s: &Summary, facts: &Reflections) -> Vec<Diagnostic> {
    if !matches!(s.key, Key::ImplMethod(..) | Key::DefaultMethod(..)) {
        return Vec::new();
    }
    let mut unseen: Vec<(Ty, String)> = facts
        .of(&s.key)
        .iter()
        .filter(|f| f.reflects.is_some() && f.param.owner.member.is_some())
        .map(|f| {
            (
                Ty::Param(f.param.clone()),
                (names.generics)(&f.param).to_string(),
            )
        })
        .collect();
    if matches!(s.key, Key::DefaultMethod(..)) {
        unseen.push((Ty::Param(super::self_param()), "Self".to_owned()));
    }
    let mut errors = Vec::new();
    for (param, name) in unseen {
        let at = s
            .shapes
            .iter()
            .find(|(t, _)| *t == param)
            .map(|(_, at)| *at)
            .or_else(|| {
                s.uses
                    .iter()
                    .find(|u| {
                        u.targs.iter().any(|(cg, x)| {
                            holds(x, &param)
                                && facts
                                    .param(&u.callee, cg)
                                    .is_some_and(|f| f.reflects.is_some())
                        })
                    })
                    .map(|u| u.at)
            });
        if let Some(at) = at {
            let message = format!(
                "this method reflects on its own `{name}`, but its callers reach it through a \
                 trait's bound, where the type given for it can't be seen"
            );
            errors.push(Diagnostic::new(codes::E0350, at, message));
        }
    }
    errors
}
