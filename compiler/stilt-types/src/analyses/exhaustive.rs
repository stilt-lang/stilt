//! The exhaustiveness and the reachability of the arms of `match` and `catch` (patterns.algorithm,
//! patterns.non-exhaustive-matches and patterns.unreachable-arms; effects.catch).
//!
//! Rule numbers in comments refer to the Reference's patterns chapter. The algorithm is Maranget's
//! usefulness ("Warnings for pattern matching", 2007): a pattern vector is useful with respect to a
//! matrix of earlier rows when some value vector matches it and no row.

mod ctors;
mod patterns;
#[cfg(test)]
mod tests;
mod usefulness;

use std::collections::HashSet;

use stilt_diag::{Alternative, AlternativeKind, Diagnostic, Edit, Fix, codes};
use stilt_hir::decls::Lookup;
use stilt_hir::hir::{Item, Name};
use stilt_syntax::TextRange;

use crate::tast::{self, Arm, Block, ExprKind, walk};
use crate::ty::Ty;

use ctors::{all_ctors, arity};
use patterns::{holds_constant, of_pattern, touches_error};
use usefulness::useful;

/// The constructors of patterns.algorithm. Lists have one constructor per length, and `AtLeast(n)`
/// stands for every length from `n` on, once no pattern tells those lengths apart.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Ctor {
    Variant(Item),
    Bool(bool),
    Tuple(usize),
    /// An array of this size, matched as a tuple of its elements, which a witness writes as a
    /// list pattern (generics.array-patterns).
    Array(usize),
    /// Its fields, in declaration order.
    Record(Item, Vec<Name>),
    /// The [`int_canonical`](crate::literal::int_canonical) form of the literal.
    Int(String),
    Str(String),
    Len(usize),
    AtLeast(usize),
}

/// A pattern as the algorithm reads it.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Pat {
    Wild,
    Ctor(Ctor, Vec<Pat>),
    /// `[p1, …, pn, ..]`, the lists of at least `n` elements.
    Prefix(Vec<Pat>),
    Or(Vec<Pat>),
}

/// `n` wildcards.
fn wilds(n: usize) -> Vec<Pat> {
    vec![Pat::Wild; n]
}

/// The errors of every `match` and `catch` of a body, and the warnings of every `if let` whose arms don't cover every value, each
/// with a missing pattern in its message, then the warnings for the arms that can never match.
/// The arms of a `catch` that handles `Never` aren't checked for reachability: the empty `try`
/// is the mistake (effects.empty-try).
pub(crate) fn check(decls: &dyn Lookup, block: &Block) -> (Vec<Diagnostic>, Vec<Diagnostic>) {
    let mut errors = Vec::new();
    let mut warnings = Vec::new();
    walk::exprs_of_block(block, &mut |e| {
        let (missing, unreachable) = match &e.kind {
            ExprKind::Match(scrutinee, arms) => check_arms(decls, e.at, true, &scrutinee.ty, arms),
            ExprKind::Try(_, Some(c)) => {
                check_arms(decls, e.at, !c.handles_never(), &c.error, &c.arms)
            }
            ExprKind::IfLet(pattern, scrutinee, _, _) => (
                None,
                always_matches(decls, &scrutinee.ty, pattern)
                    .into_iter()
                    .collect(),
            ),
            _ => return,
        };
        errors.extend(missing);
        warnings.extend(unreachable);
    });
    (errors, warnings)
}

/// expressions.if-let-always: the warning of an `if let` whose pattern matches every value of the
/// scrutinee's type, holds no constant and isn't matched against the error type.
fn always_matches(decls: &dyn Lookup, ty: &Ty, pattern: &tast::Pat) -> Option<Diagnostic> {
    let p = of_pattern(decls, pattern);
    let skipped = *ty == Ty::Error || holds_constant(pattern) || touches_error(decls, ty, &p);
    let tys = std::slice::from_ref(ty);
    if skipped || useful(decls, tys, &[vec![p]], &[Pat::Wild]).is_some() {
        return None;
    }
    let d = Diagnostic::new(
        codes::W0303,
        pattern.at,
        "this pattern matches every value, so the block always runs",
    );
    // A name bound to an `Option` is most often meant to bind what it holds, as Swift's
    // `if let` does.
    Some(match (&pattern.kind, ty.is_prelude("Option")) {
        (tast::PatKind::Bind(_), true) => {
            let at = pattern.at;
            let fix = Fix::new(
                "match what the `Option` holds",
                vec![
                    Edit::insert(at.start(), "Some("),
                    Edit::insert(at.end(), ")"),
                ],
            );
            d.with_fix(fix)
        }
        _ => d,
    })
}

/// Earlier rows that are each `_`, or constructors without fields and alternatives of them, as
/// most arms over integers, strings and enumerations are. Against them, such a pattern is
/// useful exactly when no row is `_` and one of its constructors is in no row, which
/// [`useful`] finds by scanning every row: a `match` of many arms would scan them once per arm
/// (goal bounded-checking).
struct Flat {
    /// Whether every row so far is one of those.
    simple: bool,
    wild: bool,
    seen: HashSet<Ctor>,
}

/// The constructors of a pattern that is one constructor without fields or alternatives of
/// them.
fn bare_ctors(p: &Pat) -> Option<Vec<&Ctor>> {
    match p {
        Pat::Ctor(c, ps) if ps.is_empty() => Some(vec![c]),
        Pat::Or(alts) => alts
            .iter()
            .map(|alt| match alt {
                Pat::Ctor(c, ps) if ps.is_empty() => Some(c),
                _ => None,
            })
            .collect(),
        Pat::Wild | Pat::Ctor(..) | Pat::Prefix(_) => None,
    }
}

impl Flat {
    fn add(&mut self, p: &Pat) {
        if *p == Pat::Wild {
            self.wild = true;
        } else if let Some(ctors) = bare_ctors(p) {
            self.seen.extend(ctors.into_iter().cloned());
        } else {
            self.simple = false;
        }
    }

    /// Whether `p` is useful, when the rows decide it without [`useful`].
    fn useful(&self, p: &Pat) -> Option<bool> {
        if !self.simple {
            return None;
        }
        let ctors = bare_ctors(p)?;
        Some(!self.wild && ctors.iter().any(|c| !self.seen.contains(*c)))
    }
}

/// patterns.guards-and-constants, patterns.non-exhaustive-matches and patterns.unreachable-arms
/// over the arms of one `match` or `catch`: its error if the arms leave a value, and the warnings
/// for arms that can never match. The rows of earlier arms count only when they have no guard and
/// hold no constant. An arm that looks inside a part of the error type takes no part in
/// reachability.
fn check_arms(
    decls: &dyn Lookup,
    at: TextRange,
    reachability: bool,
    ty: &Ty,
    arms: &[Arm],
) -> (Option<Diagnostic>, Vec<Diagnostic>) {
    // Arms matched against the error type take no part in reachability: no diagnostic
    // arises from it (errors.error-type).
    let reachability = reachability && *ty != Ty::Error;
    let tys = std::slice::from_ref(ty);
    let mut covering = Vec::new();
    let mut certain = Vec::new();
    let mut flat = Flat {
        simple: true,
        wild: false,
        seen: HashSet::new(),
    };
    let mut unreachable = Vec::new();
    for a in arms {
        let p = of_pattern(decls, &a.pattern);
        let unsure = touches_error(decls, ty, &p);
        let reachable = || {
            flat.useful(&p)
                .unwrap_or_else(|| useful(decls, tys, &certain, std::slice::from_ref(&p)).is_some())
        };
        if reachability && !unsure && !reachable() {
            let arm = a.pattern.at.cover(a.body.at);
            let fix = Fix::new("delete the arm", vec![Edit::delete(arm)]);
            let d = Diagnostic::new(
                codes::W0301,
                a.pattern.at,
                "the arms before this one match everything it matches",
            );
            unreachable.push(d.with_fix(fix));
        }
        if a.guard.is_none() && !holds_constant(&a.pattern) {
            if !unsure {
                flat.add(&p);
                certain.push(vec![p.clone()]);
            }
            covering.push(vec![p]);
        }
    }
    let missing = useful(decls, tys, &covering, &[Pat::Wild]).map(|w| {
        let alternatives = uncovered(decls, ty, &covering, &w[0])
            .into_iter()
            .map(|p| Alternative::new(AlternativeKind::Variant, p));
        Diagnostic::new(
            codes::E0329,
            at,
            format!("these patterns don't cover `{}`", show(&w[0])),
        )
        .with_alternatives(alternatives)
    });
    (missing, unreachable)
}

/// The patterns that the rows `covering` leave, for the admissible alternatives of E0329
/// (goal admissible-alternatives): for a type with constructors, the value of each constructor that
/// the rows miss, in the type's order; for one without, the first `witness` alone.
fn uncovered(decls: &dyn Lookup, ty: &Ty, covering: &[Vec<Pat>], witness: &Pat) -> Vec<String> {
    let tys = std::slice::from_ref(ty);
    let mut found = vec![show(witness)];
    for c in all_ctors(decls, ty).unwrap_or_default() {
        let q = Pat::Ctor(c.clone(), wilds(arity(decls, ty, &c)));
        if let Some(w) = useful(decls, tys, covering, std::slice::from_ref(&q)) {
            let text = show(&w[0]);
            if !found.contains(&text) {
                found.push(text);
            }
        }
    }
    found
}

/// A witness, as a program would write the pattern.
fn show(p: &Pat) -> String {
    match p {
        Pat::Wild => "_".to_owned(),
        Pat::Or(ps) => ps.iter().map(show).collect::<Vec<_>>().join(" | "),
        Pat::Prefix(ps) => list(ps, true),
        Pat::Ctor(c, ps) => show_ctor(c, ps),
    }
}

/// A witness built with a constructor, from the witnesses of its fields. An array's trailing `_`
/// are written `..`, as its patterns may write them (generics.array-patterns), so that a witness is
/// never as long as a large array.
fn show_ctor(c: &Ctor, ps: &[Pat]) -> String {
    let args = || ps.iter().map(show).collect::<Vec<_>>().join(", ");
    match c {
        Ctor::Variant(v) if ps.is_empty() => v.name.to_string(),
        Ctor::Variant(v) => format!("{}({})", v.name, args()),
        Ctor::Bool(b) => b.to_string(),
        Ctor::Tuple(_) => format!("({})", args()),
        Ctor::Record(item, fields) => {
            let fields: Vec<String> = fields
                .iter()
                .zip(ps)
                .map(|(f, p)| format!("{f}: {}", show(p)))
                .collect();
            format!("{} {{ {} }}", item.name, fields.join(", "))
        }
        Ctor::Int(_) | Ctor::Str(_) => "_".to_owned(),
        Ctor::Len(_) => list(ps, false),
        Ctor::Array(_) => {
            let kept = ps.len() - ps.iter().rev().take_while(|p| **p == Pat::Wild).count();
            list(&ps[..kept], kept < ps.len())
        }
        Ctor::AtLeast(_) => list(ps, true),
    }
}

/// A list pattern of these elements, followed by `..` if `open`.
fn list(ps: &[Pat], open: bool) -> String {
    let mut parts: Vec<String> = ps.iter().map(show).collect();
    if open {
        parts.push("..".to_owned());
    }
    format!("[{}]", parts.join(", "))
}
