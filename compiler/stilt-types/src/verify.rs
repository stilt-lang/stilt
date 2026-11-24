//! The analysis of verification (facts.difference-facts, facts.linear-forms and
//! facts.analysis-order): the difference facts between the integer values of each body, and the
//! checks they prove can't fail, which only release builds read. What `check` accepts is the rules
//! of acceptance's alone ([`crate::accept`]).
//!
//! Each body is analysed on its own, reading the signatures and declarations of what it names and
//! never another body (local-inference): [`verified`] is a query of one body. Its closure literals
//! and its handlers' operations are analysed apart, inside it, each capture with one term. Each
//! integer value is a term that never changes, so a fact on it holds until a loop's head gives the
//! binding a new one; the facts are kept closed, with constants exact in `i128`, and a loop's head
//! is reached by widening at the loop's thresholds and one narrowing visit.
//!
//! Rule numbers in comments refer to the Reference's facts chapter unless they name another record.

mod calls;
mod checks;
mod conds;
mod control;
pub(crate) mod dbm;
mod exprs;
mod loops;
mod paths;
mod places;
mod scan;
mod state;
mod values;
mod walker;

#[cfg(test)]
pub(crate) mod tests;

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::decls::{Lookup, QueriedOnce};
use stilt_hir::hir::{GenericId, Item, Name};
use stilt_syntax::TextRange;

use crate::owners::BodyOwner;
use crate::queries::{body_owner, infer_body};
use crate::tast::{Definition, TypedBody};

/// What a proof rules out (facts.proved-indexes, facts.proved-divisions, facts.map-keys and
/// facts.proved-overflow).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Check {
    /// A `bounds` panic of an element's read or write, or of a call of facts.proved-indexes's
    /// table.
    Bounds,
    /// A division by zero.
    DivideByZero,
    /// A read of a key a map doesn't hold.
    MissingKey,
    /// An overflow of arithmetic, a shift or a signed division or remainder, which no limit reads
    /// (facts.proved-overflow).
    Overflow,
}

impl Check {
    /// The fact as `show` prints it, as in `proved bounds`; none for an overflow
    /// (facts.shown-proofs).
    #[must_use]
    pub fn shown(self) -> Option<&'static str> {
        match self {
            Check::Bounds => Some("bounds"),
            Check::DivideByZero => Some("divide-by-zero"),
            Check::MissingKey => Some("missing-key"),
            Check::Overflow => None,
        }
    }
}

/// A check that the facts prove can't fail: where the operation is, relative to its body's
/// start, and what it rules out.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Proof {
    /// Where the operation is, relative to its body's start.
    pub at: TextRange,
    /// What it rules out.
    pub check: Check,
}

/// What the analysis of a body finds.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Proofs {
    /// The checks it proves, in the order of the body.
    pub proved: Vec<Proof>,
    /// The checks it doesn't prove.
    pub unproved: Vec<(TextRange, Check)>,
}

impl Proofs {
    /// Whether the operation at `at` can't fail by `check`: each time the analysis met it, as a
    /// guard of an or-pattern is met once for each way, the facts gave it.
    #[must_use]
    pub fn proves(&self, at: TextRange, check: Check) -> bool {
        self.proved.iter().any(|p| p.at == at && p.check == check)
            && !self.unproved.contains(&(at, check))
    }
}

/// What the analysis reads of a body's declaration and of the items it names.
pub(crate) struct Context<'a> {
    pub(crate) decls: &'a dyn Lookup,
    /// The value parameters of integer types in scope, with their types' names.
    pub(crate) values: Vec<(GenericId, String)>,
    /// The parameters' types, in order, a method's receiver first, where the signature gives
    /// them.
    pub(crate) params: Vec<crate::ty::Ty>,
    /// The value of a constant written as an integer literal, with or without a `-` (facts.terms).
    pub(crate) literal: &'a dyn Fn(&Item, Option<Name>) -> Option<i128>,
}

/// The analysis of the body `index` of a file's module (facts.verification). A body with an error,
/// and a native one, has nothing proved.
#[salsa::tracked(returns(ref))]
pub fn verified(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Proofs {
    let body = &infer_body(db, program, file, index).body;
    let owner = body_owner(db, program, file, index);
    let decls = QueriedOnce::new(db, program);
    let literal = |item: &Item, member: Option<Name>| {
        *stilt_hir::values::literal_value(db, program, item.clone(), member)
    };
    let (values, params) = match owner {
        BodyOwner::Fn { signature, .. } => (
            signature
                .values
                .iter()
                .filter_map(|(id, ty)| {
                    let ty = crate::ty::Ty::from_hir(ty, None);
                    ty.integer_name().map(|name| (id.clone(), name.to_owned()))
                })
                .collect(),
            signature
                .params
                .iter()
                .map(|(_, t)| crate::ty::Ty::from_hir(t, None))
                .collect(),
        ),
        _ => (Vec::new(), Vec::new()),
    };
    let cx = Context {
        decls: &decls,
        values,
        params,
        literal: &literal,
    };
    analyse(&cx, body)
}

/// The analysis of a typed body.
pub(crate) fn analyse(cx: &Context<'_>, body: &TypedBody) -> Proofs {
    let Definition::Code(code) = &body.code else {
        return Proofs::default();
    };
    let info = scan::Info::of(cx, body, code);
    let mut w = walker::Walker::new(cx, &info);
    w.body(body, code);
    w.finish()
}

/// The checks that a release build of the body `index` drops: those the analysis
/// proves, and those a rule of acceptance proves.
#[salsa::tracked(returns(ref))]
pub fn released(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Proofs {
    let mut proofs = verified(db, program, file, index).clone();
    let accepted = crate::accept::accepted(db, program, file, index);
    for (at, check, verdict) in &accepted.checks {
        if matches!(verdict, crate::accept::Verdict::Proved(_)) {
            proofs.unproved.retain(|u| *u != (*at, *check));
            if !proofs
                .proved
                .iter()
                .any(|p| p.at == *at && p.check == *check)
            {
                proofs.proved.push(Proof {
                    at: *at,
                    check: *check,
                });
            }
        }
    }
    proofs
}

/// Whether the `Eq` and `Hash` of a key type are a primitive type's or structural throughout
/// its parts, never a type parameter's (facts.map-keys).
pub(crate) fn keyable(decls: &dyn Lookup, ty: &crate::ty::Ty) -> bool {
    scan::keyable(decls, ty, &mut Vec::new())
}
