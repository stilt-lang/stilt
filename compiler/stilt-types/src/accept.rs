//! The rules of acceptance (facts.rules-of-acceptance): six shapes of code, each with a name, that
//! decide what `without panic` and `without div` accept, so that a reader predicts every verdict
//! and an error names the rule it misses.
//!
//! The rules read a body's text, the names it binds and their types, and never the facts of the
//! analysis (facts.rules-of-acceptance): [`accepted`] is a query of one body, which reads the
//! signatures and declarations of what it names and never another body (local-inference). A closure
//! literal's body, and each operation's body of a handler literal, is read on its own: the tests
//! around it don't guard its code, and its code writes nothing of the body around it
//! (expressions.closure-boundaries).
//!
//! Rule numbers in comments refer to the Reference's facts chapter unless they name another record.

mod code;
mod divides;
mod indexes;
mod loops;
mod recursion;
mod signs;
pub(crate) mod text;
mod walk;
mod walked;

#[cfg(test)]
mod tests;

use stilt_db::{Db, Program, SourceFile};
use stilt_hir::decls::{Lookup, QueriedOnce};
use stilt_hir::hir::{Item, LocalId, Name};
use stilt_syntax::{TextRange, TextSize};

use crate::analyses::implicit::Key;
use crate::owners::BodyOwner;
use crate::queries::{body_owner, infer_body, module_info};
use crate::tast::{Definition, TypedBody};
use crate::verify::Check;

/// A rule of acceptance (facts.range-loops, facts.guards, facts.divisors, facts.keys,
/// facts.counting-loops and facts.shrinking-recursion), by the name that E0204 and `show` print.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Rule {
    /// facts.range-loops.
    RangeLoop,
    /// facts.guards.
    Guard,
    /// facts.divisors.
    Divisor,
    /// facts.keys.
    Key,
    /// facts.counting-loops.
    CountingLoop,
    /// facts.shrinking-recursion.
    ShrinkingRecursion,
}

impl Rule {
    /// The rule's name (facts.rules-of-acceptance), as in `proved bounds by a range loop`.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Rule::RangeLoop => "range loop",
            Rule::Guard => "guard",
            Rule::Divisor => "divisor",
            Rule::Key => "key",
            Rule::CountingLoop => "counting loop",
            Rule::ShrinkingRecursion => "shrinking recursion",
        }
    }
}

/// What the rule closest to an operation needs that its code doesn't give: the first of the rule's
/// conditions that the code doesn't meet (facts.closest-rule). Ranges are relative to the body's
/// start and name the expressions whose text E0204 writes; offsets name the lines it gives.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Need {
    /// facts.range-loops: an index inside a closure literal of the loop's body.
    OutsideClosures,
    /// facts.range-loops: an index other than `i`, `i + k` or `i - k`, for the loop's variable.
    IndexForm(LocalId),
    /// A start that isn't known non-negative, for `i` and `i + k`.
    StartNonNegative,
    /// A start below `k`, for `i - k`.
    StartAtLeast(TextRange),
    /// An end other than `P.len()`, or `P.len() - k` for `i + k`: the list, the `k`, the end
    /// and whether the range includes it.
    EndAt(TextRange, Option<TextRange>, TextRange, bool),
    /// A body that changes the length of the list, and where.
    KeepsLength(TextRange, TextSize),
    /// facts.guards: an index that is no name or literal.
    GuardForm,
    /// No test that gives the index `>= 0`: the index.
    LowerTest(TextRange),
    /// No test that gives the index below the list's length: the index and the list.
    UpperTest(TextRange, TextRange),
    /// A write of the index between the test and the access: the index, and where.
    GuardWrites(TextRange, TextSize),
    /// A change of the list's length between the test and the access: the list, and where.
    GuardLength(TextRange, TextSize),
    /// facts.divisors.
    DivisorForm,
    /// No test that gives the divisor `!= 0`: the divisor.
    DivisorTest(TextRange),
    /// A write of the divisor between the test and the division: the divisor, and where.
    DivisorWrites(TextRange, TextSize),
    /// facts.keys.
    KeyForm,
    /// A key of a type whose `Eq` and `Hash` aren't structural.
    KeyType,
    /// No test or store of the key before the read: the map and the key.
    KeyTest(TextRange, TextRange),
    /// A write of the key between the test and the access: the key, and where.
    KeyWrites(TextRange, TextSize),
    /// A change of the map other than a store, before the access: the map, and where.
    KeyChanges(TextRange, TextSize),
    /// facts.counting-loops.
    Comparison,
    /// A compared name that isn't a `var` of an integer type.
    CounterVar,
    /// A bound that the loop changes where it does, or that is made of other forms.
    Bound(Option<TextSize>),
    /// No step `v += s`, or `v -= s` when the counter falls.
    Step(LocalId, bool),
    /// A `continue` before the step: the counter, whether it grows, the step's `s` and where.
    ContinueBefore(LocalId, bool, TextRange, TextSize),
    /// A write of the counter other than its step: the counter, and where.
    CounterWrites(LocalId, TextSize),
    /// facts.shrinking-recursion.
    ShrinkForm,
    /// No test that bounds the parameter, which falls or grows, at the self-call there.
    ShrinkTest(LocalId, bool, TextSize),
}

/// Whether a rule proves an operation, or what the closest rule needs.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Verdict {
    /// This rule proves it.
    Proved(Rule),
    /// The closest rule needs this.
    Lacks(Need),
}

/// What the rules of acceptance decide of a body.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Accepted {
    /// The checks of indexes, divisions and keys, each where its operation is, relative to the
    /// body's start (facts.range-loops, facts.guards, facts.divisors and facts.keys).
    pub checks: Vec<(TextRange, Check, Verdict)>,
    /// The `while` and `loop` expressions, and whether each ends (facts.counting-loops).
    pub loops: Vec<(TextRange, Verdict)>,
    /// Whether the function's self-calls shrink, when it has one (facts.shrinking-recursion).
    pub recursion: Option<Verdict>,
}

impl Accepted {
    /// The rule that proves the check at `at`, if one does.
    #[must_use]
    pub fn proves(&self, at: TextRange, check: Check) -> Option<Rule> {
        self.checks.iter().find_map(|(a, c, v)| match v {
            Verdict::Proved(rule) if *a == at && *c == check => Some(*rule),
            _ => None,
        })
    }

    /// What the closest rule needs of the check at `at`, if no rule proves it.
    #[must_use]
    pub fn lacks(&self, at: TextRange, check: Check) -> Option<&Need> {
        self.checks.iter().find_map(|(a, c, v)| match v {
            Verdict::Lacks(need) if *a == at && *c == check => Some(need),
            _ => None,
        })
    }

    /// Whether the `while` at `at` ends by facts.counting-loops.
    #[must_use]
    pub fn ends(&self, at: TextRange) -> bool {
        self.loops
            .iter()
            .any(|(a, v)| *a == at && matches!(v, Verdict::Proved(_)))
    }

    /// Whether some `while` of the body ends by facts.counting-loops.
    #[must_use]
    pub fn any_ends(&self) -> bool {
        self.loops
            .iter()
            .any(|(_, v)| matches!(v, Verdict::Proved(_)))
    }

    /// What the counting loop needs of the `while` or `loop` at `at`.
    #[must_use]
    pub fn loop_need(&self, at: TextRange) -> Option<&Need> {
        self.loops.iter().find_map(|(a, v)| match v {
            Verdict::Lacks(need) if *a == at => Some(need),
            _ => None,
        })
    }

    /// Whether the function's self-calls shrink by facts.shrinking-recursion, which holds of no
    /// self-call.
    #[must_use]
    pub fn shrinks(&self) -> bool {
        !matches!(self.recursion, Some(Verdict::Lacks(_)))
    }

    /// What shrinking recursion needs of the function's self-calls, if they don't shrink.
    #[must_use]
    pub fn recursion_need(&self) -> Option<&Need> {
        match &self.recursion {
            Some(Verdict::Lacks(need)) => Some(need),
            _ => None,
        }
    }
}

/// What the rules read of a body's declaration and of the items it names.
pub(crate) struct Context<'a> {
    pub(crate) decls: &'a dyn Lookup,
    /// The body's function, whose self-calls facts.shrinking-recursion reads.
    pub(crate) key: Option<&'a Key>,
    /// The parameters' types, in order, a method's receiver first, where the signature gives
    /// them.
    pub(crate) params: Vec<crate::ty::Ty>,
    /// The value of a constant written as an integer literal, with or without a `-` (facts.terms).
    pub(crate) literal: &'a dyn Fn(&Item, Option<Name>) -> Option<i128>,
}

/// The rules of acceptance on the body `index` of a file's module. A body with an error, and a
/// native one, has nothing proved.
#[salsa::tracked(returns(ref))]
pub fn accepted(db: &dyn Db, program: Program, file: SourceFile, index: u32) -> Accepted {
    let body = &infer_body(db, program, file, index).body;
    let module = module_info(db, program, file);
    let owner = body_owner(db, program, file, index);
    let key = owner.key(module.name);
    let decls = QueriedOnce::new(db, program);
    let literal = |item: &Item, member: Option<Name>| {
        *stilt_hir::values::literal_value(db, program, item.clone(), member)
    };
    let params = match owner {
        BodyOwner::Fn { signature, .. } => signature
            .params
            .iter()
            .map(|(_, t)| crate::ty::Ty::from_hir(t, None))
            .collect(),
        _ => Vec::new(),
    };
    let cx = Context {
        decls: &decls,
        key: key.as_ref(),
        params,
        literal: &literal,
    };
    accept(&cx, body)
}

/// The rules of acceptance on a typed body.
pub(crate) fn accept(cx: &Context<'_>, body: &TypedBody) -> Accepted {
    let Definition::Code(code) = &body.code else {
        return Accepted::default();
    };
    let walked = walk::Walk::run(cx, code);
    let signs = signs::Signs::of(cx, &walked);
    let rules = indexes::Rules {
        cx,
        walked: &walked,
        signs: &signs,
    };
    Accepted {
        checks: rules.checks(),
        loops: rules.loops(),
        recursion: rules.recursion(body),
    }
}
