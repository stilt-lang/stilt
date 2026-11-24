//! Implicit effects (facts.implicit-effects; facts.div), and the checks of `without panic`
//! (effects.without-panic), `without alloc` (facts.without-alloc) and `without div`
//! (facts.without-div).
//!
//! Each body is summarized on its own, by [`summary`], and [`effects`] finds the items that
//! have each effect as fixed points over the summaries, so that a change to one body redoes only
//! its summary and the fixed points. `copy` (facts.copy) reads the shared writes of
//! modes.shared-writes, which `stilt-rc` infers, so this crate gives its sites and that crate
//! checks it.
//!
//! Rule numbers in comments refer to the Reference's facts chapter, unless they name another
//! record.

pub(crate) mod alloc;
mod capabilities;
mod descent;
mod fixed;
mod foreign;
pub(crate) mod in_place;
mod limits;
pub(crate) mod locks;
mod names;
mod natives;
mod remedies;
mod sites;
mod storage;

use stilt_hir::decls::Lookup;
use stilt_hir::hir::{Capabilities, Capability, Item, Limits, LocalId, Name};
use stilt_syntax::TextRange;

use crate::tast::walk;
use crate::tast::{Code, Definition, TypedBody};

pub(crate) use fixed::{Effects, Summary, effects, unproved};
#[cfg(test)]
pub(crate) use fixed::{Via, reach};
pub(crate) use foreign::foreign_summaries;
pub use in_place::InPlace;
pub(crate) use limits::{Limited, errors};
pub use limits::{describe, located, through, verb};
pub(crate) use names::{callee_key, held};
use natives::{is_built_in, native_allocates, native_diverges, native_overflows, native_panics};
use remedies::Remedy;
pub(crate) use sites::divides;
use sites::find;

/// An item with a body, whose implicit effects are inferred, or a built-in method that
/// allocates.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Key {
    /// A function of a module.
    Function(Item),
    /// A function of an inherent impl, by its type constructor and name.
    Member(Item, Name),
    /// A method of a trait impl, by its trait, type constructor and name.
    ImplMethod(Item, Item, Name),
    /// A default method of a trait, by its trait and name.
    DefaultMethod(Item, Name),
    /// A method of an impl that no source declares, by its trait and name, whose result is
    /// text it makes: `Show`'s (facts.native-allocation). It has no body, and allocates.
    BuiltIn(Item, Name),
}

/// An operation that has an effect itself, as messages name it: where it is written, as in
/// "this index", and inside a function that other code names, as in "an index".
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Fact {
    /// As where it is written: "this index".
    pub this: String,
    /// As inside a function that other code names: "an index".
    pub a: String,
}

impl Fact {
    /// The operation that `noun` names, such as "index" or "`assert`".
    fn noun(noun: &str) -> Self {
        let first = noun.chars().find(char::is_ascii_alphabetic).unwrap_or('x');
        let article = if "aeiou".contains(first) { "an" } else { "a" };
        Self {
            this: format!("this {noun}"),
            a: format!("{article} {noun}"),
        }
    }

    /// An operation named the same way wherever it is, such as "the constructor `Cons`".
    fn definite(text: String) -> Self {
        Self {
            this: text.clone(),
            a: text,
        }
    }
}

/// A modification that stays in place only if modes.shared-writes doesn't make it shared, which
/// `stilt-rc` decides (facts.writes-in-place and facts.copy-at-call): the binding it modifies, and
/// where the walk of modes puts the modification, the statement of an assignment or the call of an
/// `inout` argument.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Pending {
    /// The binding it modifies.
    pub binding: LocalId,
    /// Where the walk of modes puts the modification.
    pub modified: TextRange,
    /// For an argument of an in-place parameter, the callee that updates it in place.
    pub callee: Option<Key>,
}

/// An operation of a body: one that has an effect itself, as its facts say, or one that names
/// items whose implicit effects it inherits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Site {
    at: TextRange,
    /// What the operation is, when it can panic itself.
    panic: Option<Fact>,
    /// What the operation is, when it can overflow itself (effects.overflow-effect).
    overflow: Option<Fact>,
    /// What the operation is, when it allocates itself.
    alloc: Option<Fact>,
    /// What the operation is, when it may not end itself (facts.div).
    div: Option<Fact>,
    /// What the operation is, when it copies an argument for a callee that updates it in place
    /// (facts.copy-at-call and facts.copy).
    copy: Option<Fact>,
    /// What the operation is, when it holds shared values: a `when` (shared.locks).
    locks: Option<Fact>,
    names: Vec<Key>,
    /// Whether the operation calls what it names, with arguments that facts.descending-self-calls
    /// reads, rather than using a function as a value.
    called: bool,
    /// Whether the items it names add no `alloc`: `view.into` and `view.split` on storage that
    /// the body holds (facts.writes-in-place).
    in_place: bool,
    /// The modification that keeps the operation in place unless it is shared.
    pending: Option<Pending>,
    /// Where the operation's own fact comes from, when another line causes it: the later use
    /// of an argument that makes its call copy it (facts.copy-at-call), with what to say there.
    because: Option<(TextRange, String)>,
    /// How to keep the operation from panicking, when a rewrite does.
    remedy: Option<Remedy>,
    /// The check that a rule of acceptance proves the operation can't fail, with the rule, which
    /// then adds no `panic`, itself or through what it names (facts.what-proofs-change and
    /// facts.range-loops and facts.keys).
    proved: Option<(crate::verify::Check, crate::accept::Rule)>,
    /// What the rule closest to the operation needs, which the error of its effect names
    /// (facts.closest-rule).
    need: Option<(Effect, crate::accept::Need)>,
}

impl Site {
    /// Where the operation is, relative to its body's start.
    #[must_use]
    pub fn at(&self) -> TextRange {
        self.at
    }

    /// The items the operation names.
    #[must_use]
    pub fn names(&self) -> &[Key] {
        &self.names
    }

    /// What the operation copies itself, if it does (facts.copy).
    #[must_use]
    pub fn copy(&self) -> Option<&Fact> {
        self.copy.as_ref()
    }

    /// The modification whose sharing decides whether the operation stays in place.
    #[must_use]
    pub fn pending(&self) -> Option<&Pending> {
        self.pending.as_ref()
    }

    /// An operation that only names `names`.
    fn new(at: TextRange, names: Vec<Key>) -> Self {
        Self {
            at,
            panic: None,
            overflow: None,
            alloc: None,
            div: None,
            copy: None,
            locks: None,
            names,
            called: false,
            in_place: false,
            pending: None,
            because: None,
            remedy: None,
            proved: None,
            need: None,
        }
    }

    /// The check that a rule of acceptance proves this operation can't fail, with the rule, if
    /// one proves it.
    #[must_use]
    pub fn proved(&self) -> Option<(crate::verify::Check, crate::accept::Rule)> {
        self.proved
    }

    /// What the operation is, when it has `effect` itself.
    fn own(&self, effect: Effect) -> Option<&Fact> {
        match effect {
            Effect::Panic => self.panic.as_ref(),
            Effect::Overflow => self.overflow.as_ref(),
            Effect::Alloc => self.alloc.as_ref(),
            Effect::Div => self.div.as_ref(),
            Effect::Copy => self.copy.as_ref(),
            Effect::Locks => self.locks.as_ref(),
            // Only natives have capabilities of their own (facts.capability-natives).
            Effect::Capability(_) => None,
        }
    }

    /// How the operation gives the body of `caller` `effect`, if it does: itself, through a
    /// call into the caller's recursive group (facts.div), or through the first item it
    /// names that has the effect.
    fn source<'s>(
        &'s self,
        effect: Effect,
        effects: &Effects,
        caller: Option<&'s Key>,
    ) -> Option<Source<'s>> {
        if let Some(fact) = self.own(effect) {
            return Some(Source::Own(fact));
        }
        if effect == Effect::Alloc && self.in_place {
            return None;
        }
        if effect == Effect::Panic && self.proved.is_some() {
            return None;
        }
        if effect == Effect::Div
            && let Some(caller) = caller
            && let Some(key) = self
                .names
                .iter()
                .find(|k| effects.recurses(caller, k, self))
        {
            return Some(Source::Group(key, caller));
        }
        self.names
            .iter()
            .find(|k| effects.has(effect, k))
            .map(Source::Named)
    }
}

/// How an operation gives its body an effect.
#[derive(Clone, Copy, Debug)]
enum Source<'s> {
    /// The operation has the effect itself, as the fact says.
    Own(&'s Fact),
    /// It names an item that has the effect.
    Named(&'s Key),
    /// It calls, or names as a value, the first item, which is in the recursive group of the
    /// second, the body's own (facts.div).
    Group(&'s Key, &'s Key),
}

/// An implicit effect, which a `without` can rule out, or a capability below `io`, which the
/// fixed points infer as they infer one (facts.capabilities).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Effect {
    /// An operation that can panic (effects.panicking-operations).
    Panic,
    /// An operation that can overflow (effects.overflow-effect).
    Overflow,
    /// An allocation (facts.allocation).
    Alloc,
    /// Possible non-termination (facts.div).
    Div,
    /// A write that copies shared data (facts.copy).
    Copy,
    /// Holding shared values, which a `when` does (shared.locks).
    Locks,
    /// A capability below `io` (facts.capabilities).
    Capability(Capability),
}

impl Effect {
    /// The effects that this crate infers, the capabilities in the order of facts.capabilities;
    /// `copy` reads the modes of `stilt-rc`.
    pub(crate) const INFERRED: [Effect; 13] = [
        Effect::Panic,
        Effect::Overflow,
        Effect::Alloc,
        Effect::Div,
        Effect::Locks,
        Effect::Capability(Capability::Fs),
        Effect::Capability(Capability::Net),
        Effect::Capability(Capability::Clock),
        Effect::Capability(Capability::Env),
        Effect::Capability(Capability::Console),
        Effect::Capability(Capability::Rand),
        Effect::Capability(Capability::Spawn),
        Effect::Capability(Capability::Exec),
    ];

    /// Whether `limits` rule the effect out.
    #[must_use]
    pub fn limited(self, limits: Limits) -> bool {
        match self {
            Effect::Panic => limits.panic,
            Effect::Overflow => limits.overflow,
            Effect::Alloc => limits.alloc,
            Effect::Div => limits.div,
            Effect::Copy => limits.copy,
            Effect::Locks => limits.locks,
            Effect::Capability(c) => limits.capabilities.has(c),
        }
    }

    /// The effect as a limit names it.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            Effect::Panic => "panic",
            Effect::Overflow => "overflow",
            Effect::Alloc => "alloc",
            Effect::Div => "div",
            Effect::Copy => "copy",
            Effect::Locks => "locks",
            Effect::Capability(c) => c.text(),
        }
    }
}

/// What finding the sites of a body needs to know of its function: its key, its limits, its
/// parameters and the in-place parameters of the program (facts.in-place-parameters and
/// facts.writes-in-place).
#[derive(Clone, Copy, Debug)]
pub(crate) struct Scope<'a> {
    /// The body's module, whose items messages name without it.
    pub(crate) module: &'a Name,
    pub(crate) key: Option<&'a Key>,
    pub(crate) limits: Limits,
    pub(crate) body: &'a TypedBody,
    pub(crate) in_place: &'a InPlace,
    /// What the rules of acceptance prove of the body (facts.rules-of-acceptance).
    pub(crate) accepted: &'a crate::accept::Accepted,
}

/// effects.panic-kinds and effects.panicking-operations, std.lists, std.no-panics-by-default and
/// facts.div: the operations of the code of an item with a key that can panic, other than by
/// overflow, allocate or may not end, and the items it names; or `None` for a native function,
/// which has no code, and for a body with an error, which the analysis leaves out
/// (facts.bodies-with-errors).
pub(crate) fn code_sites(decls: &dyn Lookup, scope: &Scope<'_>) -> Option<Vec<Site>> {
    match &scope.body.code {
        // The bodies of items with keys are blocks, but for a hole's `= ?`: a lone expression
        // counts as a block of one statement.
        Definition::Code(code) => Some(find(decls, scope, code).sites),
        Definition::Native | Definition::Broken => None,
    }
}

/// What each operation of a body does that gives the body an implicit effect, as the errors
/// of the limits say it, with where the operation is: once for each operation and effect
/// (facts.visibility). `module` is the body's module, whose items are named without it, and
/// `caller` the body's own item.
pub(crate) fn causes(
    module: Name,
    caller: Option<&Key>,
    effects: &Effects,
    sites: &[Site],
) -> Vec<(Effect, TextRange, String)> {
    let mut found = Vec::new();
    for site in sites {
        for effect in Effect::INFERRED {
            let Some(source) = site.source(effect, effects, caller) else {
                continue;
            };
            let says = limits::cause(module, effects, effect, source);
            found.push((effect, site.at, says));
        }
    }
    found
}

/// What the fixed points need of the body of the item `key`, which `limits` limit, or `None` for a
/// body with an error, which the analysis leaves out (facts.bodies-with-errors). A native function
/// has no `div` (facts.div) but `Lazy.get` (polymorphism.lazy-implicit-effects).
pub(crate) fn summary(decls: &dyn Lookup, scope: &Scope<'_>, key: Key) -> Option<Summary> {
    if scope.body.code == Definition::Native {
        return Some(Summary {
            panics: native_panics(&key).then_some(None),
            panics_unproved: native_panics(&key).then_some(None),
            overflows: native_overflows(&key).then_some(None),
            allocates: native_allocates(decls, &key).then_some(None),
            diverges: native_diverges(&key).then_some(None),
            diverges_unproved: native_diverges(&key).then_some(None),
            // shared.locks: only a `when` holds a shared value, and no native runs one.
            locks: None,
            capabilities: capabilities::native(&key),
            key,
            names: Vec::new(),
            descends: true,
            descends_unproved: true,
            limits: scope.limits,
        });
    }
    let Definition::Code(code) = &scope.body.code else {
        return None;
    };
    let found = find(decls, scope, code);
    let ss = found.sites;
    // facts.shrinking-recursion: self-calls that all shrink.
    let descends = found.descends || scope.accepted.shrinks();
    let first = |effect| ss.iter().find_map(|s| s.own(effect).cloned()).map(Some);
    // facts.div: a use of the function itself as a value may not end.
    let as_value = ss
        .iter()
        .any(|s| !s.called && s.names.contains(&key))
        .then(|| Some(Fact::definite("a use of itself as a value".to_owned())));
    let panics = first(Effect::Panic);
    // versions.facts-without-proofs: with no check proved, a proved check panics.
    let proved = (ss.iter().any(|s| s.proved.is_some())).then(|| {
        Some(Fact::definite(
            "a check that a rule of acceptance proves".to_owned(),
        ))
    });
    let diverges = first(Effect::Div).or(as_value);
    // versions.facts-without-proofs: with no proof, a loop that ends may not.
    let ends = scope.accepted.any_ends().then(|| {
        Some(Fact::definite(
            "a loop that a counting loop shows ends".to_owned(),
        ))
    });
    Some(Summary {
        panics_unproved: panics.clone().or(proved),
        panics,
        overflows: first(Effect::Overflow),
        allocates: first(Effect::Alloc),
        diverges_unproved: diverges.clone().or(ends),
        diverges,
        locks: first(Effect::Locks),
        capabilities: Capabilities::default(),
        descends,
        descends_unproved: found.descends,
        names: ss.into_iter().flat_map(|s| s.names).collect(),
        key,
        limits: scope.limits,
    })
}

/// The walk of a body's code: `stmt` on every statement and `expr` on every expression.
pub(crate) fn walk_code<'a>(
    code: &'a Code,
    stmt: &mut dyn FnMut(&'a crate::tast::Stmt),
    expr: &mut dyn FnMut(&'a crate::tast::Expr),
) {
    match code {
        Code::Block(b) => walk::iter_block(b, stmt, expr),
        Code::Expr(e) => walk::iter(e, stmt, expr),
    }
}

#[cfg(test)]
mod tests;
