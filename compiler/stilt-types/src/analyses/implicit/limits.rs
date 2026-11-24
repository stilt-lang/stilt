//! The checks of `without panic` (effects.without-panic), `without alloc` (facts.without-alloc),
//! `without div` (facts.without-div) and the capability limits (facts.without): in a function that
//! a `without` limits, each operation that has the effect, itself or through the items it names, is
//! an error where it is written, with a note on the limit and the fix that keeps the operation from
//! panicking, where one does.

use stilt_diag::{Diagnostic, codes};
use stilt_hir::hir::{Capability, Limit, Name};
use stilt_syntax::{TextRange, TextSize};

use super::{Effect, Effects, Key, Site, Source};

/// What limits a function's body, and what the check needs to say so.
#[derive(Clone, Copy, Debug)]
pub struct Limited<'a> {
    /// The function's module, whose own items messages name without their module.
    pub module: &'a Name,
    /// The function's name.
    pub function: &'a Name,
    /// The function's own item.
    pub key: Option<&'a Key>,
    /// The limits that its module's header writes, each where it is written in the file.
    pub header: &'a [(Limit, TextRange)],
    /// The limits that its own `without` writes, each where it is written, relative to the
    /// body's start.
    pub own: &'a [(Limit, TextRange)],
    /// Whether the function's row raises a `str`, so that an `assert` can raise instead.
    pub raises_str: bool,
    pub(crate) effects: &'a Effects,
}

/// The limit that rules `effect` out.
fn limit_of(effect: Effect) -> Limit {
    match effect {
        Effect::Panic => Limit::Panic,
        Effect::Overflow => Limit::Overflow,
        Effect::Alloc => Limit::Alloc,
        Effect::Div => Limit::Div,
        Effect::Copy => Limit::Copy,
        Effect::Locks => Limit::Locks,
        Effect::Capability(c) => Limit::Capability(c),
    }
}

/// Where `limits` rule `effect` out, if they do.
fn find(limits: &[(Limit, TextRange)], effect: Effect) -> Option<TextRange> {
    let limit = limit_of(effect);
    limits
        .iter()
        .find_map(|(l, at)| (*l == limit).then_some(*at))
}

impl Limited<'_> {
    /// Whether the function's or its module's `without` rules `effect` out.
    #[must_use]
    pub fn limits(&self, effect: Effect) -> bool {
        find(self.own, effect).is_some() || find(self.header, effect).is_some()
    }
}

/// The errors of a limited function's body, given its sites: for each limit, one for each line
/// whose sites go beyond it, at the first of them, which names the others and takes their
/// fixes (facts.without), for the effects this crate infers. `line` gives the line of an
/// offset. `note` writes what the rule of acceptance closest to an operation needs, which the
/// error of its effect gives as its help (facts.closest-rule).
pub(crate) fn errors(
    limited: &Limited<'_>,
    sites: &[Site],
    line: &dyn Fn(TextSize) -> u32,
    note: &dyn Fn(&crate::accept::Need) -> String,
) -> Vec<Diagnostic> {
    let mut found = Vec::new();
    for effect in Effect::INFERRED.into_iter().filter(|e| limited.limits(*e)) {
        let mut lines: Vec<(u32, Diagnostic)> = Vec::new();
        let mut ordered: Vec<&Site> = sites.iter().collect();
        ordered.sort_by_key(|s| s.at.start());
        for s in ordered {
            let Some(mut d) = error(limited, effect, s) else {
                continue;
            };
            if let Some((_, need)) = s.need.as_ref().filter(|(e, _)| *e == effect) {
                d = d.with_help(sentence(&note(need)));
            } else if effect == Effect::Alloc && s.because.is_none() {
                d = d.with_help(ALLOC_HELP);
            }
            let at = line(s.at.start());
            match lines.iter_mut().position(|(l, _)| *l == at) {
                Some(i) => {
                    let (l, first) = lines.remove(i);
                    // The first names the fact; the others need only say they share it, and
                    // what their rules of acceptance need joins its help.
                    let mut merged = first.with_note(s.at, format!("also {}", verb(effect)));
                    if s.need.as_ref().is_some_and(|(e, _)| *e == effect) {
                        let (mine, theirs) = (merged.help().to_owned(), d.help().to_owned());
                        if !mine.contains(&theirs) {
                            merged = merged.with_help(format!("{mine} {theirs}"));
                        }
                    }
                    merged.fixes.extend(d.fixes);
                    lines.insert(i, (l, merged));
                }
                None => lines.push((at, d)),
            }
        }
        found.extend(lines.into_iter().map(|(_, d)| d));
    }
    found
}

/// What code under `without alloc` can do instead (facts.without-alloc): the function owns its
/// list parameters' storage, so the caller makes the list and the function writes into it.
const ALLOC_HELP: &str = "Code under `without alloc` makes no list or string. Let the caller make \
     it, and take it `inout`: writes through its indexes stay in its storage, as \
     `out[i] = x` does.";

/// `text` as a sentence of a help: with a capital and a full stop.
fn sentence(text: &str) -> String {
    let mut chars = text.chars();
    let first = chars.next().map(|c| c.to_uppercase().collect::<String>());
    format!("{}{}.", first.unwrap_or_default(), chars.as_str())
}

/// What code that has `effect` does.
#[must_use]
pub fn verb(effect: Effect) -> &'static str {
    match effect {
        Effect::Panic => "can panic",
        Effect::Overflow => "can overflow",
        Effect::Alloc => "allocates",
        Effect::Div => "may not end",
        Effect::Copy => "copies a shared value",
        Effect::Locks => "holds shared values",
        Effect::Capability(c) => uses(c),
    }
}

/// What code that has the capability `c` does (facts.without).
fn uses(c: Capability) -> &'static str {
    match c {
        Capability::Fs => "uses `fs`",
        Capability::Net => "uses `net`",
        Capability::Clock => "uses `clock`",
        Capability::Env => "uses `env`",
        Capability::Console => "uses `console`",
        Capability::Rand => "uses `rand`",
        Capability::Spawn => "uses `spawn`",
        Capability::Exec => "uses `exec`",
    }
}

/// The error of a site that goes beyond the limit on `effect`: what it does, where that comes
/// from, and which `without` rules it out. An operation that panics itself gets the fix that
/// keeps it from panicking, if it has one.
fn error(limited: &Limited<'_>, effect: Effect, site: &Site) -> Option<Diagnostic> {
    let source = site.source(effect, limited.effects, limited.key)?;
    let fact = match source {
        Source::Own(fact) => format!("{} {}", fact.this, verb(effect)),
        Source::Named(key) => named(*limited.module, limited.effects, effect, key),
        Source::Group(key, caller) => recursion(*limited.module, key, caller, site),
    };
    let mut d = located(limited, effect, site.at, &fact);
    if matches!(source, Source::Own(_))
        && let Some((at, why)) = &site.because
    {
        d = d.with_note(*at, why.clone());
    }
    if effect == Effect::Panic
        && matches!(source, Source::Own(_))
        && let Some(fix) = site.remedy.as_ref().and_then(|r| r.fix(limited.raises_str))
    {
        return Some(d.with_fix(fix));
    }
    Some(d)
}

/// What a cause of `effect` does, as `show` prints it (facts.visibility).
pub(super) fn cause(module: Name, effects: &Effects, effect: Effect, source: Source<'_>) -> String {
    match source {
        Source::Own(fact) => format!("{} {}", fact.a, verb(effect)),
        Source::Named(key) => named(module, effects, effect, key),
        Source::Group(key, caller) if key == caller => {
            format!("a call of {} to itself may not end", describe(&module, key))
        }
        Source::Group(key, _) => {
            format!(
                "a call into the recursive group of {} may not end",
                describe(&module, key)
            )
        }
    }
}

/// A site that may not end by naming `key`, in the recursive group of `caller` (facts.div and
/// facts.descending-self-calls): a call of the caller itself, which doesn't descend, a call of
/// another item of its group, or a use of one as a value.
fn recursion(module: Name, key: &Key, caller: &Key, site: &Site) -> String {
    let named = describe(&module, key);
    let verb = verb(Effect::Div);
    match (key == caller, site.called) {
        (true, true) => {
            format!("this call of {named} to itself, on no part of a parameter, {verb}")
        }
        (true, false) => format!("this use of {named} as a value {verb}"),
        (false, true) => format!(
            "this call of {named}, which calls back into {}, {verb}",
            describe(&module, caller)
        ),
        (false, false) => format!(
            "this use of {named}, which calls back into {}, as a value {verb}",
            describe(&module, caller)
        ),
    }
}

/// The error of `fact`, at `at`, which names the `without` that rules `effect` out, with a
/// note where it names the limit: the function's own clause if it has one, and the module's
/// header otherwise, which comes before the body.
#[must_use]
pub fn located(limited: &Limited<'_>, effect: Effect, at: TextRange, fact: &str) -> Diagnostic {
    let limit = format!("`without {}`", effect.word());
    if let Some(own) = find(limited.own, effect) {
        let message = format!("{fact}, but `{}` says {limit}", limited.function);
        return Diagnostic::new(codes::E0204, at, message).with_note(own, "the limit");
    }
    let message = format!("{fact}, but the module's header says {limit}");
    let d = Diagnostic::new(codes::E0204, at, message);
    if let Some(header) = find(limited.header, effect) {
        d.with_note_in_file(header, "the limit")
    } else {
        d
    }
}

/// What an item that has `effect` does, and where that comes from: the operation of its own
/// code that has the effect, or the item whose own code does, and that code's operation. The
/// items of `module` are named without their module.
pub(super) fn named(module: Name, effects: &Effects, effect: Effect, key: &Key) -> String {
    let (origin, operation) = effects.origin(effect, key);
    through(
        &module,
        effect,
        key,
        origin,
        operation.map(|f| f.a.as_str()),
    )
}

/// What `key` does that has `effect`, through `operation` of the code of `origin`, the item
/// whose own code has it: "`f` allocates, through a list in `g`".
#[must_use]
pub fn through(
    module: &Name,
    effect: Effect,
    key: &Key,
    origin: &Key,
    operation: Option<&str>,
) -> String {
    let shown = describe(module, key);
    let verb = verb(effect);
    match operation {
        Some(fact) if origin == key => format!("{shown} {verb}, through {fact}"),
        Some(fact) => format!(
            "{shown} {verb}, through {fact} in {}",
            describe(module, origin)
        ),
        None if origin == key => format!("{shown} {verb}"),
        None => format!("{shown} {verb}, through {}", describe(module, origin)),
    }
}

/// An item as messages name it in the module `module`: as code names it there, with its
/// module when it is another's and not the prelude's.
#[must_use]
pub fn describe(module: &Name, key: &Key) -> String {
    match key {
        Key::Function(item) if item.home == *module || &*item.home == "std.prelude" => {
            format!("`{}`", item.name)
        }
        Key::Function(item) => {
            let last = item.home.rsplit('.').next().unwrap_or(&item.home);
            format!("`{last}.{}`", item.name)
        }
        Key::Member(owner, name) | Key::ImplMethod(_, owner, name) => {
            format!("`{}.{name}`", owner.name)
        }
        Key::DefaultMethod(trait_item, name) => format!("`{}.{name}`", trait_item.name),
        Key::BuiltIn(_, name) => format!("the built-in `{name}`"),
    }
}
