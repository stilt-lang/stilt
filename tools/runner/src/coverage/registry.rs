//! The codes of the registry, `reference/errors.toml`, that implementations may report: the
//! paragraph of the Reference that defines each, the tier in which each can first occur, and
//! the phase each belongs to (errors.registry-phases), as [`codes`](super::codes) lists them.

use std::collections::{BTreeMap, BTreeSet};

use crate::annotations::Tier;

/// A code that implementations may report, as the registry gives it.
#[derive(Debug)]
pub(super) struct Registered {
    pub(super) code: &'static str,
    /// The ID of the paragraph that defines it, its home, such as `numbers.integer-panics`.
    pub(super) reference: &'static str,
    /// The tier in which it can first occur.
    pub(super) tier: Tier,
    /// The phase in which it is checked.
    pub(super) phase: &'static str,
}

/// The codes of the registry that implementations may report: every code but the retired
/// ones.
#[derive(Debug)]
pub(crate) struct Registry {
    pub(super) codes: BTreeSet<String>,
    /// The ID of the paragraph that defines each code, its home.
    pub(super) references: BTreeMap<String, String>,
    /// The tier in which each code can first occur.
    pub(super) tiers: BTreeMap<String, Tier>,
    /// The phase of each code.
    phases: BTreeMap<String, String>,
}

impl Registry {
    /// The codes of the registry.
    pub(crate) fn new() -> Self {
        Self::of(super::codes::CODES)
    }

    fn of(registered: &[Registered]) -> Self {
        let by_code = |value: fn(&Registered) -> String| {
            (registered.iter())
                .map(|r| (r.code.to_owned(), value(r)))
                .collect()
        };
        Self {
            codes: registered.iter().map(|r| r.code.to_owned()).collect(),
            references: by_code(|r| r.reference.to_owned()),
            tiers: registered
                .iter()
                .map(|r| (r.code.to_owned(), r.tier))
                .collect(),
            phases: by_code(|r| r.phase.to_owned()),
        }
    }

    /// The codes that implementations may report in the given phases.
    pub(crate) fn codes_in(&self, phases: &[String]) -> Result<BTreeSet<String>, String> {
        if let Some(unknown) = phases.iter().find(|p| !PHASES.contains(&p.as_str())) {
            return Err(format!(
                "`{unknown}` is no phase; the phases are {}",
                PHASES.join(", ")
            ));
        }
        Ok(self
            .codes
            .iter()
            .filter(|code| self.phases.get(*code).is_some_and(|p| phases.contains(p)))
            .cloned()
            .collect())
    }
}

/// The phases a registry entry may name (errors.registry-phases).
const PHASES: [&str; 6] = [
    "syntax", "items", "types", "analyses", "warnings", "refusal",
];

#[cfg(test)]
pub(super) mod tests {
    use super::*;

    /// A registry whose codes are all defined by `numbers.overflow`, except `E07…` codes,
    /// defined by `numbers.wrapping`, and `E09…` codes, whose paragraph no chapter has.
    /// `E08…` codes can first occur in the advanced tier, and the others in core.
    pub(in crate::coverage) fn registry(codes: &[&'static str]) -> Registry {
        let home = |code: &str| match &code[..3] {
            "E07" => "numbers.wrapping",
            "E09" => "numbers.gone",
            _ => "numbers.overflow",
        };
        let registered: Vec<Registered> = (codes.iter())
            .map(|code| Registered {
                code,
                reference: home(code),
                tier: if code.starts_with("E08") {
                    Tier::Advanced
                } else {
                    Tier::Core
                },
                phase: if code.starts_with('W') {
                    "warnings"
                } else {
                    "types"
                },
            })
            .collect();
        Registry::of(&registered)
    }

    #[test]
    fn every_phase_of_the_registry_is_one_of_its_phases() {
        let registry = Registry::new();
        let all: Vec<String> = PHASES.iter().map(|p| (*p).to_owned()).collect();
        assert_eq!(registry.codes_in(&all), Ok(registry.codes.clone()));
    }

    #[test]
    fn selects_the_codes_of_a_phase() {
        let registry = registry(&["E0320", "W0300"]);
        let warnings = registry.codes_in(&["warnings".to_owned()]);
        assert_eq!(warnings, Ok(BTreeSet::from(["W0300".to_owned()])));
        assert!(registry.codes_in(&["later".to_owned()]).is_err());
    }
}
