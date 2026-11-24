//! What the expansions of a use make (macros.nested-expansions and macros.expansion-size): the
//! expansions that a use the user wrote leads to hold at most [`EXPANSION_TOKENS`] tokens in
//! all, and an expansion too large or too deep ends the use, so that nothing more of its
//! expansions is resolved or reported. A macro that uses itself twice would otherwise nest
//! 128 deep in 2^128 expansions.

use stilt_diag::codes;
use stilt_syntax::TextRange;

use crate::hir::Name;
use crate::lower::Resolver;
use crate::procs::EXPANSION_TOKENS;

/// What the expansions of the use the user wrote that is being resolved have made.
#[derive(Debug, Default)]
pub(crate) struct Budget {
    /// The tokens of its expansions so far.
    tokens: usize,
    /// Whether an expansion too large or too deep ended it.
    ended: bool,
}

impl Resolver<'_> {
    /// `expand` on a use. A use the user wrote, outside every expansion, counts the tokens of
    /// its expansions from none, and gives `None` when an expansion too large or too deep ended
    /// it, keeping nothing that its expansions reported after that error.
    pub(super) fn written_use<T>(&mut self, expand: impl FnOnce(&mut Self) -> T) -> Option<T> {
        if !self.regions.is_empty() {
            return Some(expand(self));
        }
        let from = self.diagnostics.len();
        self.budget = Budget::default();
        let made = expand(self);
        if !std::mem::take(&mut self.budget).ended {
            return Some(made);
        }
        let end = self.diagnostics[from..]
            .iter()
            .position(|d| d.code == codes::E0224 || d.code == codes::E0231)
            .map_or(self.diagnostics.len(), |i| from + i + 1);
        self.diagnostics.truncate(end);
        if let Some(unknown) = &mut self.unknown {
            unknown.retain(|(_, at)| at.is_none_or(|i| i < end));
        }
        None
    }

    /// Whether an error has ended the use the user wrote, so that no use inside it expands.
    pub(super) fn ended(&self) -> bool {
        self.budget.ended
    }

    /// E0224 at the use the user wrote, for a use of `name` inside 128 expansions, which ends
    /// it.
    pub(super) fn too_deep(&mut self, name: Name, use_at: TextRange) {
        let message = format!("expansions of {} nest more than 128 deep", self.chain(name));
        self.error(codes::E0224, use_at, message);
        self.budget.ended = true;
    }

    /// Counts the `tokens` of an expansion that `name!` gives, or ends the use the user wrote
    /// with E0231 at `use_at` when they take its expansions past [`EXPANSION_TOKENS`].
    pub(super) fn spend(&mut self, tokens: usize, name: Name, use_at: TextRange) -> bool {
        self.budget.tokens = self.budget.tokens.saturating_add(tokens);
        if self.budget.tokens <= EXPANSION_TOKENS {
            return true;
        }
        let outer = self.regions.first().map_or(name, |r| r.name);
        let message = if outer == name {
            format!("the expansion of `{name}!` holds more than 100,000 tokens")
        } else {
            format!(
                "the expansions of `{outer}!` hold more than 100,000 tokens once `{name}!` \
                 expands in them"
            )
        };
        self.error(codes::E0231, use_at, message);
        self.budget.ended = true;
        false
    }
}
