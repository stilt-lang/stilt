//! The types of handlers.handler-types: handlers' types, what a row that effects are fitted into
//! handles, and the effects of rows.

use stilt_hir::hir::Item;

use super::{Row, Ty};

/// A handler's type (handlers.handler-types): its effect with its type arguments, the `R` of one
/// that takes control (handlers.resuming), and the row its bodies perform beyond their operations'
/// rows.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HandlerTy {
    /// Its effect.
    pub effect: Item,
    /// The effect's type arguments.
    pub args: Vec<Ty>,
    /// The `R` of one that takes control.
    pub answer: Option<Ty>,
    /// The row its bodies perform beyond their operations' rows.
    pub row: Row,
}

/// What a row that effects are fitted into handles on the way: nothing, the raises of a `try …
/// catch` of an error type (effects.innermost-catch), or the performances of an effect that a
/// `with` handles, with its type arguments (handlers.with).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Handled {
    /// Nothing.
    Nothing,
    /// The raises of this error type.
    Raise(Ty),
    /// The performances of this effect, with its type arguments.
    Effect(Item, Vec<Ty>),
}

impl Row {
    /// The type arguments of the effect `e` in the row, if it holds it.
    #[must_use]
    pub fn effect(&self, e: &Item) -> Option<&[Ty]> {
        self.effects
            .iter()
            .find(|(f, _)| f == e)
            .map(|(_, args)| args.as_slice())
    }

    /// The row without the effect `e`.
    #[must_use]
    pub fn without_effect(mut self, e: &Item) -> Self {
        self.effects.retain(|(f, _)| f != e);
        self
    }
}
