//! Effects and handlers (handlers.declaring-effect and handlers.handler-literals; tasks.async): the
//! declaration of an effect, the effects of rows and handler types, and the handler literals,
//! `with` and `resume` of bodies.

use stilt_syntax::TextRange;
use stilt_syntax::ast::Mode;

use super::{Block, Ident, Item, LocalId, Name, Row, Ty, TypeRef};

/// An effect's declaration (handlers.declaring-effect): its type parameters, whose generics are
/// those of the declaration's own index, and its operations, each named once.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EffectDecl {
    /// Its name.
    pub name: Name,
    /// Its type parameters' names.
    pub params: Vec<Name>,
    /// Its operations, in order.
    pub ops: Vec<Operation>,
}

/// An operation of an effect: a function's head without generics, receiver or body, whose row
/// holds no row variable.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Operation {
    /// Its name.
    pub name: Name,
    /// Each parameter's mode and type.
    pub params: Vec<(Mode, Ty)>,
    /// The written result, or `None` for `()`.
    pub ret: Option<Ty>,
    /// Its own row.
    pub row: Row,
}

/// An effect with its type arguments, as a row holds it (handlers.effects-in-rows). `async` is the
/// effect [`Item::async_effect`] (tasks.async).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct EffectInst {
    /// The effect.
    pub effect: Item,
    /// Its type arguments.
    pub args: Vec<Ty>,
}

/// A handler's type (handlers.handler-types): its effect, the `R` of one that takes control, and
/// the row its bodies perform beyond their operations' rows.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct HandlerTy {
    /// Its effect.
    pub effect: EffectInst,
    /// The `R` of a handler that takes control.
    pub answer: Option<Ty>,
    /// The row its bodies perform beyond their operations' rows.
    pub row: Row,
}

/// A handler literal (handlers.handler-literals).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandlerLit {
    /// Its effect, or `None` when it names none or names `async`, which resolution or type
    /// checking reports.
    pub effect: Option<EffectInst>,
    /// Where its effect is written, which E0511 reports, or its `handler` for `async`.
    pub effect_at: TextRange,
    /// Whether it names `async`, which only `std.task` gives handlers of (tasks.async).
    pub is_async: bool,
    /// The `R` of a handler that takes control (handlers.resuming).
    pub answer: Option<TypeRef>,
    /// Its operations' implementations, in order.
    pub ops: Vec<HandlerOp>,
}

/// An operation's implementation in a handler literal, written as a function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HandlerOp {
    /// The operation's name.
    pub name: Ident,
    /// Each parameter's mode, the local it binds and its written type.
    pub params: Vec<(Mode, LocalId, TypeRef)>,
    /// Its written result type.
    pub ret: Option<TypeRef>,
    /// Its row.
    pub row: Row,
    /// Whether it is written as an operation's head is: no generics, receiver, `inout` result,
    /// `where` or `without`.
    pub plain: bool,
    /// Its body.
    pub body: Block,
}

impl Item {
    /// `async`, the effect of tasks (tasks.async), as the prelude's.
    #[must_use]
    pub fn async_effect() -> Self {
        Self {
            home: Name::from(crate::scope::PRELUDE),
            name: Name::from("async"),
        }
    }

    /// Whether it is `async`.
    #[must_use]
    pub fn is_async(&self) -> bool {
        &*self.name == "async" && &*self.home == crate::scope::PRELUDE
    }
}
