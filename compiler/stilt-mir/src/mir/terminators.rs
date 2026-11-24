//! How blocks end: jumps, calls, returns, raises and panics, and what a call calls and passes.

use serde::{Deserialize, Serialize};

use super::{BlockId, Heapness, Local, Operand};
use crate::FnRef;

/// What a call calls.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Callee {
    /// A function, by name.
    Direct(FnRef),
    /// The code of a closure, which is passed the closure.
    Value(Operand),
    /// Method `index` of a dictionary, which is passed the dictionary.
    Method(Operand, u32),
}

/// An argument of a call, by how the callee takes it.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Arg {
    /// An argument the callee borrows.
    Borrow(Operand),
    /// An argument the callee consumes, which takes its reference.
    Own(Operand),
    /// A pointer to a slot, for an `inout` parameter.
    Ref(Operand),
    /// The words of a value of several words, lent for the call in a box on the caller's
    /// stack, which no count frees: the one word in which natives and the methods of
    /// dictionaries take a value of a type parameter (`stilt_runtime::abi`), which they borrow.
    Lend(Vec<(Operand, Heapness)>),
}

impl Arg {
    /// The operands the argument reads.
    #[must_use]
    pub fn operands(&self) -> Vec<&Operand> {
        match self {
            Arg::Borrow(o) | Arg::Own(o) | Arg::Ref(o) => vec![o],
            Arg::Lend(words) => words.iter().map(|(o, _)| o).collect(),
        }
    }
}

/// How a block ends.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Terminator {
    /// Goes to the block.
    Goto(BlockId),
    /// Goes to `then` when `cond` isn't 0, and to `otherwise` when it is.
    Branch {
        /// The condition.
        cond: Operand,
        /// The block when it holds.
        then: BlockId,
        /// The block when it doesn't.
        otherwise: BlockId,
    },
    /// Goes to the block of the case equal to `value`, or to `otherwise`.
    Switch {
        /// The value switched on.
        value: Operand,
        /// Each case's value and block.
        cases: Vec<(u64, BlockId)>,
        /// The block when no case is equal.
        otherwise: BlockId,
    },
    /// A call, whose first argument is its location. It continues at `next` with the words of
    /// its result in `dest`, or if it can raise and does, at the block of `raised` with the
    /// words of the error in its locals.
    Call {
        /// What it calls.
        callee: Callee,
        /// Its arguments, the location first.
        args: Vec<Arg>,
        /// The locals of its result's words.
        dest: Vec<Local>,
        /// The block where it continues.
        next: BlockId,
        /// The locals of the error's words, and the block where a raise continues.
        raised: Option<(Vec<Local>, BlockId)>,
    },
    /// Returns the words of the result.
    Return(Vec<Operand>),
    /// Raises the words of an error.
    Raise(Vec<Operand>),
    /// A panic of the runtime's kind number `kind`, with a string as its detail or none.
    Panic {
        /// The panic's kind.
        kind: u64,
        /// Its detail, a string.
        detail: Option<Operand>,
        /// Its location.
        loc: Operand,
    },
    /// Code that no run reaches.
    Unreachable,
}

impl Terminator {
    /// The operands the terminator reads.
    #[must_use]
    pub fn operands(&self) -> Vec<&Operand> {
        match self {
            Terminator::Branch { cond: o, .. } | Terminator::Switch { value: o, .. } => vec![o],
            Terminator::Call { callee, args, .. } => {
                let callee = match callee {
                    Callee::Direct(_) => None,
                    Callee::Value(o) | Callee::Method(o, _) => Some(o),
                };
                let args = args.iter().flat_map(Arg::operands);
                callee.into_iter().chain(args).collect()
            }
            Terminator::Return(os) | Terminator::Raise(os) => os.iter().collect(),
            Terminator::Panic { detail, loc, .. } => detail.iter().chain([loc]).collect(),
            Terminator::Goto(_) | Terminator::Unreachable => Vec::new(),
        }
    }

    /// The blocks control can go to next.
    #[must_use]
    pub fn successors(&self) -> Vec<BlockId> {
        match self {
            Terminator::Goto(b) => vec![*b],
            Terminator::Branch {
                then, otherwise, ..
            } => vec![*then, *otherwise],
            Terminator::Switch {
                cases, otherwise, ..
            } => cases.iter().map(|(_, b)| *b).chain([*otherwise]).collect(),
            Terminator::Call { next, raised, .. } => std::iter::once(*next)
                .chain(raised.as_ref().map(|(_, b)| *b))
                .collect(),
            Terminator::Return(_)
            | Terminator::Raise(_)
            | Terminator::Panic { .. }
            | Terminator::Unreachable => Vec::new(),
        }
    }
}
