//! Lost reuse (values.consumed-parameters): a call that consumes a value its caller still needs,
//! after the call or in the call itself, or, for the value of an `inout` parameter, to give back to
//! its own caller (values.inout-arguments). Reference counting copies the value before such a call,
//! so the callee gets it still shared, and its first write copies it rather than reuse its memory.
//! `stilt show` prints each such call where it is (Inferred facts, "Consumption is inferred";
//! goal shown-facts).

use stilt_hir::hir::Name;

use stilt_db::{Db, Program};
use stilt_mir::FnRef;
use stilt_mir::mir::{BlockId, Function};

use crate::queries::conventions;
use crate::{Copied, counted};

/// A call that can't reuse the memory of a value it consumes, because its caller still needs
/// the value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LostReuse {
    /// The place the caller passes, as the source names it, such as `xs` or `p.left`.
    pub place: Name,
    /// The function called.
    pub callee: FnRef,
    /// What still needs the place's value.
    pub need: Need,
    /// The location word of the call, as `Stmt::At` marks it, or 0 when no marker comes before
    /// it in its block.
    pub at: u64,
}

/// What still needs a value that a call consumes, so that the call can't reuse it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Need {
    /// The caller uses the place after the call.
    After,
    /// The call is given the place twice.
    Twice,
    /// The place is an `inout` parameter, which goes back to the caller when the function
    /// returns, when it raises, or both, as `returns` and `raises` say (values.inout-arguments).
    Back {
        /// Whether the value goes back when the function returns.
        returns: bool,
        /// Whether the value goes back when the function raises.
        raises: bool,
    },
}

impl Need {
    /// What needs a place that a call consumes several words of, when `self` needs some and
    /// `other` others: the first of a use after the call, the call itself, and the caller.
    #[must_use]
    pub fn and(self, other: Need) -> Need {
        match (self, other) {
            (Need::After, _) | (_, Need::After) => Need::After,
            (Need::Twice, _) | (_, Need::Twice) => Need::Twice,
            (
                Need::Back { returns, raises },
                Need::Back {
                    returns: r,
                    raises: s,
                },
            ) => Need::Back {
                returns: returns || r,
                raises: raises || s,
            },
        }
    }
}

/// Each call in the code of `f`, and of the closures it holds, that consumes a value `f` still
/// needs, in the order of their blocks: the calls before which reference counting copies what
/// they consume, in the code that a build gives `f` before it inlines the standard library,
/// since the facts are of the calls the source writes. A function called only through values
/// and a native have none.
#[must_use]
pub fn losing_reuse(db: &dyn Db, program: Program, f: &FnRef) -> Vec<LostReuse> {
    stilt_mir::functions(db, program, f.clone())
        .iter()
        .flat_map(|g| {
            let (code, copied) = counted(g, &conventions(db, program, g));
            places(&code, &copied)
        })
        .collect()
}

/// The losses of reuse that the copies of a function's code make, each once for each place it
/// copies at a call. A value held in several locals, one per word, as a record is, is named as a
/// whole when the call copies each of its counted words, and otherwise by the words it copies. A
/// local that the source doesn't name names no place: the compiler made it.
fn places(code: &Function, copied: &[Copied]) -> Vec<LostReuse> {
    let name = |c: &Copied| code.locals[c.local.0 as usize].name;
    let words: Vec<Name> = code
        .locals
        .iter()
        .filter(|d| d.repr.counted())
        .filter_map(|d| d.name)
        .collect();
    let mut out: Vec<(BlockId, LostReuse)> = Vec::new();
    for c in copied {
        let Some(full) = name(c) else { continue };
        let at_call: Vec<Name> = copied
            .iter()
            .filter(|d| d.block == c.block)
            .filter_map(name)
            .collect();
        let place = whole(full, &at_call, &words);
        if let Some((_, seen)) = out
            .iter_mut()
            .find(|(b, l)| *b == c.block && l.place == place)
        {
            seen.need = seen.need.and(c.need);
            continue;
        }
        let lost = LostReuse {
            place,
            callee: c.callee.clone(),
            need: c.need,
            at: c.at,
        };
        out.push((c.block, lost));
    }
    out.into_iter().map(|(_, l)| l).collect()
}

/// The place that a copy of the word named `name` stands for, at a call that copies the words
/// named `copied`: the shortest part of the name, such as `p` of `p.left`, whose every counted
/// word, among the function's counted locals, named `words`, the call copies.
fn whole(name: Name, copied: &[Name], words: &[Name]) -> Name {
    for (i, _) in name.match_indices('.') {
        let prefix = &name[..i];
        let under = |n: &&Name| {
            n.strip_prefix(prefix)
                .is_some_and(|rest| rest.is_empty() || rest.starts_with('.'))
        };
        if words.iter().filter(under).all(|n| copied.contains(n)) {
            return Name::from(prefix);
        }
    }
    name
}

#[cfg(test)]
mod tests;
