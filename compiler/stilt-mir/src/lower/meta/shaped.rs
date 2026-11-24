//! Shape dictionaries (traits.structural-impls): the structural impls of `Eq`, `Ord`,
//! `Hash` and `Show` that a descriptor's table holds for a tuple, a record, a variant type or an
//! array. Each is a data object whose methods are code shared by every type of its shape, which
//! walks the parts of the values it is given through the descriptor's own parts, the accessor
//! and the thunk of each, so that a table compiles nothing for its type alone. They call the
//! parts' impls from the first part to the last, as the structural impls compiled for a type do
//! (`crate::synth::structural`), so they give the same results, the same hashes and text
//! included, and a map built through a table's `Hash` finds its keys by a compiled one.
//!
//! After its methods, a shape dictionary holds its type's witness, then the descriptor's first
//! two fields: the number of fields or variants and their entries, or an array's element thunk
//! and size, then an array's closure that gives its elements as a list. `Show` of a tuple or a
//! record holds its text's opening and closing, and whether its fields are written with their
//! names.

mod variants;
mod walks;

use stilt_hir::decls::Lookup;
use stilt_hir::hir::Item;
use stilt_types::ty::Ty;

use super::impls::Parts;
use crate::FnRef;
use crate::Held;
use crate::described::{Walk, numbered};
use crate::lower::{Conv, Cx, Lower};
use crate::mir::{Const, Function, Heapness, Local, Operand, ParamMode, Repr, Terminator};

/// The fields of a shape dictionary after its methods.
const WITNESS: u32 = 0;
const COUNT: u32 = 1;
const ENTRIES: u32 = 2;
const THUNK: u32 = 1;
const SIZE: u32 = 2;
const GET: u32 = 3;
const OPEN: u32 = 3;
const CLOSE: u32 = 4;
const LABELED: u32 = 5;

/// What a method of a shape dictionary does: the one method of `Eq`, `Ord` or `Hash`, or `Show`'s
/// text, which both of its methods give for a structural impl (std.show-output).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Op {
    Eq,
    Compare,
    Hash,
    Show,
}

impl Op {
    fn of(t: &Item) -> Option<Self> {
        if &*t.home != "std.prelude" {
            return None;
        }
        Some(match &*t.name {
            "Eq" => Self::Eq,
            "Ord" => Self::Compare,
            "Hash" => Self::Hash,
            "Show" => Self::Show,
            _ => return None,
        })
    }

    fn binary(self) -> bool {
        matches!(self, Self::Eq | Self::Compare)
    }

    fn returns(self) -> Ty {
        match self {
            Self::Eq => Ty::bool(),
            Self::Compare => Ty::named("Ordering"),
            Self::Hash => Ty::named("u64"),
            Self::Show => Ty::str(),
        }
    }
}

/// The fields a shape dictionary of `op` that walks `walk` holds after its methods.
fn env_len(op: Op, walk: Walk) -> u32 {
    match (walk, op) {
        (Walk::Array, _) => 4,
        (Walk::Fields, Op::Show) => 6,
        _ => 3,
    }
}

/// What the shape dictionaries of a descriptor of the case `case` walk, if it has them.
pub(crate) fn walk_of(case: Option<&str>) -> Option<Walk> {
    match case? {
        "Tuple" | "Record" => Some(Walk::Fields),
        "Variants" => Some(Walk::Variants),
        "Array" => Some(Walk::Array),
        _ => None,
    }
}

impl Lower<'_> {
    /// The shape dictionary of `t` for the type `ty` that a descriptor with the parts `parts`
    /// describes, whose shape `walk` walks.
    pub(crate) fn shape_dict(
        &mut self,
        ty: &Ty,
        t: &Item,
        walk: Walk,
        parts: &Parts<'_>,
    ) -> Operand {
        let methods = self.decls().trait_info(t).map_or(0, |i| i.methods.len());
        let code = Operand::Const(Const::Code(FnRef::Shaped(t.clone(), walk)));
        let mut fields = vec![(code, Heapness::Static(false)); methods];
        fields.push((parts.witness.clone(), Heapness::Static(false)));
        fields.extend(parts.fields[..2].iter().cloned());
        if walk == Walk::Array {
            fields.push(parts.fields[2].clone());
        }
        if walk == Walk::Fields && Op::of(t) == Some(Op::Show) {
            fields.extend(self.show_frame(ty));
        }
        self.alloc(0, fields)
    }

    /// The opening and the closing of the text of a tuple or a record (std.show-output), as
    /// the structural `show` compiled for it writes them, and whether its fields are written
    /// with their names: `(` and `)`, or `,)` for one element; `Name { ` and ` }`, `{ ` and ` }`
    /// for an anonymous record (records.field-order), and `Name {}` for a record without fields.
    fn show_frame(&self, ty: &Ty) -> [(Operand, Heapness); 3] {
        let text = |s: String| (Operand::Const(Const::Str(s.into())), Heapness::Static(true));
        let labeled = |l: bool| (Operand::word(u64::from(l)), Heapness::Static(false));
        let name = match ty {
            Ty::Con(item, _) => item.name.to_string(),
            _ => String::new(),
        };
        match ty {
            Ty::Tuple(ts) => {
                let close = if ts.len() == 1 { ",)" } else { ")" };
                [text("(".into()), text(close.into()), labeled(false)]
            }
            _ if self.named_parts(ty).is_empty() => [
                text(format!("{name} {{}}")),
                text(String::new()),
                labeled(false),
            ],
            Ty::Con(item, _) if item.is_record() => {
                [text("{ ".into()), text(" }".into()), labeled(true)]
            }
            _ => [
                text(format!("{name} {{ ")),
                text(" }".into()),
                labeled(true),
            ],
        }
    }
}

/// The code of method `t` of the shape dictionaries that walk `walk`: it takes the location, the
/// dictionary, and each value in one word, as a dictionary's entry does.
pub(crate) fn shaped(cx: &Cx<'_>, f: &FnRef, t: &Item, walk: Walk) -> Option<Function> {
    let op = Op::of(t)?;
    let methods = u32::try_from(cx.decls().trait_info(t)?.methods.len()).ok()?;
    let mut l = Lower::new(cx, f.clone(), true);
    let dict = l.b.param(Repr::Heap, ParamMode::Borrowed, None);
    let env = Env {
        dict,
        len: methods + env_len(op, walk),
        at: methods,
    };
    let witness = l.borrowed_field(dict, env.len, env.at + WITNESS, Repr::Scalar);
    let ty = Ty::Param(numbered(u32::MAX));
    l.push_generic(ty.clone(), witness, Vec::new(), Some(&Held::Word));
    let repr = l.repr(&ty);
    let mut values = vec![Operand::Local(l.b.param(repr, ParamMode::Borrowed, None))];
    if op.binary() {
        values.push(Operand::Local(l.b.param(repr, ParamMode::Borrowed, None)));
    }
    l.ret = Conv::of(op.returns());
    let value = l.walk_shape(op, walk, &env, (&ty, &values));
    l.b.terminate(Terminator::Return(vec![value]));
    Some(l.into_function())
}

/// Where a shape dictionary's code finds the fields of its dictionary.
struct Env {
    dict: Local,
    len: u32,
    at: u32,
}

impl Lower<'_> {
    /// Field `k` after the methods of the dictionary.
    fn env(&mut self, env: &Env, k: u32, repr: Repr) -> Operand {
        Operand::Local(self.borrowed_field(env.dict, env.len, env.at + k, repr))
    }

    fn walk_shape(&mut self, op: Op, walk: Walk, env: &Env, values: (&Ty, &[Operand])) -> Operand {
        match walk {
            Walk::Fields => {
                let count = self.env(env, COUNT, Repr::Scalar);
                let entries = self.env(env, ENTRIES, Repr::Heap);
                let frame = (op == Op::Show).then(|| {
                    let open = self.env(env, OPEN, Repr::Heap);
                    let close = self.env(env, CLOSE, Repr::Heap);
                    let labeled = self.env(env, LABELED, Repr::Scalar);
                    (open, close, labeled)
                });
                self.walk_fields(op, &(count, entries), values, frame)
            }
            Walk::Variants => {
                let count = self.env(env, COUNT, Repr::Scalar);
                let entries = self.env(env, ENTRIES, Repr::Heap);
                self.walk_variants(op, (count, entries), values)
            }
            Walk::Array => {
                let thunk = self.env(env, THUNK, Repr::Heap);
                let size = self.env(env, SIZE, Repr::Scalar);
                let get = self.env(env, GET, Repr::Heap);
                self.walk_array(op, (thunk, size, get), values)
            }
        }
    }
}
