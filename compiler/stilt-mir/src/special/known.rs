//! What an instantiation knows of a value, and the rvalues it computes from what it knows.
//!
//! A value is known as a constant: a witness, a value parameter's number, a dictionary or a
//! descriptor, which are static data once their parts are known (builds.specialization), or for an
//! object that the code makes, a closure or a dictionary, as the fields of it that are
//! constants. Only operations that can't panic are computed, so a static expression that
//! panics still panics where the run reaches it (meta.erasure).

use std::sync::Arc;

use crate::mir::{Const, Heapness, NumKind, Operand, Prim, Repr, Runtime, Rvalue};
use crate::shape;

/// The most parts a constant that specialization makes may have: past it, the code that would
/// make it, as a dictionary of a type that holds itself ever more deeply does, makes it at run
/// time, which bounds the instantiations of a program (builds.what-stays-generic).
pub(crate) const MOST_PARTS: usize = 512;

/// What an instantiation knows of one of its hidden parameters.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Known {
    Unknown,
    Const(Const),
    /// An object whose fields, by index, are the constants given, or unknown.
    Fields(Arc<[Option<Const>]>),
}

/// What an instantiation knows of each of its hidden parameters but the location.
pub(crate) type Key = Vec<Known>;

/// Whether a key knows nothing.
pub(crate) fn knows_nothing(key: &Key) -> bool {
    key.iter().all(|k| *k == Known::Unknown)
}

/// The number of parts of a constant, itself among them.
pub(crate) fn parts(c: &Const) -> usize {
    match c {
        Const::Data(_, fields) => 1 + fields.iter().map(|(f, _)| parts(f)).sum::<usize>(),
        _ => 1,
    }
}

/// What the code knows of each local: its constant value, if it has one, and the fields of
/// the object it holds that are constants.
#[derive(Debug, Default)]
pub(crate) struct Facts {
    pub(crate) values: Vec<Option<Const>>,
    pub(crate) objects: Vec<Option<Arc<[Option<Const>]>>>,
}

impl Facts {
    pub(crate) fn new(locals: usize) -> Self {
        Self {
            values: vec![None; locals],
            objects: vec![None; locals],
        }
    }

    /// The constant an operand holds, if it is known.
    pub(crate) fn value(&self, o: &Operand) -> Option<Const> {
        match o {
            Operand::Const(c) => Some(c.clone()),
            Operand::Local(l) => self.values[l.0 as usize].clone(),
        }
    }

    fn word(&self, o: &Operand) -> Option<u64> {
        match self.value(o)? {
            Const::Word(w) => Some(w),
            _ => None,
        }
    }

    /// The constant field `index` of the object an operand holds, if it is known.
    pub(crate) fn field(&self, o: &Operand, index: u32) -> Option<Const> {
        let i = index as usize;
        match o {
            Operand::Const(Const::Data(_, fields)) => fields.get(i).map(|(c, _)| c.clone()),
            Operand::Local(l) => match &self.values[l.0 as usize] {
                Some(Const::Data(_, fields)) => fields.get(i).map(|(c, _)| c.clone()),
                Some(_) => None,
                None => self.objects[l.0 as usize].as_ref()?.get(i).cloned()?,
            },
            Operand::Const(_) => None,
        }
    }

    /// Whether a word of this heapness is a heap word, if that is known.
    pub(crate) fn heap(&self, h: Heapness) -> Option<bool> {
        match h {
            Heapness::Static(heap) => Some(heap),
            Heapness::Witness(w) => self.values[w.0 as usize].as_ref().and_then(|c| match c {
                Const::Word(shape) => Some(shape & shape::HEAP != 0),
                _ => None,
            }),
            Heapness::Array(_) => None,
        }
    }

    /// A representation with each word whose witness is known a scalar or a heap word.
    pub(crate) fn repr(&self, r: Repr) -> Repr {
        let known = |w: crate::mir::Local| match &self.values[w.0 as usize] {
            Some(Const::Word(shape)) if shape & shape::HEAP != 0 => Some(Repr::Heap),
            Some(Const::Word(_)) => Some(Repr::Scalar),
            _ => Some(Repr::Generic(w)),
        };
        r.map_witnesses(&known).unwrap_or(r)
    }

    /// The constant that an rvalue computes, when everything it reads is known and computing
    /// it can't panic.
    pub(crate) fn fold(&self, r: &Rvalue) -> Option<Const> {
        match r {
            Rvalue::Use(o) => self.value(o),
            Rvalue::Field {
                base, len, index, ..
            } => {
                let field = self.field(base, *index)?;
                match self.value(base) {
                    Some(Const::Data(_, fields)) if fields.len() != *len as usize => None,
                    _ => Some(field),
                }
            }
            Rvalue::Tag(o) => match self.value(o)? {
                Const::Word(w) if w & 1 == 1 => Some(Const::Word(w >> 1)),
                Const::Data(tag, _) => Some(Const::Word(u64::from(tag))),
                _ => None,
            },
            Rvalue::Prim(p, args, _) => {
                let words: Option<Vec<u64>> = args.iter().map(|a| self.word(a)).collect();
                prim(*p, &words?).map(Const::Word)
            }
            Rvalue::Runtime(Runtime::Shape, words) => {
                let heap: Option<Vec<bool>> = words
                    .iter()
                    .map(|w| self.word(w).map(|s| s & shape::HEAP != 0))
                    .collect();
                shape::of_words(&heap?).map(Const::Word)
            }
            Rvalue::Alloc(tag, fields) => self.data(*tag, fields),
            _ => None,
        }
    }

    /// The static data that an allocation of known fields makes, as lowering makes it of a
    /// value whose parts are all known.
    fn data(&self, tag: u16, fields: &[(Operand, Heapness)]) -> Option<Const> {
        let fields: Option<Vec<(Const, bool)>> = fields
            .iter()
            .map(|(o, h)| Some((self.value(o)?, self.heap(*h)?)))
            .collect();
        let data = Const::Data(tag, fields?);
        (parts(&data) <= MOST_PARTS).then_some(data)
    }

    /// The fields of an allocation that are known, for an object the code makes.
    pub(crate) fn object(&self, fields: &[(Operand, Heapness)]) -> Arc<[Option<Const>]> {
        fields.iter().map(|(o, _)| self.value(o)).collect()
    }
}

/// The value of a primitive operation of known words that can't panic, on 64-bit integers
/// and `bool`s, as witnesses and value parameters are.
fn prim(op: Prim, words: &[u64]) -> Option<u64> {
    let wide = |kind: NumKind| matches!(kind, NumKind::I64 | NumKind::U64);
    let signed = |x: u64| x.cast_signed();
    Some(match (op, words) {
        (Prim::BitAnd, [a, b]) => a & b,
        (Prim::BitOr, [a, b]) => a | b,
        (Prim::BitXor, [a, b]) => a ^ b,
        (Prim::BoolNot, [a]) => u64::from(*a == 0),
        (Prim::WordEq, [a, b]) => u64::from(a == b),
        (Prim::Shr(NumKind::U64), [a, b]) if *b < 64 => a >> b,
        (Prim::Shr(NumKind::I64), [a, b]) if *b < 64 => (signed(*a) >> b).cast_unsigned(),
        (Prim::Shl(kind), [a, b]) if wide(kind) && *b < 64 => a << b,
        (Prim::Eq(kind), [a, b]) if wide(kind) => u64::from(a == b),
        (Prim::Lt(NumKind::U64), [a, b]) => u64::from(a < b),
        (Prim::Le(NumKind::U64), [a, b]) => u64::from(a <= b),
        (Prim::Lt(NumKind::I64), [a, b]) => u64::from(signed(*a) < signed(*b)),
        (Prim::Le(NumKind::I64), [a, b]) => u64::from(signed(*a) <= signed(*b)),
        (Prim::AddWrap(kind), [a, b]) if wide(kind) => a.wrapping_add(*b),
        (Prim::SubWrap(kind), [a, b]) if wide(kind) => a.wrapping_sub(*b),
        (Prim::MulWrap(kind), [a, b]) if wide(kind) => a.wrapping_mul(*b),
        (Prim::Add(NumKind::I64), [a, b]) => signed(*a).checked_add(signed(*b))?.cast_unsigned(),
        (Prim::Sub(NumKind::I64), [a, b]) => signed(*a).checked_sub(signed(*b))?.cast_unsigned(),
        (Prim::Mul(NumKind::I64), [a, b]) => signed(*a).checked_mul(signed(*b))?.cast_unsigned(),
        (Prim::Add(NumKind::U64), [a, b]) => a.checked_add(*b)?,
        (Prim::Sub(NumKind::U64), [a, b]) => a.checked_sub(*b)?,
        (Prim::Mul(NumKind::U64), [a, b]) => a.checked_mul(*b)?,
        _ => return None,
    })
}
