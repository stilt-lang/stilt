//! The values of a property's cases (tests.property-cases, tests.composite-values and
//! tests.minimal-values): minimal values, and values generated from a case's draws, as data that a
//! tape gives the property's entry ([`super::tape`]). The reference interpreter's `Prop_gen`
//! generates the same values.

use stilt_types::generable::{Graph, Node};

use super::draw::Draws;

/// A value of a node's type. A scalar is the word that compiled code holds it in: a `bool`'s 0
/// or 1, an integer sign- or zero-extended to 64 bits, and a float's bits. A tuple's elements,
/// a list's and a record's fields are a sequence, in declaration order for a record. A map is
/// its entries in insertion order, and a variant its number among its type's variants, in
/// declaration order, with its payloads. Two values are identical, as tests.shrink-candidates
/// compares them, when they are equal.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Val {
    Word(u64),
    Str(String),
    Unit,
    Seq(Vec<Val>),
    Map(Vec<(Val, Val)>),
    Variant(usize, Vec<Val>),
}

/// The minimal value of a node's type (tests.minimal-values).
pub(super) fn minimal(g: &Graph, k: usize) -> Val {
    match &g.nodes[k] {
        Node::Bool | Node::Int { .. } => Val::Word(0),
        Node::Float { f32 } => Val::Word(if *f32 {
            u64::from(0f32.to_bits())
        } else {
            0f64.to_bits()
        }),
        Node::Str => Val::Str(String::new()),
        Node::Unit => Val::Unit,
        Node::List(_) => Val::Seq(Vec::new()),
        Node::Map(..) => Val::Map(Vec::new()),
        Node::Tuple(slots) => Val::Seq(slots.iter().map(|&s| minimal(g, s)).collect()),
        Node::Record(_, fields) => Val::Seq(fields.iter().map(|&(_, s)| minimal(g, s)).collect()),
        Node::Variants(vs) => {
            let v = g.nearest(vs)[0];
            Val::Variant(v, vs[v].1.iter().map(|&s| minimal(g, s)).collect())
        }
    }
}

/// The word of an integer of `bits` bits, as compiled code holds it.
pub(super) fn int_word(value: i128, signed: bool) -> u64 {
    if signed {
        #[expect(clippy::cast_possible_truncation, reason = "the value is of the kind")]
        let w = value as i64;
        w.cast_unsigned()
    } else {
        #[expect(
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss,
            reason = "as above"
        )]
        let w = value as u64;
        w
    }
}

/// The value of an integer's word.
pub(super) fn int_value(word: u64, signed: bool) -> i128 {
    if signed {
        i128::from(word.cast_signed())
    } else {
        i128::from(word)
    }
}

/// The smallest and largest values of an integer kind.
pub(super) fn range(bits: u32, signed: bool) -> (i128, i128) {
    if signed {
        (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
    } else {
        (0, (1i128 << bits) - 1)
    }
}

/// The boundary values of an integer type (tests.boundary-values).
fn int_bounds(bits: u32, signed: bool) -> Vec<i128> {
    let (lo, hi) = range(bits, signed);
    if signed {
        vec![0, 1, -1, lo, hi, lo + 1, hi - 1]
    } else {
        vec![0, 1, hi, hi - 1]
    }
}

/// The boundary values of a float type, as their words (tests.boundary-values).
fn float_bounds(f32: bool) -> Vec<u64> {
    if f32 {
        [
            0.0,
            -0.0,
            1.0,
            -1.0,
            f32::MAX,
            -f32::MAX,
            f32::MIN_POSITIVE,
            f32::from_bits(1),
            f32::INFINITY,
            f32::NEG_INFINITY,
            f32::NAN,
        ]
        .map(|x| u64::from(x.to_bits()))
        .to_vec()
    } else {
        [
            0.0,
            -0.0,
            1.0,
            -1.0,
            f64::MAX,
            -f64::MAX,
            f64::MIN_POSITIVE,
            f64::from_bits(1),
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
        ]
        .map(f64::to_bits)
        .to_vec()
    }
}

fn int(d: &mut Draws, size: u64, bits: u32, signed: bool) -> Val {
    let value = match d.below(4) {
        0 => {
            let b = int_bounds(bits, signed);
            b[d.below_usize(b.len())]
        }
        1 | 2 if signed => i128::from(d.below(2 * size + 1)) - i128::from(size),
        1 | 2 => i128::from(d.below(size + 1)),
        _ => {
            let low = d.next();
            let shift = 64 - bits;
            return Val::Word(if signed {
                ((low << shift).cast_signed() >> shift).cast_unsigned()
            } else {
                (low << shift) >> shift
            });
        }
    };
    Val::Word(int_word(value, signed))
}

#[expect(clippy::cast_precision_loss, reason = "the integer is far below 2^24")]
fn float(d: &mut Draws, size: u64, f32: bool) -> Val {
    Val::Word(match d.below(4) {
        0 => {
            let b = float_bounds(f32);
            b[d.below_usize(b.len())]
        }
        1 | 2 => {
            let n = i128::from(d.below(512 * size + 1)) - i128::from(256 * size);
            if f32 {
                u64::from((n as f32 / 256.0).to_bits())
            } else {
                (n as f64 / 256.0).to_bits()
            }
        }
        _ if f32 => d.next() & 0xffff_ffff,
        _ => d.next(),
    })
}

fn scalar_value(d: &mut Draws) -> char {
    let c = match d.below(4) {
        0 | 1 => 0x20 + d.below(95),
        2 => d.below(128),
        _ => {
            let v = d.below(0x10_F800);
            if v >= 0xD800 { v + 0x800 } else { v }
        }
    };
    u32::try_from(c)
        .ok()
        .and_then(char::from_u32)
        .unwrap_or('\0')
}

/// A value of a scalar type at a size (tests.generated-scalars).
pub(super) fn scalar(d: &mut Draws, size: u64, node: &Node) -> Val {
    match node {
        Node::Bool => Val::Word(u64::from(d.below(2) == 1)),
        Node::Int { bits, signed } => int(d, size, *bits, *signed),
        Node::Float { f32 } => float(d, size, *f32),
        Node::Str => {
            let n = d.below(size + 1);
            Val::Str((0..n).map(|_| scalar_value(d)).collect())
        }
        _ => Val::Unit,
    }
}

/// tests.composite-values: each of `k` components' budget.
fn share(budget: u64, k: usize) -> u64 {
    if budget >= 1 && k > 0 {
        (budget - 1) / k as u64
    } else {
        0
    }
}

/// A value of a node's type at a budget and a size (tests.generated-scalars and
/// tests.composite-values). A map's entries are generated as they come, a key equal to an earlier
/// one included: inserting them is the entry's work ([`super::tape`]).
pub(super) fn generate(g: &Graph, draws: &mut Draws, budget: u64, size: u64, k: usize) -> Val {
    let make = |draws: &mut Draws, each: u64, node: usize| generate(g, draws, each, size, node);
    match &g.nodes[k] {
        Node::Tuple(slots) => {
            let each = share(budget, slots.len());
            Val::Seq(slots.iter().map(|&s| make(draws, each, s)).collect())
        }
        Node::Record(_, fields) => {
            let each = share(budget, fields.len());
            Val::Seq(fields.iter().map(|&(_, s)| make(draws, each, s)).collect())
        }
        Node::List(elem) => {
            let n = draws.below_usize(usize::try_from(budget + 1).unwrap_or(usize::MAX));
            let each = share(budget, n);
            Val::Seq((0..n).map(|_| make(draws, each, *elem)).collect())
        }
        Node::Map(key, value) => {
            let n = draws.below_usize(usize::try_from(budget + 1).unwrap_or(usize::MAX));
            let each = share(budget, 2 * n);
            Val::Map(
                (0..n)
                    .map(|_| (make(draws, each, *key), make(draws, each, *value)))
                    .collect(),
            )
        }
        Node::Variants(vs) => {
            let among = if budget >= 1 {
                g.live(vs)
            } else {
                g.nearest(vs)
            };
            let v = among[draws.below_usize(among.len())];
            let each = share(budget, vs[v].1.len());
            Val::Variant(v, vs[v].1.iter().map(|&s| make(draws, each, s)).collect())
        }
        node => scalar(draws, size, node),
    }
}

/// The values of case `case` of a property whose parameters have the nodes `params`
/// (tests.property-cases).
pub(super) fn case(g: &Graph, seed: u64, params: &[usize], case: u64) -> Vec<Val> {
    if case == 0 {
        return params.iter().map(|&k| minimal(g, k)).collect();
    }
    let mut d = Draws::new(seed, case);
    params
        .iter()
        .map(|&k| generate(g, &mut d, case, case, k))
        .collect()
}
