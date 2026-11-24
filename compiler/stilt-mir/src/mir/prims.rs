//! The numeric kinds, and the primitive operations that compile inline.

use serde::{Deserialize, Serialize};

/// The numeric types, by the kinds the runtime numbers them with.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum NumKind {
    /// `i8`.
    I8,
    /// `i16`.
    I16,
    /// `i32`.
    I32,
    /// `i64`.
    I64,
    /// `u8`.
    U8,
    /// `u16`.
    U16,
    /// `u32`.
    U32,
    /// `u64`.
    U64,
    /// `f32`.
    F32,
    /// `f64`.
    F64,
}

/// A primitive operation, which compiles inline. Those that can panic take a location.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Prim {
    /// Arithmetic that panics on overflow and division by zero (numbers.integer-panics).
    Add(NumKind),
    /// An addition of two integers that the optimizer proved at least 0, which can only
    /// overflow past the maximum, and panics there.
    AddUp(NumKind),
    /// `-`, which panics as [`Prim::Add`] does.
    Sub(NumKind),
    /// `*`, which panics as [`Prim::Add`] does.
    Mul(NumKind),
    /// `/`, which panics as [`Prim::Add`] does.
    Div(NumKind),
    /// `%`, which panics as [`Prim::Add`] does.
    Rem(NumKind),
    /// `-x`, which panics as [`Prim::Add`] does.
    Neg(NumKind),
    /// Wrapping arithmetic (numbers.wrapping).
    AddWrap(NumKind),
    /// `-%`.
    SubWrap(NumKind),
    /// `*%`.
    MulWrap(NumKind),
    /// Division and remainder of integers by a divisor that the optimizer proved positive,
    /// which can't fail.
    DivByPositive(NumKind),
    /// The remainder by a divisor proved positive.
    RemByPositive(NumKind),
    /// `&`.
    BitAnd,
    /// `|`.
    BitOr,
    /// `^`.
    BitXor,
    /// Bitwise not of an integer, or logical not of a `bool`.
    Not(NumKind),
    /// `!` of a `bool`.
    BoolNot,
    /// `<<`.
    Shl(NumKind),
    /// `>>`.
    Shr(NumKind),
    /// Comparisons of numbers: IEEE on floats (numbers.ieee-754).
    Eq(NumKind),
    /// `<`.
    Lt(NumKind),
    /// `<=`.
    Le(NumKind),
    /// Equality of words: scalars that aren't floats, and immediates.
    WordEq,
    /// The total order of traits.floats on floats, as an `Ordering`, and the order of
    /// integers.
    Compare(NumKind),
    /// `.to_T()` between integers, which can't lose the value.
    Widen(NumKind, NumKind),
    /// Whether an integer of the first kind fits in the second.
    Fits(NumKind, NumKind),
    /// `.wrap_to_T()` (numbers.wrapping-conversions).
    Wrap(NumKind, NumKind),
    /// Integer to float, and float to float (numbers.conversions).
    ToFloat(NumKind, NumKind),
    /// Whether a float's truncation fits in an integer kind, and the truncation.
    FloatFits(NumKind, NumKind),
    /// The truncation of a float that [`Prim::FloatFits`] has found to fit.
    FloatToInt(NumKind, NumKind),
    /// `.abs()`.
    Abs(NumKind),
    /// `.min(b)`.
    Min(NumKind),
    /// `.max(b)`.
    Max(NumKind),
    /// `.sqrt()`.
    Sqrt(NumKind),
    /// `.floor()`.
    Floor(NumKind),
    /// `.ceil()`.
    Ceil(NumKind),
    /// `.trunc()`.
    Trunc(NumKind),
    /// `.round()`.
    Round(NumKind),
    /// `.is_nan()`.
    IsNan(NumKind),
}
