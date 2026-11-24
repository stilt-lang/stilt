//! Numbers (numbers.numeric-types): literals, and the native methods of the numeric types, which
//! compile to primitive operations rather than calls.
//!
//! An integer is held sign-extended or zero-extended to 64 bits, as its kind is signed or not,
//! so a conversion between integer types that keeps the value keeps the word.

use stilt_hir::hir::Item;
use stilt_types::tast::{self, Callee, Expr};
use stilt_types::ty::Ty;

use super::Lower;
use super::exprs::immediate;
use crate::items::{Code, code_of};
use crate::mir::{NumKind, Operand, Prim, Repr, Rvalue};
use crate::repr::{num_kind, num_kind_of};

/// Whether a trait is one of the prelude's, whose methods on primitive types compile inline
/// (traits.prelude-traits).
fn is_prelude_trait(t: &Item) -> bool {
    &*t.home == "std.prelude" && crate::lower::dicts::PRELUDE_TRAITS.contains(&&*t.name)
}

/// Whether a native method of the integer types is a function of the runtime, as those of
/// std.integers are, rather than an operation that compiles inline.
pub(crate) fn in_runtime(name: &str) -> bool {
    matches!(
        name,
        "checked_add"
            | "checked_sub"
            | "checked_mul"
            | "saturating_add"
            | "saturating_sub"
            | "pow"
            | "div_euclid"
            | "rem_euclid"
            | "count_ones"
            | "leading_zeros"
            | "trailing_zeros"
            | "gcd"
            | "lcm"
    )
}

/// The radix and the digits of an integer literal (lexical.integer-literals), without its
/// underscores.
fn digits(text: &str) -> (u32, String) {
    let text: String = text.chars().filter(|&c| c != '_').collect();
    match text.get(..2) {
        Some("0x") => (16, text[2..].to_owned()),
        Some("0o") => (8, text[2..].to_owned()),
        Some("0b") => (2, text[2..].to_owned()),
        _ => (10, text),
    }
}

/// The value of an integer literal of an integer type, which fits in 64 bits.
fn int_value(text: &str) -> i128 {
    let (radix, digits) = digits(text);
    i128::from_str_radix(&digits, radix).unwrap_or(0)
}

/// The value of an integer literal of a float type, which the type represents exactly
/// (numbers.integer-literals), and may exceed every integer type.
fn float_value(text: &str) -> f64 {
    match digits(text) {
        (10, digits) => digits.parse().unwrap_or(0.0),
        // Each prefix of the digits is the value shifted right, so it is exact too.
        (radix, digits) => digits
            .chars()
            .filter_map(|c| c.to_digit(radix))
            .fold(0.0, |x, d| x * f64::from(radix) + f64::from(d)),
    }
}

/// The word of an integer literal of type `ty`, negated if `negative` (numbers.integer-literals and
/// numbers.negative-literals). A literal of a float type is exact (numbers.integer-literals), and
/// `-0` is `-0.0` (numbers.negative-literals).
pub(crate) fn int_literal(text: &str, negative: bool, ty: &Ty) -> u64 {
    let float = || {
        let x = float_value(text);
        if negative { -x } else { x }
    };
    match num_kind(ty) {
        Some(NumKind::F64) => float().to_bits(),
        Some(NumKind::F32) => {
            #[expect(
                clippy::cast_possible_truncation,
                reason = "the literal is exact as an f32"
            )]
            let x = float() as f32;
            u64::from(x.to_bits())
        }
        kind => {
            let value = int_value(text);
            kind.unwrap_or(NumKind::I64)
                .word(if negative { -value } else { value })
        }
    }
}

/// The word of a float literal of type `ty`, rounded to nearest with ties to even
/// (numbers.float-literals).
pub(crate) fn float_literal(text: &str, ty: &Ty) -> u64 {
    let text: String = text.chars().filter(|&c| c != '_').collect();
    if num_kind(ty) == Some(NumKind::F32) {
        u64::from(text.parse::<f32>().unwrap_or(0.0).to_bits())
    } else {
        text.parse::<f64>().unwrap_or(0.0).to_bits()
    }
}

impl Lower<'_> {
    fn prim(&mut self, repr: Repr, prim: Prim, args: Vec<Operand>, loc: Operand) -> Operand {
        self.b.define_op(repr, Rvalue::Prim(prim, args, loc))
    }

    /// `Some(x)` of a scalar `x`, or `None` when `fits` is false: an `Option` held inline, its
    /// tag then its payload, which is 0 for `None`.
    pub(crate) fn some_if(&mut self, fits: Operand, x: Operand) -> Vec<Operand> {
        let (tag, payload) = (self.b.temp(Repr::Scalar), self.b.temp(Repr::Scalar));
        let (yes, no, join) = (self.b.new_block(), self.b.new_block(), self.b.new_block());
        self.b.branch(fits, yes, no);
        self.b.switch_to(yes);
        self.b.assign(tag, Rvalue::Use(Operand::word(immediate(1))));
        self.b.assign(payload, Rvalue::Use(x));
        self.b.goto(join);
        self.b.switch_to(no);
        self.b.assign(tag, Rvalue::Use(Operand::word(immediate(0))));
        self.b.assign(payload, Rvalue::Use(Operand::word(0)));
        self.b.goto(join);
        self.b.switch_to(join);
        vec![Operand::Local(tag), Operand::Local(payload)]
    }

    /// A call that compiles inline: a native method of a numeric type, or a method of a
    /// prelude trait on a primitive type.
    pub(crate) fn inline_call(
        &mut self,
        callee: &Callee,
        args: &[tast::Arg],
        e: &Expr,
    ) -> Option<Vec<Operand>> {
        match callee {
            Callee::Member(owner, name)
                if &**name == "push"
                    && stilt_types::ty::is_prelude(owner, "List")
                    && self.is_native(owner, name) =>
            {
                self.push(args)
            }
            Callee::Member(owner, name) => {
                let kind = num_kind(&Ty::Con(owner.clone(), Vec::new()))?;
                if !self.is_native(owner, name) || in_runtime(name) {
                    return None;
                }
                let values: Vec<Operand> = args.iter().map(|a| self.expr1(&a.value)).collect();
                let loc = self.loc_at(e.at);
                Some(self.numeric_native(kind, name, values, loc, &e.ty))
            }
            Callee::TraitMethod(t, name, ty)
                if super::traits::primitive(ty) && is_prelude_trait(t) =>
            {
                let values: Vec<Operand> = args.iter().map(|a| self.expr1(&a.value)).collect();
                let loc = self.loc_at(e.at);
                Some(vec![self.primitive_trait(t, name, ty, values, loc)])
            }
            _ => None,
        }
    }

    fn is_native(&self, owner: &Item, name: &str) -> bool {
        let key = crate::FnRef::Member(owner.clone(), name.into());
        matches!(
            code_of(self.cx.db, self.cx.program, key),
            Some(Code::Native)
        )
    }

    /// A native method of a numeric type (numbers.conversions and numbers.wrapping-conversions;
    /// std.integers and std.floats).
    pub(crate) fn numeric_native(
        &mut self,
        kind: NumKind,
        name: &str,
        args: Vec<Operand>,
        loc: Operand,
        ty: &Ty,
    ) -> Vec<Operand> {
        let repr = self.repr(ty);
        let unary = |p: fn(NumKind) -> Prim| p(kind);
        let simple = match name {
            "abs" => Some(unary(Prim::Abs)),
            "min" => Some(unary(Prim::Min)),
            "max" => Some(unary(Prim::Max)),
            "sqrt" => Some(unary(Prim::Sqrt)),
            "floor" => Some(unary(Prim::Floor)),
            "ceil" => Some(unary(Prim::Ceil)),
            "trunc" => Some(unary(Prim::Trunc)),
            "round" => Some(unary(Prim::Round)),
            "is_nan" => Some(unary(Prim::IsNan)),
            _ => None,
        };
        if let Some(p) = simple {
            return vec![self.prim(repr, p, args, loc)];
        }
        if let Some(target) = name.strip_prefix("wrap_to_").and_then(num_kind_of) {
            return vec![self.prim(repr, Prim::Wrap(kind, target), args, loc)];
        }
        let target = name
            .strip_prefix("to_")
            .and_then(num_kind_of)
            .unwrap_or(kind);
        let x = args.into_iter().next().unwrap_or(Operand::word(0));
        self.convert(kind, target, x, loc, ty)
    }

    /// `.to_T()` (numbers.conversions).
    fn convert(
        &mut self,
        from: NumKind,
        to: NumKind,
        x: Operand,
        loc: Operand,
        ty: &Ty,
    ) -> Vec<Operand> {
        let optional = ty.is_prelude("Option");
        match (from.is_float(), to.is_float()) {
            (_, true) if from == to => vec![x],
            (_, true) => vec![self.prim(Repr::Scalar, Prim::ToFloat(from, to), vec![x], loc)],
            (true, false) => {
                let fits = self.prim(
                    Repr::Scalar,
                    Prim::FloatFits(from, to),
                    vec![x.clone()],
                    loc.clone(),
                );
                let value = self.prim(Repr::Scalar, Prim::FloatToInt(from, to), vec![x], loc);
                self.some_if(fits, value)
            }
            (false, false) if optional => {
                let fits = self.prim(Repr::Scalar, Prim::Fits(from, to), vec![x.clone()], loc);
                self.some_if(fits, x)
            }
            (false, false) => vec![x],
        }
    }
}

impl Lower<'_> {
    /// The body of a native method of a numeric type used as a value: its operation, on the
    /// value parameters.
    pub(crate) fn inline_native(
        &mut self,
        f: &crate::FnRef,
        args: &[crate::mir::Arg],
        ret: &Ty,
    ) -> Option<Vec<Operand>> {
        let crate::FnRef::Member(owner, name) = f else {
            return None;
        };
        let kind = num_kind(&Ty::Con(owner.clone(), Vec::new()))?;
        if !self.is_native(owner, name) || in_runtime(name) {
            return None;
        }
        let values = args
            .iter()
            .flat_map(|a| a.operands().into_iter().cloned())
            .collect();
        let loc = Operand::Local(self.loc);
        Some(self.numeric_native(kind, name, values, loc, ret))
    }
}
