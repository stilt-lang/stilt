//! The prelude's traits behind the operators, interpolation and map keys (traits.prelude-traits,
//! traits.operators and traits.structural-impls): on the primitive types, whose structural impls
//! compile inline, and on every other type, through a call of its impl.

use stilt_hir::decls::{Lookup, TypeDefInfo, prelude_item};
use stilt_hir::hir::{BinaryOp, Item};
use stilt_types::ty::{Row, Ty};

use super::Lower;
use super::exprs::immediate;
use super::words::word;
use crate::items::ImplRef;
use crate::mir::{Const, NumKind, Operand, Prim, Repr, Runtime, Rvalue};
use crate::repr::num_kind;

/// `Less`, `Equal` and `Greater`, as immediates (std.option-result-and-ordering).
pub(crate) const LESS: u64 = immediate(0);
pub(crate) const EQUAL: u64 = immediate(1);
pub(crate) const GREATER: u64 = immediate(2);

/// The type a method of a prelude trait returns.
fn returns(name: &str) -> Ty {
    match name {
        "eq" => Ty::bool(),
        "compare" => Ty::named("Ordering"),
        "hash" => Ty::named("u64"),
        _ => Ty::str(),
    }
}

/// Whether a type is primitive: its structural impls of the prelude's traits compile inline.
pub(crate) fn primitive(ty: &Ty) -> bool {
    match ty {
        Ty::Tuple(ts) => ts.is_empty(),
        Ty::Con(item, args) => {
            args.is_empty()
                && &*item.home == "std.prelude"
                && (num_kind(ty).is_some() || ["bool", "str"].contains(&&*item.name))
        }
        _ => false,
    }
}

impl Lower<'_> {
    fn op(&mut self, prim: Prim, args: Vec<Operand>) -> Operand {
        self.b
            .define_op(Repr::Scalar, Rvalue::Prim(prim, args, Operand::word(0)))
    }

    pub(crate) fn rt(&mut self, repr: Repr, f: Runtime, args: Vec<Operand>) -> Operand {
        self.b.define_op(repr, Rvalue::Runtime(f, args))
    }

    /// A method of a prelude trait on a primitive type: its structural impl
    /// (traits.structural-impls, traits.floats and traits.show; std.show-output).
    pub(crate) fn primitive_trait(
        &mut self,
        t: &Item,
        name: &str,
        ty: &Ty,
        args: Vec<Operand>,
        _loc: Operand,
    ) -> Operand {
        let _ = t;
        let kind = num_kind(ty);
        let is_str = ty.is_prelude("str");
        let unit = matches!(ty, Ty::Tuple(_));
        let first = args.first().cloned().unwrap_or(Operand::word(0));
        match name {
            "eq" if unit => Operand::word(1),
            "eq" if is_str => self.rt(Repr::Scalar, Runtime::StrEq, args),
            "eq" => match kind {
                Some(k) if k.is_float() => self.op(Prim::Eq(k), args),
                _ => self.op(Prim::WordEq, args),
            },
            "compare" if unit => Operand::word(EQUAL),
            "compare" if is_str => self.rt(Repr::Scalar, Runtime::StrCompare, args),
            "compare" => self.op(Prim::Compare(kind.unwrap_or(NumKind::U8)), args),
            "hash" if unit => self.rt(Repr::Scalar, Runtime::HashStart, Vec::new()),
            "hash" if is_str => self.rt(Repr::Scalar, Runtime::HashStr, args),
            "hash" => self.rt(Repr::Scalar, Runtime::HashWord, args),
            "show_nested" if is_str => self.rt(Repr::Heap, Runtime::Quote, args),
            _ if unit => Operand::Const(Const::Str("()".into())),
            _ if is_str => self.b.define_op(Repr::Heap, Rvalue::Use(first)),
            _ => match kind {
                Some(k) if k.is_float() => self.rt(
                    Repr::Heap,
                    Runtime::ShowFloat,
                    vec![Operand::word(k.code()), first],
                ),
                Some(k) => self.rt(
                    Repr::Heap,
                    Runtime::ShowInt,
                    vec![Operand::word(k.code()), first],
                ),
                None => self.rt(Repr::Heap, Runtime::ShowBool, vec![first]),
            },
        }
    }

    /// A method of a prelude trait, `trait_name.name`, on values of type `ty`, given by their
    /// words, which it borrows.
    pub(crate) fn trait_call(
        &mut self,
        trait_name: &str,
        name: &str,
        ty: &Ty,
        args: Vec<Vec<Operand>>,
        loc: Operand,
    ) -> Operand {
        let t = prelude_item(trait_name);
        if primitive(ty) {
            let args = args.iter().map(|a| word(a, 0)).collect();
            return self.primitive_trait(&t, name, ty, args, loc);
        }
        if trait_name == "Eq"
            && let Some(equal) = self.inline_eq(ty, &args)
        {
            return equal;
        }
        let target = self.trait_target(&t, name.into(), ty, &[]);
        let forms = self.forms_of(&target);
        let mut values = Vec::new();
        for (i, a) in args.into_iter().enumerate() {
            values.extend(self.pass(a, ty, forms.param(i)));
        }
        let result = self.emit_call(target, values, &[], loc, false, &returns(name), &Row::EMPTY);
        word(&result, 0)
    }

    /// `x == y` for a value held inline of a record, a tuple or a variant type with one variant,
    /// whose structural `Eq` (traits.structural-impls) compares at most two words of primitive
    /// fields: the comparison of each field, in place of a call of the generated impl.
    fn inline_eq(&mut self, ty: &Ty, args: &[Vec<Operand>]) -> Option<Operand> {
        let structural = match ty {
            Ty::Tuple(_) => true,
            Ty::Con(item, _) => {
                let one = match self.decls().type_info(item)?.def {
                    TypeDefInfo::Record(_) => true,
                    TypeDefInfo::Variants(ref variants) => variants.len() == 1,
                    TypeDefInfo::Builtin => false,
                };
                one && !self.templates.heap(item)
                    && matches!(
                        self.impl_of(&prelude_item("Eq"), ty),
                        Some(ImplRef::Structural { .. })
                    )
            }
            _ => false,
        };
        let fields = self.fields_of(ty, 0);
        let small = fields.all.iter().map(|f| f.at.len()).sum::<usize>() <= 2;
        let flat = fields
            .all
            .iter()
            .all(|f| primitive(&f.ty) && !f.ty.is_prelude("str"));
        if !(structural && small && flat) || fields.object.is_some() {
            return None;
        }
        let (x, y) = (args.first()?, args.get(1)?);
        let mut equal: Option<Operand> = None;
        for j in 0..fields.all.len() {
            let (a, b) = (
                self.field_words(x, &fields, j),
                self.field_words(y, &fields, j),
            );
            let here = Operand::word(0);
            let one = self.primitive_trait(
                &prelude_item("Eq"),
                "eq",
                &fields.all[j].ty,
                vec![word(&a, 0), word(&b, 0)],
                here,
            );
            equal = Some(match equal {
                Some(so_far) => self.op(Prim::BitAnd, vec![so_far, one]),
                None => one,
            });
        }
        Some(equal.unwrap_or(Operand::word(1)))
    }

    /// The dictionaries through which a map finds keys of this type: `Eq` and `Hash`.
    pub(crate) fn key_dicts(&mut self, key: &Ty) -> (Operand, Operand) {
        let eq = self.dict(key, &prelude_item("Eq"));
        let hash = self.dict(key, &prelude_item("Hash"));
        (eq, hash)
    }

    /// `a op b`, on operands of type `ty` (numbers.integer-panics, numbers.wrapping and
    /// numbers.comparisons; traits.operators).
    pub(crate) fn binary_values(
        &mut self,
        op: BinaryOp,
        ty: &Ty,
        x: Vec<Operand>,
        y: Vec<Operand>,
        loc: Operand,
    ) -> Operand {
        if let Some(k) = num_kind(ty) {
            return self.numeric_binary(op, k, word(&x, 0), word(&y, 0), loc);
        }
        match op {
            BinaryOp::Eq => self.trait_call("Eq", "eq", ty, vec![x, y], loc),
            BinaryOp::Ne => {
                let eq = self.trait_call("Eq", "eq", ty, vec![x, y], loc);
                self.op(Prim::BoolNot, vec![eq])
            }
            _ => {
                let order = self.trait_call("Ord", "compare", ty, vec![x, y], loc);
                let (against, same) = match op {
                    BinaryOp::Lt => (LESS, true),
                    BinaryOp::Le => (GREATER, false),
                    BinaryOp::Gt => (GREATER, true),
                    _ => (LESS, false),
                };
                let eq = self.op(Prim::WordEq, vec![order, Operand::word(against)]);
                if same {
                    eq
                } else {
                    self.op(Prim::BoolNot, vec![eq])
                }
            }
        }
    }

    fn numeric_binary(
        &mut self,
        op: BinaryOp,
        k: NumKind,
        x: Operand,
        y: Operand,
        loc: Operand,
    ) -> Operand {
        let prim = match op {
            BinaryOp::Add => Prim::Add(k),
            BinaryOp::Sub => Prim::Sub(k),
            BinaryOp::Mul => Prim::Mul(k),
            BinaryOp::Div => Prim::Div(k),
            BinaryOp::Rem => Prim::Rem(k),
            BinaryOp::AddWrap => Prim::AddWrap(k),
            BinaryOp::SubWrap => Prim::SubWrap(k),
            BinaryOp::MulWrap => Prim::MulWrap(k),
            BinaryOp::BitAnd => Prim::BitAnd,
            BinaryOp::BitOr => Prim::BitOr,
            BinaryOp::BitXor => Prim::BitXor,
            BinaryOp::Shl => Prim::Shl(k),
            BinaryOp::Shr => Prim::Shr(k),
            BinaryOp::Eq => Prim::Eq(k),
            BinaryOp::Lt => Prim::Lt(k),
            BinaryOp::Le => Prim::Le(k),
            BinaryOp::Ne => {
                let eq = self.op(Prim::Eq(k), vec![x, y]);
                return self.op(Prim::BoolNot, vec![eq]);
            }
            BinaryOp::Gt => return self.op(Prim::Lt(k), vec![y, x]),
            BinaryOp::Ge => return self.op(Prim::Le(k), vec![y, x]),
            BinaryOp::And | BinaryOp::Or => unreachable!("lowered as branches"),
        };
        self.b
            .define_op(Repr::Scalar, Rvalue::Prim(prim, vec![x, y], loc))
    }
}
