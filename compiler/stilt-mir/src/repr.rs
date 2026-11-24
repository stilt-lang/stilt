//! How the types of the typed bodies are represented as words.

use std::sync::Arc;

use stilt_types::ty::{FLOAT_TYPES, INTEGER_TYPES, Ty};

use crate::mir::{NumKind, Shown, ShownKind};

/// The numeric kind of a type, if it is a numeric type.
pub(crate) fn num_kind(ty: &Ty) -> Option<NumKind> {
    num_kind_of(ty.numeric_name()?)
}

/// The numeric kind of a numeric type's name.
pub(crate) fn num_kind_of(name: &str) -> Option<NumKind> {
    Some(match name {
        "i8" => NumKind::I8,
        "i16" => NumKind::I16,
        "i32" => NumKind::I32,
        "i64" => NumKind::I64,
        "u8" => NumKind::U8,
        "u16" => NumKind::U16,
        "u32" => NumKind::U32,
        "u64" => NumKind::U64,
        "f32" => NumKind::F32,
        "f64" => NumKind::F64,
        _ => return None,
    })
}

impl NumKind {
    /// The runtime's number for the kind.
    #[must_use]
    pub fn code(self) -> u64 {
        match self {
            NumKind::I8 => 0,
            NumKind::I16 => 1,
            NumKind::I32 => 2,
            NumKind::I64 => 3,
            NumKind::U8 => 4,
            NumKind::U16 => 5,
            NumKind::U32 => 6,
            NumKind::U64 => 7,
            NumKind::F32 => 8,
            NumKind::F64 => 9,
        }
    }

    /// Whether it is a float kind.
    #[must_use]
    pub fn is_float(self) -> bool {
        matches!(self, NumKind::F32 | NumKind::F64)
    }

    /// Whether it is a signed integer kind.
    #[must_use]
    pub fn is_signed(self) -> bool {
        matches!(
            self,
            NumKind::I8 | NumKind::I16 | NumKind::I32 | NumKind::I64
        )
    }

    /// The width of an integer kind, in bits.
    #[must_use]
    pub fn bits(self) -> u32 {
        match self {
            NumKind::I8 | NumKind::U8 => 8,
            NumKind::I16 | NumKind::U16 => 16,
            NumKind::I32 | NumKind::U32 | NumKind::F32 => 32,
            NumKind::I64 | NumKind::U64 | NumKind::F64 => 64,
        }
    }

    /// The smallest and largest values of an integer kind, as `i128`.
    #[must_use]
    pub fn range(self) -> (i128, i128) {
        let bits = self.bits();
        if self.is_signed() {
            (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
        } else {
            (0, (1i128 << bits) - 1)
        }
    }

    /// The word that holds an integer of this kind: sign-extended for a signed kind, and
    /// zero-extended for an unsigned one.
    #[must_use]
    pub fn word(self, value: i128) -> u64 {
        #[expect(clippy::cast_possible_truncation, reason = "the value is of the kind")]
        let w = value as i64;
        w.cast_unsigned()
    }
}

/// Whether a type's values are scalars: numbers, `bool`, `()`, `Never`, and `std.c`'s addresses.
pub(crate) fn is_scalar(ty: &Ty) -> bool {
    match ty {
        Ty::Tuple(ts) => ts.is_empty(),
        // An address that C reads or writes, and a string C ends with a NUL, each one word
        // (c.module-std-c).
        Ty::Con(item, _) if &*item.home == "std.c" => matches!(&*item.name, "Ptr" | "Str"),
        Ty::Con(item, args) if args.is_empty() && &*item.home == "std.prelude" => {
            let name = &*item.name;
            INTEGER_TYPES.contains(&name)
                || FLOAT_TYPES.contains(&name)
                || name == "bool"
                || name == "Never"
        }
        _ => false,
    }
}

/// How a debugger shows a word of `ty` (goal debuggable-builds).
pub(crate) fn shown(ty: &Ty, by_ref: bool) -> Shown {
    let kind = match num_kind(ty) {
        Some(NumKind::I8) => ShownKind::Signed(8),
        Some(NumKind::I16) => ShownKind::Signed(16),
        Some(NumKind::I32) => ShownKind::Signed(32),
        Some(NumKind::I64) => ShownKind::Signed(64),
        Some(NumKind::U8) => ShownKind::Unsigned(8),
        Some(NumKind::U16) => ShownKind::Unsigned(16),
        Some(NumKind::U32) => ShownKind::Unsigned(32),
        Some(NumKind::U64) => ShownKind::Unsigned(64),
        Some(NumKind::F32) => ShownKind::Float(32),
        Some(NumKind::F64) => ShownKind::Float(64),
        None => match ty {
            Ty::Con(item, args) if args.is_empty() && &*item.home == "std.prelude" => {
                match &*item.name {
                    "bool" => ShownKind::Bool,
                    "str" => ShownKind::Str,
                    _ if is_scalar(ty) => ShownKind::Opaque,
                    _ => ShownKind::Heap,
                }
            }
            Ty::Param(_) | Ty::SelfTy | Ty::Var(_) | Ty::Error => ShownKind::Opaque,
            _ if is_scalar(ty) => ShownKind::Opaque,
            _ => ShownKind::Heap,
        },
    };
    let mut name = String::new();
    write_type(&mut name, ty);
    Shown {
        name: name.into(),
        kind,
        by_ref,
        variants: Arc::from(Vec::new()),
        elements: None,
    }
}

/// Writes a type as the source writes it, for a debugger's type names.
pub(crate) fn write_type(out: &mut String, ty: &Ty) {
    let list = |out: &mut String, ts: &[Ty]| {
        for (i, t) in ts.iter().enumerate() {
            if i > 0 {
                out.push_str(", ");
            }
            write_type(out, t);
        }
    };
    match ty {
        Ty::Con(item, args) => {
            out.push_str(&item.name);
            if !args.is_empty() {
                out.push('<');
                list(out, args);
                out.push('>');
            }
        }
        Ty::Tuple(ts) => {
            out.push('(');
            list(out, ts);
            out.push(')');
        }
        Ty::Fn(_) => out.push_str("fn"),
        Ty::Handler(_) => out.push_str("handler"),
        Ty::App(head, args) => {
            write_type(out, head);
            out.push('<');
            list(out, args);
            out.push('>');
        }
        Ty::SelfTy => out.push_str("Self"),
        Ty::Spread(s) => {
            out.push_str("..");
            write_type(out, &s.elem);
        }
        Ty::Value(v) => out.push_str(&v.to_string()),
        Ty::Param(_) | Ty::Var(_) | Ty::Error => out.push('_'),
    }
}
