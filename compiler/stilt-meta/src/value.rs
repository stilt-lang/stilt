//! The values of a macro's run: those of the language, each self-describing enough that the
//! structural impls and the traits' dispatch read it without its type (traits.structural-impls and
//! traits.prelude-traits), and those of `std.meta` that only a run makes (macros.tokens-and-code).
//!
//! A value is shared and copied when written, so that a variable holds its own value however it was
//! made (values.independent-copies). Every value a run makes on the heap is weighed as it is made
//! and dropped, so that the run stops when they would hold more than [`weight::MEMORY`]
//! bytes (macros.step-limits).

use std::sync::{Arc, LazyLock, Mutex};

use stilt_hir::hir::{Item, Name};
use stilt_types::tast;

mod code;
mod kinds;
mod weight;

pub(crate) use code::{
    Code, ErrorValue, Lex, Meta, NameValue, Span, Text, TextOrigin, Token, TokenKind,
};
pub(crate) use kinds::{Deferred, HandlerValue, IterValue, Step, Window};
pub(crate) use weight::{Counted, Held, fits, meter, use_meter};

/// The width and sign of an integer type, as the runtime numbers them: 0 to 3 for `i8` to
/// `i64`, and 4 to 7 for `u8` to `u64`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct IntKind(pub(crate) u8);

impl IntKind {
    pub(crate) const I64: Self = Self(3);
    pub(crate) const U8: Self = Self(4);
    pub(crate) const U32: Self = Self(6);
    pub(crate) const U64: Self = Self(7);

    /// The kind of the integer type `name`.
    pub(crate) fn named(name: &str) -> Option<Self> {
        let i = ["i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64"]
            .iter()
            .position(|n| *n == name)?;
        u8::try_from(i).ok().map(Self)
    }

    pub(crate) fn signed(self) -> bool {
        self.0 < 4
    }

    pub(crate) fn bits(self) -> u32 {
        8 << (self.0 % 4)
    }

    pub(crate) fn min(self) -> i128 {
        if self.signed() {
            -(1i128 << (self.bits() - 1))
        } else {
            0
        }
    }

    pub(crate) fn max(self) -> i128 {
        if self.signed() {
            (1i128 << (self.bits() - 1)) - 1
        } else {
            (1i128 << self.bits()) - 1
        }
    }

    pub(crate) fn holds(self, x: i128) -> bool {
        x >= self.min() && x <= self.max()
    }

    /// `x` cut to the low bits of the type, read with its sign.
    pub(crate) fn wrap(self, x: i128) -> i128 {
        let bits = self.bits();
        let m = x & ((1i128 << bits) - 1);
        if self.signed() && m >= 1i128 << (bits - 1) {
            m - (1i128 << bits)
        } else {
            m
        }
    }
}

/// A record's fields, in its type's order, weighed while they live.
pub(crate) type Fields<'a> = Counted<Vec<(Name, Value<'a>)>>;

/// A value of a run.
#[derive(Clone, Debug)]
pub(crate) enum Value<'a> {
    Bool(bool),
    Int(i128, IntKind),
    /// A float, and whether it is an `f32`, whose value it holds rounded to `f32`.
    Float(f64, bool),
    Str(Arc<Counted<String>>),
    Tuple(Arc<Counted<Vec<Value<'a>>>>),
    List(Arc<Counted<Vec<Value<'a>>>>),
    /// A map's entries in the order their keys were first inserted, and its default.
    Map(Arc<MapValue<'a>>),
    /// A record of a declared type, or an anonymous one, with its fields in its type's order.
    Record(Arc<(Item, Fields<'a>)>),
    Variant(Arc<(Item, Counted<Vec<Value<'a>>>)>),
    Closure(Arc<Closure<'a>>),
    Func(Arc<Func>),
    Meta(Arc<Meta>),
    Handler(Arc<HandlerValue<'a>>),
    /// A shared value (shared.std-sync), which every copy of the handle reaches.
    Shared(Arc<Mutex<Value<'a>>>),
    Iter(Arc<IterValue<'a>>),
    Deferred(Arc<Deferred<'a>>),
    Window(Arc<Window<'a>>),
}

/// A map's entries and its default.
#[derive(Clone, Debug)]
pub(crate) struct MapValue<'a> {
    pub(crate) entries: Counted<Vec<(Value<'a>, Value<'a>)>>,
    pub(crate) default: Option<Value<'a>>,
}

/// A closure: its parameters, its body, and the values of the locals it captured, of the body
/// that holds it, which it runs with the types of `tenv`.
#[derive(Debug)]
pub(crate) struct Closure<'a> {
    pub(crate) params: &'a [tast::Pat],
    pub(crate) body: &'a tast::Expr,
    pub(crate) locals: Counted<Vec<Option<Value<'a>>>>,
    pub(crate) frame: Arc<crate::eval::FrameInfo<'a>>,
    /// The type parameters of its polymorphic function type, which instantiating it binds
    /// (polymorphism.instantiation).
    pub(crate) poly: Vec<stilt_hir::hir::GenericId>,
}

/// A function used as a value, with its type arguments, or a variant's constructor.
#[derive(Debug)]
pub(crate) enum Func {
    Callee(tast::Callee, Vec<stilt_types::ty::Ty>),
    Constructor(Item),
}

impl<'a> Value<'a> {
    pub(crate) fn unit() -> Self {
        Value::Tuple(Arc::new(Counted::empty(Vec::new())))
    }

    pub(crate) fn tuple(xs: Vec<Value<'a>>) -> Self {
        Value::Tuple(Arc::new(Counted::new(xs)))
    }

    pub(crate) fn record(item: Item, fields: Vec<(Name, Value<'a>)>) -> Self {
        Value::Record(Arc::new((item, Counted::new(fields))))
    }

    pub(crate) fn str(s: impl Into<String>) -> Self {
        Value::Str(Arc::new(Counted::new(s.into())))
    }

    pub(crate) fn list(xs: Vec<Value<'a>>) -> Self {
        Value::List(Arc::new(Counted::new(xs)))
    }

    pub(crate) fn i64(x: i128) -> Self {
        Value::Int(x, IntKind::I64)
    }

    pub(crate) fn variant(item: Item, payload: Vec<Value<'a>>) -> Self {
        Value::Variant(Arc::new((item, Counted::new(payload))))
    }

    pub(crate) fn meta(m: Meta) -> Self {
        Value::Meta(Arc::new(m))
    }

    /// `Some(v)` or `None`.
    pub(crate) fn option(v: Option<Value<'a>>) -> Self {
        static SOME: LazyLock<Item> = LazyLock::new(|| prelude("Some"));
        static NONE: LazyLock<Item> = LazyLock::new(|| prelude("None"));
        match v {
            Some(v) => Self::variant(SOME.clone(), vec![v]),
            None => Self::variant(NONE.clone(), Vec::new()),
        }
    }

    pub(crate) fn as_str(&self) -> &str {
        match self {
            Value::Str(s) => s.get(),
            _ => "",
        }
    }

    pub(crate) fn as_int(&self) -> i128 {
        match self {
            Value::Int(x, _) => *x,
            _ => 0,
        }
    }

    pub(crate) fn as_bool(&self) -> bool {
        matches!(self, Value::Bool(true))
    }

    pub(crate) fn as_list(&self) -> &[Value<'a>] {
        match self {
            Value::List(xs) => xs.get(),
            _ => &[],
        }
    }

    pub(crate) fn as_meta(&self) -> Option<&Meta> {
        match self {
            Value::Meta(m) => Some(m),
            _ => None,
        }
    }

    /// The field `name` of a record.
    pub(crate) fn field(&self, name: &str) -> Option<&Value<'a>> {
        match self {
            Value::Record(r) => r.1.iter().find(|(n, _)| &**n == name).map(|(_, v)| v),
            _ => None,
        }
    }

    /// The field `name` of a record, found by the name rather than its text.
    pub(crate) fn field_named(&self, name: Name) -> Option<&Value<'a>> {
        match self {
            Value::Record(r) => r.1.iter().find(|(n, _)| *n == name).map(|(_, v)| v),
            _ => None,
        }
    }
}

/// The name of the prelude's module, interned once.
pub(crate) static PRELUDE: LazyLock<Name> = LazyLock::new(|| Name::from("std.prelude"));

/// The name of `std.meta`, interned once.
static META: LazyLock<Name> = LazyLock::new(|| Name::from("std.meta"));

/// The item `name` of the prelude.
pub(crate) fn prelude(name: &str) -> Item {
    Item {
        home: *PRELUDE,
        name: Name::from(name),
    }
}

/// The item `name` of `std.meta`.
pub(crate) fn meta_item(name: &str) -> Item {
    Item {
        home: *META,
        name: Name::from(name),
    }
}
