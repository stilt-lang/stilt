//! The types that type checking works with.
//!
//! A type may hold unification variables, which inference creates inside one body and solves
//! before the body is done (errors.phases; principle 2 of the design sketch). Everything else
//! is fixed by signatures. The variables live in a [`Table`], one per body.

mod diff;
mod effects;
mod meta;
mod named;
mod passing;
mod poly;
mod print;
mod spread;
mod subst;
mod table;

use stilt_hir::decls::prelude_item;
use stilt_hir::hir::{self, GenericId, Item, Mode, Owner};

pub use effects::{Handled, HandlerTy};
pub use meta::{META, SHAPE_CASES, case_payload, is_meta, is_shape_case, meta_item, meta_ty};
pub use named::{is_array, is_prelude, is_shared, is_view_type};
pub use passing::{Passing, own_row};
use poly::{poly_bound_args, poly_bounds};
pub use spread::{Spread, replace};
pub use subst::Subst;
pub use table::{Kind, RowState, Table, VarInfo};

/// A unification variable, by its place in its body's [`Table`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct VarId(pub(crate) u32);

/// An open row, by its place in its body's [`Table`]: the least row that holds every effect
/// added to it, until it is closed by being made one with a row of a signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RowVarId(pub(crate) u32);

/// A type, as inference solves it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    /// A named type with its arguments, the built-in types included.
    Con(Item, Vec<Ty>),
    /// A type parameter, which is rigid where it is declared.
    Param(GenericId),
    /// `Self` in a trait: the type that implements it, rigid in the trait's default methods.
    SelfTy,
    /// A constructor applied to its arguments: a constructor parameter, a constructor trait's
    /// `Self`, or a variable that stands for a constructor (traits.constructor-traits and
    /// traits.constructor-parameters). The head is a [`Ty::Param`], [`Ty::SelfTy`] or [`Ty::Var`];
    /// a variable solved with a constructor written without its arguments, as `Option`, makes it
    /// that constructor applied.
    App(Box<Ty>, Vec<Ty>),
    /// A tuple type, `()` the empty one.
    Tuple(Vec<Ty>),
    /// A function type.
    Fn(Box<FnTy>),
    /// A spread of a pack, an element of a tuple type or a parameter of a function type
    /// (variadics.type-spreads).
    Spread(Box<Spread>),
    /// A handler's type (handlers.handler-types).
    Handler(Box<HandlerTy>),
    /// A value argument, by its value, equal only to the same value (generics.constant-arguments).
    /// A value parameter is a [`Ty::Param`], and a value that inference finds a [`Ty::Var`].
    Value(hir::Value),
    /// A type variable of inference.
    Var(VarId),
    /// The error type of errors.error-type.
    Error,
}

/// A function type. A polymorphic one declares type parameters, each with the traits that
/// bound it, sorted, which its parameters and result name as rigid types, and the arguments
/// its bounds give traits with parameters (polymorphism.function-types; traits.bound-arguments).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FnTy {
    /// Its type parameters, each with its bounds.
    pub generics: Vec<(GenericId, Vec<Item>)>,
    /// The arguments its bounds give traits with parameters: the parameter, the trait and them.
    pub bound_args: Vec<(GenericId, Item, Vec<Ty>)>,
    /// Each parameter's mode and type.
    pub params: Vec<(Mode, Ty)>,
    /// Its result type.
    pub ret: Ty,
    /// Its row.
    pub row: Row,
}

/// An effect row (effects.rows).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Row {
    /// Whether it holds `io`.
    pub io: bool,
    /// The type of the error it raises.
    pub raise: Option<Box<Ty>>,
    /// Its effects, each once with its type arguments, `async` among them
    /// (handlers.effects-in-rows; tasks.async).
    pub effects: Vec<(Item, Vec<Ty>)>,
    /// What follows its elements.
    pub tail: Tail,
}

/// What follows the elements of a row.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Tail {
    /// Nothing: the row holds only its elements.
    Closed,
    /// Row variables of a signature, at least one, in order and each once. A written row holds
    /// at most one, but a function's own row, and the rows a body forms, may hold several
    /// implicit ones (effects.row-variables).
    Params(Vec<RowParam>),
    /// A row being inferred, such as that of a closure.
    Var(RowVarId),
}

/// A row variable of a signature (effects.row-variables and effects.non-escaping-parameters).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RowParam {
    /// One that its generics declare.
    Written(GenericId),
    /// The implicit one of the non-escaping parameter at `index` of `owner`'s parameters, its
    /// receiver's included, which no program writes.
    Passed {
        /// The declaration whose parameter it is.
        owner: Owner,
        /// The parameter's place, the receiver's included.
        index: u32,
    },
}

impl RowParam {
    /// Whether it is the implicit row variable of a non-escaping parameter.
    #[must_use]
    pub fn is_passed(&self) -> bool {
        matches!(self, Self::Passed { .. })
    }
}

impl Tail {
    /// The tail that holds the row variables `params`, closed if there are none.
    #[must_use]
    pub fn of_params(mut params: Vec<RowParam>) -> Self {
        params.sort();
        params.dedup();
        if params.is_empty() {
            Self::Closed
        } else {
            Self::Params(params)
        }
    }

    /// The row variables that the tail holds, none for an open row.
    #[must_use]
    pub fn params(&self) -> &[RowParam] {
        match self {
            Self::Params(ps) => ps,
            Self::Closed | Self::Var(_) => &[],
        }
    }
}

impl Row {
    /// The row of no effect.
    pub const EMPTY: Self = Self {
        io: false,
        raise: None,
        effects: Vec::new(),
        tail: Tail::Closed,
    };

    /// The row that raises `t` and holds nothing else.
    #[must_use]
    pub fn raising(t: Ty) -> Self {
        Self {
            raise: Some(Box::new(t)),
            ..Self::EMPTY
        }
    }

    /// Whether a frozen row holds nothing at all: no label, no effect and no row variable, as
    /// the row of a call that a staging annotation reads must be (meta.static-expressions).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        !self.io && self.raise.is_none() && self.effects.is_empty() && self.tail == Tail::Closed
    }

    /// Whether a frozen row holds a `raise` label.
    #[must_use]
    pub fn raises(&self) -> bool {
        self.raise.is_some()
    }

    /// The row with the row variable `p` added. It is a signature's, so it holds no open row.
    #[must_use]
    pub fn with_param(self, p: RowParam) -> Self {
        let mut params = self.tail.params().to_vec();
        params.push(p);
        Self {
            tail: Tail::of_params(params),
            ..self
        }
    }

    /// The row with the labels of `extra` added. Where both raise, the raise of `self` is kept:
    /// the checker makes the two one before rows meet.
    #[must_use]
    pub(crate) fn merge_labels(mut self, extra: &Self) -> Self {
        self.io |= extra.io;
        if self.raise.is_none() {
            self.raise.clone_from(&extra.raise);
        }
        for (e, args) in &extra.effects {
            if self.effect(e).is_none() {
                self.effects.push((e.clone(), args.clone()));
            }
        }
        self
    }
}

/// The integer types' names.
pub const INTEGER_TYPES: [&str; 8] = ["i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64"];
/// The float types' names.
pub const FLOAT_TYPES: [&str; 2] = ["f32", "f64"];

impl Ty {
    /// The prelude's type `name`, without arguments.
    #[must_use]
    pub fn named(name: &str) -> Self {
        Self::Con(prelude_item(name), Vec::new())
    }

    /// `Never`.
    #[must_use]
    pub fn never() -> Self {
        Self::named("Never")
    }

    /// `()`.
    #[must_use]
    pub fn unit() -> Self {
        Self::Tuple(Vec::new())
    }

    /// `bool`.
    #[must_use]
    pub fn bool() -> Self {
        Self::named("bool")
    }

    /// `str`.
    #[must_use]
    pub fn str() -> Self {
        Self::named("str")
    }

    /// `i64`.
    #[must_use]
    pub fn i64() -> Self {
        Self::named("i64")
    }

    /// `f64`.
    #[must_use]
    pub fn f64() -> Self {
        Self::named("f64")
    }

    /// `List<t>`.
    #[must_use]
    pub fn list(t: Self) -> Self {
        Self::Con(prelude_item("List"), vec![t])
    }

    /// `Option<t>`.
    #[must_use]
    pub fn option(t: Self) -> Self {
        Self::Con(prelude_item("Option"), vec![t])
    }

    /// A monomorphic function type.
    #[must_use]
    pub fn func(params: Vec<(Mode, Self)>, ret: Self, row: Row) -> Self {
        Self::Fn(Box::new(FnTy {
            generics: Vec::new(),
            bound_args: Vec::new(),
            params,
            ret,
            row,
        }))
    }

    /// Whether the type is the prelude's type constructor `name`, with any arguments.
    #[must_use]
    pub fn is_prelude(&self, name: &str) -> bool {
        matches!(self, Self::Con(item, _) if is_prelude(item, name))
    }

    /// The name of a numeric type, such as `u8`, if the type is one.
    #[must_use]
    pub fn numeric_name(&self) -> Option<&str> {
        match self {
            Self::Con(item, args) if args.is_empty() && is_numeric(item) => Some(&item.name),
            _ => None,
        }
    }

    /// The name of an integer type, if the type is one.
    #[must_use]
    pub fn integer_name(&self) -> Option<&str> {
        self.numeric_name()
            .filter(|name| INTEGER_TYPES.contains(name))
    }

    /// The type that a type of a signature stands for. `self_ty` is what `Self` means, where it
    /// is known.
    #[must_use]
    pub fn from_hir(t: &hir::Ty, self_ty: Option<&Self>) -> Self {
        match t {
            hir::Ty::Con(item, args) => Self::Con(
                item.clone(),
                args.iter().map(|a| Self::from_hir(a, self_ty)).collect(),
            ),
            hir::Ty::Param(p) => Self::Param(p.clone()),
            hir::Ty::SelfTy => self_ty.cloned().unwrap_or(Self::SelfTy),
            hir::Ty::App(head, args) => apply(
                Self::from_hir(head, self_ty),
                args.iter().map(|a| Self::from_hir(a, self_ty)).collect(),
            ),
            hir::Ty::Tuple(ts) => {
                Self::Tuple(ts.iter().map(|t| Self::from_hir(t, self_ty)).collect())
            }
            hir::Ty::Fn(f) => Self::Fn(Box::new(FnTy {
                generics: f
                    .generics
                    .iter()
                    .map(|(g, bounds)| (g.clone(), poly_bounds(bounds)))
                    .collect(),
                bound_args: poly_bound_args(f, self_ty),
                params: f
                    .params
                    .iter()
                    .map(|(m, t)| (*m, Self::from_hir(t, self_ty)))
                    .collect(),
                ret: f
                    .ret
                    .as_ref()
                    .map_or_else(Self::unit, |t| Self::from_hir(t, self_ty)),
                row: Row::from_hir(&f.row, self_ty),
            })),
            hir::Ty::Spread(pack, elem) => Self::spread(
                Self::Param(pack.clone()),
                pack.clone(),
                Self::from_hir(elem, self_ty),
            ),
            hir::Ty::Handler(h) => Self::Handler(Box::new(HandlerTy {
                effect: h.effect.effect.clone(),
                args: h
                    .effect
                    .args
                    .iter()
                    .map(|a| Self::from_hir(a, self_ty))
                    .collect(),
                answer: h.answer.as_ref().map(|t| Self::from_hir(t, self_ty)),
                row: Row::from_hir(&h.row, self_ty),
            })),
            hir::Ty::Value(v) => Self::Value(*v),
            hir::Ty::Error => Self::Error,
        }
    }
}

/// A constructor applied to `args` (traits.constructor-traits and traits.constructor-parameters): a
/// type constructor written without its arguments takes them, a constructor parameter, `Self` or a
/// variable stays applied, and anything else is no constructor, the error type.
#[must_use]
pub fn apply(head: Ty, args: Vec<Ty>) -> Ty {
    match head {
        Ty::Con(item, none) if none.is_empty() => Ty::Con(item, args),
        head @ (Ty::Param(_) | Ty::SelfTy | Ty::Var(_)) => Ty::App(Box::new(head), args),
        _ => Ty::Error,
    }
}

/// The type `t` of a declaration, with the declaration's type parameters `params` replaced by
/// `args`, or the error type when their numbers differ.
#[must_use]
pub fn instantiate(t: &hir::Ty, params: &[GenericId], args: &[Ty]) -> Ty {
    if params.len() != args.len() {
        return Ty::Error;
    }
    let s = Subst {
        types: params.iter().cloned().zip(args.iter().cloned()).collect(),
        ..Subst::default()
    };
    Table::default().subst(&s, &Ty::from_hir(t, None))
}

impl Row {
    /// A row that a signature writes, `Self` meaning `self_ty` when it is given.
    #[must_use]
    pub fn from_hir(r: &hir::Row, self_ty: Option<&Ty>) -> Self {
        Self {
            io: r.io,
            raise: r.raise.as_ref().map(|t| Box::new(Ty::from_hir(t, self_ty))),
            effects: r
                .effects
                .iter()
                .map(|e| {
                    let args = e.args.iter().map(|a| Ty::from_hir(a, self_ty)).collect();
                    (e.effect.clone(), args)
                })
                .collect(),
            tail: r
                .var
                .clone()
                .map_or(Tail::Closed, |v| Tail::Params(vec![RowParam::Written(v)])),
        }
    }
}

/// Whether a type constructor is a numeric type of the prelude.
#[must_use]
pub fn is_numeric(item: &Item) -> bool {
    &*item.home == "std.prelude"
        && (INTEGER_TYPES.contains(&&*item.name) || FLOAT_TYPES.contains(&&*item.name))
}

/// Whether a type constructor is a float type of the prelude.
#[must_use]
pub fn is_float(item: &Item) -> bool {
    &*item.home == "std.prelude" && FLOAT_TYPES.contains(&&*item.name)
}
