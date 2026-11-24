//! The evaluation of typed bodies, as the reference interpreter evaluates them, with
//! the counts of macros.step-limits: a step for each call of a function, a method, a closure or a
//! native, and for each turn of a loop; a frame for each call of a body or a closure.

mod args;
mod calls;
mod control;
mod handlers;
mod ops;
mod patterns;
mod places;
mod project;
pub(crate) mod reflect;
mod spread;
mod when;
pub(crate) mod windows;

use std::collections::HashMap;
use std::sync::{Arc, LazyLock};

use stilt_hir::hir::{GenericId, Item, Name};
use stilt_types::tast::{Expr, ExprKind, Segment};
use stilt_types::ty::Ty;

pub(crate) use crate::frame::{Frame, FrameInfo, Locals};
use crate::limits::Run;
use crate::value::{Func, IntKind, PRELUDE, Value};

pub(crate) use ops::float as ops_float;
pub(crate) use when::shared;

/// Why evaluation leaves an expression early.
#[derive(Clone, Debug)]
pub(crate) enum Flow<'a> {
    Break,
    Continue,
    Return(Value<'a>),
    Raise(Value<'a>),
    Stop(Stop),
    /// The rest of a `with`'s block that a handler dropped, or of a projection whose caller's
    /// access raised, which unwinds without any `catch` seeing it (handlers.resuming;
    /// projections.raising-during-access).
    Abandon,
}

/// Why a run stops before it finishes (macros.step-limits).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Stop {
    Steps,
    Frames,
    Memory,
    Panic(String, String),
    /// A call that would reach C, through the function this names (c.calls).
    C(String),
}

impl Stop {
    /// The reason E0226 names.
    pub(crate) fn reason(&self) -> String {
        match self {
            Stop::Steps => "it took more than 10,000,000 steps".to_owned(),
            Stop::Frames => "it called deeper than 10,000 frames".to_owned(),
            Stop::Memory => "it ran out of memory".to_owned(),
            Stop::Panic(kind, detail) => format!("it panicked: {kind}: {detail}"),
            Stop::C(name) => format!("it reached C through `{name}`"),
        }
    }
}

pub(crate) type R<'a> = Result<Value<'a>, Flow<'a>>;

/// A panic of kind `kind`, which stops the run.
pub(crate) fn panic<'a, T>(kind: &str, detail: impl Into<String>) -> Result<T, Flow<'a>> {
    Err(Flow::Stop(Stop::Panic(kind.to_owned(), detail.into())))
}

/// The machine that runs a macro: the program of its module, its counts, what it read, and
/// the handlers, the `when`s and the projection that the running code is in.
pub(crate) struct Machine<'a> {
    pub(crate) image: &'a crate::image::Image<'a>,
    pub(crate) run: Run,
    pub(crate) io: crate::run::Io<'a>,
    pub(crate) constants: HashMap<(Item, Option<Name>), Value<'a>>,
    pub(crate) fx: crate::fiber::Effects<'a>,
    /// The locals of the body that a call just ran, with the slots of its `inout` parameters
    /// and their arguments' indexes, when what it returned holds a window into them.
    pub(crate) escaped: Option<(Locals<'a>, Vec<(usize, usize)>)>,
    /// The locals of frames that ended, for the next frames.
    pub(crate) pool: crate::frame::Pool<'a>,
}

impl<'a> Machine<'a> {
    /// Evaluates an expression.
    pub(crate) fn expr(&mut self, fr: &mut Frame<'a>, e: &'a Expr) -> R<'a> {
        match &e.kind {
            ExprKind::Int(text) => Ok(int_literal(text, &e.ty)),
            ExprKind::Float(text) => Ok(float_literal(text, &e.ty)),
            ExprKind::Str(s) => Ok(Value::str(s.as_str())),
            ExprKind::Bool(b) => Ok(Value::Bool(*b)),
            ExprKind::Interpolated(segments) => self.interpolated(fr, segments),
            ExprKind::Local(id) => Ok(fr.get(*id).unwrap_or_else(Value::unit)),
            ExprKind::Callee(c, targs) => {
                let targs = substituted_all(fr, targs);
                let c = match c {
                    stilt_types::tast::Callee::TraitMethod(t, name, ty) => {
                        let ty = match (ty, &fr.info.self_ty) {
                            (Ty::SelfTy, Some(s)) => s.clone(),
                            _ => substituted(&fr.info.tenv, ty),
                        };
                        stilt_types::tast::Callee::TraitMethod(t.clone(), *name, ty)
                    }
                    c => c.clone(),
                };
                Ok(Value::Func(Arc::new(Func::Callee(c, targs))))
            }
            ExprKind::Constructor(item, _) => {
                Ok(Value::Func(Arc::new(Func::Constructor(item.clone()))))
            }
            ExprKind::Construct(item, _, args) => {
                let values = self.elements(fr, args)?;
                Ok(Value::variant(item.clone(), values))
            }
            ExprKind::Record(item, _, fields) => self.record(fr, item, fields),
            ExprKind::Update(base, fields) => self.update(fr, base, fields),
            ExprKind::Tuple(es) => Ok(Value::tuple(self.elements(fr, es)?)),
            ExprKind::List(es) => {
                let values = self.elements(fr, es)?;
                reserve(values.len() * std::mem::size_of::<Value<'_>>())?;
                Ok(Value::list(values))
            }
            ExprKind::Field(base, name) => {
                let v = self.expr(fr, base)?;
                Ok(v.field_named(*name).cloned().unwrap_or_else(Value::unit))
            }
            ExprKind::TupleField(base, i) => match self.expr(fr, base)? {
                Value::Tuple(t) => Ok(t.get().get(*i).cloned().unwrap_or_else(Value::unit)),
                _ => Ok(Value::unit()),
            },
            ExprKind::Call(callee, targs, args, _) => self.call(fr, callee, targs, args),
            ExprKind::CallValue(f, args) => self.call_value(fr, f, args),
            ExprKind::Instantiate(f, targs) => {
                let v = self.expr(fr, f)?;
                Ok(instantiate(v, substituted_all(fr, targs)))
            }
            ExprKind::Index(base, i) => self.index(fr, base, i),
            ExprKind::Unary(op, x) => {
                let v = self.expr(fr, x)?;
                ops::unary(*op, v)
            }
            ExprKind::Binary(op, a, b) => self.binary(fr, *op, a, b),
            _ => self.control(fr, e),
        }
    }

    /// A string's interpolation: each splice shown in turn, and formatted by its spec, the text
    /// weighed as it grows (macros.step-limits).
    fn interpolated(&mut self, fr: &mut Frame<'a>, segments: &'a [Segment]) -> R<'a> {
        let mut out = String::new();
        for s in segments {
            let piece = match s {
                Segment::Text(t) => t.clone(),
                Segment::Splice(e, spec) => {
                    let v = self.expr(fr, e)?;
                    if let Value::Str(x) = &v {
                        reserve(out.len() + x.get().len())?;
                    }
                    let shown = self.show("show", v.clone())?;
                    crate::structural::formatted(&v, shown, spec.as_deref())
                }
            };
            reserve(out.len() + piece.len())?;
            out.push_str(&piece);
        }
        Ok(Value::str(out))
    }

    /// A record literal, its fields in its type's order.
    fn record(&mut self, fr: &mut Frame<'a>, item: &'a Item, fields: &'a [(Name, Expr)]) -> R<'a> {
        let mut values = Vec::with_capacity(fields.len());
        for (name, e) in fields {
            values.push((*name, self.expr(fr, e)?));
        }
        let order = self.field_order(item);
        if !order.is_empty() {
            values.sort_by_key(|(n, _)| order.iter().position(|o| o == n).unwrap_or(usize::MAX));
        }
        Ok(Value::record(item.clone(), values))
    }

    /// The names of a record type's fields, in its order.
    pub(crate) fn field_order(&self, item: &Item) -> Vec<Name> {
        if item.is_record() {
            return item.record_fields();
        }
        self.image.record(item).cloned().unwrap_or_default()
    }

    /// `{ ..base, f: e }`: the base with the fields given.
    fn update(&mut self, fr: &mut Frame<'a>, base: &'a Expr, fields: &'a [(Name, Expr)]) -> R<'a> {
        let mut v = self.expr(fr, base)?;
        for (name, e) in fields {
            let x = self.expr(fr, e)?;
            if let Value::Record(r) = &mut v {
                let r = Arc::make_mut(r);
                match r.1.iter().position(|(n, _)| n == name) {
                    Some(i) => r.1.slots()[i].1 = x,
                    None => r.1.update(|fields| fields.push((*name, x))),
                }
            }
        }
        Ok(v)
    }

    /// `a op b`: `&&` and `||` evaluate `b` only when they need it.
    fn binary(
        &mut self,
        fr: &mut Frame<'a>,
        op: stilt_hir::hir::BinaryOp,
        a: &'a Expr,
        b: &'a Expr,
    ) -> R<'a> {
        use stilt_hir::hir::BinaryOp as B;
        let x = self.expr(fr, a)?;
        match op {
            B::And if !x.as_bool() => return Ok(x),
            B::Or if x.as_bool() => return Ok(x),
            B::And | B::Or => return self.expr(fr, b),
            _ => {}
        }
        let y = self.expr(fr, b)?;
        match op {
            B::Eq => Ok(Value::Bool(self.equal(&x, &y)?)),
            B::Ne => Ok(Value::Bool(!self.equal(&x, &y)?)),
            B::Lt | B::Le | B::Gt | B::Ge => self.compared(op, &x, &y),
            _ => ops::arithmetic(op, &x, &y),
        }
    }

    /// `a < b` and the others: IEEE on floats, and `Ord.compare` on every other type.
    fn compared(&mut self, op: stilt_hir::hir::BinaryOp, x: &Value<'a>, y: &Value<'a>) -> R<'a> {
        use stilt_hir::hir::BinaryOp as B;
        if let (Value::Float(a, _), Value::Float(b, _)) = (x, y) {
            return Ok(Value::Bool(match op {
                B::Lt => a < b,
                B::Le => a <= b,
                B::Gt => a > b,
                _ => a >= b,
            }));
        }
        let c = self.order(x, y)?;
        Ok(Value::Bool(match op {
            B::Lt => c.is_lt(),
            B::Le => c.is_le(),
            B::Gt => c.is_gt(),
            _ => c.is_ge(),
        }))
    }
}

/// `t` with the type arguments of `tenv` for its type parameters.
pub(crate) fn substituted(tenv: &[(GenericId, Ty)], t: &Ty) -> Ty {
    match t {
        Ty::Param(g) => tenv
            .iter()
            .find(|(p, _)| p == g)
            .map_or_else(|| t.clone(), |(_, x)| x.clone()),
        Ty::Con(item, args) => Ty::Con(
            item.clone(),
            args.iter().map(|a| substituted(tenv, a)).collect(),
        ),
        Ty::Tuple(args) => Ty::Tuple(args.iter().map(|a| substituted(tenv, a)).collect()),
        _ => t.clone(),
    }
}

/// The kind of an integer type, `i64` when the type isn't one.
pub(crate) fn int_kind(ty: &Ty) -> IntKind {
    match ty {
        Ty::Con(item, args) if args.is_empty() && item.home == *PRELUDE => {
            IntKind::named(&item.name).unwrap_or(IntKind::I64)
        }
        _ => IntKind::I64,
    }
}

/// Whether a type is `f32`.
pub(crate) fn is_f32(ty: &Ty) -> bool {
    static F32: LazyLock<Name> = LazyLock::new(|| Name::from("f32"));
    matches!(ty, Ty::Con(item, args) if args.is_empty() && item.home == *PRELUDE && item.name == *F32)
}

fn int_literal<'a>(text: &str, ty: &Ty) -> Value<'a> {
    // A literal of decimal digits alone, as most are, is read as it is written.
    let plain = text.bytes().all(|b| b.is_ascii_digit());
    let digits: String = if plain {
        String::new()
    } else {
        text.chars().filter(|c| *c != '_').collect()
    };
    let x = if plain {
        text.parse()
    } else if let Some(hex) = digits.strip_prefix("0x") {
        i128::from_str_radix(hex, 16)
    } else if let Some(oct) = digits.strip_prefix("0o") {
        i128::from_str_radix(oct, 8)
    } else if let Some(bin) = digits.strip_prefix("0b") {
        i128::from_str_radix(bin, 2)
    } else {
        digits.parse()
    };
    let x = x.unwrap_or(0);
    if matches!(ty, Ty::Con(item, _) if matches!(&*item.name, "f32" | "f64")) {
        #[allow(clippy::cast_precision_loss)]
        return Value::Float(x as f64, is_f32(ty));
    }
    Value::Int(x, int_kind(ty))
}

fn float_literal<'a>(text: &str, ty: &Ty) -> Value<'a> {
    let digits: String = text.chars().filter(|c| *c != '_').collect();
    let f32 = is_f32(ty);
    let x = if f32 {
        digits.parse::<f32>().map_or(0.0, f64::from)
    } else {
        digits.parse::<f64>().unwrap_or(0.0)
    };
    Value::Float(x, f32)
}

/// A value of a polymorphic function type at type arguments, one for each of its type parameters
/// (polymorphism.instantiation): a closure that binds them in its body, or a function that takes
/// them after those it has.
pub(crate) fn instantiate(v: Value<'_>, targs: Vec<Ty>) -> Value<'_> {
    match v {
        Value::Closure(c) if !c.poly.is_empty() => {
            let mut info = (*c.frame).clone();
            let mut tenv: Vec<(GenericId, Ty)> = c.poly.iter().cloned().zip(targs).collect();
            tenv.append(&mut info.tenv);
            info.tenv = tenv;
            Value::Closure(Arc::new(crate::value::Closure {
                params: c.params,
                body: c.body,
                locals: c.locals.clone(),
                frame: Arc::new(info),
                poly: Vec::new(),
            }))
        }
        Value::Func(f) => match &*f {
            Func::Callee(c, given) => {
                let mut all = given.clone();
                all.extend(targs);
                Value::Func(Arc::new(Func::Callee(c.clone(), all)))
            }
            Func::Constructor(_) => Value::Func(f),
        },
        v => v,
    }
}

/// Stops the run unless `bytes` more fit in its memory (macros.step-limits).
pub(crate) fn reserve<'a>(bytes: usize) -> Result<(), Flow<'a>> {
    if crate::value::fits(bytes) {
        Ok(())
    } else {
        Err(Flow::Stop(Stop::Memory))
    }
}

/// The types `ts`, with the frame's type arguments for its type parameters.
pub(crate) fn substituted_all(fr: &Frame<'_>, ts: &[Ty]) -> Vec<Ty> {
    ts.iter().map(|t| substituted(&fr.info.tenv, t)).collect()
}
