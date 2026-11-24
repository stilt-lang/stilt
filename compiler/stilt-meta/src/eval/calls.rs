//! Calls (expressions.heads; traits.method-resolution): what a call runs, a body, a closure, a
//! native, a structural impl or a variant's constructor, and the run of it, which leaves the final
//! values of its `inout` parameters in its arguments (values.inout-arguments). A trait's method
//! runs the impl's for the type of its receiver, the trait's default, or the structural one
//! (traits.structural-impls).

use std::sync::{Arc, LazyLock};

use stilt_hir::hir::{GenericId, Item, Name};
use stilt_mir::FnRef;
use stilt_syntax::ast::Mode;
use stilt_types::tast::{self, Arg, Callee, Code, Definition, Expr, TypedBody};
use stilt_types::ty::Ty;

use super::{Flow, Frame, FrameInfo, Machine, R, panic, substituted, substituted_all};
use crate::image::FnCode;
use crate::value::{Closure, Func, Value, meta_item, prelude};

/// The types a body's type parameters stand for.
type Bound = Vec<(GenericId, Ty)>;

/// What a call runs.
#[derive(Debug)]
pub(crate) enum Target<'a> {
    Body {
        info: Arc<FrameInfo<'a>>,
        params: &'a [(Mode, stilt_hir::hir::LocalId)],
        code: &'a Code,
        name: Name,
    },
    /// A native of the standard library, by what runs it, if it performs nothing, its owner,
    /// if it is a member, and its name, with its type arguments, its impl's first.
    Native(Option<crate::natives::Run>, Option<Item>, Item, Vec<Ty>),
    /// The structural impl of a prelude trait's method (traits.structural-impls).
    Structural(Name),
    Variant(Item),
    Closure(Arc<Closure<'a>>),
}

impl<'a> Machine<'a> {
    /// A call of `callee` with type arguments `targs` on `args`.
    pub(super) fn call(
        &mut self,
        fr: &mut Frame<'a>,
        callee: &'a Callee,
        targs: &'a [Ty],
        args: &'a [Arg],
    ) -> R<'a> {
        let targs = substituted_all(fr, targs);
        if let Callee::Operation(effect, name) = callee {
            let values = self.values_of(fr, args)?;
            return self.perform(effect, *name, values);
        }
        if let Some(window) = crate::eval::windows::window_native(callee) {
            return self.window_call(fr, window, args);
        }
        let mut args = self.arguments(fr, args)?;
        let target = self.target(fr, callee, &targs, &args.values)?;
        let mut target = Some(target);
        self.escaped = None;
        let result = self.opened(&mut args, &mut |m, values| {
            let target = target.take().expect("a call runs its target once");
            m.apply(target, values)
        });
        let result = self.kept_windows(result, &args);
        self.written_back(args)?;
        result
    }

    /// What a call gives, its windows into the callee's `inout` parameters writing the places
    /// of its arguments instead (projections.what-view-writes).
    fn kept_windows(&mut self, result: R<'a>, args: &super::args::Args<'a>) -> R<'a> {
        let Some((callee, params)) = self.escaped.take() else {
            return result;
        };
        let places: Vec<_> = params
            .iter()
            .filter_map(|(slot, i)| {
                let found = args.places().iter().find(|(_, j)| j == i);
                found.map(|(place, _)| (*slot, place.clone()))
            })
            .collect();
        result.map(|v| Self::retargeted(v, &callee, &places))
    }

    /// A call of a value: a closure, a function, or a variant's constructor.
    pub(super) fn call_value(&mut self, fr: &mut Frame<'a>, f: &'a Expr, args: &'a [Arg]) -> R<'a> {
        let callee = self.expr(fr, f)?;
        if let Value::Func(func) = &callee
            && let Func::Callee(c, _) = &**func
            && let Some(window) = crate::eval::windows::window_native(c)
        {
            return self.window_call(fr, window, args);
        }
        let mut args = self.arguments(fr, args)?;
        self.escaped = None;
        let result = self.opened(&mut args, &mut |m, values| m.apply_value(&callee, values));
        let result = self.kept_windows(result, &args);
        self.written_back(args)?;
        result
    }

    /// Calls a function value on `values`.
    pub(crate) fn apply_value(&mut self, f: &Value<'a>, values: &mut Vec<Value<'a>>) -> R<'a> {
        let target = match f {
            Value::Closure(c) => Target::Closure(Arc::clone(c)),
            Value::Func(func) => match &**func {
                Func::Constructor(item) => Target::Variant(item.clone()),
                Func::Callee(c, targs) => self.target_in((&[], None), c, targs, values)?,
            },
            _ => unreachable!("a call calls a function, as its checking found"),
        };
        self.apply(target, values)
    }

    /// What a call of `callee` runs.
    pub(crate) fn target(
        &mut self,
        fr: &Frame<'a>,
        callee: &Callee,
        targs: &[Ty],
        values: &[Value<'a>],
    ) -> Result<Target<'a>, Flow<'a>> {
        let info = Arc::clone(&fr.info);
        self.target_in((&info.tenv, info.self_ty.as_ref()), callee, targs, values)
    }

    /// What a call of `callee` runs, where type parameters have the types of `tenv` and `Self`
    /// is `self_ty`.
    pub(crate) fn target_in(
        &mut self,
        (tenv, self_ty): (&[(GenericId, Ty)], Option<&Ty>),
        callee: &Callee,
        targs: &[Ty],
        values: &[Value<'a>],
    ) -> Result<Target<'a>, Flow<'a>> {
        match callee {
            Callee::Function(item) => {
                self.code(&FnRef::Function(item.clone()), (None, targs), None)
            }
            Callee::Member(owner, name) => {
                self.code(&FnRef::Member(owner.clone(), *name), (None, targs), None)
            }
            Callee::TraitMethod(trait_item, name, ty) => {
                let ty = match (ty, self_ty) {
                    (Ty::SelfTy, Some(t)) => t.clone(),
                    _ => substituted(tenv, ty),
                };
                let ty = match ty {
                    Ty::Con(..) | Ty::Tuple(_) => ty,
                    _ => values.first().map_or(ty, |v| self.type_of(v)),
                };
                self.trait_target(trait_item, *name, ty, targs)
            }
            Callee::Operation(..) => {
                unreachable!("a performance is no call of a target (handlers.performing-operation)")
            }
        }
    }

    /// The method `name` of `trait_item` for the type `ty`.
    fn trait_target(
        &mut self,
        trait_item: &Item,
        name: Name,
        ty: Ty,
        targs: &[Ty],
    ) -> Result<Target<'a>, Flow<'a>> {
        let Ty::Con(owner, args) = &ty else {
            return Ok(Target::Structural(name));
        };
        let image = self.image;
        let Some(imp) = image.impl_of(trait_item, owner) else {
            return Ok(Target::Structural(name));
        };
        let mut tenv: Vec<(GenericId, Ty)> = Vec::new();
        matching(
            &imp.self_ty,
            &Ty::Con(owner.clone(), args.clone()),
            &mut tenv,
        );
        if let Some((_, params)) = imp.members.iter().find(|(n, _)| *n == name) {
            tenv.extend(bind(Some(params), targs));
            let key = FnRef::ImplMethod(trait_item.clone(), owner.clone(), name);
            let all: Vec<Ty> = tenv.iter().map(|(_, t)| t.clone()).collect();
            return self.code(&key, (Some(tenv), &all), Some(ty));
        }
        let key = FnRef::DefaultMethod(trait_item.clone(), name);
        if image.holds(&key) {
            return self.code(&key, (Some(tenv), targs), Some(ty));
        }
        Ok(Target::Structural(name))
    }

    /// The code of `f`: its body, with the types of `tenv`, or without one, `targs` for its
    /// own type parameters, and `Self` as `self_ty`; or its native, which takes the type
    /// arguments `targs`, its impl's first.
    fn code(
        &mut self,
        f: &FnRef,
        (tenv, targs): (Option<Bound>, &[Ty]),
        self_ty: Option<Ty>,
    ) -> Result<Target<'a>, Flow<'a>> {
        let native = |run| match f {
            FnRef::Function(item) => Ok(Target::Native(run, None, item.clone(), targs.to_vec())),
            FnRef::Member(owner, name) | FnRef::ImplMethod(_, owner, name) => Ok(Target::Native(
                run,
                Some(owner.clone()),
                Item {
                    home: owner.home,
                    name: *name,
                },
                targs.to_vec(),
            )),
            _ => unreachable!("only functions and members are native: {f}"),
        };
        let Some((found, params)) = self.image.function(f) else {
            unreachable!("the image holds every function a run reaches: {f}")
        };
        match found {
            FnCode::Body {
                body,
                module,
                name,
                info,
            } => {
                let body: &'a TypedBody = body;
                let Definition::Code(code) = &body.code else {
                    unreachable!("the image holds a native as one: {f}")
                };
                let tenv = tenv.unwrap_or_else(|| bind(params, targs));
                // A body without type arguments shares what its frames share.
                let info = if tenv.is_empty() && self_ty.is_none() {
                    Arc::clone(info)
                } else {
                    Arc::new(FrameInfo {
                        body,
                        module: *module,
                        tenv,
                        self_ty,
                    })
                };
                Ok(Target::Body {
                    info,
                    params: &body.params,
                    code,
                    name: *name,
                })
            }
            FnCode::Broken => panic(
                "check-error",
                "this code has an error, which `check` reports",
            ),
            FnCode::Native(run) => native(*run),
        }
    }

    /// Runs a target on `values`, leaving the final values of its `inout` parameters there.
    pub(crate) fn apply(&mut self, target: Target<'a>, values: &mut Vec<Value<'a>>) -> R<'a> {
        match target {
            Target::Body {
                info,
                params,
                code,
                name,
            } => {
                self.run.step()?;
                let module = info.module;
                self.run.enter(Some(module), name)?;
                let mut frame = self.pool.frame(info);
                for ((_, local), v) in params.iter().zip(values.iter()) {
                    frame.set(*local, v.clone());
                }
                let result = match code {
                    Code::Block(block) => self.block(&mut frame, block),
                    Code::Expr(e) => self.expr(&mut frame, e),
                };
                for (i, (mode, local)) in params.iter().enumerate() {
                    if *mode == Mode::Inout
                        && let Some(v) = frame.get(*local)
                    {
                        values[i] = v;
                    }
                }
                let result = self.returned(Some(module), result);
                if let Ok(v) = &result
                    && super::windows::holds_window_into(v, &frame.locals)
                {
                    let inouts = params.iter().enumerate();
                    let inouts = inouts.filter(|(_, (mode, _))| *mode == Mode::Inout);
                    let slots = inouts
                        .map(|(i, (_, local))| (frame.slot(*local), i))
                        .collect();
                    self.escaped = Some((Arc::clone(&frame.locals), slots));
                }
                self.pool.recycle(frame);
                result
            }
            Target::Closure(c) => self.closure_call(&c, values),
            Target::Native(run, owner, item, targs) => {
                self.run.step()?;
                crate::natives::call(self, run, (owner.as_ref(), &item, &targs), values)
            }
            Target::Structural(name) => {
                // A writable view has the structural impls of the part it views
                // (projections.writable-views and projections.places-through-views).
                for v in values.iter_mut() {
                    *v = self.thaw(std::mem::replace(v, Value::unit()))?;
                }
                self.structural(&name, values)
            }
            Target::Variant(item) => Ok(Value::variant(item, std::mem::take(values))),
        }
    }

    /// The end of a body's run: its result, a `return`'s value among them.
    fn returned(&mut self, module: Option<Name>, result: R<'a>) -> R<'a> {
        let stopping = matches!(result, Err(Flow::Stop(_)));
        self.run.leave(module, stopping);
        match result {
            Err(Flow::Return(v)) => Ok(v),
            Err(Flow::Break | Flow::Continue) => Ok(Value::unit()),
            other => other,
        }
    }

    fn closure_call(&mut self, c: &Arc<Closure<'a>>, values: &mut [Value<'a>]) -> R<'a> {
        self.run.step()?;
        self.run.enter(None, *UNNAMED)?;
        let mut frame = self.pool.frame_with(Arc::clone(&c.frame), &c.locals);
        for (p, v) in c.params.iter().zip(values.iter()) {
            if !self.bind_pattern(&mut frame, p, v.clone())? {
                let result = panic("unreachable", "a closure's parameter didn't match");
                return self.returned(None, result);
            }
        }
        let result = self.expr(&mut frame, c.body);
        for (p, v) in c.params.iter().zip(values.iter_mut()) {
            if let tast::PatKind::Bind(id) = p.kind
                && let Some(x) = frame.get(id)
            {
                *v = x;
            }
        }
        self.pool.recycle(frame);
        self.returned(None, result)
    }

    /// The type of a value, as its traits' impls are found for it.
    pub(crate) fn type_of(&self, v: &Value<'a>) -> Ty {
        let named = |n: &str| Ty::Con(prelude(n), Vec::new());
        match v {
            Value::Bool(_) => named("bool"),
            Value::Int(_, k) => {
                named(["i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64"][usize::from(k.0 % 8)])
            }
            Value::Float(_, f32) => named(if *f32 { "f32" } else { "f64" }),
            Value::Str(_) => named("str"),
            Value::Tuple(xs) => Ty::Tuple(xs.iter().map(|x| self.type_of(x)).collect()),
            Value::List(_) => Ty::Con(prelude("List"), Vec::new()),
            Value::Map(_) => Ty::Con(prelude("Map"), Vec::new()),
            Value::Record(r) => Ty::Con(r.0.clone(), Vec::new()),
            Value::Variant(v) => match self.image.variant(&v.0) {
                Some((ty, _)) => Ty::Con(ty.clone(), Vec::new()),
                None => Ty::Error,
            },
            Value::Meta(m) => Ty::Con(meta_item(crate::meta::type_name(m)), Vec::new()),
            Value::Shared(_) => Ty::Con(item("std.sync", "Shared"), Vec::new()),
            Value::Iter(_) => Ty::Con(item("std.view", "Iter"), Vec::new()),
            Value::Window(_) => Ty::Con(item("std.view", "View"), Vec::new()),
            Value::Deferred(_) => Ty::Con(item("std.lazy", "Lazy"), Vec::new()),
            Value::Closure(_) | Value::Func(_) | Value::Handler(_) => Ty::Error,
        }
    }
}

/// The name of a closure's frame, which is never shown: only the module's own functions' are.
static UNNAMED: LazyLock<Name> = LazyLock::new(Name::default);

/// The item `name` of the module `home`.
fn item(home: &str, name: &str) -> Item {
    Item {
        home: Name::from(home),
        name: Name::from(name),
    }
}

/// The type arguments of a signature's type parameters: `targs` gives the last of them, its
/// own after those of its impl block.
fn bind(params: Option<&[GenericId]>, targs: &[Ty]) -> Vec<(GenericId, Ty)> {
    let Some(params) = params else {
        return Vec::new();
    };
    let skip = params.len().saturating_sub(targs.len());
    params
        .iter()
        .skip(skip)
        .cloned()
        .zip(targs.iter().cloned())
        .collect()
}

/// Binds the type parameters of `pattern`, an impl's type, to the parts of `ty` it matches.
pub(crate) fn matching(pattern: &Ty, ty: &Ty, bound: &mut Vec<(GenericId, Ty)>) {
    match (pattern, ty) {
        (Ty::Param(g), t) => bound.push((g.clone(), t.clone())),
        (Ty::Con(_, ps), Ty::Con(_, ts)) | (Ty::Tuple(ps), Ty::Tuple(ts)) => {
            for (p, t) in ps.iter().zip(ts) {
                matching(p, t, bound);
            }
        }
        _ => {}
    }
}

/// A closure of type `ty`, capturing the locals of its frame.
pub(super) fn closure<'a>(
    fr: &Frame<'a>,
    params: &'a [tast::Pat],
    body: &'a Expr,
    ty: &Ty,
) -> Value<'a> {
    let poly = match ty {
        Ty::Fn(f) => f.generics.iter().map(|(g, _)| g.clone()).collect(),
        _ => Vec::new(),
    };
    Value::Closure(Arc::new(Closure {
        params,
        body,
        locals: crate::value::Counted::new(fr.snapshot()),
        frame: Arc::clone(&fr.info),
        poly,
    }))
}
