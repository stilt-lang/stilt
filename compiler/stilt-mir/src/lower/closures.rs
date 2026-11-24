//! Closures and function values (expressions.closures and expressions.capture;
//! traits.qualified-calls).
//!
//! A closure is a data object: its code, then the witnesses and dictionaries of the type
//! parameters in scope, then the words of a copy of each variable it uses, made when it is
//! created. Its code takes the closure, and reads those back, as borrowed locals. It takes each
//! argument and gives its result in the words of its layout, as generic code compiled for the
//! layouts of its type arguments holds them, and raises its error in one word, or for an error
//! of several words, to memory that its caller provides, since a row variable may stand for the
//! error where the closure is called (`super::raises`; `stilt_runtime::abi`).

use std::collections::BTreeSet;

use stilt_hir::hir::{Item, ListRest, LocalId, Mode};
use stilt_types::tast::{self, Callee, Expr, ExprKind, Pat, PatKind, StmtKind};
use stilt_types::ty::Ty;

use super::bridge::Past;
use super::calls::{Target, error_type};
use super::{Conv, Lower, Var};
use crate::FnRef;
use crate::mir::{Arg, Const, Heapness, Local, Operand, ParamMode, Repr};

/// The variables a pattern binds.
pub(crate) fn bound(p: &Pat, out: &mut BTreeSet<LocalId>) {
    match &p.kind {
        PatKind::Bind(id) => {
            out.insert(*id);
        }
        PatKind::Tuple(ps) | PatKind::Variant(_, ps) | PatKind::Or(ps) => {
            for q in ps {
                bound(q, out);
            }
        }
        PatKind::Record(fields) => {
            for (_, q) in fields {
                bound(q, out);
            }
        }
        PatKind::List(ps, rest) => {
            for q in ps {
                bound(q, out);
            }
            if let ListRest::Bind(id) = rest {
                out.insert(*id);
            }
        }
        PatKind::Wild
        | PatKind::Int(_)
        | PatKind::Str(_)
        | PatKind::Bool(_)
        | PatKind::Const(_)
        | PatKind::Error => {}
    }
}

/// The type of a captured variable, as the closure's body uses it.
fn var_type(id: LocalId, body: &Expr) -> Ty {
    let mut found = None;
    tast::walk::iter(body, &mut |_| {}, &mut |e| {
        if let ExprKind::Local(l) = &e.kind
            && *l == id
            && found.is_none()
        {
            found = Some(e.ty.clone());
        }
    });
    found.unwrap_or(Ty::Error)
}

/// The variables a closure uses that are bound outside it, in order.
fn captured(params: &[Pat], body: &Expr) -> Vec<LocalId> {
    let mut inside = BTreeSet::new();
    for p in params {
        bound(p, &mut inside);
    }
    let mut used = BTreeSet::new();
    let mut in_stmts = BTreeSet::new();
    let mut stmt = |s: &tast::Stmt| {
        if let StmtKind::Let(b) | StmtKind::Var(b) = &s.kind {
            bound(&b.pattern, &mut in_stmts);
        }
    };
    tast::walk::iter(body, &mut stmt, &mut |e| match &e.kind {
        ExprKind::Local(id) => {
            used.insert(*id);
        }
        ExprKind::Closure(ps, _) => ps.iter().for_each(|p| bound(p, &mut inside)),
        ExprKind::For(p, _, _) | ExprKind::IfLet(p, ..) => bound(p, &mut inside),
        ExprKind::Match(_, arms) => arms.iter().for_each(|a| bound(&a.pattern, &mut inside)),
        ExprKind::Try(_, Some(c)) => c.arms.iter().for_each(|a| bound(&a.pattern, &mut inside)),
        ExprKind::When(held, _) => inside.extend(held.iter().map(|(_, place)| *place)),
        _ => {}
    });
    inside.extend(in_stmts);
    used.difference(&inside).copied().collect()
}

/// What a closure's code is made from.
struct ClosureCode<'e> {
    name: FnRef,
    params: &'e [Pat],
    fty: &'e stilt_types::ty::FnTy,
    body: &'e Expr,
    captured: Vec<(LocalId, Ty)>,
    /// The words of its environment, which an array held in memory takes all of.
    len: usize,
    /// Whether the code takes its arguments in one box of all their words and gives its result
    /// in one word, as a handler's operation does (`super::handlers`).
    packed: bool,
}

impl<'a> Lower<'a> {
    pub(crate) fn closure(&mut self, params: &[Pat], body: &Expr, e: &Expr) -> Operand {
        self.closure_of(params, body, e, false)
    }

    /// A closure, whose code takes its arguments in one box when `packed`.
    pub(crate) fn closure_of(
        &mut self,
        params: &[Pat],
        body: &Expr,
        e: &Expr,
        packed: bool,
    ) -> Operand {
        let Ty::Fn(fty) = &e.ty else {
            return Operand::word(0);
        };
        let index = self.next_closure;
        self.next_closure += 1;
        let name = FnRef::Closure(Box::new(self.b.name().clone()), index);
        let captured: Vec<(LocalId, Ty)> = captured(params, body)
            .into_iter()
            .filter(|id| self.vars.contains_key(id))
            .map(|id| (id, var_type(id, body)))
            .collect();
        let mut env: Vec<(Operand, Heapness)> = vec![(
            Operand::Const(Const::Code(name.clone())),
            Heapness::Static(false),
        )];
        for (_, g) in self.generics.clone() {
            env.push((Operand::Local(g.witness), Heapness::Static(false)));
            env.extend(
                g.dicts
                    .iter()
                    .map(|(_, d)| (d.clone(), Heapness::Static(true))),
            );
            // Its descriptor, where it has one.
            env.extend(g.desc.map(|d| (d, Heapness::Static(true))));
        }
        for (id, ty) in &captured {
            let words = self.read_var(*id, ty);
            for (w, repr) in words.into_iter().zip(self.layout(ty)) {
                env.push((w, Heapness::of(repr)));
            }
        }
        let code = ClosureCode {
            name,
            params,
            fty,
            body,
            captured,
            len: env.iter().map(|(_, h)| h.words()).sum(),
            packed,
        };
        let functions = self.closure_function(&code);
        self.closures.extend(functions);
        self.alloc(0, env)
    }

    /// Reads a closure's environment into borrowed locals: after its code, the witnesses and
    /// dictionaries of the enclosing function's generics, then the words of the captured
    /// values.
    fn read_env(&self, l: &mut Lower<'a>, env: Local, code: &ClosureCode<'_>) {
        let len = u32::try_from(code.len).expect("under 4G captures");
        let mut field = 1u32;
        let mut read = |l: &mut Lower<'a>, repr: Repr| {
            let local = l.borrowed_field(env, len, field, repr);
            field += u32::try_from(repr.words()).expect("under 4G words");
            local
        };
        for (ty, g) in &self.generics {
            let witness = read(l, Repr::Scalar);
            let dicts = g
                .dicts
                .iter()
                .map(|(t, _)| (t.clone(), Operand::Local(read(l, Repr::Heap))))
                .collect();
            l.push_generic(ty.clone(), witness, dicts, Some(&super::keys::held_of(g)));
            if g.desc.is_some() {
                let desc = Operand::Local(read(l, Repr::Heap));
                l.set_descriptor(ty, desc);
            }
        }
        for (id, ty) in &code.captured {
            let locals = l.layout(ty).into_iter().map(|repr| read(l, repr)).collect();
            l.vars.insert(
                *id,
                Var::Value {
                    locals,
                    mutable: false,
                },
            );
        }
    }

    fn closure_function(&mut self, code: &ClosureCode<'_>) -> Vec<crate::mir::Function> {
        let mut l = Lower::new(self.cx, code.name.clone(), self.std);
        l.scope = self.scope.inner();
        l.origin.clone_from(&self.origin);
        l.bound_args.clone_from(&self.bound_args);
        l.names.clone_from(&self.names);
        l.cons.params.clone_from(&self.cons.params);
        l.cons.self_ty.clone_from(&self.cons.self_ty);
        l.elements.clone_from(&self.elements);
        l.ret = if code.packed {
            Conv::boxed(code.fty.ret.clone())
        } else {
            Conv::of(code.fty.ret.clone())
        };
        l.err = Conv::boxed(error_type(&code.fty.row));
        l.raises_to_slot = true;
        let env = l.b.param(Repr::Heap, ParamMode::Borrowed, None);
        self.read_env(&mut l, env, code);
        if code.packed {
            let args = l.b.param(Repr::Heap, ParamMode::Borrowed, None);
            l.unpack(args, code.params);
        } else {
            l.params(code);
        }
        let value = l.expr(code.body);
        l.return_(value);
        l.finish()
    }

    /// Binds the parameters of a closure's code, which takes each argument in the words of its
    /// layout, or a pointer to the place of an `inout` one.
    fn params(&mut self, code: &ClosureCode<'_>) {
        let l = self;
        // A closure of a polymorphic function type takes its type parameters' witnesses and
        // dictionaries before its arguments.
        l.poly_params(code.fty);
        let modes = code
            .fty
            .params
            .iter()
            .map(|(m, _)| *m)
            .chain(std::iter::repeat(Mode::Let));
        let args: Vec<(Vec<Local>, &Pat, Mode)> = code
            .params
            .iter()
            .zip(modes)
            .map(|(p, mode)| {
                let locals = match mode {
                    Mode::Let => l
                        .layout(&p.ty)
                        .into_iter()
                        .map(|r| l.b.param(r, ParamMode::Borrowed, None))
                        .collect(),
                    Mode::Inout => {
                        let repr = l.ref_repr(&p.ty);
                        vec![l.b.param(repr, ParamMode::Ref, None)]
                    }
                };
                (locals, p, mode)
            })
            .collect();
        for (locals, p, _) in &args {
            l.field_descriptor(code.fty, &p.ty, locals);
        }
        for (locals, p, mode) in args {
            if let (PatKind::Bind(id), Mode::Inout) = (&p.kind, mode) {
                l.vars.insert(*id, Var::Ref(locals[0]));
            } else {
                let words = locals.into_iter().map(Operand::Local).collect();
                l.binding(p, words, false, None);
            }
        }
    }

    /// Binds the parameters of a handler's operation to the words of the box `args`, which
    /// holds those of each argument in turn, borrowed.
    fn unpack(&mut self, args: Local, params: &[Pat]) {
        let layouts: Vec<Vec<Repr>> = params.iter().map(|p| self.layout(&p.ty)).collect();
        let all = layouts.iter().flatten().map(|r| r.words()).sum::<usize>();
        let len = u32::try_from(all).expect("under 4G");
        let mut field = 0u32;
        for (p, layout) in params.iter().zip(layouts) {
            let words = layout
                .into_iter()
                .map(|repr| {
                    let word = self.borrowed_field(args, len, field, repr);
                    field += u32::try_from(repr.words()).expect("under 4G words");
                    Operand::Local(word)
                })
                .collect();
            self.binding(p, words, false, None);
        }
    }

    /// A function named as a value: a closure whose code calls it with the type arguments the
    /// closure holds (traits.qualified-calls). The code of a dictionary's method also holds the
    /// witness of the type it is called on. A function called past the caps is named as such a
    /// value for its type arguments as past the caps, which a closure that converts holds.
    pub(crate) fn function_value(&mut self, callee: &Callee, targs: &[Ty], e: &Expr) -> Operand {
        match self.resolve(callee, targs) {
            Target::Crossing(c) if !matches!(c.callee, Past::Method(..)) => {
                self.crossing_value(&c, callee, &e.ty)
            }
            target => self.target_value(target, callee, targs),
        }
    }

    /// The closure of the code a target calls, named as a value with the type arguments
    /// `targs`.
    pub(crate) fn target_value(
        &mut self,
        target: Target,
        callee: &Callee,
        targs: &[Ty],
    ) -> Operand {
        let (code, hidden) = match target {
            Target::Direct(f, hidden) => {
                let value = FnRef::Value(Box::new(f.generic().clone()));
                (FnRef::instance(value, f.held().to_vec()), hidden)
            }
            // The code of a method past the caps calls it as calls past the caps do.
            Target::Crossing(c) => {
                let Past::Method(dict, index) = c.callee.clone() else {
                    unreachable!("a function past the caps is converted as a value")
                };
                let hidden = {
                    let packs = self.pack_kinds(&c.sig, &c.targs, None);
                    self.generic_args(&c.sig.type_params, &packs, &c.targs)
                };
                self.method_value(callee, targs, (dict, index), hidden)
            }
            Target::Method(dict, index, hidden, _) => {
                self.method_value(callee, targs, (dict, index), hidden)
            }
        };
        let mut env = vec![(Operand::Const(Const::Code(code)), Heapness::Static(false))];
        // A witness is a scalar, and a dictionary a heap word, or static data.
        env.extend(hidden.iter().flat_map(Arg::operands).map(|v| {
            let heap = match v {
                Operand::Local(l) => self.b.repr_of(*l) == Repr::Heap,
                Operand::Const(c) => !matches!(c, Const::Word(_)),
            };
            (v.clone(), Heapness::Static(heap))
        }));
        self.alloc(0, env)
    }

    /// The code of method `index` of a type parameter's dictionary `dict` named as a value, and
    /// what its closure holds: the dictionary, the witness of the type, and the hidden arguments
    /// of the method's own type parameters.
    fn method_value(
        &mut self,
        callee: &Callee,
        targs: &[Ty],
        (dict, index): (Operand, u32),
        hidden: Vec<Arg>,
    ) -> (FnRef, Vec<Arg>) {
        let Callee::TraitMethod(t, _, ty) = callee else {
            unreachable!("a dictionary's method is a trait's")
        };
        let mut all = vec![Arg::Borrow(dict), Arg::Borrow(self.witness(ty))];
        all.extend(hidden);
        let own: Vec<Ty> = std::iter::once(ty.clone()).chain(targs.to_vec()).collect();
        (self.instance(FnRef::Method(t.clone(), index), &own), all)
    }

    /// A variant with a payload named as a value: a closure that builds it, holding the
    /// witnesses of its type's arguments.
    pub(crate) fn constructor_value(&mut self, item: &Item, targs: &[Ty]) -> Operand {
        let code = self.instance(FnRef::Constructor(item.clone()), targs);
        let mut env = vec![(Operand::Const(Const::Code(code)), Heapness::Static(false))];
        for t in targs {
            env.push((self.witness(t), Heapness::Static(false)));
        }
        self.alloc(0, env)
    }
}
