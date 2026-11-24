//! Bodies of functions, tests, doc examples, properties and constants, each checked on its own.

use stilt_diag::{Diagnostic, codes};
use stilt_hir::decls::{FnSig, prelude_item};
use stilt_hir::hir::{self, BodyValue, ExprKind, Item};
use stilt_syntax::TextRange;

use super::types::Sig;
use super::{Cx, Env, State, node};
use crate::implements::{Answer, Traits};
use crate::params::{Args, TraitArgs};
use crate::tast::{self, Code, Definition, TestKind, Tested, TypedBody};
use crate::ty::{Handled, Kind, Row, Tail, Ty};

/// tasks.sequential-run: `main` and tests run under `task.sequential()` when no `with` installs
/// another handler, which handles their `async`.
fn sequential() -> Handled {
    Handled::Effect(Item::async_effect(), Vec::new())
}

/// What a body is the code of.
#[derive(Clone, Copy, Debug)]
pub(crate) enum BodyKind<'s> {
    /// A function's block, checked against its signature.
    Fn(&'s FnSig),
    /// A function's `= ?`. In the standard library it marks a native function;
    /// anywhere else it is a hole of the function's return type (declarations.typed-holes).
    Hole(&'s FnSig),
    Test,
    /// A doc example or a property.
    Example,
    /// A constant's value, of the constant's type. In the standard library, a hole marks a
    /// native constant.
    Const(&'s hir::Ty),
}

/// Checks a body, of a module of the standard library if `std`, and returns its elaboration
/// and its type errors. A function's body is checked where its signature's type parameters
/// have their bounds, after those of `env`.
pub(crate) fn check_body(
    mut env: Env<'_>,
    body: &hir::Body,
    kind: BodyKind<'_>,
    std: bool,
) -> (TypedBody, Vec<Diagnostic>) {
    let sig = match kind {
        BodyKind::Fn(s) | BodyKind::Hole(s) => Some(Sig::of(s, None)),
        BodyKind::Test | BodyKind::Example | BodyKind::Const(_) => None,
    };
    if let Some(s) = &sig {
        env.bounds.extend(
            s.type_params
                .iter()
                .map(|(v, traits)| (Ty::Param(v.clone()), traits.clone())),
        );
        env.bound_args.extend(
            s.bound_args
                .iter()
                .map(|(v, t, args)| (Ty::Param(v.clone()), t.clone(), args.clone())),
        );
    }
    let names = body.locals.iter().map(|l| l.name).collect();
    let mut st = State::new(env, names);
    st.unsafe_blocks = body.unsafe_blocks.iter().map(|u| u.whole).collect();
    let params = match &sig {
        Some(s) => body
            .params
            .iter()
            .zip(&s.params)
            .map(|(v, (mode, ty))| {
                st.locals.insert(*v, ty.clone());
                (*mode, *v)
            })
            .collect(),
        None => Vec::new(),
    };
    st.modifiable = (params.iter())
        .filter(|(mode, _)| *mode == hir::Mode::Inout)
        .map(|(_, v)| *v)
        .collect();
    let (code, tested) = st.code(body, kind, sig.as_ref(), std);
    st.fit_splices();
    st.offer_bindings(body);
    st.settle_unknown_names(&body.held);
    let passed = st
        .passed
        .iter()
        .map(|(at, row, l)| (*at, st.table.freeze_row(row), l.map(|t| st.table.freeze(t))))
        .collect();
    let typed = TypedBody {
        locals: st.local_names,
        params,
        passing: sig.as_ref().map(|s| passing(body, s)).unwrap_or_default(),
        pairs: sig.map(|s| s.pairs()).unwrap_or_default(),
        passed,
        tested,
        staged: std::mem::take(&mut st.staged),
        renamed: std::mem::take(&mut st.renamed),
        code,
    };
    (typed, st.errors)
}

/// A function's parameters that pass their arguments' effects through
/// (effects.non-escaping-parameters).
fn passing(body: &hir::Body, s: &Sig) -> Vec<hir::LocalId> {
    body.params
        .iter()
        .zip(&s.passing)
        .filter(|&(_, &passes)| passes)
        .map(|(v, _)| *v)
        .collect()
}

fn is_hole(body: &hir::Body) -> bool {
    matches!(&body.value, BodyValue::Expr(e) if e.kind == ExprKind::Hole)
}

/// declarations.constant-expressions: the first part of a constant's value, in evaluation order,
/// that a constant expression can't hold. A trait's constant, which `constant` tells, is read as a
/// constant is (traits.trait-constants), though a use of it calls the impl's member.
fn non_constant<'e>(
    e: &'e tast::Expr,
    constant: &dyn Fn(&tast::Callee) -> bool,
) -> Option<&'e tast::Expr> {
    use tast::ExprKind as E;
    let each = |es: &'e [tast::Expr]| es.iter().find_map(|e| non_constant(e, constant));
    match &e.kind {
        E::Int(_)
        | E::Float(_)
        | E::Str(_)
        | E::Bool(_)
        | E::Constant(_)
        | E::MemberConstant(..)
        | E::Error => None,
        E::Call(callee, _, args, _) if args.is_empty() && constant(callee) => None,
        E::Unary(hir::UnaryOp::Neg, operand) => non_constant(operand, constant),
        E::Tuple(es) | E::List(es) | E::Construct(_, _, es) => each(es),
        E::Record(_, _, fields) => fields.iter().find_map(|(_, e)| non_constant(e, constant)),
        _ => Some(e),
    }
}

impl State<'_> {
    /// The elaboration of a body of this kind, of a module of the standard library if `std`,
    /// and what it performs if it is a test's or a doc example.
    fn code(
        &mut self,
        body: &hir::Body,
        kind: BodyKind<'_>,
        sig: Option<&Sig>,
        std: bool,
    ) -> (Definition<Code>, Option<Tested>) {
        let code = match (kind, &body.value) {
            (BodyKind::Hole(_) | BodyKind::Const(_), _) if std && is_hole(body) => {
                Definition::Native
            }
            (BodyKind::Hole(_), BodyValue::Expr(e)) => {
                let ret = sig.map_or(Ty::Error, |s| s.ret.clone());
                let hole = node(tast::ExprKind::Hole, ret, e.at);
                Definition::Code(Code::Block(vec![tast::Stmt {
                    kind: tast::StmtKind::Expr(hole),
                    at: e.at,
                }]))
            }
            (BodyKind::Fn(_), BodyValue::Block(block)) => {
                let s = sig.expect("a function has a signature");
                self.function(body, s, block)
            }
            (BodyKind::Test, BodyValue::Block(block)) => {
                let (code, tested) = self.test(body, block);
                return (code, Some(tested));
            }
            (BodyKind::Example, BodyValue::Expr(claim)) => {
                let (code, tested) = self.example(body, claim);
                return (code, Some(tested));
            }
            (BodyKind::Example, BodyValue::Property(closure, _)) => {
                let (code, tested) = self.property(body, closure);
                return (code, Some(tested));
            }
            (BodyKind::Const(ty), BodyValue::Expr(value)) => self.constant(body, ty, value),
            _ => unreachable!("a body's kind matches its value"),
        };
        (code, None)
    }

    /// The elaboration of a body, or `Broken` if resolving or checking it found an error, so
    /// that the later phases skip it (errors.phases).
    pub(super) fn outcome(
        &self,
        body: &hir::Body,
        code: impl FnOnce(&crate::tast::retype::Retype<'_>) -> Code,
    ) -> Definition<Code> {
        if self.errors.is_empty() && !self.broken && !body.has_errors {
            Definition::Code(crate::tast::retype::freeze(&self.table, code))
        } else {
            Definition::Broken
        }
    }

    /// traits.where: a member type that a bound's argument fixes meets the bounds of the
    /// `where` clause, as a type parameter's argument does, or the bound is E0318. A bound
    /// that writes the trait's arguments is met by an impl that gives those
    /// (traits.bound-arguments).
    fn fixed_bounds(&mut self, fixed: &[(hir::Ty, Item, Vec<hir::Ty>, TextRange)]) {
        for (t, trait_item, args, at) in fixed {
            let ty = Ty::from_hir(t, None);
            let traits = Traits {
                decls: self.env.decls,
                scope: &self.env.bound_args,
                table: &self.table,
            };
            let met = traits.implements(&self.env.bounds, &ty, trait_item) != Answer::No
                && self.gives_args(&ty, trait_item, args);
            if !met {
                let message = format!(
                    "`{}` doesn't implement `{}`, which this `where` clause asks of it",
                    self.show(&ty),
                    trait_item.name
                );
                self.error(codes::E0318, *at, message);
            }
        }
    }

    /// Whether the impl of `trait_item` for `ty` gives it the arguments `args`, which a bound
    /// without arguments leaves open.
    fn gives_args(&self, ty: &Ty, trait_item: &Item, args: &[hir::Ty]) -> bool {
        let wanted: Vec<Ty> = args.iter().map(|a| Ty::from_hir(a, None)).collect();
        let given = Args {
            decls: self.env.decls,
            scope: &self.env.bound_args,
            table: &self.table,
        }
        .of(ty, trait_item);
        match given {
            TraitArgs::Known(actual) if !wanted.is_empty() && actual.len() == wanted.len() => {
                actual == wanted
            }
            TraitArgs::Known(_) | TraitArgs::Unknown | TraitArgs::Missing => true,
        }
    }

    fn function(&mut self, body: &hir::Body, s: &Sig, block: &[hir::Stmt]) -> Definition<Code> {
        // A projection's body has type `()`, and yields its result type (projections.yield).
        let ret = if s.projection {
            Ty::unit()
        } else {
            s.ret.clone()
        };
        let mut cx = Cx::new(ret.clone());
        cx.yields = s.projection.then(|| s.ret.clone());
        cx.known = self.table.row_contents(&s.row).effects;
        self.fixed_bounds(&body.fixed);
        let (mut b, _) = self.block_expr(&mut cx, body.at, Some(&ret), block);
        // handlers.no-effect-reaches-main, and tasks.sequential-run: no user-defined effect reaches
        // `main`, which runs under `task.sequential()`.
        if self.env.main {
            self.settle_handled(&cx.effects, &s.row, (true, true), &sequential());
        } else {
            self.settle(&cx.effects, &s.row, true);
        }
        self.finish();
        self.outcome(body, |f| {
            f.block(&mut b);
            Code::Block(b)
        })
    }

    /// Checks a test's body or a doc example, which may perform `io` and raise any error that can
    /// be shown (program.test-results and program.doc-examples), and tells what it performs: `io`
    /// when any of its effects, as inference leaves them, may be `io`.
    pub(super) fn test_body<T>(
        &mut self,
        (at, handled): (TextRange, &Handled),
        ret: Ty,
        check: impl FnOnce(&mut Self, &mut Cx) -> T,
    ) -> (T, Tested) {
        let error_ty = self.table.fresh(Kind::Any, at);
        self.obligation(&error_ty, prelude_item("Show"), at);
        let mut cx = Cx::new(ret);
        let result = check(self, &mut cx);
        let row = Row {
            io: true,
            raise: Some(Box::new(error_ty.clone())),
            effects: Vec::new(),
            tail: Tail::Closed,
        };
        // handlers.no-effect-reaches-main: no user-defined effect reaches a test or a doc example.
        self.settle_handled(&cx.effects, &row, (false, true), handled);
        // A body that raises nothing raises `Never`.
        if self.table.unsolved(&error_ty).is_some() {
            self.table.solve(&error_ty, Ty::never());
        }
        self.finish();
        let io = cx.effects.iter().any(|(r, _)| {
            let r = self.table.freeze_row(r);
            r.io || !matches!(r.tail, Tail::Closed)
        });
        let tested = Tested {
            kind: TestKind::Test,
            io,
            error: self.table.freeze(&error_ty),
        };
        (result, tested)
    }

    fn test(&mut self, body: &hir::Body, block: &[hir::Stmt]) -> (Definition<Code>, Tested) {
        let ((mut b, _), tested) =
            self.test_body((body.at, &sequential()), Ty::unit(), |st, cx| {
                st.block_expr(cx, body.at, Some(&Ty::unit()), block)
            });
        let code = self.outcome(body, |f| {
            f.block(&mut b);
            Code::Block(b)
        });
        (code, tested)
    }

    /// A doc example, whose claim the later phases read as a block of one statement.
    fn example(&mut self, body: &hir::Body, claim: &hir::Expr) -> (Definition<Code>, Tested) {
        let (mut c, tested) =
            self.test_body((claim.at, &Handled::Nothing), Ty::bool(), |st, cx| {
                st.check(cx, &Ty::bool(), claim)
            });
        let code = self.outcome(body, |f| {
            f.expr(&mut c);
            let at = c.at;
            Code::Block(vec![tast::Stmt {
                kind: tast::StmtKind::Expr(c),
                at,
            }])
        });
        let tested = Tested {
            kind: TestKind::Example,
            ..tested
        };
        (code, tested)
    }

    fn constant(&mut self, body: &hir::Body, ty: &hir::Ty, value: &hir::Expr) -> Definition<Code> {
        let ty = Ty::from_hir(ty, None);
        let mut cx = Cx::new(ty.clone());
        let mut v = self.check(&mut cx, &ty, value);
        self.finish();
        if let Some(part) = non_constant(&v, &|c| self.is_trait_constant(c)) {
            let message = "a constant's value is built only from literals, constants, tuples, \
                           lists, records and variants";
            self.error(codes::E0326, part.at, message.to_owned());
        }
        self.outcome(body, |f| {
            f.expr(&mut v);
            Code::Expr(Box::new(v))
        })
    }
}
