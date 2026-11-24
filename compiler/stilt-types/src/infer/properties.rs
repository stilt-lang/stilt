//! Properties, the `/// prop:` lines of doc comments (tests.property-form and
//! tests.property-checking): a closure with typed parameters, whose types can be generated, and
//! whose body is a `bool` that performs no `io` and may raise an error that can be shown. The
//! reference interpreter's `Check_properties` checks them alike.

use stilt_diag::{Edit, Fix, codes};
use stilt_hir::decls::prelude_item;
use stilt_hir::hir::{self, ClosureParam, ExprKind, Mode, PatKind, StmtKind};
use stilt_syntax::TextRange;

use super::effects::Reported;
use super::{Cx, State, node};
use crate::generable::{self, Unfit};
use crate::tast::{self, Code, Definition, TestKind, Tested};
use crate::ty::{Kind, Row, Tail, Ty};
use crate::unify::Problem;

impl State<'_> {
    /// A property, whose closure the later phases read as a block of one statement.
    pub(super) fn property(
        &mut self,
        body: &hir::Body,
        e: &hir::Expr,
    ) -> (Definition<Code>, Tested) {
        let tested = Tested {
            kind: TestKind::Property,
            io: false,
            error: Ty::never(),
        };
        let ExprKind::Closure(params, closure_body) = &e.kind else {
            let message = "a property is a closure whose parameters' values are generated, such \
                           as `|x: i64| …`";
            self.error(codes::E0332, e.at, message.to_owned());
            return (Definition::Broken, tested);
        };
        if params.is_empty() {
            let message = "this property has no parameter, so it checks one case, as an example \
                           does";
            self.error(codes::E0332, e.at, message.to_owned());
            return (Definition::Broken, tested);
        }
        if params
            .iter()
            .any(|p| p.annotation.is_none() || p.mode == Mode::Inout)
        {
            self.malformed(e.at, params, closure_body);
            return (Definition::Broken, tested);
        }
        let mut c = self.property_closure(e.at, params, closure_body);
        let code = self.outcome(body, |f| {
            f.expr(&mut c);
            let at = c.at;
            Code::Block(vec![tast::Stmt {
                kind: tast::StmtKind::Expr(c),
                at,
            }])
        });
        (code, tested)
    }

    /// tests.property-form: E0332 at each parameter without a type, with a fix that writes the type
    /// that checking the closure without one gives it, when that type is known, and at each
    /// parameter marked `inout`, which is no pattern (expressions.closure-parameter-types and
    /// expressions.inout-closure-parameters).
    fn malformed(&mut self, at: TextRange, params: &[ClosureParam], body: &hir::Expr) {
        let errors = self.errors.len();
        let mut cx = Cx::new(Ty::bool());
        let closure = self.closure(&mut cx, None, at, params, body);
        let found: Vec<Option<String>> = match &closure.kind {
            tast::ExprKind::Closure(patterns, _) => {
                patterns.iter().map(|p| self.written(&p.ty)).collect()
            }
            _ => Vec::new(),
        };
        // What the closure's check reported goes, with what points at it.
        self.errors.truncate(errors);
        self.unknown_names.retain(|&(_, i)| i < errors);
        self.mismatches.retain(|&(i, _)| i < errors);
        for (i, p) in params.iter().enumerate() {
            if p.mode == Mode::Inout {
                let message = "this parameter is `inout`, but a property's parameters take \
                               generated values";
                let mark = TextRange::new(p.at.start(), p.pattern.at.start());
                let fix = Fix::new("delete the `inout`", vec![Edit::delete(mark)]);
                self.error_fixed(codes::E0332, p.pattern.at, message.to_owned(), vec![fix]);
                continue;
            }
            if p.annotation.is_some() {
                continue;
            }
            let (message, title) = match &p.pattern.kind {
                PatKind::Bind(v) => {
                    let name = &self.local_names[v.0 as usize];
                    (
                        format!(
                            "the parameter `{name}` has no type, so no values can be generated for it"
                        ),
                        format!("write the type of `{name}`"),
                    )
                }
                _ => (
                    "this parameter has no type, so no values can be generated for it".to_owned(),
                    "write the parameter's type".to_owned(),
                ),
            };
            let fixes = found.get(i).cloned().flatten().map(|ty| {
                let edit = Edit::insert(p.pattern.at.end(), format!(": {ty}"));
                Fix::new(title, vec![edit])
            });
            self.error_fixed(
                codes::E0332,
                p.pattern.at,
                message,
                fixes.into_iter().collect(),
            );
        }
    }

    fn property_closure(
        &mut self,
        at: TextRange,
        params: &[ClosureParam],
        body: &hir::Expr,
    ) -> tast::Expr {
        let error_ty = self.table.fresh(Kind::Any, at);
        self.obligation(&error_ty, prelude_item("Show"), at);
        let mut cx = Cx::new(Ty::bool());
        let patterns: Vec<tast::Pat> = params
            .iter()
            .map(|p| self.property_param(&mut cx, p))
            .collect();
        let b = self.check(&mut cx, &Ty::bool(), body);
        let row = Row {
            io: false,
            raise: Some(Box::new(error_ty.clone())),
            effects: Vec::new(),
            tail: Tail::Closed,
        };
        self.settle_property(&cx.effects, &row, body);
        // A body that raises nothing raises `Never`.
        if self.table.unsolved(&error_ty).is_some() {
            self.table.solve(&error_ty, Ty::never());
        }
        self.finish();
        let params = patterns.iter().map(|p| (Mode::Let, p.ty.clone())).collect();
        let ty = Ty::func(params, Ty::bool(), row);
        node(tast::ExprKind::Closure(patterns, Box::new(b)), ty, at)
    }

    /// tests.generable-types: a parameter, whose type must be generable.
    fn property_param(&mut self, cx: &mut Cx, p: &ClosureParam) -> tast::Pat {
        let written = p
            .annotation
            .as_ref()
            .expect("a property's parameters are typed");
        let ty = self.of_hir(written);
        if let Some(unfit) = generable::unfit(self.env.decls, &ty) {
            let message = format!(
                "values of `{}` can't be generated: {}",
                self.show(&ty),
                self.unfit(&ty, unfit)
            );
            self.error(codes::E0333, written.at, message);
        }
        let checked = self.pattern(cx, &p.pattern, &ty);
        self.require_irrefutable(&p.pattern);
        checked
    }

    /// Why values of `ty` can't be generated.
    fn unfit(&self, ty: &Ty, unfit: Unfit) -> String {
        match unfit {
            Unfit::Function if matches!(ty, Ty::Fn(_)) => "it is a function type".to_owned(),
            Unfit::Function => "it holds a function type".to_owned(),
            Unfit::NoValues(t) if t == *ty => "it has no values".to_owned(),
            Unfit::NoValues(t) => format!("it holds `{}`, which has no values", self.show(&t)),
            Unfit::Key(k) => format!(
                "it holds a map keyed by `{}`, which doesn't implement both `Eq` and `Hash`",
                self.show(&k)
            ),
            Unfit::Infinite => "it holds infinitely many types".to_owned(),
        }
    }

    /// tests.property-io: the body's effects fit a row of no `io`, where the first call that
    /// performs `io` is E0510 rather than E0502.
    fn settle_property(&mut self, effects: &[(Row, TextRange)], row: &Row, body: &hir::Expr) {
        let mut reported = Reported::default();
        let mut io = false;
        for (r, at) in effects {
            let (performs, rest): (Vec<Problem>, Vec<Problem>) = self
                .table
                .fit(&crate::ty::Handled::Nothing, r, row)
                .into_iter()
                .partition(|p| matches!(p, Problem::MissingIo));
            if !performs.is_empty() && !io {
                io = true;
                let message = "this performs `io`, which a property can't".to_owned();
                let fix = removal(body, *at);
                self.error_fixed(codes::E0510, *at, message, fix.into_iter().collect());
            }
            self.report(&mut reported, (*at, false), rest);
        }
    }
}

/// The fix that removes a call that performs `io`, when it is a statement of the closure's
/// block that another statement follows, so that the block keeps its value.
fn removal(body: &hir::Expr, at: TextRange) -> Option<Fix> {
    let ExprKind::Block(stmts) = &body.kind else {
        return None;
    };
    let i = stmts
        .iter()
        .position(|s| matches!(&s.kind, StmtKind::Expr(e) if e.at == at))?;
    let next = stmts.get(i + 1)?;
    let StmtKind::Expr(call) = &stmts[i].kind else {
        return None;
    };
    let ExprKind::Call(callee, _) = &call.kind else {
        return None;
    };
    let ExprKind::Func(item) = &callee.kind else {
        return None;
    };
    let range = TextRange::new(stmts[i].at.start(), next.at.start());
    Some(Fix::new(
        format!("remove the `{}`", item.name),
        vec![Edit::delete(range)],
    ))
}
