//! Type checking an input of the REPL (repl.input-checking): its body is checked as a test's body
//! is, so that it may perform `io` and raise any error that can be shown, with each of its
//! parameters, the session's bindings, of the type it was bound with. Its type is the type of
//! its last expression, which a `return` in it gives too; one that never ends, as `exit(0)`,
//! has type `Never`.

use stilt_diag::Diagnostic;
use stilt_hir::hir::{self, BodyValue, Mode};

use super::State;
use crate::tast::{Code, TypedBody};
use crate::ty::{Handled, Kind, Ty};

/// Checks the body of an input whose parameters have the types `params`, and returns its
/// elaboration, its type and its type errors.
pub(crate) fn check_input(
    env: super::Env<'_>,
    body: &hir::Body,
    params: &[Ty],
) -> (TypedBody, Ty, Vec<Diagnostic>) {
    let names = body.locals.iter().map(|l| l.name).collect();
    let mut st = State::new(env, names);
    let params = body
        .params
        .iter()
        .zip(params)
        .map(|(v, ty)| {
            st.locals.insert(*v, ty.clone());
            (Mode::Let, *v)
        })
        .collect();
    let BodyValue::Block(block) = &body.value else {
        unreachable!("an input's body is a block");
    };
    // Not one of the body's own variables, which must be solved: a body of type `Never`
    // solves it only by a `return`.
    let ret = st.table.fresh(Kind::Any, body.at);
    let ((mut b, ty), tested) =
        st.test_body((body.at, &Handled::Nothing), ret.clone(), |st, cx| {
            let (b, ty) = st.block_expr(cx, body.at, None, block);
            if *st.table.resolve(&ty) != Ty::never() {
                st.subsume(body.at, &ret, &ty);
            }
            (b, ty)
        });
    let ty = match st.table.unsolved(&ret) {
        None if *st.table.resolve(&ty) == Ty::never() => ret,
        _ => ty,
    };
    let code = st.outcome(body, |f| {
        f.block(&mut b);
        Code::Block(b)
    });
    st.fit_splices();
    st.settle_unknown_names(&body.held);
    let passed = st
        .passed
        .iter()
        .map(|(at, row, l)| (*at, st.table.freeze_row(row), l.map(|t| st.table.freeze(t))))
        .collect();
    let typed = TypedBody {
        locals: st.local_names,
        params,
        pairs: Vec::new(),
        passing: Vec::new(),
        passed,
        tested: Some(tested),
        staged: std::mem::take(&mut st.staged),
        renamed: std::mem::take(&mut st.renamed),
        code,
    };
    let ty = st.table.freeze(&ty);
    (typed, ty, st.errors)
}
