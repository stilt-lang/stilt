//! Once (modes.once-closures and modes.once-parameters): the closure literals that can run at most
//! once, and the parameters of function type that their function calls at most once. A parameter's
//! fact reads its callees' when it passes the parameter on, so each function's one use of each
//! parameter is a query of its own, and the parameters of a recursive group are solved as a fixed
//! point over them, starting from `once`.

use std::collections::HashSet;

use stilt_db::{Db, Program};
use stilt_hir::hir::LocalId;
use stilt_mir::{Code, FnRef, code_of};
use stilt_syntax::TextRange;
use stilt_types::tast::{self, Definition, TypedBody};

use super::calls::callee;
use super::uses::{Seen, Use, uses};

/// The one use of a parameter of function type that can make it `once`, where it is in its
/// body: a call, or a pass to a parameter of a function called by name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum One {
    Called(TextRange),
    Passed(FnRef, usize, TextRange),
}

/// For each parameter of `f`, by its place among the source's, a receiver first, its one use
/// if it has one that can make it `once`: it uses the parameter exactly once, as a call or a pass
/// outside every loop and every closure literal (modes.once-parameters). A native has none.
// Salsa takes a query's key by value.
#[allow(clippy::needless_pass_by_value)]
#[salsa::tracked(returns(ref))]
pub(crate) fn param_uses(db: &dyn Db, program: Program, f: FnRef) -> Vec<Option<One>> {
    let Some(Code::Body(file, index)) = code_of(db, program, f) else {
        return Vec::new();
    };
    let typed = &stilt_types::infer_body(db, program, file, index).body;
    let Definition::Code(code) = &typed.code else {
        return Vec::new();
    };
    let found = uses(code, &|c| callee(db, program, c));
    typed
        .params
        .iter()
        .map(|(_, v)| one(found.locals.get(v).map_or(&[], Vec::as_slice), 0))
        .collect()
}

/// The one use among `seen` that can make a value of function type `once`: a call or a pass,
/// held by as many loops and closure literals as the value's binding, `depth`.
fn one(seen: &[Seen], depth: u32) -> Option<One> {
    let [s] = seen else { return None };
    if !s.function || s.depth != depth {
        return None;
    }
    match &s.how {
        Use::Called => Some(One::Called(s.at)),
        Use::Passed(g, j) => Some(One::Passed(g.clone(), *j, s.at)),
        Use::Other => None,
    }
}

/// Whether parameter `i` of `f` is `once`: its one use is a call, or a pass to a parameter that
/// is `once` in turn. Each parameter depends on one other at most, so the greatest fixed point
/// follows the passes, and a chain of them that comes back to a parameter it passed is `once`.
pub(crate) fn once_param(db: &dyn Db, program: Program, f: &FnRef, i: usize) -> bool {
    let mut seen = HashSet::new();
    let (mut f, mut i) = (f.generic().clone(), i);
    loop {
        if !seen.insert((f.clone(), i)) {
            return true;
        }
        match param_uses(db, program, f.clone()).get(i) {
            Some(Some(One::Called(_))) => return true,
            Some(Some(One::Passed(g, j, _))) => (f, i) = (g.generic().clone(), *j),
            _ => return false,
        }
    }
}

/// A `once` closure literal or parameter, where its fact is, and the binding that names it: the
/// `let` that binds a closure, or the parameter, whose fact is at its one use (modes.once-closures
/// and modes.once-parameters).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OnceAt {
    pub(crate) at: TextRange,
    pub(crate) binding: Option<LocalId>,
    pub(crate) param: bool,
}

/// The `once` parameters and closure literals of the function `f`, whose typed body is `typed`
/// with the code `code`, in the order they are written.
pub(crate) fn facts(
    db: &dyn Db,
    program: Program,
    f: &FnRef,
    typed: &TypedBody,
    code: &tast::Code,
) -> Vec<OnceAt> {
    let mut found = Vec::new();
    let params = param_uses(db, program, f.generic().clone());
    for (i, (_, v)) in typed.params.iter().enumerate() {
        if let Some(Some(One::Called(at) | One::Passed(_, _, at))) = params.get(i)
            && once_param(db, program, f, i)
        {
            found.push(OnceAt {
                at: *at,
                binding: Some(*v),
                param: true,
            });
        }
    }
    let used = uses(code, &|c| callee(db, program, c));
    let runs_once = |how: &Use| match how {
        Use::Called => true,
        Use::Passed(g, j) => once_param(db, program, g, *j),
        Use::Other => false,
    };
    for (v, at, depth) in &used.bound {
        let seen = used.locals.get(v).map_or(&[][..], Vec::as_slice);
        let once = match one(seen, *depth) {
            Some(One::Called(_)) => true,
            Some(One::Passed(g, j, _)) => once_param(db, program, &g, j),
            None => false,
        };
        if once {
            let binding = Some(*v);
            found.push(OnceAt {
                at: *at,
                binding,
                param: false,
            });
        }
    }
    for (at, how) in &used.unbound {
        if runs_once(how) {
            let (at, binding, param) = (*at, None, false);
            found.push(OnceAt { at, binding, param });
        }
    }
    found.sort_by_key(|o| o.at.start());
    found
}
