//! The calls of a function that a release build leaves on dictionaries, each with its reason
//! (builds.what-stays-generic): in a function of a recursive group whose instantiations could grow
//! without end, each call that passes a dictionary of its own type parameters, by name, as a
//! trait's method or through an operator or an interpolation, for polymorphic recursion; and in any
//! function, each call of a polymorphic argument (polymorphism.arguments).

use stilt_db::{Database, Program};
use stilt_diag::LineIndex;
use stilt_hir::hir::BinaryOp;
use stilt_mir::special::groups::mentions_params;
use stilt_types::tast::{Callee, Code, Definition, Expr, ExprKind, Segment, walk};

use crate::report::text;
use stilt_ide::show::facts::Function;

/// Why a call is left on a dictionary.
pub(crate) const RECURSION: &str = "polymorphic recursion";
pub(crate) const ARGUMENT: &str = "polymorphic argument";

/// The lines of the calls of `f` left on dictionaries, with their reasons, in order: `kept`
/// says that its group keeps its dictionaries.
pub(crate) fn dictionaries(
    db: &Database,
    program: Program,
    f: &Function,
    kept: bool,
) -> Vec<(u32, &'static str)> {
    let typed = &stilt_types::infer_body(db, program, f.file, f.index).body;
    let Definition::Code(code) = &typed.code else {
        return Vec::new();
    };
    let mut found = Vec::new();
    let mut visit = |e: &Expr| {
        if let Some(reason) = reason(e, kept) {
            found.push((e.at.start(), reason));
        }
    };
    match code {
        Code::Block(b) => walk::exprs_of_block(b, &mut visit),
        Code::Expr(e) => walk::iter(e, &mut |_| {}, &mut visit),
    }
    let text = text(db, f.file);
    let lines = LineIndex::new(&text);
    let start = stilt_hir::body_starts(db, program, f.file)[f.index as usize];
    let mut out: Vec<(u32, &'static str)> = found
        .into_iter()
        .map(|(at, reason)| (lines.position(&text, start + at).line, reason))
        .collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// Why the expression's call is left on a dictionary, if it is.
fn reason(e: &Expr, kept: bool) -> Option<&'static str> {
    if let ExprKind::CallValue(callee, _) = &e.kind
        && let ExprKind::Instantiate(..) = &callee.kind
    {
        return Some(ARGUMENT);
    }
    (kept && passes_own(e)).then_some(RECURSION)
}

/// Whether the expression calls a function with a dictionary of a type built from the type
/// parameters of the function it is in.
fn passes_own(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Call(c, targs, ..)
        | ExprKind::Project(c, targs, ..)
        | ExprKind::Callee(c, targs) => {
            let receiver = match c {
                Callee::TraitMethod(_, _, self_ty) => mentions_params(self_ty),
                Callee::Operation(..) => return false,
                Callee::Function(_) | Callee::Member(..) => false,
            };
            receiver || targs.iter().any(mentions_params)
        }
        ExprKind::Binary(op, a, _) => {
            let compares = matches!(
                op,
                BinaryOp::Eq
                    | BinaryOp::Ne
                    | BinaryOp::Lt
                    | BinaryOp::Le
                    | BinaryOp::Gt
                    | BinaryOp::Ge
            );
            compares && mentions_params(&a.ty)
        }
        ExprKind::Interpolated(segments) => segments.iter().any(|s| match s {
            Segment::Splice(x, _) => mentions_params(&x.ty),
            Segment::Text(_) => false,
        }),
        ExprKind::Index(base, key) => base.ty.is_prelude("Map") && mentions_params(&key.ty),
        _ => false,
    }
}
