//! Inferred modes (modes.bindings-and-axes): the facts of a function's bindings that core can
//! observe, which `stilt show` prints (modes.show). Like consumption, they are kept apart from the
//! signatures that type checking reads (modes.fact-not-type), and read lexically from the typed
//! body, as the rules are.
//!
//! - Locality (modes.escaping and modes.not-escaping): where a `let` or `var` binding of a copy-on-write type first
//!   escapes. A parameter's locality is its consumption ([`crate::consumed`]).
//! - Uniqueness (modes.copy-on-write-types, modes.copies and modes.shared-writes): where a `var` binding or an `inout` parameter is modified while a
//!   copy of the modified part may still last.
//! - Once (modes.once-closures and modes.once-parameters): the closure literals that run at most once, and the parameters of
//!   function type that their function calls at most once.
//!
//! No core type is fixed or contended (modes.fixed-values, modes.contended-values and
//! modes.mode-crossing), so no binding of a core module is anything but `portable` and `calm`, and
//! those axes have nothing to infer yet.

mod calls;
mod flow;
mod locality;
mod once;
mod paths;
mod sharing;
mod uses;

use stilt_db::{Db, Program};
use stilt_hir::decls::QueriedOnce;
use stilt_hir::hir::{LocalId, Name};
use stilt_mir::{Code, FnRef, code_of};
use stilt_syntax::{TextRange, TextSize};
use stilt_types::Cow;
use stilt_types::tast::{Callee, Definition};
use stilt_types::ty::Ty;

use self::flow::{Calls, Kind};
pub use self::flow::{How, Stored};

/// Where a `let` or `var` binding first escapes its function, and how (modes.escaping).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Escape {
    /// The binding.
    pub name: Name,
    /// Where in its file.
    pub at: TextSize,
    /// How the value leaves the function.
    pub how: How,
}

/// A modification of a `var` binding or an `inout` parameter while it is shared
/// (modes.shared-writes).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Shared {
    /// The binding.
    pub name: Name,
    /// Where in its file.
    pub at: TextSize,
    /// The binding that holds the copy that shares it, if one does.
    pub with: Option<Name>,
    /// What the modification is.
    pub how: Modification,
}

/// What a shared modification is: a write of a place, or one of those that modes.handles adds.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Modification {
    /// An assignment, a `yield` or an `inout` argument.
    #[default]
    Write,
    /// The end of a `when`, which gives its names' values back to their handles, where later
    /// `when`s may write them.
    WhenEnd,
    /// A call of `Shared.new`, which gives a binding's value to a handle.
    NewHandle,
}

/// A modification of a `var` binding or an `inout` parameter while it is shared, as the
/// checks of facts.writes-in-place, facts.copy-at-call and facts.copy read it: where the walk puts
/// it relative to its body's start, the statement of an assignment or the call of an `inout`
/// argument.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedWrite {
    /// The binding that is modified.
    pub binding: LocalId,
    /// The name of the binding.
    pub name: Name,
    /// Where the modification is in the body.
    pub at: TextRange,
    /// The binding that holds the copy that shares it, if one does.
    pub with: Option<Name>,
    /// What the modification is.
    pub how: Modification,
}

/// A `once` closure literal or parameter of function type (modes.once-closures and
/// modes.once-parameters).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Once {
    /// The `let` that binds the closure, or the parameter; none for an unbound closure.
    pub name: Option<Name>,
    /// Where its fact is in its file: at the closure literal, or at the parameter's one use.
    pub at: TextSize,
    /// Whether the closure is a parameter.
    pub param: bool,
}

/// The modes of a function's bindings that aren't at their defaults, each in source order.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Modes {
    /// The bindings that escape.
    pub escapes: Vec<Escape>,
    /// The modifications while shared.
    pub shared: Vec<Shared>,
    /// The `once` closures and parameters.
    pub once: Vec<Once>,
}

/// The modes of the bindings of `f`, a function with a body. A body with an error has none
/// (facts.bodies-with-errors).
#[must_use]
pub fn modes(db: &dyn Db, program: Program, f: &FnRef) -> Modes {
    let Some(Code::Body(file, index)) = code_of(db, program, f.clone()) else {
        return Modes::default();
    };
    let typed = &stilt_types::infer_body(db, program, file, index).body;
    let Definition::Code(code) = &typed.code else {
        return Modes::default();
    };
    let start = stilt_hir::body_starts(db, program, file)[index as usize];
    let decls = QueriedOnce::new(db, program);
    let reader = Reader {
        db,
        program,
        cow: Cow::new(&decls),
    };
    let flow = flow::flow(&typed.params, &typed.locals, code, &reader);
    let name = |v: LocalId| typed.locals[v.0 as usize];
    let first = locality::escapes(&flow);
    let mut escapes: Vec<Escape> = first
        .iter()
        .filter(|(v, _)| {
            flow.decls
                .get(v)
                .is_some_and(|d| matches!(d.kind, Kind::Let | Kind::Var))
        })
        .map(|(v, (at, how))| Escape {
            name: name(*v),
            at: start + *at,
            how: how.clone(),
        })
        .collect();
    escapes.sort_by_key(|e| (e.at, e.name));
    let shared = sharing::shared(&flow, &first)
        .into_iter()
        .map(|(v, at, with, how)| Shared {
            name: name(v),
            at: start + at.start(),
            with: with.map(name),
            how,
        })
        .collect();
    let once = once::facts(db, program, f, typed, code)
        .into_iter()
        .map(|o| Once {
            name: o.binding.map(name),
            at: start + o.at.start(),
            param: o.param,
        })
        .collect();
    Modes {
        escapes,
        shared,
        once,
    }
}

/// The shared modifications of the body of `f`, a function with a body, relative to the
/// body's start. A body with an error has none (facts.bodies-with-errors).
#[must_use]
pub fn shared_writes(db: &dyn Db, program: Program, f: &FnRef) -> Vec<SharedWrite> {
    let Some(Code::Body(file, index)) = code_of(db, program, f.clone()) else {
        return Vec::new();
    };
    let typed = &stilt_types::infer_body(db, program, file, index).body;
    let Definition::Code(code) = &typed.code else {
        return Vec::new();
    };
    let decls = QueriedOnce::new(db, program);
    let reader = Reader {
        db,
        program,
        cow: Cow::new(&decls),
    };
    let flow = flow::flow(&typed.params, &typed.locals, code, &reader);
    let first = locality::escapes(&flow);
    let name = |v: LocalId| typed.locals[v.0 as usize];
    sharing::shared(&flow, &first)
        .into_iter()
        .map(|(v, at, with, how)| SharedWrite {
            binding: v,
            name: name(v),
            at,
            with: with.map(name),
            how,
        })
        .collect()
}

/// What the walk reads of the program, through the database.
struct Reader<'a> {
    db: &'a dyn Db,
    program: Program,
    cow: Cow<'a>,
}

impl Calls for Reader<'_> {
    fn callee(&self, c: &Callee) -> Option<FnRef> {
        calls::callee(self.db, self.program, c)
    }

    fn consumed(&self, f: &FnRef) -> Vec<usize> {
        calls::consumed_params(self.db, self.program, f)
    }

    fn cow(&self, t: &Ty) -> bool {
        self.cow.ty(t)
    }

    fn may_store(&self, from: &Ty, targets: &[Ty]) -> bool {
        self.cow.may_store(from, targets)
    }
}
