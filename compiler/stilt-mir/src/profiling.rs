//! Whether lowering marks what profiles count (builds.profiles): the entry of each body of the
//! program's own files, each arm of an `if` or a `match` and each loop's body, at the place of
//! each ([`crate::mir::Stmt::Count`]), and for a profiled run, each call through a function
//! value or a dictionary, by the function it reaches.
//!
//! A process that builds code for profiles says so before it makes a database, as `stilt test
//! --std` does for the standard library's examples, so that its lowering is the same
//! throughout: a profiled run, whose code counts each mark, and a release build that reads a
//! profile, whose C reads each mark as a hint. Every other build marks nothing, so a debug run
//! without `--profile` counts nothing and keeps its speed (goal debug-speed).

use std::sync::atomic::{AtomicU8, Ordering};

use stilt_hir::decls::Lookup as _;

use stilt_syntax::TextRange;

use crate::FnRef;
use crate::items::ImplRef;
use crate::lower::{Cx, Lower, stilt_runtime_location};
use crate::mir::{Const, Counted, Operand, Runtime, Stmt};

/// What lowering marks for profiles.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Profiling {
    /// Nothing.
    Off,
    /// Each place a profile counts, and each call through a function value or a dictionary:
    /// a profiled run's code.
    Count,
    /// Each place a profile counts, which the C of a release build reads.
    Hint,
}

static MODE: AtomicU8 = AtomicU8::new(0);

/// Makes the lowering this process does from now on mark what `mode` says.
pub fn set_profiling(mode: Profiling) {
    let n = match mode {
        Profiling::Off => 0,
        Profiling::Count => 1,
        Profiling::Hint => 2,
    };
    MODE.store(n, Ordering::Relaxed);
}

/// What lowering marks.
#[must_use]
pub fn profiling() -> Profiling {
    match MODE.load(Ordering::Relaxed) {
        1 => Profiling::Count,
        2 => Profiling::Hint,
        _ => Profiling::Off,
    }
}

/// The address of the function that the code `f` of a dictionary's method or of a function
/// used as a value calls, if a profile counts calls that reach it: a function
/// with a body, of the program or the standard library.
pub(crate) fn callee_address(cx: &Cx<'_>, f: &FnRef) -> Option<String> {
    let decls = cx.decls();
    let item = |i: &stilt_hir::hir::Item| format!("{}.{}", i.home, i.name);
    match f {
        FnRef::Instance(g, _) | FnRef::Value(g) => callee_address(cx, g),
        FnRef::Function(i) => Some(item(i)),
        FnRef::Member(owner, name) => Some(format!("{}.{name}", item(owner))),
        FnRef::DefaultMethod(t, name) => Some(format!("{}.{name}", item(t))),
        FnRef::ImplMethod(t, owner, name) => {
            let module = decls.trait_impl(t, owner)?.module;
            Some(format!("{module}.{}.{}.{name}", owner.name, t.name))
        }
        FnRef::Entry(imp, index) => match &**imp {
            ImplRef::Written { trait_item, owner } => {
                let info = decls.trait_info(trait_item)?;
                let name = info.methods.get(*index as usize)?.name;
                let own = crate::lower::functions::calls_own(&decls, trait_item, owner, name);
                let held = decls
                    .trait_impl(trait_item, owner)?
                    .members
                    .iter()
                    .any(|m| m.name == name);
                if held || own {
                    callee_address(
                        cx,
                        &FnRef::ImplMethod(trait_item.clone(), owner.clone(), name),
                    )
                } else {
                    callee_address(cx, &FnRef::DefaultMethod(trait_item.clone(), name))
                }
            }
            ImplRef::Structural { .. } => None,
        },
        _ => None,
    }
}

impl Lower<'_> {
    /// Marks the place, at `at` in the body, of what a profile counts, in a build that marks
    /// them: in the program's own files, not the standard library's.
    pub(crate) fn count_at(&mut self, counted: Counted, at: TextRange) {
        if profiling() == Profiling::Off || self.std {
            return;
        }
        let Some(o) = &self.origin else {
            return;
        };
        let position = o.lines.position(&o.text, o.start + at.start());
        let word = stilt_runtime_location(o.file, position.line, position.col);
        self.b.emit(Stmt::Count(counted, word));
    }

    /// In a profiled run's code, counts the call that reaches the code `f` of a dictionary's
    /// method or of a function used as a value, by the call's location, which this code takes
    /// first, and the address of the function it reaches.
    pub(crate) fn count_call(&mut self, f: &FnRef) {
        if profiling() != Profiling::Count {
            return;
        }
        let Some(address) = callee_address(self.cx, f) else {
            return;
        };
        let args = vec![
            Operand::Local(self.loc),
            Operand::Const(Const::Str(address.into())),
        ];
        self.b.emit(Stmt::Effect(Runtime::ProfileCall, args));
    }
}
