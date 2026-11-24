//! The entry of a test or doc example, which `stilt test` runs on a thread of its own
//! (program.test-results and program.doc-examples): it calls the test's body, and gives 1 when the
//! body returns, or for an example when it gives `true`, and 0 when it raises or the example gives
//! `false`. A raise first tells `stilt test` the error as `Show` shows it. A panic or an `exit`
//! ends the thread, which the runtime reports as a failure.

use stilt_hir::hir::Name;
use stilt_types::infer_body;
use stilt_types::tast::TestKind;
use stilt_types::ty::Ty;

use crate::FnRef;
use crate::items::{Code, code_of};
use crate::lower::words::operands;
use crate::lower::{Conv, Cx, Lower};
use crate::mir::{Arg, Callee, Function, Operand, Runtime, Stmt, Terminator};

/// The entry `f` of the test or example whose body is `index` in `module`, if it has one.
pub(super) fn entry(cx: &Cx<'_>, f: &FnRef, module: Name, index: u32) -> Option<Function> {
    let test = FnRef::Test(module, index);
    let Some(Code::Body(file, _)) = code_of(cx.db, cx.program, test.clone()) else {
        return None;
    };
    let tested = infer_body(cx.db, cx.program, file, index)
        .body
        .tested
        .clone()?;
    let mut l = Lower::new(cx, f.clone(), false);
    super::load_libraries(cx, &mut l);
    l.ret = Conv::of(Ty::bool());
    l.err = Conv::of(Ty::never());
    let example = match tested.kind {
        TestKind::Test => false,
        TestKind::Example => true,
        TestKind::Property => return None,
    };
    let result = if example { Ty::bool() } else { Ty::unit() };
    let dest = l.temps(&result);
    let next = l.b.new_block();
    let raised = (tested.error != Ty::never()).then(|| (l.temps(&tested.error), l.b.new_block()));
    l.b.terminate(Terminator::Call {
        callee: Callee::Direct(test),
        args: vec![Arg::Borrow(Operand::Local(l.loc))],
        dest: dest.clone(),
        next,
        raised: raised.clone(),
    });
    if let Some((caught, block)) = raised {
        l.b.switch_to(block);
        // What the test raised, as `Show` shows it, for `stilt test` to report.
        let loc = Operand::Local(l.loc);
        let shown = l.trait_call("Show", "show", &tested.error, vec![operands(&caught)], loc);
        l.b.emit(Stmt::Effect(
            Runtime::TestNote,
            vec![shown, Operand::word(0)],
        ));
        l.b.terminate(Terminator::Return(vec![Operand::word(0)]));
    }
    l.b.switch_to(next);
    let passed = if example {
        Operand::Local(dest[0])
    } else {
        Operand::word(1)
    };
    l.b.terminate(Terminator::Return(vec![passed]));
    Some(l.into_function())
}
