use std::sync::Arc;

use stilt_mir::FnRef;
use stilt_mir::Guards;
use stilt_mir::mir::{Function, Terminator};

use crate::testing::{block, float_loop, function, op, scalar};
use crate::{Built, Target, object};

/// A program of an entry and three loops, the second of which returns its count unchanged
/// when `edited`.
fn program(edited: bool) -> Vec<Arc<Function>> {
    let mut functions: Vec<Arc<Function>> = (0..3)
        .map(|k| {
            let mut f = if edited && k == 1 {
                function(
                    &[scalar()],
                    &[],
                    vec![block(Vec::new(), Terminator::Return(vec![op(1)]))],
                )
            } else {
                float_loop()
            };
            f.name = FnRef::Input(k);
            Arc::new(f)
        })
        .collect();
    functions.push(Arc::new(float_loop()));
    functions
}

fn build(functions: &[Arc<Function>], built: &mut Built) -> Vec<u8> {
    object(
        (functions, Guards::new()),
        &[],
        &[],
        (Target::Aarch64Macos, built),
    )
    .expect("an object")
}

/// Whether `built` holds the same code of each of the loops as `before`.
fn same(built: &Built, before: &Built) -> [bool; 3] {
    [0, 1, 2].map(|k| {
        let f = FnRef::Input(k);
        Arc::ptr_eq(&built.functions[&f], &before.functions[&f])
    })
}

#[test]
fn a_build_compiles_only_the_functions_that_changed() {
    let mut built = Built::default();
    let first = build(&program(false), &mut built);
    let kept = Built {
        target: built.target,
        functions: built.functions.clone(),
        data: built.data,
    };
    assert_eq!(build(&program(false), &mut built), first);
    assert_eq!(same(&built, &kept), [true, true, true]);
    let edited = build(&program(true), &mut built);
    assert_eq!(edited, build(&program(true), &mut Built::default()));
    assert_eq!(same(&built, &kept), [true, false, true]);
}

#[test]
fn a_build_keeps_the_code_of_the_functions_it_reached_alone() {
    let mut built = Built::default();
    build(&program(false), &mut built);
    let fewer: Vec<Arc<Function>> = program(false).into_iter().skip(1).collect();
    build(&fewer, &mut built);
    assert!(!built.functions.contains_key(&FnRef::Input(0)));
    assert_eq!(built.functions.len(), 3);
}

#[test]
fn a_build_for_another_target_compiles_everything_again() {
    let mut built = Built::default();
    build(&program(false), &mut built);
    let kept = Built {
        target: built.target,
        functions: built.functions.clone(),
        data: built.data,
    };
    let linux = object(
        (&program(false), Guards::new()),
        &[],
        &[],
        (Target::X86_64Linux, &mut built),
    );
    let clean = object(
        (&program(false), Guards::new()),
        &[],
        &[],
        (Target::X86_64Linux, &mut Built::default()),
    );
    assert_eq!(linux.expect("an object"), clean.expect("an object"));
    assert_eq!(built.target, Some(Target::X86_64Linux));
    assert_eq!(same(&built, &kept), [false, false, false]);
}
