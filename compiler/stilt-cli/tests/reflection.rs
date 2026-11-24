//! Reflection (meta.std-meta and meta.shapes), run in memory by `stilt run` and as executables
//! that `stilt build` writes: each program prints what the Reference gives it, and ends with every
//! count back to zero, which a debug build's check at exit would fail otherwise (goal no-leaks).
//! The programs build what `std.json` (std.json) is built of: fields and variants iterated and
//! built, `make` of every case, a bound test whose branch calls the trait's method, raises through
//! `fields.build`, and recursion through a function that reflects on a recursive type. And what a
//! call can't see: a bound test's arguments and an impl's own bounds, an impl's type parameters, a
//! trait method's own, and `Self` and a trait's parameters in a default. And the structural impls
//! of a descriptor's table, which walk its parts, against the impls compiled for each type.

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Output};

/// Writes `source` as a program of its own directory, and gives its file.
fn program(name: &str, source: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("reflection")
        .join(name);
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("the directory can be made");
    let file = dir.join("main.lt");
    fs::write(&file, source).expect("the program can be written");
    file
}

/// The program's run with `stilt run`, then the run of the executable `stilt build` writes.
fn runs(name: &str, source: &str) -> [Output; 2] {
    let file = program(name, source);
    let stilt = env!("CARGO_BIN_EXE_stilt");
    let ran = Command::new(stilt)
        .arg("run")
        .arg(&file)
        .output()
        .expect("stilt runs");
    let exe = file.with_file_name("program");
    let built = Command::new(stilt)
        .args(["build", "-o"])
        .arg(&exe)
        .arg(&file)
        .output()
        .expect("stilt runs");
    assert!(built.status.success(), "{built:?}");
    let executed = Command::new(&exe).output().expect("the program runs");
    [ran, executed]
}

/// Checks that both runs of `source` print `expected` and succeed.
fn prints(name: &str, source: &str, expected: &str) {
    for (how, out) in ["run", "build"].iter().zip(runs(name, source)) {
        assert_eq!(
            String::from_utf8_lossy(&out.stdout),
            expected,
            "{how}: {out:?}"
        );
        assert!(out.status.success(), "{how}: {out:?}");
    }
}

#[test]
fn a_value_is_described_by_its_shape() {
    // meta.shapes, meta.fields and meta.variant-cases: a record's fields in the order of its
    // declaration, a variant's payload as a tuple, `()` for a variant without one.
    let expected = "{x=1, y=2}\nCircle({x=0, y=3}, 1.5)\nDot()\n";
    prints("describe", include_str!("reflection/describe.lt"), expected);
}

#[test]
fn the_blocks_of_a_derive_write_read_and_raise_as_the_records_say() {
    let expected = [
        // The format of std.json-writing: a record's members in the order of its fields, a variant
        // without a payload as its name, one with as an object of its payload, and the impl of the
        // guard, `Out`, where the type has one (meta.bound-tests).
        r#"{"name":"ana","age":31,"roles":["Admin",{"Guest":["lab"]}],"email":null,"pay":$250}"#,
        // A recursive type, through its descriptor's thunks.
        r#"{"Node":[{"Node":["Leaf",1,"Leaf"]},2,"Leaf"]}"#,
        // A set in insertion order, a map as its entries, an array, a tuple and `()`
        // (std.json-writing).
        r#"[[3,1],[["a",1],["b",2]],[4,5],[true,0.5],null]"#,
        // `make` of every case: each string gains `!` and each `bool` flips.
        r#"{"name":"ana!","age":31,"roles":["Admin",{"Guest":["lab!"]}],"email":null,"pay":$250}"#,
        r#"[[3,1],[["a!",1],["b!",2]],[4,5],[false,0.5],null]"#,
        r#"{"Node":["Leaf",7,"Leaf"]}"#,
        // A set's `make` keeps the first of equal elements (std.json-reading).
        "[3,1]",
        // `fields.build` calls its closure once on each field, in order (meta.building)...
        "field left",
        "field right",
        "1 2",
        // ...and on no field after one of its calls raises, whose error passes through.
        "field left",
        "raised unlucky",
        "0 0",
        // A bound test's branch calls the trait's function on the type parameter
        // (meta.bound-tests).
        "$0",
        "5",
        // meta.shape-and-name: a type's name as a diagnostic writes it.
        "Pair",
        "3",
    ];
    let expected = expected.map(|line| format!("{line}\n")).concat();
    prints("blocks", include_str!("reflection/blocks.lt"), &expected);
}

#[test]
fn a_bound_test_reads_the_bounds_arguments_and_the_impls_own_bounds() {
    let expected = [
        // meta.bound-tests: an impl of the trait with the bound's arguments, `Convert<i64>`, which
        // `Other`'s `Convert<str>` isn't.
        "7 from i64",
        "no Convert<i64>: Other",
        // `Wrap<T>`'s impl holds only where `T: Show` does, which a function type's doesn't.
        "wrap 3",
        "no Show: Wrap<fn() -> i64>",
        // The bound's argument names the function's other type parameter, whose type is given.
        "true false true",
    ];
    let expected = expected.map(|line| format!("{line}\n")).concat();
    prints(
        "bound_args",
        include_str!("reflection/bound_args.lt"),
        &expected,
    );
}

#[test]
fn an_impls_own_type_parameters_are_described_where_the_bound_is_met() {
    let expected = [
        // meta.unseen-instantiations: the impl's `X` is `Point` where `Holder<Point>` meets the
        // bound, by a call...
        "2 fields",
        "Point",
        // ...through a bound...
        "2 fields, Point",
        // ...and through a function that meets it with its own `X`, which its caller gives.
        "3 fields, (i64, bool, str)",
    ];
    let expected = expected.map(|line| format!("{line}\n")).concat();
    prints(
        "impl_params",
        include_str!("reflection/impl_params.lt"),
        &expected,
    );
}

#[test]
fn a_call_through_a_trait_passes_what_its_methods_read() {
    let expected = [
        // meta.bound-tests in an impl's method on its own `U`, by a call and through a bound.
        "point with true",
        "point with fn() -> i64",
        // meta.shape-and-name: `X.name()` and `U.name()`, through a bound, a call and a method
        // value.
        "holder of f64 with List<bool>",
        "holder of i64 with (i64, str)",
        "holder of i64 with (i64, f64)",
        // A default method's `Self` and trait parameter, by a call, through a bound, and
        // through a function that meets the bound with its own type parameter.
        "Point to i64",
        "Holder<bool> to bool",
        "Holder<List<f64>> to List<f64>",
    ];
    let expected = expected.map(|line| format!("{line}\n")).concat();
    prints(
        "trait_methods",
        include_str!("reflection/trait_methods.lt"),
        &expected,
    );
}

#[test]
fn the_structural_impls_of_a_table_give_what_the_compiled_impls_give() {
    // meta.bound-tests's branch calls the type's impl, the structural one of
    // traits.structural-impls, which a descriptor's table holds as code shared by every type of its
    // shape: the same text, equality, order and hash, so a map made through a table's `Hash` finds
    // its keys by the compiled one (std.finding-keys).
    let expected = [
        "record true true",
        "nested true",
        "empty true",
        "generic true",
        "variants true",
        "recursive true true",
        "without payloads true",
        "tuples true true",
        "anonymous true",
        "arrays true",
        "in memory true",
        "floats true true",
        "options true true true",
        "lists true true",
        "maps true",
        "sets true",
        "array of records true",
        "fields true",
        "map keys true true true",
        "set elements true true true",
    ];
    let expected = expected.map(|line| format!("{line}\n")).concat();
    prints(
        "structural",
        include_str!("reflection/structural.lt"),
        &expected,
    );
}
