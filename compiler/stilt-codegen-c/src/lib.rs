//! Stilt's release back end (builds.release-builds): the
//! counted MIR that a debug build compiles, lowered to C11, which clang compiles at `-O2`. A
//! release build means what a debug build means (builds.same-meaning), so the C keeps every check
//! that a debug build makes, overflow, bounds, division and shifts, and every reference count, but
//! those that verification proves can't fail (facts.verification), whose operations lowering marks
//! ([`proved`]).
//!
//! A program is one C file per module, and one more, `program.c`, for the code that no module
//! holds, the constants' cells and C's `main` ([`assemble`]), so that clang compiles the files
//! across the machine's cores and a build compiles again only the files whose C changed. A
//! function that no other file names is `static`, so that clang sees every call of it.
//!
//! The runtime's fast paths are a header of static inline C ([`header`]), which mirrors what
//! `stilt-codegen-clif` compiles inline, with the layout constants of `stilt-runtime`, and
//! every slow path is a call into the runtime's library, which stays Rust. The C needs no
//! system header and reaches none of C's undefined behaviour: overflow goes through checked
//! builtins, wrapping arithmetic through unsigned types, a shift checks its amount, a division
//! its divisor and `MIN / -1`, a float converted to an integer saturates where a range check
//! guards it, and loops are labels and jumps. `#line` directives give the program's lines to
//! the line tables, so debuggers and profilers show them (builds.line-tables).
//!
//! Its place among the crates (`compiler/README.md`): it depends on `stilt-mir` and `stilt-
//! runtime` alone, and on no database: it writes the C of the functions it is given.

#![forbid(unsafe_code)]
#![warn(missing_docs)]

mod assemble;
mod cached;
mod calls;
mod exports;
mod file;
mod floats;
mod foreign;
mod function;
mod header;
mod hints;
mod lists;
mod names;
mod prim;
mod program;
mod proved;
mod runtime;
mod stmts;

use std::sync::Arc;

use stilt_mir::mir::{
    Callee, Const, Effects, Function, Operand, Runtime, Rvalue, Stmt, Terminator,
};

pub use assemble::Source;
pub use header::header;
pub use hints::Hints;

/// The flags of every release build's C: the optimizer at `-O2`, a
/// freestanding program that includes no system header, signed overflow defined, since the
/// C's own checks come first, no type-based aliasing, since a word may be read as any type,
/// no fused multiply and add, which would round once where the reference interpreter rounds twice
/// (numbers.lengths-are-i64), no `errno` for math builtins, so `sqrt` is one instruction on every
/// target, and a probe of each page of a large frame, so that a frame larger than the guard page
/// still faults in it and a stack overflow still ends with status 134 (program.recursion-depth),
/// which only the compiler's own option of the flag asks for on macOS. Line tables come from
/// `#line`, relative to the build's directory, so the executable holds no path of the machine
/// (builds.same-bytes).
pub const FLAGS: &[&str] = &[
    "-std=c11",
    "-O2",
    "-ffreestanding",
    "-fwrapv",
    "-fno-strict-aliasing",
    "-ffp-contract=off",
    "-fno-math-errno",
    "-fno-stack-protector",
    "-Xclang",
    "-fstack-clash-protection",
    "-gline-tables-only",
    "-fdebug-compilation-dir=.",
    "-w",
];

/// The flags of a target's builds: on aarch64, no merging of neighbouring loads and stores
/// into pairs, since a load of a pair right after a store to half of it can't take the
/// store's value and waits for it to reach the cache, which takes nbody from 64 ms to 41 ms
/// and changes no other program of the benchmark suite by more than 3%.
#[must_use]
pub fn target_flags(triple: &str) -> &'static [&'static str] {
    if triple.starts_with("arm64") || triple.starts_with("aarch64") {
        &["-mllvm", "-aarch64-enable-ldst-opt=false"]
    } else {
        &[]
    }
}

/// What a build asks of its C beyond the program's code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Options {
    /// Whether the checks that verification proves are dropped, as a release build drops them
    /// (builds.dropped-checks), rather than kept, as a WebAssembly build without `--release` keeps
    /// every check (wasm.target).
    pub proved: bool,
    /// Whether the C is for WebAssembly: each function checks the stack
    /// pointer at its entry against the stack's end, C's `main` is the one WASI's start calls,
    /// and `program.c` defines the functions through which the runtime reads and moves the
    /// stack pointer, a global of the module that only WebAssembly's instructions reach.
    pub wasm: bool,
    /// Whether the program checks at its end that every count is back to zero, as a debug
    /// build does and a release build doesn't (goal no-leaks; cycles.check-at-exit).
    pub counts: bool,
    /// How the program reaches the foreign functions it calls.
    pub c_functions: CFunctions,
}

/// How a program reaches the foreign functions it calls (c.build-targets and c.calls).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CFunctions {
    /// By name, at each one's first call, among the C library and the libraries the program
    /// loads when it starts: where the target's executables load shared libraries.
    Found,
    /// Linked from the target's C library, where its executables load none.
    Linked,
}

impl Options {
    /// The options of a release build for a native target.
    pub const RELEASE: Self = Self {
        proved: true,
        wasm: false,
        counts: false,
        // A library's C program loads libraries, from which its foreign functions come.
        c_functions: CFunctions::Found,
    };
}

/// The C of a program's functions, its entry among them, one file per module and
/// `program.c`. `files` are the paths of the program's files as its panics report them,
/// `hints` what the program's profile tells clang (builds.profile-use), and `options` the build's.
///
/// # Errors
///
/// Fails on MIR that names code the program doesn't compile, which lowering never gives.
pub fn emit(
    functions: &[Arc<Function>],
    files: &[String],
    hints: &Hints,
    options: Options,
) -> Result<Vec<Source>, String> {
    let functions = prepared(functions, options);
    let mut prog = program::Program::new(&functions, files, hints, options);
    assemble::assemble(&mut prog, None)
}

/// The functions as their C is written: those whose appends are in place, and with
/// `options.proved`, those whose proved reads of elements check nothing.
fn prepared(functions: &[Arc<Function>], options: Options) -> Vec<Arc<Function>> {
    functions
        .iter()
        .map(|f| {
            if options.proved {
                in_place(&proved::unchecked_lists(f))
            } else {
                in_place(f)
            }
        })
        .collect()
}

/// The C names of the functions that call `resume`, the bodies of handlers that take control
/// and resume (handlers.resuming), which are on a body's frames when it switches back to its
/// performance: WebAssembly's build instruments them for the runtime's switches
/// (wasm.handlers-that-resume).
#[must_use]
pub fn resuming(functions: &[Arc<Function>]) -> Vec<String> {
    let resumes = |f: &Function| {
        (f.blocks.iter().flat_map(|b| &b.stmts)).any(|s| {
            matches!(s, Stmt::Assign(_, Rvalue::Runtime(Runtime::Effects(Effects::Code), args))
                if matches!(args[..], [Operand::Const(Const::Word(RESUME))]))
        })
    };
    (functions.iter())
        .filter(|f| resumes(f))
        .map(|f| names::c_name("f_", &f.name.symbol()))
        .collect()
}

/// The argument of [`Runtime::Effects(Effects::Code)`] that gives `resume`'s closure
/// (`stilt_mir`'s `lower::handlers`).
const RESUME: u64 = 1;

/// The C of a library's functions, as [`emit`] gives a program's, with the hints of its profile
/// and `program.c` ending in a C function for each of `exports` and in `stilt_runtime_once`, in
/// place of the entry and C's `main` (c.calls-from-c and c.static-library).
///
/// # Errors
///
/// Fails on MIR that names code the program doesn't compile, which lowering never gives, or
/// that lacks an export's function.
pub fn emit_library(
    functions: &[Arc<Function>],
    files: &[String],
    exports: &[stilt_mir::Export],
    hints: &Hints,
) -> Result<Vec<Source>, String> {
    let functions = prepared(functions, Options::RELEASE);
    let mut prog = program::Program::new(&functions, files, hints, Options::RELEASE);
    assemble::assemble(&mut prog, Some(exports))
}

/// A function whose appends to and pops from the lists it proves unique append and pop where
/// the lists are, so that its C keeps their lengths and elements in locals across them
/// ([`stilt_mir::opt::in_place`]).
fn in_place(f: &Arc<Function>) -> Arc<Function> {
    let appends = (f.blocks.iter().flat_map(|b| &b.stmts))
        .any(|s| matches!(s, Stmt::Effect(Runtime::ListAppend, _)));
    let pops = f.blocks.iter().any(|b| {
        matches!(&b.term, Terminator::Call { callee: Callee::Direct(f), .. } if lists::is_pop(f))
    });
    if !appends && !pops {
        return Arc::clone(f);
    }
    let mut f = Function::clone(f);
    stilt_mir::opt::in_place(&mut f);
    Arc::new(f)
}
