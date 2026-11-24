//! The runtime of Stilt's compiled programs: the memory of their values, the native functions of
//! the standard library, and the entry that runs a program and ends it as program.exit-statuses and
//! program.panic-report require.
//!
//! [`abi`] gives the calling convention that compiled code and natives share, and [`object`]
//! the representation of values: one word each, scalars inline and everything else in
//! reference-counted objects. The compiler's JIT calls the runtime's functions by the
//! addresses [`symbols`] lists; an ahead-of-time build links the same functions by name.
//!
//! Its place among the crates (`compiler/README.md`): it depends on no crate of the compiler, since
//! compiled programs link it; the compiler calls into it, never the reverse.

#![warn(missing_docs)]

/// Pairs each function the compiler may call by name with its address.
macro_rules! exports {
    ($($f:ident),* $(,)?) => {
        vec![$((stringify!($f), $f as *const u8)),*]
    };
}
pub(crate) use exports;

pub mod abi;
#[cfg(not(target_os = "wasi"))]
pub mod c_libraries;
mod constants;
mod effects;
mod entry;
mod fiber;
mod format;
mod io;
mod iter;
pub mod layout;
mod library;
mod limits;
mod list;
mod map;
mod maps;
mod object;
mod packs;
mod panic;
mod pool;
mod prelude;
pub mod profile;
mod prop;
#[cfg(any(stilt_sanitizers, stilt_tsan))]
mod sanitizers;
mod session;
mod shape;
mod show;
mod sort;
mod stacks;
mod std_c;
mod std_fs;
mod std_int;
mod std_io;
mod std_lazy;
mod std_list;
mod std_macros;
mod std_map;
mod std_math;
mod std_meta;
mod std_net;
mod std_par;
mod std_process;
mod std_scope;
mod std_str;
mod std_sync;
mod std_system;
mod std_task;
mod std_view;
mod stdin;
mod structural;
mod support;
mod tasks;
mod text;
#[cfg(target_family = "wasm")]
mod wasm;
mod watch;
mod workers;

pub use entry::{Entry, Program, leaked, prepare_tests, release, run};
pub use panic::location;
pub use prop::Tape;
pub use session::{Value, evaluate, prepare_session};
pub use stdin::line as input_line;
pub use watch::{Ended, Evaluated, Note, Outcome, Running, Tested, property, start, test};

/// The text of a float, given as its bits, as numbers.printing-floats prints it: an `f32`'s in the
/// low 32 bits.
#[must_use]
pub fn shown_float(f32: bool, bits: u64) -> String {
    let kind = if f32 { show::F32 } else { show::F32 + 1 };
    show::float(kind, show::float_of(kind, bits))
}

/// A splice formatted by its spec, given as the two words of std.width-fill-and-alignment,
/// std.precision, std.integer-kinds, std.scientific-notation and std.format-special-values that the
/// compiler passes: a number `value` of kind `kind` (0 to 7 for the integer types, 8 and 9 for
/// `f32` and `f64`, as their bits), or the text `shown` when `kind` is 255.
#[must_use]
pub fn formatted(kind: u64, value: u64, shown: &str, spec: (u64, u64)) -> String {
    format::formatted(kind, value, shown, spec.0, spec.1)
}

/// A string as it shows nested inside another value: quoted and escaped
/// (std.show-names-and-escapes).
#[must_use]
pub fn quoted(s: &str) -> String {
    text::quote(s)
}

/// The name and address of every function of the runtime that compiled code calls.
#[must_use]
pub fn symbols() -> Vec<(&'static str, *const u8)> {
    [
        panic::symbols(),
        limits::symbols(),
        constants::symbols(),
        prelude::symbols(),
        show::symbols(),
        support::symbols(),
        object::reuse::symbols(),
        pool::symbols(),
        structural::symbols(),
        packs::symbols(),
        maps::symbols(),
        format::symbols(),
        std_str::symbols(),
        std_int::symbols(),
        std_list::symbols(),
        std_map::symbols(),
        std_io::symbols(),
        std_fs::symbols(),
        std_math::symbols(),
        std_net::symbols(),
        std_net::datagrams::symbols(),
        std_meta::symbols(),
        std_macros::symbols(),
        std_system::symbols(),
        std_view::symbols(),
        std_lazy::symbols(),
        std_c::symbols(),
        #[cfg(not(target_os = "wasi"))]
        c_libraries::symbols(),
        std_task::symbols(),
        std_sync::symbols(),
        std_par::symbols(),
        std_process::symbols(),
        std_scope::symbols(),
        tasks::symbols(),
        effects::symbols(),
        iter::symbols(),
        shape::symbols(),
        watch::symbols(),
        entry::symbols(),
        library::symbols(),
        prop::symbols(),
        profile::symbols(),
    ]
    .concat()
}
