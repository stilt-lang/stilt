//! The native functions of `std.prelude` (program.prelude-functions).

use crate::abi::Ret;
use crate::{entry, io, panic, text};

/// `print(s)`: writes `s` and a newline to standard output.
///
/// # Safety
///
/// `s` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_print(_loc: u64, s: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    io::print(unsafe { text::bytes(&s) });
    Ret::unit()
}

/// `eprint(s)`: writes `s` and a newline to standard error.
///
/// # Safety
///
/// `s` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_eprint(_loc: u64, s: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    io::eprint(unsafe { text::bytes(&s) });
    Ret::unit()
}

/// `panic(msg)`: a panic of kind `explicit`, whose detail is `msg` quoted (program.panic-detail).
///
/// # Safety
///
/// `msg` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_panic(loc: u64, msg: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    let detail = text::quote(unsafe { text::text(&msg) });
    panic::panic(loc, panic::EXPLICIT, &detail)
}

/// `unreachable()`: a panic of kind `unreachable`.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_prelude_unreachable(loc: u64) -> Ret {
    panic::panic(loc, panic::UNREACHABLE, "")
}

/// `unwrap_failed(detail)`: a panic of kind `unwrap`, whose detail is `detail`, for `unwrap`
/// on a `None` or an `Err` (effects.panic-kinds).
///
/// # Safety
///
/// `detail` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_unwrap_failed(loc: u64, detail: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    let detail = unsafe { text::text(&detail) };
    panic::panic(loc, panic::UNWRAP, detail)
}

/// `expect_failed(msg)`: a panic of kind `unwrap`, whose detail is `msg` quoted, for `expect`
/// on a `None` or an `Err` (program.panic-detail).
///
/// # Safety
///
/// `msg` is a live string.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_prelude_expect_failed(loc: u64, msg: u64) -> Ret {
    // SAFETY: the caller guarantees the string is alive.
    let detail = text::quote(unsafe { text::text(&msg) });
    panic::panic(loc, panic::UNWRAP, &detail)
}

/// `exit(code)`: ends the program with status `code`, once its output is written.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_prelude_exit(_loc: u64, code: u64) -> Ret {
    entry::exit(i32::try_from(code & 0xff).unwrap_or(0))
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_prelude_print,
        stilt_std_prelude_eprint,
        stilt_std_prelude_panic,
        stilt_std_prelude_unreachable,
        stilt_std_prelude_unwrap_failed,
        stilt_std_prelude_expect_failed,
        stilt_std_prelude_exit,
    ]
}
