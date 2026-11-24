//! The natives of `std.process` (std.process-starting, std.process-runs and std.children), on
//! the runs of [`runs`]. A command that can't start, and a write to a child that fails, raise
//! a `std.io.IoError` that names the program, or the directory that isn't one, written to the
//! memory that the caller passes a pointer to, as its last argument (`crate::abi`).

mod runs;

use runs::{Failure, Mode, Spec};

use crate::abi::{Ret, immediate, option};
use crate::object::Header;
use crate::{list, text};

/// Raises the failure: writes the error's two words, the tag of its variant and a new string
/// of the path it names, to the memory `err` points to.
///
/// # Safety
///
/// `err` points to room for two words.
unsafe fn raise((error, at): Failure, err: u64) -> Ret {
    let err = err as usize as *mut u64;
    // SAFETY: the caller guarantees the room for two words.
    unsafe {
        err.write(immediate(error as u64));
        err.add(1).write(text::from(&at));
    }
    Ret::raise(0)
}

/// The texts of a live list of strings.
///
/// # Safety
///
/// `xs` is a live list of strings, which outlives the texts.
unsafe fn texts<'a>(xs: u64) -> Vec<&'a str> {
    // SAFETY: the caller guarantees the list; each of its words is a live string.
    unsafe {
        list::words(xs as *mut Header)
            .iter()
            .map(|s| text::text(s))
            .collect()
    }
}

/// `start(program, args, set, removed, dir, mode, input)`: starts a command, run to its end
/// with `input` for `mode` 0, run to its end with the program's own streams for 1, and
/// beside the program for 2, and gives its run's number. What the program wrote reaches its
/// streams first, where the command shares them.
///
/// # Safety
///
/// `program`, `dir` and `input` are live strings, `args`, `set` and `removed` live lists of
/// strings, and `err` points to room for an error's two words.
#[unsafe(no_mangle)]
#[allow(clippy::too_many_arguments)]
pub(crate) unsafe extern "C" fn stilt_std_process_start(
    _loc: u64,
    program: u64,
    args: u64,
    set: u64,
    removed: u64,
    dir: u64,
    mode: i64,
    input: u64,
    err: u64,
) -> Ret {
    // SAFETY: the caller guarantees the strings and the lists, which outlive the call.
    let (spec, input) = unsafe {
        let spec = Spec {
            program: text::text(&program),
            args: texts(args),
            set: texts(set),
            removed: texts(removed),
            dir: text::text(&dir),
        };
        (spec, text::text(&input))
    };
    let shares = mode != 0;
    let mode = match mode {
        0 => Mode::Captured(input),
        1 => Mode::Inherited,
        _ => Mode::Piped,
    };
    if shares {
        // A run that shares the program's streams writes after what the program wrote, in
        // its turn among the tasks (tasks.same-output-under-every-handler).
        crate::tasks::turn();
        crate::io::flush();
    }
    match runs::start(&spec, mode) {
        Ok(id) => Ret::ok(id as u64),
        // SAFETY: the caller guarantees the room.
        Err(failure) => unsafe { raise(failure, err) },
    }
}

/// `waited(id)`: the run's status, once it has ended.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_process_waited(_loc: u64, id: i64) -> Ret {
    Ret::ok(runs::with(id, runs::Run::wait) as u64)
}

/// `captured(id, stream)`: what a run to its end wrote to its standard output, for 1, or its
/// standard error.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_process_captured(_loc: u64, id: i64, stream: i64) -> Ret {
    runs::with(id, |run| {
        let (out, errors) = &run.captured;
        Ret::ok(text::from(if stream == 1 { out } else { errors }))
    })
}

/// `write_input(id, text)`: writes `text` to the child's standard input.
///
/// # Safety
///
/// `s` is a live string, and `err` points to room for an error's two words.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_std_process_write_input(
    _loc: u64,
    id: i64,
    s: u64,
    err: u64,
) -> Ret {
    // SAFETY: the caller guarantees the string, which outlives the write.
    let bytes = unsafe { text::bytes(&s) };
    match runs::with(id, |run| run.write(bytes)) {
        Ok(()) => Ret::unit(),
        // SAFETY: the caller guarantees the room.
        Err(failure) => unsafe { raise(failure, err) },
    }
}

/// `close(id)`: closes the child's standard input.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_process_close(_loc: u64, id: i64) -> Ret {
    runs::with(id, runs::Run::close_input);
    Ret::unit()
}

/// `next_line(id)`: the next line of the child's standard output, or `None` at its end.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_process_next_line(_loc: u64, id: i64) -> Ret {
    let line = runs::with(id, runs::Run::read_line);
    option(line.map(|l| text::from(&l)))
}

/// `rest(id)`: the rest of the child's standard output.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_process_rest(_loc: u64, id: i64) -> Ret {
    Ret::ok(text::from(&runs::with(id, runs::Run::read_all)))
}

/// `stop(id)`: ends the child at once, unless it has ended already.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn stilt_std_process_stop(_loc: u64, id: i64) -> Ret {
    runs::with(id, runs::Run::kill);
    Ret::unit()
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![
        stilt_std_process_start,
        stilt_std_process_waited,
        stilt_std_process_captured,
        stilt_std_process_write_input,
        stilt_std_process_close,
        stilt_std_process_next_line,
        stilt_std_process_rest,
        stilt_std_process_stop,
    ]
}
