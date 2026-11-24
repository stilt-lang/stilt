//! Running a program: its entry, how it ends, and its exit status (program.exit-statuses and
//! program.recursion-depth).
//!
//! The program runs on a thread of its own, whose stack of [`STACK`] bytes, or a smaller one where the system grants
//! less ([`crate::stacks`]), holds far more than the
//! 10,000 frames that program.recursion-depth requires, as does every thread that runs its code.
//! Running past the end of such a stack is caught by a handler of the fault it causes, on a stack
//! of its own, which reports it and aborts with status 134.

#[cfg(not(target_family = "wasm"))]
use std::cell::{Cell, RefCell};
use std::io::Write;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::abi::Ret;
#[cfg(not(target_family = "wasm"))]
use crate::stacks::STACK;
use crate::watch::{self, Ended};
use crate::{io, object, panic, text};

/// The compiled entry of a program: it runs `main`, shows the error that escapes it, if one
/// does, and releases the program's constants. It returns the error's text, with `raised` set,
/// or nothing.
pub type Entry = unsafe extern "C" fn(u64) -> Ret;

/// The exit status of a debug build that ends with objects still referenced, against
/// goal no-leaks: no test expects it.
const LEAKED: i32 = 70;

/// Whether the program has errors, so that it ends with status 2 however it ends
/// (program.programs-with-errors).
static WITH_ERRORS: AtomicBool = AtomicBool::new(false);

/// The exit status of a program with errors.
const WITH_ERRORS_STATUS: i32 = 2;

/// What the runtime needs to run a program.
#[derive(Debug)]
pub struct Program {
    /// The entry, compiled.
    pub entry: Entry,
    /// The paths of the program's files, by the indexes its locations use.
    pub files: Vec<String>,
    /// The arguments of the program, without its name.
    pub args: Vec<String>,
    /// Whether to check, when the program ends, that it released every object.
    pub check_leaks: bool,
    /// Whether the program has errors, whose code panics where it is reached: it then exits
    /// with status 2 however it ends (program.programs-with-errors).
    pub with_errors: bool,
}

/// The exit status of a program that ends with `status`: 2 for a program with errors.
pub(crate) fn status(status: i32) -> i32 {
    if WITH_ERRORS.load(Ordering::Relaxed) {
        WITH_ERRORS_STATUS
    } else {
        status
    }
}

/// Runs a program to its end, and returns its exit status. A panic, a call of `exit`, a stack
/// overflow and running out of memory end the process instead.
///
/// # Panics
///
/// Panics when the system can't start the thread the program runs on.
#[must_use]
pub fn run(program: Program) -> i32 {
    let entry = program.entry;
    let check_leaks = program.check_leaks;
    prepare(program);
    // WebAssembly runs one thread, whose stack is the module's own (wasm.limits).
    #[cfg(target_family = "wasm")]
    let status = run_main(entry, check_leaks);
    #[cfg(not(target_family = "wasm"))]
    let status = crate::stacks::spawn("main", move || run_main(entry, check_leaks))
        .expect("a thread for the program")
        .join()
        .unwrap_or(LEAKED);
    io::flush();
    self::status(status)
}

/// Ends the process with `status`, once its output is written: on WebAssembly a status of 134
/// is a trap.
pub(crate) fn exit_process(status: i32) -> ! {
    #[cfg(target_family = "wasm")]
    crate::wasm::end(status);
    #[cfg(not(target_family = "wasm"))]
    std::process::exit(status)
}

/// The start of a program that `stilt build` linked: its C `main` passes its arguments' count
/// and vector, its compiled entry, the paths of its files, each ended by a NUL and the whole by
/// an empty one, and `counts`, which a debug build sets and a release build doesn't. It runs
/// the program, checking at its end that every count is back to zero if `counts` is set
/// (goal no-leaks; cycles.check-at-exit), and returns the exit status.
///
/// # Safety
///
/// `vector` holds `count` C strings, `entry` was compiled as an [`Entry`], and `files` is a
/// table as above.
#[unsafe(no_mangle)]
pub(crate) unsafe extern "C" fn stilt_rt_start(
    count: u64,
    vector: u64,
    entry: u64,
    files: u64,
    counts: u64,
) -> u64 {
    let vector = vector as usize as *const *const libc::c_char;
    let files = files as usize as *const libc::c_char;
    // SAFETY: the caller guarantees `entry` is the address of an `Entry`.
    let entry: Entry = unsafe { std::mem::transmute(entry as usize) };
    // SAFETY: the caller guarantees `vector` holds `count` C strings.
    let program_args = (1..count as usize)
        .map(|i| unsafe { std::ffi::CStr::from_ptr(*vector.add(i)) })
        .map(|arg| String::from_utf8_lossy(arg.to_bytes()).into_owned())
        .collect();
    // SAFETY: the caller guarantees `files` is such a table.
    let paths = unsafe { file_table(files) };
    let status = run(Program {
        entry,
        files: paths,
        args: program_args,
        check_leaks: counts != 0,
        with_errors: false,
    });
    u64::try_from(status).unwrap_or(1)
}

/// The paths of a table of the program's files, each ended by a NUL and the whole by an empty
/// one, as compiled code passes it.
///
/// # Safety
///
/// `files` is such a table.
pub(crate) unsafe fn file_table(files: *const libc::c_char) -> Vec<String> {
    let mut paths = Vec::new();
    let mut at = files;
    loop {
        // SAFETY: the caller guarantees the table is NUL-ended strings, ended by an empty one.
        let path = unsafe { std::ffi::CStr::from_ptr(at) };
        if path.is_empty() {
            break;
        }
        paths.push(path.to_string_lossy().into_owned());
        // SAFETY: as above; the next string starts after this one's NUL.
        at = unsafe { at.add(path.to_bytes().len() + 1) };
    }
    paths
}

/// The functions of this module that compiled code calls, by name.
pub(crate) fn symbols() -> Vec<(&'static str, *const u8)> {
    crate::exports![stilt_rt_start]
}

/// Registers what reports name, and the program's arguments, catches stack overflows, and
/// lets a write to a closed standard output fail rather than end the process, so that the
/// program ends with the status of program.exit-statuses (`crate::io`).
pub(crate) fn prepare(program: Program) {
    #[cfg(any(stilt_sanitizers, stilt_tsan))]
    crate::sanitizers::keep();
    WITH_ERRORS.store(program.with_errors, Ordering::Relaxed);
    panic::set_files(program.files);
    io::set_args(program.args);
    #[cfg(not(target_family = "wasm"))]
    catch_overflow();
    #[cfg(unix)]
    // SAFETY: setting a signal's disposition to "ignore" installs no handler, and a child the
    // program starts gets the default back, as `Command` resets it in each.
    unsafe {
        libc::signal(libc::SIGPIPE, libc::SIG_IGN);
    }
    #[cfg(target_family = "wasm")]
    crate::wasm::prepare();
}

/// Prepares this process to run the tests of a program without errors, whose files have the paths
/// `files` (program.running-tests): what they print goes to standard error, and running out of
/// memory ends the process, as a stack overflow does, so that no test reports a result.
pub fn prepare_tests(files: Vec<String>) {
    TESTING.store(true, Ordering::Relaxed);
    io::print_to_stderr();
    prepare(Program {
        entry: no_entry,
        files,
        args: Vec::new(),
        check_leaks: false,
        with_errors: false,
    });
}

/// The entry of a process that runs tests or inputs, each of which has its own.
pub(crate) extern "C" fn no_entry(_: u64) -> Ret {
    Ret::ok(0)
}

/// Whether the process runs tests, which a fatal error ends at once (program.running-tests).
static TESTING: AtomicBool = AtomicBool::new(false);

/// Starts running compiled code on the current thread, whose stack overflow the fault handler
/// then reports.
pub(crate) fn enter() {
    crate::pool::own();
    #[cfg(not(target_family = "wasm"))]
    {
        let top = 0u8;
        STACK_TOP.set(std::ptr::from_ref(&top) as usize);
        install_alternate_stack();
    }
}

/// Runs a program's entry on the current thread, and returns its exit status.
pub(crate) fn run_main(entry: Entry, check_leaks: bool) -> i32 {
    enter();
    // SAFETY: the compiler compiled `entry` with the signature `Entry`.
    let ended = unsafe { entry(0) };
    let status = if ended.raised == 0 {
        0
    } else {
        // program.exit-statuses: a raise that escapes `main`.
        io::flush();
        // SAFETY: the entry returns the error's text as a string it owns.
        let message = unsafe { text::bytes(&ended.value) };
        let mut line = b"error: ".to_vec();
        line.extend_from_slice(message);
        io::eprint(&line);
        // SAFETY: as above, the string is owned here.
        unsafe { object::drop(ended.value) };
        1
    };
    if std::env::var_os("STILT_COUNTS").is_some() {
        io::flush();
        let _ = writeln!(std::io::stderr(), "stilt: boxes {}", object::boxes());
    }
    match leaked().filter(|_| check_leaks) {
        Some(leaked) => leaked,
        None => status,
    }
}

/// Checks that every count is back to zero, once the program has ended, or once every test that
/// ran passed and the constants are released (goal no-leaks), after collecting the cycles that
/// nothing reaches (cycles.freeing and cycles.check-at-exit): reports the objects that were never
/// freed, the toolchain's bug, and gives the exit status of a debug build that leaks, if there are
/// any. While code that the sequential run never reaches holds a thread, it checks nothing.
#[must_use]
pub fn leaked() -> Option<i32> {
    // : what a thread of code that the sequential run never reaches still holds
    // can't be told from a leak, so the check isn't made, and nothing is said of it, since the
    // program's output is the sequential run's.
    if crate::tasks::unreached_threads() > 0 {
        return None;
    }
    object::collect_at_end();
    let leaked = object::live_objects();
    if leaked == 0 {
        return None;
    }
    io::flush();
    let _ = writeln!(
        std::io::stderr(),
        "stilt: internal error: {leaked} objects were never freed"
    );
    Some(LEAKED)
}

/// Releases a word of a constant's value that a compiled program computed, once no code of the
/// program runs, so that a check of the counts finds it freed.
///
/// # Safety
///
/// `word` is a heap word that owns one reference to its object, if it has one, and nothing reads
/// it after.
pub unsafe fn release(word: u64) {
    // SAFETY: as the caller guarantees.
    unsafe { object::drop(word) }
}

/// Ends the program because it ran out of a resource (program.exit-statuses), and under `stilt
/// test` the process, since it ends every test (program.running-tests).
pub(crate) fn fatal(reason: &str) -> ! {
    crate::workers::end(|| crate::workers::Ending::Fatal(reason.to_owned()));
    crate::tasks::turn();
    io::flush();
    let _ = writeln!(std::io::stderr(), "fatal: {reason}");
    if TESTING.load(Ordering::Relaxed) {
        exit_process(134);
    }
    watch::end(Ended::Status(134))
}

/// Ends the program with status `code`, once its output is written (program.output-flushing).
pub(crate) fn exit(code: i32) -> ! {
    crate::tasks::turn();
    watch::end(Ended::Status(code))
}

#[cfg(not(target_family = "wasm"))]
/// The stack the fault handler of a thread runs on, which the thread keeps until it ends,
/// when it unregisters the stack and gives back its memory.
struct AlternateStack(#[expect(dead_code, reason = "the memory the kernel uses")] Box<[u8]>);

#[cfg(not(target_family = "wasm"))]
impl Drop for AlternateStack {
    fn drop(&mut self) {
        let off = libc::stack_t {
            ss_sp: std::ptr::null_mut(),
            ss_flags: libc::SS_DISABLE,
            ss_size: 0,
        };
        // SAFETY: disabling a thread's alternate stack has no preconditions.
        unsafe { libc::sigaltstack(&raw const off, std::ptr::null_mut()) };
    }
}

#[cfg(not(target_family = "wasm"))]
thread_local! {
    static ALTERNATE: RefCell<Option<AlternateStack>> = const { RefCell::new(None) };
    /// The highest address of the current thread's stack, which the fault handler compares
    /// with, set before the thread runs compiled code, so that the handler reads it without
    /// making it.
    static STACK_TOP: Cell<usize> = const { Cell::new(0) };
}

#[cfg(not(target_family = "wasm"))]
/// Gives the program's thread a stack for the fault handler, which can't run on the stack
/// that overflowed.
fn install_alternate_stack() {
    const SIZE: usize = 64 * 1024;
    let mut memory = vec![0u8; SIZE].into_boxed_slice();
    let stack = libc::stack_t {
        ss_sp: memory.as_mut_ptr().cast(),
        ss_flags: 0,
        ss_size: SIZE,
    };
    // SAFETY: `stack` describes memory that the thread keeps until it ends, when it
    // unregisters the stack before giving the memory back.
    unsafe { libc::sigaltstack(&raw const stack, std::ptr::null_mut()) };
    ALTERNATE.with_borrow_mut(|alternate| *alternate = Some(AlternateStack(memory)));
}

#[cfg(not(target_family = "wasm"))]
/// Installs the handler of the faults that running past the end of a stack causes.
fn catch_overflow() {
    // SAFETY: the handler only calls async-signal-safe functions, and the action is set up as
    // `sigaction` requires.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = on_fault as *const () as usize;
        action.sa_flags = libc::SA_SIGINFO | libc::SA_ONSTACK;
        libc::sigemptyset(&raw mut action.sa_mask);
        libc::sigaction(libc::SIGSEGV, &raw const action, std::ptr::null_mut());
        libc::sigaction(libc::SIGBUS, &raw const action, std::ptr::null_mut());
    }
}

#[cfg(not(target_family = "wasm"))]
extern "C" fn on_fault(signal: libc::c_int, info: *mut libc::siginfo_t, _: *mut libc::c_void) {
    // SAFETY: the kernel passes a valid `siginfo_t` to a handler installed with `SA_SIGINFO`.
    let address = unsafe { (*info).si_addr() } as usize;
    let top = STACK_TOP.with(Cell::get);
    let guard = 16 * 1024 * 1024;
    if address < top && address + STACK + guard >= top {
        // A task's report waits for its turn, as a panic does.
        crate::tasks::fault_turn();
        let message = b"fatal: stack overflow\n";
        // An atomic load is async-signal-safe.
        let code = status(134);
        // SAFETY: `write` and `_exit` are async-signal-safe.
        unsafe {
            libc::write(2, message.as_ptr().cast(), message.len());
            libc::_exit(code);
        }
    }
    // Any other fault is the runtime's own bug: let it end the process as it would have.
    // SAFETY: restoring the default action and raising the signal again are async-signal-safe.
    unsafe {
        libc::signal(signal, libc::SIG_DFL);
        libc::raise(signal);
    }
}
