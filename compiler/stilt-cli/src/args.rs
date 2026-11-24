//! The command line of `stilt`: its commands, in the order a newcomer meets them, each with a
//! one-line summary, its arguments and examples. `parse` and `engine` serve tools, and the
//! help leaves them out.

use std::ffi::OsString;
use std::path::PathBuf;

use clap::{Parser, Subcommand};
use stilt_codegen_clif::Target;

#[cfg(test)]
mod page;
pub(crate) mod shells;

/// Start, check, run, test, build and document Stilt programs.
#[derive(Debug, Parser)]
#[command(
    name = "stilt",
    version = env!("STILT_VERSION"),
    after_help = "Examples:
  stilt new hello            Start a package in the directory hello
  stilt run                  Run the program in the working directory
  stilt test                 Run its tests, doc examples and properties
  stilt show main.parse      Show a function with its inferred facts
  stilt help run             Show the options of a command

Diagnostics are coloured on a terminal, unless NO_COLOR is set or TERM is dumb.
With STILT_DIAGNOSTIC_LOG naming a file, `stilt check` and the language server
append to it, for each check, the code and byte span of each diagnostic, under
a hash of its file's path, with no source text."
)]
pub(crate) struct Args {
    #[command(subcommand)]
    pub(crate) command: Command,
}

/// A path's help: what it may name, and its default.
const PROGRAM: &str = "A source file, a directory holding a program's main.lt, or a package";

#[derive(Debug, Subcommand)]
pub(crate) enum Command {
    /// Start a package in a new directory.
    ///
    /// It writes the package's manifest, a program with a test, and a README, or with `--lib`
    /// a library with a test and a doc example. The directory's name is the package's.
    #[command(after_help = "Examples:\n  stilt new hello\n  stilt new --lib sums")]
    New {
        /// Write a library, with no `main`.
        #[arg(long)]
        lib: bool,
        /// The directory, which must not exist or must be empty. Its name is the package's.
        path: PathBuf,
    },
    /// Run a program, and patch each edit of its files into it as it runs.
    ///
    /// The program is compiled in memory. Code with an error panics where it is reached, and a
    /// program with errors exits with status 2. Every argument after the path is the program's,
    /// `--help` among them.
    #[command(
        after_help = "Examples:\n  stilt run\n  stilt run examples/pick -c '.rows[0]' data.json"
    )]
    Run {
        /// Count, as the program runs, how often each body is entered, each arm taken, each
        /// loop's body run and each call through a function value or a dictionary reaches each
        /// function, and add the counts to the program's profile, which its release builds read.
        /// The run patches no edit.
        #[arg(long)]
        profile: bool,
        #[arg(default_value = ".", help = PROGRAM)]
        path: PathBuf,
        /// The program's arguments.
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<OsString>,
    },
    /// Report a program's errors and warnings.
    ///
    /// Each diagnostic shows its place, its explanation and the fix it offers. With `--edit`,
    /// the edits are applied first, as an agent sends them.
    #[command(after_help = "Examples:\n  stilt check\n  stilt check --json src/report.lt")]
    Check {
        /// Print the diagnostics as one JSON object.
        #[arg(long)]
        json: bool,
        /// Replace a declaration or a body, addressed by its path and hash, with a text, or
        /// with `-` the text on standard input, before checking. The option repeats.
        #[arg(long, num_args = 2, value_names = ["ADDRESS", "TEXT"], allow_hyphen_values = true)]
        edit: Vec<String>,
        #[arg(default_value = ".", help = PROGRAM)]
        path: PathBuf,
    },
    /// Run a program's tests, doc examples and properties.
    ///
    /// A program with errors runs none, and its diagnostics come first. With `--edit`, the
    /// edits are applied first.
    #[command(after_help = "Examples:\n  stilt test\n  stilt test --json")]
    Test {
        /// Print the verdict as one JSON object.
        #[arg(long)]
        json: bool,
        /// Run the standard library's own tests and doc examples instead of the program's.
        #[arg(long, hide = true)]
        std: bool,
        /// Count, as the tests run, what `run --profile` counts, and add the counts to the
        /// program's profile.
        #[arg(long, conflicts_with = "std")]
        profile: bool,
        /// Replace a declaration or a body, addressed by its path and hash, with a text, or
        /// with `-` the text on standard input, before testing. The option repeats.
        #[arg(long, num_args = 2, value_names = ["ADDRESS", "TEXT"], allow_hyphen_values = true)]
        edit: Vec<String>,
        #[arg(default_value = ".", help = PROGRAM)]
        path: PathBuf,
    },
    /// Build a program into an executable.
    ///
    /// A program with errors is refused. A debug build compiles quickly; a release build is
    /// optimized and means the same.
    #[command(after_help = "Examples:
  stilt build . -o hello
  stilt build --release . -o hello
  stilt build --target wasm32-wasip1 .")]
    Build {
        /// Where to write the executable. Defaults to the program's name.
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// The machine the executable runs on: aarch64-macos, x86_64-linux, aarch64-linux, or wasm32-wasip1,
        /// a WebAssembly module, NAME.wasm, that a WASI preview 1 runtime runs, which every build
        /// compiles through C, as a release build is, and which builds no library. Defaults to
        /// this one.
        #[arg(long, value_parser = target)]
        target: Option<Target>,
        /// Build the release build: the program compiled through C by clang, optimized, which
        /// means what the debug build means and refuses a program with a hole. The first one
        /// fetches clang, unless the toolchain holds one or `STILT_CC` names one.
        #[arg(long)]
        release: bool,
        /// Build a static library of the program's exported functions, those written `pub
        /// extern fn`, and its header, which a C program calls them by: with `-o DIR/NAME`,
        /// DIR/libNAME.a and DIR/NAME.h.
        #[arg(long)]
        lib: bool,
        #[arg(help = PROGRAM)]
        path: PathBuf,
    },
    /// Format source files in place.
    ///
    /// It formats a file, or every .lt file under a directory, prints each file it rewrote,
    /// and exits with status 1 when any file wasn't formatted or has a syntax error, which it
    /// leaves as it is.
    #[command(after_help = "Example:\n  stilt fmt")]
    Fmt {
        /// A source file or a directory. Defaults to the working directory.
        #[arg(default_value = ".")]
        path: PathBuf,
    },
    /// Write a package's documentation.
    ///
    /// Each module has a page, with each `pub` declaration's signature, doc and examples, and
    /// each function's facts.
    #[command(
        after_help = "Examples:\n  stilt doc\n  stilt doc --json\n  stilt doc --std -o std-doc"
    )]
    Doc {
        /// The directory to write the pages into. Defaults to `doc` at the package's root, or
        /// in the working directory with `--std`.
        #[arg(short, value_name = "DIR")]
        o: Option<PathBuf>,
        /// Print the pages as one JSON object instead of writing them.
        #[arg(long)]
        json: bool,
        /// Document the standard library instead of a package.
        #[arg(long, conflicts_with = "path")]
        std: bool,
        #[arg(default_value = ".", help = PROGRAM)]
        path: PathBuf,
    },
    /// Show a module, a function with its inferred facts, or an error code's explanation.
    #[command(after_help = "Examples:
  stilt show main
  stilt show main.parse
  stilt show --release main.parse
  stilt show E0204")]
    Show {
        /// Print what is shown as JSON records, one per line.
        #[arg(long)]
        json: bool,
        /// Print each macro use's expansion in its place, each name its template binds written
        /// with `#` and a number, as `tmp#1`.
        #[arg(long)]
        expanded: bool,
        /// Print the release build's performance report of a function: the instantiations it
        /// is compiled for, the calls left on dictionaries, the reference counts its code still
        /// performs, the checks proved and kept, and the lines of the profile it dropped.
        #[arg(long, conflicts_with = "expanded")]
        release: bool,
        /// A diagnostic code, such as E0404; a module, such as main; or a part: a declaration by
        /// its path, such as main.totals, main.Point.norm or main.Point.Show.show, or its body,
        /// such as main.totals/body, with its hash after a `#` or without.
        address: String,
        #[arg(default_value = ".", help = PROGRAM)]
        path: PathBuf,
    },
    /// Evaluate expressions in the scope of a program, as its files change.
    ///
    /// Each line of standard input is an expression or a `let`, in the scope of the program
    /// in the working directory.
    Repl,
    /// Print the API changes between two versions of a package, and the version they need.
    ///
    /// Each change is printed with the change of version number it needs, then the change
    /// they need together, as the check of a version before it is written into a manifest
    /// computes them.
    #[command(after_help = "Example:\n  stilt diff ../sums-1.4.2 . --from 1.4.2")]
    Diff {
        /// The version that NEW follows, to print the number NEW needs.
        #[arg(long, value_name = "VERSION")]
        from: Option<String>,
        /// The earlier version's package directory.
        old: PathBuf,
        /// The later version's package directory.
        new: PathBuf,
    },
    /// Move a package to the newest edition.
    ///
    /// It rewrites each method that an edition renames, writes the edition into stilt.toml,
    /// and checks the package again. A package with errors is left as it is.
    Migrate {
        /// A package's directory. Defaults to the working directory.
        #[arg(default_value = ".")]
        path: PathBuf,
    },
    /// Write a smaller program on which a command still stops on an internal error.
    ///
    /// It reruns the command on smaller and smaller copies of the program the command names,
    /// each in a process of its own, keeping each copy on which it still stops at the same place
    /// in stilt's code, and writes the smallest, with a report, to attach to the bug.
    Reduce {
        /// The directory to write the program and its report into.
        #[arg(short = 'o', value_name = "DIR", default_value = "stilt-bug")]
        o: PathBuf,
        /// The command that stopped, as it was given to stilt, such as `check main.lt`.
        #[arg(required = true, trailing_var_arg = true, allow_hyphen_values = true)]
        command: Vec<String>,
    },
    /// Serve the Language Server Protocol to an editor, on stdin and stdout.
    Lsp,
    /// Print the syntax tree of a program.
    #[command(hide = true)]
    Parse {
        /// Print each file's syntax tree as an S-expression.
        #[arg(long, required = true)]
        sexp: bool,
        #[arg(help = PROGRAM)]
        path: PathBuf,
    },
    /// Print the completions of `stilt`'s commands and options for a shell, as its scripts
    /// load them: `stilt completions zsh > _stilt`.
    #[command(hide = true)]
    Completions {
        /// The shell: bash, elvish, fish, powershell or zsh.
        shell: clap_complete::Shell,
    },
    /// Write a manual page for `stilt` and one for each of its commands into a directory.
    #[command(hide = true)]
    Manual {
        /// The directory, made if it doesn't exist, as `share/man/man1`.
        dir: PathBuf,
    },
    /// Hold a program's query database in this process, and answer the commands that check,
    /// build and run it, until no command has come for a while.
    #[command(hide = true)]
    Engine {
        /// Stop the program's engine, if one runs, and exit with status 1 if none does.
        #[arg(long, conflicts_with = "ran")]
        stop: bool,
        /// Print the queries the program's engine has run since this was last asked, if it
        /// keeps a record of them.
        #[arg(long)]
        ran: bool,
        /// Keep a record of the queries this engine runs, for `--ran`.
        #[arg(long, conflicts_with_all = ["stop", "ran"])]
        record: bool,
        /// How many seconds without a command the engine waits before it stops.
        #[arg(long, default_value_t = crate::engine::IDLE)]
        idle: u64,
        #[arg(help = PROGRAM)]
        path: PathBuf,
    },
}

/// The target `name` names, for `--target`.
fn target(name: &str) -> Result<Target, String> {
    Target::from_name(name).ok_or_else(|| {
        let names: Vec<&str> = Target::ALL.iter().map(|t| t.name()).collect();
        let (last, rest) = names.split_last().unwrap_or((&"", &[]));
        format!("the targets are {} and {last}", rest.join(", "))
    })
}

/// The command line, with `--` after the path of `run`, so that every argument after the path
/// is the program's, even one that `run` itself would read, as `--help`.
pub(crate) fn program_arguments(args: impl Iterator<Item = OsString>) -> Vec<OsString> {
    let mut args: Vec<_> = args.collect();
    if args.get(1).is_some_and(|a| a == "run") {
        let path = (2..args.len()).find(|&i| !args[i].to_string_lossy().starts_with('-'));
        if let Some(i) = path
            && args.get(i + 1).is_some_and(|a| a != "--")
        {
            args.insert(i + 1, "--".into());
        }
    }
    args
}
