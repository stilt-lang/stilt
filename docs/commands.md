# The command line

The commands of `stilt`, the compiler and the tools around it. This page is written from `stilt`'s own help, so each command's section is what `stilt help COMMAND` prints; a test of `compiler/stilt-cli` checks that it is current.

| Command | Does |
| --- | --- |
| [`new`](#stilt-new) | Start a package in a new directory |
| [`run`](#stilt-run) | Run a program, and patch each edit of its files into it as it runs |
| [`check`](#stilt-check) | Report a program's errors and warnings |
| [`test`](#stilt-test) | Run a program's tests, doc examples and properties |
| [`build`](#stilt-build) | Build a program into an executable |
| [`fmt`](#stilt-fmt) | Format source files in place |
| [`doc`](#stilt-doc) | Write a package's documentation |
| [`show`](#stilt-show) | Show a module, a function with its inferred facts, or an error code's explanation |
| [`repl`](#stilt-repl) | Evaluate expressions in the scope of a program, as its files change |
| [`diff`](#stilt-diff) | Print the API changes between two versions of a package, and the version they need |
| [`migrate`](#stilt-migrate) | Move a package to the newest edition |
| [`reduce`](#stilt-reduce) | Write a smaller program on which a command still stops on an internal error |
| [`lsp`](#stilt-lsp) | Serve the Language Server Protocol to an editor, on stdin and stdout |

```text
Start, check, run, test, build and document Stilt programs

Usage: stilt <COMMAND>

Commands:
  new      Start a package in a new directory
  run      Run a program, and patch each edit of its files into it as it runs
  check    Report a program's errors and warnings
  test     Run a program's tests, doc examples and properties
  build    Build a program into an executable
  fmt      Format source files in place
  doc      Write a package's documentation
  show     Show a module, a function with its inferred facts, or an error code's explanation
  repl     Evaluate expressions in the scope of a program, as its files change
  diff     Print the API changes between two versions of a package, and the version they need
  migrate  Move a package to the newest edition
  reduce   Write a smaller program on which a command still stops on an internal error
  lsp      Serve the Language Server Protocol to an editor, on stdin and stdout
  help     Print this message or the help of the given subcommand(s)

Options:
  -h, --help
          Print help

  -V, --version
          Print version

Examples:
  stilt new hello            Start a package in the directory hello
  stilt run                  Run the program in the working directory
  stilt test                 Run its tests, doc examples and properties
  stilt show main.parse      Show a function with its inferred facts
  stilt help run             Show the options of a command

Diagnostics are coloured on a terminal, unless NO_COLOR is set or TERM is dumb.
With STILT_DIAGNOSTIC_LOG naming a file, `stilt check` and the language server
append to it, for each check, the code and byte span of each diagnostic, under
a hash of its file's path, with no source text.
```

## stilt new

```text
Start a package in a new directory.

It writes the package's manifest, a program with a test, and a README, or with `--lib` a library with a test and a doc example. The directory's name is the package's.

Usage: stilt new [OPTIONS] <PATH>

Arguments:
  <PATH>
          The directory, which must not exist or must be empty. Its name is the package's

Options:
      --lib
          Write a library, with no `main`

  -h, --help
          Print help (see a summary with '-h')

Examples:
  stilt new hello
  stilt new --lib sums
```

## stilt run

```text
Run a program, and patch each edit of its files into it as it runs.

The program is compiled in memory. Code with an error panics where it is reached, and a program with errors exits with status 2. Every argument after the path is the program's, `--help` among them.

Usage: stilt run [OPTIONS] [PATH] [ARGS]...

Arguments:
  [PATH]
          A source file, a directory holding a program's main.lt, or a package

          [default: .]

  [ARGS]...
          The program's arguments

Options:
      --profile
          Count, as the program runs, how often each body is entered, each arm taken, each loop's body run and each call through a function value or a dictionary reaches each function, and add the counts to the program's profile, which its release builds read. The run patches no edit

  -h, --help
          Print help (see a summary with '-h')

Examples:
  stilt run
  stilt run examples/pick -c '.rows[0]' data.json
```

## stilt check

```text
Report a program's errors and warnings.

Each diagnostic shows its place, its explanation and the fix it offers. With `--edit`, the edits are applied first, as an agent sends them.

Usage: stilt check [OPTIONS] [PATH]

Arguments:
  [PATH]
          A source file, a directory holding a program's main.lt, or a package

          [default: .]

Options:
      --json
          Print the diagnostics as one JSON object

      --edit <ADDRESS> <TEXT>
          Replace a declaration or a body, addressed by its path and hash, with a text, or with `-` the text on standard input, before checking. The option repeats

  -h, --help
          Print help (see a summary with '-h')

Examples:
  stilt check
  stilt check --json src/report.lt
```

## stilt test

```text
Run a program's tests, doc examples and properties.

A program with errors runs none, and its diagnostics come first. With `--edit`, the edits are applied first.

Usage: stilt test [OPTIONS] [PATH]

Arguments:
  [PATH]
          A source file, a directory holding a program's main.lt, or a package

          [default: .]

Options:
      --json
          Print the verdict as one JSON object

      --profile
          Count, as the tests run, what `run --profile` counts, and add the counts to the program's profile

      --edit <ADDRESS> <TEXT>
          Replace a declaration or a body, addressed by its path and hash, with a text, or with `-` the text on standard input, before testing. The option repeats

  -h, --help
          Print help (see a summary with '-h')

Examples:
  stilt test
  stilt test --json
```

## stilt build

```text
Build a program into an executable.

A program with errors is refused. A debug build compiles quickly; a release build is optimized and means the same.

Usage: stilt build [OPTIONS] <PATH>

Arguments:
  <PATH>
          A source file, a directory holding a program's main.lt, or a package

Options:
  -o, --output <OUTPUT>
          Where to write the executable. Defaults to the program's name

      --target <TARGET>
          The machine the executable runs on: aarch64-macos, x86_64-linux, aarch64-linux, or wasm32-wasip1, a WebAssembly module, NAME.wasm, that a WASI preview 1 runtime runs, which every build compiles through C, as a release build is, and which builds no library. Defaults to this one

      --release
          Build the release build: the program compiled through C by clang, optimized, which means what the debug build means and refuses a program with a hole. The first one fetches clang, unless the toolchain holds one or `STILT_CC` names one

      --lib
          Build a static library of the program's exported functions, those written `pub extern fn`, and its header, which a C program calls them by: with `-o DIR/NAME`, DIR/libNAME.a and DIR/NAME.h

  -h, --help
          Print help (see a summary with '-h')

Examples:
  stilt build . -o hello
  stilt build --release . -o hello
  stilt build --target wasm32-wasip1 .
```

## stilt fmt

```text
Format source files in place.

It formats a file, or every .lt file under a directory, prints each file it rewrote, and exits with status 1 when any file wasn't formatted or has a syntax error, which it leaves as it is.

Usage: stilt fmt [PATH]

Arguments:
  [PATH]
          A source file or a directory. Defaults to the working directory

          [default: .]

Options:
  -h, --help
          Print help (see a summary with '-h')

Example:
  stilt fmt
```

## stilt doc

```text
Write a package's documentation.

Each module has a page, with each `pub` declaration's signature, doc and examples, and each function's facts.

Usage: stilt doc [OPTIONS] [PATH]

Arguments:
  [PATH]
          A source file, a directory holding a program's main.lt, or a package

          [default: .]

Options:
  -o <DIR>
          The directory to write the pages into. Defaults to `doc` at the package's root, or in the working directory with `--std`

      --json
          Print the pages as one JSON object instead of writing them

      --std
          Document the standard library instead of a package

  -h, --help
          Print help (see a summary with '-h')

Examples:
  stilt doc
  stilt doc --json
  stilt doc --std -o std-doc
```

## stilt show

```text
Show a module, a function with its inferred facts, or an error code's explanation

Usage: stilt show [OPTIONS] <ADDRESS> [PATH]

Arguments:
  <ADDRESS>
          A diagnostic code, such as E0404; a module, such as main; or a part: a declaration by its path, such as main.totals, main.Point.norm or main.Point.Show.show, or its body, such as main.totals/body, with its hash after a `#` or without

  [PATH]
          A source file, a directory holding a program's main.lt, or a package

          [default: .]

Options:
      --json
          Print what is shown as JSON records, one per line

      --expanded
          Print each macro use's expansion in its place, each name its template binds written with `#` and a number, as `tmp#1`

      --release
          Print the release build's performance report of a function: the instantiations it is compiled for, the calls left on dictionaries, the reference counts its code still performs, the checks proved and kept, and the lines of the profile it dropped

  -h, --help
          Print help

Examples:
  stilt show main
  stilt show main.parse
  stilt show --release main.parse
  stilt show E0204
```

## stilt repl

```text
Evaluate expressions in the scope of a program, as its files change.

Each line of standard input is an expression or a `let`, in the scope of the program in the working directory.

Usage: stilt repl

Options:
  -h, --help
          Print help (see a summary with '-h')
```

## stilt diff

```text
Print the API changes between two versions of a package, and the version they need.

Each change is printed with the change of version number it needs, then the change they need together, as the check of a version before it is written into a manifest computes them.

Usage: stilt diff [OPTIONS] <OLD> <NEW>

Arguments:
  <OLD>
          The earlier version's package directory

  <NEW>
          The later version's package directory

Options:
      --from <VERSION>
          The version that NEW follows, to print the number NEW needs

  -h, --help
          Print help (see a summary with '-h')

Example:
  stilt diff ../sums-1.4.2 . --from 1.4.2
```

## stilt migrate

```text
Move a package to the newest edition.

It rewrites each method that an edition renames, writes the edition into stilt.toml, and checks the package again. A package with errors is left as it is.

Usage: stilt migrate [PATH]

Arguments:
  [PATH]
          A package's directory. Defaults to the working directory

          [default: .]

Options:
  -h, --help
          Print help (see a summary with '-h')
```

## stilt reduce

```text
Write a smaller program on which a command still stops on an internal error.

It reruns the command on smaller and smaller copies of the program the command names, each in a process of its own, keeping each copy on which it still stops at the same place in stilt's code, and writes the smallest, with a report, to attach to the bug.

Usage: stilt reduce [OPTIONS] <COMMAND>...

Arguments:
  <COMMAND>...
          The command that stopped, as it was given to stilt, such as `check main.lt`

Options:
  -o <DIR>
          The directory to write the program and its report into

          [default: stilt-bug]

  -h, --help
          Print help (see a summary with '-h')
```

## stilt lsp

```text
Serve the Language Server Protocol to an editor, on stdin and stdout

Usage: stilt lsp

Options:
  -h, --help
          Print help
```
