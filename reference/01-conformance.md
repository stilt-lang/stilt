# 1. Conformance

A conforming implementation of Stilt gives, for every program, what the conformance suite and the reference interpreter give. This chapter defines what an implementation is judged on, and the command-line protocol through which the suite drives it. It also defines the annotations with which each test states what it expects, and where tests live and run. [Programs with errors](18-errors.md) says which diagnostics a program reports. [Programs, modules and packages](04-programs.md) says how a program ends, and which reports it writes then.

## Implementations

<a id="conformance.implementations"></a>
An implementation of Stilt is judged against the **conformance suite**: a set of programs, each annotated with what an implementation must give for it. It is also judged against the reference interpreter: both run the same programs, and what each gives is compared. Both comparisons go through the command-line protocol of this chapter, and look only at the observables it defines ([conformance.observables](#conformance.observables)). An implementation takes part in both by providing the four commands of [conformance.commands](#conformance.commands).

Checked by: the conformance runner (`tools/runner/`), which runs the suite against an implementation, and runs the suite and generated programs under two implementations and compares them.

<a id="conformance.tiers"></a>
The conformance suite is divided by tier ([program.tiers](04-programs.md#program.tiers)). Each test belongs to one tier: `core`, unless its header names another ([conformance.header-annotations](#conformance.header-annotations)). The suite of a tier holds the tests of that tier and of the tiers before it. An implementation that supports the tiers up to one of them is tested by that tier's suite. A test's tier only selects the test. The tier of each of its modules is inferred from the features that the module uses ([program.module-tier](04-programs.md#program.module-tier)). A feature of a tier that an implementation doesn't support is E0203, *feature of an unsupported tier* ([program.unsupported-tiers](04-programs.md#program.unsupported-tiers)).

Checked by: the conformance runner, whose `--tier` runs the suite of one tier (`tools/runner/src/main.rs`).

## What is observable

<a id="conformance.observables"></a>
An implementation is judged only on these **observables**:

- its **diagnostics**, each given as a code, a file and a line ([conformance.diagnostic-objects](#conformance.diagnostic-objects));
- what `run` gives, whether or not the program has errors: its standard output, compared byte for byte, and its exit status;
- when a test asks for them, the standard error of `run`, or the panic report that ends it ([program.panic-report](04-programs.md#program.panic-report));
- for a program that has no errors, what `test` gives: whether each test, doc example and property passed.

Tests: [protocol/byte_exact_output.lt](../conformance/protocol/byte_exact_output.lt), [protocol/nested_file_paths](../conformance/protocol/nested_file_paths/), [protocol/run_prints_only_program_output.lt](../conformance/protocol/run_prints_only_program_output.lt).

<a id="conformance.diagnostic-text"></a>
Conformance never compares the text of a diagnostic. It looks only at the diagnostic's code, file and line. The wording of its message, its labelled spans and its fixes are each implementation's own. The toolchain checks its own with a snapshot of each code's rendering.

Checked by: the conformance runner, which reads only the `code`, `file` and `line` of each diagnostic (`tools/runner/src/protocol.rs`), and the snapshots of `tests/diagnostics/`, which `just diagnostics` checks.

<a id="conformance.diagnostic-lines"></a>
The **line** of a diagnostic is the 1-based line on which its primary span starts. Its file is the file that holds that span. The registry of codes, [`errors.toml`](errors.toml), gives each code's primary span ([errors.primary-spans](18-errors.md#errors.primary-spans)). An error that involves several places is reported at one of them ([errors.several-places](18-errors.md#errors.several-places)).

Tests: [lexical/end_of_file_error.lt](../conformance/lexical/end_of_file_error.lt), [protocol/primary_span_start_line.lt](../conformance/protocol/primary_span_start_line.lt).

<a id="conformance.determinism"></a>
An implementation is deterministic: two runs of the same test give identical observables.

Checked by: every test of the suite, whose observables must be the expected ones on every run.

## The command-line protocol

<a id="conformance.commands"></a>
Every implementation under test provides these four commands, where `IMPL` names the implementation:

| Command | Output |
| --- | --- |
| `IMPL check --json PATH` | A JSON object `{"diagnostics": [D, …]}` on stdout. Exit status 0 if there are no errors, 1 otherwise |
| `IMPL run PATH [ARGS...]` | Runs the program. Its stdout, stderr and exit status are observables |
| `IMPL test --json PATH` | A JSON object `{"diagnostics": [D, …], "tests": [T, …]}` on stdout, and nothing else. Exit status 0 if there are no errors and every test passes, 1 otherwise. A stack overflow or running out of memory ends it as it ends `run` ([program.test-results](04-programs.md#program.test-results)) |
| `IMPL parse --sexp PATH` | The syntax tree of each file as an S-expression, in the tree form of [syntax.tree-form](03-syntax.md#syntax.tree-form), for comparing two implementations' parsers |

Tests: [protocol/args_and_stdin.lt](../conformance/protocol/args_and_stdin.lt), [protocol/run_prints_only_program_output.lt](../conformance/protocol/run_prints_only_program_output.lt), [protocol/test_lines.lt](../conformance/protocol/test_lines.lt).

Checked by: also the runner's own tests of reports whose status contradicts their diagnostics or results (`tools/runner/src/protocol.rs`), and `just parse`, which compares the trees of two implementations.

<a id="conformance.diagnostic-objects"></a>
Each diagnostic `D` that `check --json` and `test --json` write is an object. It has at least the fields `code`, `file` and `line` ([conformance.diagnostic-lines](#conformance.diagnostic-lines)), as in `{"code": "E0404", "file": "main.lt", "line": 14}`.

Tests: [protocol/nested_file_paths](../conformance/protocol/nested_file_paths/), [protocol/several_entries_on_one_line.lt](../conformance/protocol/several_entries_on_one_line.lt).

<a id="conformance.test-objects"></a>
Each test result `T` that `test --json` writes is an object. It has at least the fields `file`, `line` and `passed`, which is `true` or `false`. Its line is that of the `test` keyword, or of the `/// ex:` or `/// prop:` comment ([program.doc-examples](04-programs.md#program.doc-examples), [tests.property-results](19-tools.md#tests.property-results)). If the program has errors, no test runs, and `tests` is empty.

Tests: [protocol/test_lines.lt](../conformance/protocol/test_lines.lt), [protocol/tests_in_nested_module](../conformance/protocol/tests_in_nested_module/).

Checked by: also the runner's own tests of a report that lists tests after errors (`tools/runner/src/protocol.rs`).

<a id="conformance.extra-fields"></a>
An implementation may add fields to any of these objects, and the runner ignores them. Among the fields it ignores are the message, the spans and the fixes of the compiler's diagnostic objects, and the `property` object of a property's result ([tests.property-verdict](19-tools.md#tests.property-verdict)).

Checked by: the runner's own tests of reports with fields of their own (`tools/runner/src/protocol.rs`).

<a id="conformance.run-output"></a>
`run` writes to stdout only what the program writes. It writes these to stderr:

- what the program writes;
- the packages it fetched ([packages.fetch-report](04-programs.md#packages.fetch-report));
- the program's diagnostics, before it runs a program that has errors ([program.programs-with-errors](04-programs.md#program.programs-with-errors));
- the reports that end a program ([program.exit-statuses](04-programs.md#program.exit-statuses), [program.panic-report](04-programs.md#program.panic-report)).

Check tests and run tests get a program's diagnostics from `check --json`, never from what `run` writes.

Tests: [protocol/run_prints_only_program_output.lt](../conformance/protocol/run_prints_only_program_output.lt).

<a id="conformance.run-statuses"></a>
`run` runs a program that has errors, and then exits with status 2 however the program ends ([program.programs-with-errors](04-programs.md#program.programs-with-errors)). It also exits with status 2, without running anything, when the program has no `main` ([program.missing-main](04-programs.md#program.missing-main)). Otherwise the exit status is the program's own ([program.exit-statuses](04-programs.md#program.exit-statuses)).

Tests: [program/error_never_reached.lt](../conformance/program/error_never_reached.lt), [program/run_with_warnings.lt](../conformance/program/run_with_warnings.lt), [protocol/main_in_other_module](../conformance/protocol/main_in_other_module/).

<a id="conformance.load-errors"></a>
If `PATH` names no program, or one of the program's files can't be read, every command ends with a message on stderr. Its exit status is then neither 0 nor 1. No verdict of `check` or `test` is read from such a run. The status is the implementation's own, and no conformance test expects one.

Checked by: each implementation's own tests, of a missing path and of a `stilt.toml` that is a directory (`compiler/stilt-cli/tests/build.rs`, `interpreter/test/test_program.ml`).

<a id="conformance.paths"></a>
`PATH` is a single `.lt` file or a directory test ([conformance.directory-tests](#conformance.directory-tests)). For a single file, the **working directory** is the directory that holds the file. For a directory test, it is the test's directory. `PATH` and every `file` that an implementation reports are relative to the working directory, and use `/` as the separator ([program.report-paths](04-programs.md#program.report-paths)).

Tests: [protocol/nested_file_paths](../conformance/protocol/nested_file_paths/), [protocol/tests_in_nested_module](../conformance/protocol/tests_in_nested_module/), [protocol/working_directory.lt](../conformance/protocol/working_directory.lt).

## Annotations

<a id="conformance.annotations"></a>
A test states what it expects in **annotations**. An annotation is a line comment that starts with `//~`, which the language reads as an ordinary comment ([lexical.annotations](02-lexical.md#lexical.annotations)). On a `/// ex:` or `/// prop:` line, an annotation follows the example or the property, whose text ends where the annotation begins ([syntax.doc-comment-text](03-syntax.md#syntax.doc-comment-text)). In a test, `//~` appears only to start an annotation, never inside a string literal. The one exception is a string literal that its line leaves unterminated, which is E0005, *unterminated string literal* ([lexical.string-literals](02-lexical.md#lexical.string-literals)): the annotation that expects the error ends that line. The runner finds annotations without lexing Stilt.

Tests: [lexical/annotations_are_comments.lt](../conformance/lexical/annotations_are_comments.lt), [lexical/commented_out_code.lt](../conformance/lexical/commented_out_code.lt), [lexical/example_comments.lt](../conformance/lexical/example_comments.lt).

<a id="conformance.header-region"></a>
A file's **header region** is every line before the first line that is neither blank nor a comment. A line in it that starts with `//~` is a **header annotation**. Any other `//~` follows code or a comment on its line, and is an **inline annotation**, which describes that line. An inline annotation that follows a `//` comment describes the comment, such as one that holds commented-out code ([lexical.commented-out-code](02-lexical.md#lexical.commented-out-code)).

Tests: [lexical/annotations_are_comments.lt](../conformance/lexical/annotations_are_comments.lt), [lexical/commented_out_code.lt](../conformance/lexical/commented_out_code.lt).

<a id="conformance.header-annotations"></a>
Header annotations take the form `//~ key: value`, and a test gives each key at most once:

| Annotation | Meaning |
| --- | --- |
| `//~ tier: core` | The tier of the suite that includes the test ([conformance.tiers](#conformance.tiers)): `core`, `advanced`, `meta` or `systems`. Defaults to `core` |
| `//~ rule: numbers.integer-literals, patterns.or-patterns` | The paragraphs that the test covers ([conformance.rule-citations](#conformance.rule-citations)) |
| `//~ args: a b "c d"` | Command-line arguments: words separated by spaces. A double-quoted word may hold spaces and escapes |
| `//~ stdin: "text\n"` | Standard input, as a quoted string. Defaults to empty |
| `//~ run-output: "text"` | Expected stdout: the text and one trailing newline |
| `//~ stdout:` then `//~ \| line` … | Expected stdout as a block. Each following `//~ \| ` line holds one output line, which ends in a newline, and `//~ \|` alone is an empty line. The block ends at the first line that doesn't start with `//~ \|` |
| `//~ stderr:` then `//~ \| line` … | Expected stderr as a block, read as the stdout block is. Without it, stderr isn't compared |
| `//~ exit: N` | Expected exit status, from 0 to 255. Defaults to 2 when the test has an `ERROR` entry, and otherwise to 0, or to 101 when `panic` is given. With 134, stdout isn't compared, since an abort may lose buffered output ([program.output-flushing](04-programs.md#program.output-flushing)) |
| `//~ panic: KIND` | The program panics with this kind ([effects.panic-kinds](12-effects.md#effects.panic-kinds)): it exits with status 101, or 2 when the test has an `ERROR` entry, and the second-to-last line of its stderr begins with `panic: KIND: ` |
| `//~ panic-at: PATH:LINE:COL` | Where the panic is reported: the last line of stderr is `  at PATH:LINE:COL` ([program.panic-location](04-programs.md#program.panic-location)). Needs `panic` |

The keys after `rule` are the **run keys**.

Tests: [lexical/annotations_are_comments.lt](../conformance/lexical/annotations_are_comments.lt), [protocol/args_and_stdin.lt](../conformance/protocol/args_and_stdin.lt), [protocol/byte_exact_output.lt](../conformance/protocol/byte_exact_output.lt), [protocol/run_prints_only_program_output.lt](../conformance/protocol/run_prints_only_program_output.lt).

Checked by: also the runner's own tests of every header key (`tools/runner/src/annotations/tests.rs`).

<a id="conformance.quoted-strings"></a>
A quoted string in an annotation uses the escapes `\n`, `\r`, `\t`, `\"`, `\\` and `\xNN`, which is the byte whose hexadecimal value is `NN`. Only `stdin` may hold bytes that aren't UTF-8.

Tests: [protocol/args_and_stdin.lt](../conformance/protocol/args_and_stdin.lt), [protocol/byte_exact_output.lt](../conformance/protocol/byte_exact_output.lt).

<a id="conformance.rule-citations"></a>
`//~ rule:` lists the IDs of the paragraphs of this Reference that the test covers, separated by commas ([Paragraph IDs](README.md#paragraph-ids)). Each paragraph that a conformance test can observe lists the tests that cite it. Each paragraph that no conformance test can observe says what checks it instead.

Checked by: the runner's coverage report, `just coverage`, which lists the paragraphs that no test cites (`tools/runner/src/coverage.rs`).

<a id="conformance.inline-annotations"></a>
An inline annotation goes at the end of the line it describes, and holds one or more entries, as `//~ ERROR E0001 WARN W0002`:

| Entry | Expects |
| --- | --- |
| `ERROR E0404` | An error with this code on this line |
| `WARN W0101` | A warning with this code on this line |
| `PASS` | A test, doc example or property declared on this line, which passes |
| `FAIL` | A test, doc example or property declared on this line, which fails |

Error codes match `E[0-9]{4}`, and warning codes `W[0-9]{4}`. In a manifest of a directory test, an inline annotation follows the `#` of a TOML comment, as `csv = { path = "deps/csv" } # //~ ERROR E0608`.

Tests: [protocol/several_entries_on_one_line.lt](../conformance/protocol/several_entries_on_one_line.lt), [protocol/test_lines.lt](../conformance/protocol/test_lines.lt), [protocol/tests_in_nested_module](../conformance/protocol/tests_in_nested_module/).

## Kinds of test

<a id="conformance.exact-matching"></a>
Every test matches its `ERROR` and `WARN` entries exactly against the diagnostics that the implementation reports. Their order doesn't matter, but their number does: two identical diagnostics on one line need two entries. A diagnostic that no entry expects, a warning included, fails the test.

Tests: [protocol/run_prints_only_program_output.lt](../conformance/protocol/run_prints_only_program_output.lt), [protocol/several_entries_on_one_line.lt](../conformance/protocol/several_entries_on_one_line.lt).

Checked by: also the runner's own tests of exact matching: an extra diagnostic, a missing one, a duplicate and a warning that no entry expects (`tools/runner/src/judge.rs`).

<a id="conformance.kinds-of-test"></a>
A test is of one of three kinds, which its entries and run keys decide:

- **Check tests** have at least one `ERROR` entry, no run keys, and no `PASS` or `FAIL` entry. The runner calls `check --json`, and doesn't run them.
- **Test-block tests** have at least one `PASS` or `FAIL` entry, no `ERROR` entry and no run keys. The runner calls `test --json`, whose list of tests must match the `PASS` and `FAIL` entries exactly.
- **Run tests** have no `PASS` or `FAIL` entry. A run test with an `ERROR` entry has at least one run key, and runs a program with errors ([conformance.run-statuses](#conformance.run-statuses)). The runner calls `check --json`, then `run`, whose result must match the run keys. A run test with neither `run-output` nor `stdout` expects an empty stdout.

Tests: [program/error_never_reached.lt](../conformance/program/error_never_reached.lt), [protocol/run_prints_only_program_output.lt](../conformance/protocol/run_prints_only_program_output.lt), [protocol/several_entries_on_one_line.lt](../conformance/protocol/several_entries_on_one_line.lt), [protocol/tests_in_nested_module](../conformance/protocol/tests_in_nested_module/).

<a id="conformance.malformed-tests"></a>
A test is **malformed**, and fails without being run, when it has any of these:

- an unknown key or entry;
- a header key given twice;
- a malformed value;
- both `run-output` and `stdout`;
- an `exit` other than 2 in a test with an `ERROR` entry;
- an `exit` other than 101 together with `panic`, in a test without an `ERROR` entry;
- `panic-at` without `panic`;
- a `stderr` block in a test that expects status 2, whose stderr is unspecified ([program.stderr-with-status-2](04-programs.md#program.stderr-with-status-2));
- a line after the header region that starts with `//~`;
- a header annotation in a file of a directory test other than `main.lt`;
- a key or an entry that its kind of test doesn't allow ([conformance.kinds-of-test](#conformance.kinds-of-test)).

Checked by: the runner's own tests of malformed annotations (`tools/runner/src/annotations/tests.rs`).

## Where tests live and run

<a id="conformance.location"></a>
The conformance suite lives in the folder `conformance/` at the root of the repository, with a folder for each area, `conformance/<area>/`. Each test is a `.lt` file or a directory test. The runner skips every file and directory whose name starts with `_` or `.`, where drafts are kept. Where a test lives never changes what it expects.

Checked by: the runner's own tests of discovery (`tools/runner/src/discovery.rs`).

<a id="conformance.directory-tests"></a>
A **directory test** is a directory that holds `main.lt`. It is a directory program, or a package if it also holds `stilt.toml` ([program.forms](04-programs.md#program.forms)). The dependencies of such a package are path dependencies inside the test. Its header annotations are in `main.lt`, and its inline annotations may be in any of its `.lt` files and manifests.

Tests: [protocol/nested_file_paths](../conformance/protocol/nested_file_paths/), [protocol/tests_in_nested_module](../conformance/protocol/tests_in_nested_module/).

<a id="conformance.environment"></a>
The runner runs each test's commands in the working directory of [conformance.paths](#conformance.paths), with an environment that holds only `PATH` and `LC_ALL=C`. Each command has two limits: 10 seconds of processor time, and 120 seconds in all. A test that exceeds either limit fails. Where the platform supports it, continuous runs of the suite also limit memory to 1 GiB.

Tests: [protocol/working_directory.lt](../conformance/protocol/working_directory.lt).

Checked by: also the runner's own tests of the environment and of the time limit (`tools/runner/src/process.rs`).
