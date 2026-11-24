# Rationale: Conformance

Stilt has more than one implementation: a reference interpreter, written to be read, and a compiler with debug and release builds. They must agree on every program, and a new implementation, or a new back end of one, must be able to show that it agrees. That needs four things defined exactly: what an implementation is judged on, which diagnostics it reports, how a test states what it expects, and how a runner drives an implementation. [Conformance](../01-conformance.md) defines three of them, and [Programs with errors](../18-errors.md) defines the fourth.

## Implementations

An implementation is compared with the suite and with the reference interpreter through one protocol of four commands ([conformance.implementations](../01-conformance.md#conformance.implementations)). A new back end joins every comparison by implementing those commands, and needs to know nothing of the runner. The reference interpreter is the implementation that others are compared with on programs that no test holds, such as generated ones, for which no expected output is written down.

The suite is divided by tier ([conformance.tiers](../01-conformance.md#conformance.tiers)). An implementation that supports only the first tiers, such as a small interpreter for teaching the core language, can show that it conforms on those. A test's tier never changes what a program means: the tier of a module is inferred from its features, and the annotation only says which suite the test belongs to.

## What is observable

An implementation is judged on its diagnostics' codes, files and lines, on what a run prints and how it exits, and on which tests pass ([conformance.observables](../01-conformance.md#conformance.observables)).

Comparing the text of diagnostics is rejected ([conformance.diagnostic-text](../01-conformance.md#conformance.diagnostic-text)). Conformance would then depend on wording, and each implementation is free to improve its own. The reference interpreter has no reason to word its messages well, and it only has to report codes and lines, which keeps it small. The compiler's wording is tested where it matters, in snapshots of its rendering.

Matching codes without lines is rejected as too weak: an error on the right line can't be told apart from the same error somewhere else. The line is that of the start of the primary span ([conformance.diagnostic-lines](../01-conformance.md#conformance.diagnostic-lines)), which the registry fixes for each code. Two implementations that agree on a mistake then report it on the same line.

Implementations are deterministic ([conformance.determinism](../01-conformance.md#conformance.determinism)). An exact comparison of two runs means nothing otherwise. A deterministic implementation's results can also be cached by the command and the program alone.

## The command-line protocol

`check --json` and `test --json` write JSON objects that hold at least a code, a file and a line ([conformance.diagnostic-objects](../01-conformance.md#conformance.diagnostic-objects)), and may hold anything else ([conformance.extra-fields](../01-conformance.md#conformance.extra-fields)). The compiler's richer objects, with messages, spans, fixes and the alternatives an agent reads, come from the same command that conformance tests. So the verdict that an agent reads is the one that the suite checks. `test --json` writes nothing else on stdout, and a tool reads its verdict without parsing anything around it.

Every path is relative to the working directory, with `/` as the separator ([conformance.paths](../01-conformance.md#conformance.paths)). Two machines, and two implementations, then report the same text.

A program with errors runs, and exits with status 2 however it ends ([conformance.run-statuses](../01-conformance.md#conformance.run-statuses)). Each implementation renders its diagnostics on stderr in its own form, so what a run writes to stderr then is unspecified. A test that expects status 2 can't expect a stderr block ([conformance.malformed-tests](../01-conformance.md#conformance.malformed-tests)). Check tests and run tests read diagnostics from `check --json`, where every implementation gives them in one form ([conformance.run-output](../01-conformance.md#conformance.run-output)).

A path that names no program, or a file that can't be read, ends a command with a status other than 0 and 1 ([conformance.load-errors](../01-conformance.md#conformance.load-errors)). A runner then never mistakes it for a verdict of `check` or `test`. The status itself is left to each implementation, because no conformance test can observe it: every test is a program that can be read.

## Annotations

A test states what it expects in comments of its own source ([conformance.annotations](../01-conformance.md#conformance.annotations)). A separate file for each test, as a `.toml` beside it, is rejected: it doubles the number of files and splits each test's intent across two of them. An inline annotation sits on the line on which it expects a diagnostic ([conformance.inline-annotations](../01-conformance.md#conformance.inline-annotations)). The line number needs no writing, and a reader sees the mistake and its code together.

`//~` never appears inside a string literal of a test, so the runner finds annotations without a lexer of Stilt, and never depends on the code it is testing. The one exception, a string literal that its line leaves unterminated, ends at the line's end anyway.

Each test cites the paragraphs it covers ([conformance.rule-citations](../01-conformance.md#conformance.rule-citations)). A paragraph that no test cites shows up in the coverage report, and a reader of a paragraph finds the programs that show it.

## Kinds of test

Every test matches its expected diagnostics exactly ([conformance.exact-matching](../01-conformance.md#conformance.exact-matching)). Matching a subset of the reported diagnostics is rejected. Cascades and spurious warnings would then pass unnoticed, and agents, which read the diagnostics of every run, would learn to ignore them. Exact matching is fair only because every implementation suppresses the same diagnostics, which [Programs with errors](../18-errors.md) fixes. Warnings are part of conformance too, so a new lint can fail existing tests, and every lint has to be justified against the suite.

A test's kind follows from its annotations ([conformance.kinds-of-test](../01-conformance.md#conformance.kinds-of-test)), so no test names its own kind. A malformed test fails, and is never skipped ([conformance.malformed-tests](../01-conformance.md#conformance.malformed-tests)). A mistyped annotation then can't silently make a test expect nothing.

## Where tests live and run

The suite lives in its own folder at the root of the repository ([conformance.location](../01-conformance.md#conformance.location)), because it is the Reference's executable form. Each test cites its paragraphs, and each paragraph lists its tests. It is kept apart from `tests/`, which holds the toolchain's own tests of its commands, because the two have different roles. Keeping the suite in the runner's folder is rejected too: the suite judges every implementation and belongs to none. Drafts sit in folders whose names start with `_`, so they never count until they are moved out.

A directory test that is a package holds its dependencies as path dependencies inside it ([conformance.directory-tests](../01-conformance.md#conformance.directory-tests)), so that no test needs the network. Each test runs in a fixed environment, with the C locale and nothing but `PATH` ([conformance.environment](../01-conformance.md#conformance.environment)), so that what it gives depends on the program alone.

Each command runs under two time limits, so that a program that never ends fails its test instead of stalling the suite. The limit on processor time catches a command that computes forever, whatever else the machine runs. The limit on time in all catches a command that waits forever, which uses no processor time while it waits.
