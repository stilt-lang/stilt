# Tests

The toolchain's test suites, beside the conformance suite: each pairs programs with what a tool must give for them.

| Path | Contents |
| --- | --- |
| [`diagnostics/`](diagnostics/) | The compiler's diagnostics snapshots: one program per code, with its reviewed rendering |
| [`format/`](format/) | The formatter's tests: inputs, each paired with the output that the canonical format of [syntax.format](../reference/03-syntax.md#syntax.format) gives it |
| [`facts/`](facts/) | The facts suite: programs whose lines carry the inferred facts that the Reference gives them, which `stilt show` must print |
| [`holes/`](holes/) | The holes suite: programs whose holes carry the context that the rules of `show` give them, which `stilt show` must report |
| [`alternatives/`](alternatives/) | The alternatives suite: programs whose diagnostics carry the admissible alternatives that its rules give them, which `stilt check --json` must list |
| [`costs/`](costs/) | The costs suite: programs whose functions carry the instantiations, the calls left on dictionaries and the checks proved and kept that the Reference gives them, which `stilt show --release` must report, with their reference counts pinned by reviewed snapshots |

The `justfile` at the root gives the commands that run them.
