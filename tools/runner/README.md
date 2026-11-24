# Runner

`stilt-test` runs the conformance suite, the guide's examples and generated programs against an implementation of Stilt, and compares two implementations with `--diff`, `--parse`, `--check` and `--runs`. With `--diff`, `--tests` also compares each program's tests, as `test --json` reports their results ([program.test-results](../../reference/04-programs.md#program.test-results)), and each property's `property` object, all but the detail of a panic other than `explicit` ([tests.property-verdict](../../reference/19-tools.md#tests.property-verdict)), and `--succeed` also requires each run to exit with status 0, so that two runs that fail alike, as two that run out of memory do, don't pass. `--runs` gives each program the arguments and input that its annotations give, so a program from the suite that waits for a line reads it. `--declines STATUS` names the exit status by which an implementation of part of the language declines a program: a run test whose `run` ends with it is declined, neither passed nor failed, and the summary counts it apart, as `just formal` counts the programs that the Lean model's calculus can't write (`model.sh`, [formal/README.md](../../formal/README.md#executable-semantics)).


## Staging erases

A test whose program writes `comptime` and expects no diagnostic, once it passes, runs again on its erased copy, with each `comptime` deleted with the space after it, and must give what the test expects there too, since deleting the annotations changes no observable ([meta.erasure](../../reference/16-meta.md#meta.erasure); goal `staging-erases`). The copy is written to a directory of its own under the system's temporary directory and removed after: a directory test's whole tree, its `.lt` files erased, or a single file's erased text. A `comptime` in a comment or a string literal stays (`src/erased.rs`).

## The reference interpreter cache

`--cache DIR` keeps the results of the *other* implementation, the one that `--diff`, `--parse`, `--check` or `--runs` names, and answers a command from `DIR` when it has run before. It never applies to `--impl`, the implementation under test. A recipe that compares the compiler with the reference interpreter passes `--cache target/interpreter-cache`, so that the reference interpreter runs each program once however often the recipe runs (goal `quick-ci`).

The cache is safe because the reference interpreter is deterministic: its output is a function of its binary and of the command. The key of a command hashes:

- the contents of the other implementation's binary, read once at startup;
- the arguments and the standard input;
- the test's target;
- the contents of the program's files: the one file, or for a directory program every file under it, in name order with their paths.

The hash is SipHash from `std::hash`. A rebuilt reference interpreter, an edited program or other arguments change the key and miss, which costs one run. A command is stored only when it exited, never when it timed out or was killed by a signal, and each result is written to a temporary name and renamed, since jobs run in parallel (`src/cache.rs`).

The recipes that run the reference interpreter against itself (`generated`, `stress` and `scale`) pass no cache: they test that two runs of the reference interpreter agree, which a cache would hide.
