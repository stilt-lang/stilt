# 20. Builds, C and WebAssembly

This chapter gives what `stilt build` writes beyond a debug build:

- release builds, which mean what debug builds mean and drop only the checks that can't fail;
- how a release build specializes generic code, reads a profile and reports what its code still costs;
- functions exported to C, and the static library that holds them;
- foreign functions, which a program calls from `unsafe` blocks, with the facts and grants that keep them visible;
- the WebAssembly target.

Calling C belongs to the systems tier, and everything else here to core. [Inferred facts and limits](15-facts.md) gives verification and `without`, and [Programs](04-programs.md) gives exit statuses, panic reports and the manifest.

## Release builds

<a id="builds.release-builds"></a>
`stilt build` writes a **debug build**, which keeps every check. `stilt build --release PATH` writes a **release build** of the program at `PATH`. It writes an executable for the host, or for the target that `--target` names, at the path that `-o` names, as `stilt build` does without the flag. Every target of debug builds has release builds, from every host that has a release toolchain ([builds.finding-clang](#builds.finding-clang)).

Checked by: `just run`, which builds the conformance suite's run tests as release builds, and `just cross`, which builds them for each target.

<a id="builds.same-meaning"></a>
A release build of a program prints what its debug build and the reference interpreter print, reads what they read, and ends as they do. It ends with the same status. After a panic, it ends with its debug build's report, which has the reference interpreter's kind and place ([program.panic-report](04-programs.md#program.panic-report), [effects.panic-kinds](12-effects.md#effects.panic-kinds)). Only these may differ: its speed, its memory, and the depth of calls at which its stack overflows, which is at least what [program.recursion-depth](04-programs.md#program.recursion-depth) requires. A call in tail position may become a jump. So a recursion that overflows the stack in one build may run on in the other. Running out of memory, too, may happen in one build and not in the other ([program.exit-statuses](04-programs.md#program.exit-statuses)).

Tests: [builds/unfused_multiply_add.lt](../conformance/builds/unfused_multiply_add.lt).

Checked by: also `just run`, which runs every run test of the conformance suite as a release build, and `just differential`, which compares generated programs under the reference interpreter, debug builds and release builds.

<a id="builds.dropped-checks"></a>
A release build drops each check that verification proves can't fail ([facts.verification](15-facts.md#facts.verification), [facts.proved-overflow](15-facts.md#facts.proved-overflow)), and keeps every other. A proved check can't fail, so dropping it changes nothing that the program does ([facts.what-proofs-change](15-facts.md#facts.what-proofs-change)).

Checked by: the costs suite, whose `PROVED` and `KEPT` annotations in `tests/costs/checks.lt` its tests check (`compiler/stilt-cli/tests/costs.rs`), and the toolchain's tests of release builds, in which a release build prints and panics as its debug build does (`compiler/stilt-cli/tests/release.rs`).

<a id="builds.what-it-refuses"></a>
A release build refuses a program with an error, as a debug build does, and reports its diagnostics with status 2. It refuses a program with a hole too ([declarations.typed-holes](10-declarations.md#declarations.typed-holes)). It reports each hole's W0300 as `check` does, then a line that counts the holes, and ends with status 2. That line is `stilt: a release build refuses a program with holes, and this one has N holes`.

Checked by: the toolchain's tests of release builds, a hole's W0300 and an error's diagnostics with status 2 (`compiler/stilt-cli/tests/release.rs`).

<a id="builds.line-tables"></a>
A release build's line tables map its code to the program's lines, with the files named as its panics name them, so a debugger and a profiler show them. A Linux executable holds them. A macOS executable's line tables are gathered into the `.dSYM` bundle beside it, as a debug build's are, when the machine has `dsymutil`. A release build's local variables may be gone where the optimizer moved them. A debugger shows every local variable of a debug build.

Checked by: the toolchain's tests of release builds, a macOS build's `.dSYM` and a Linux build's executable (`compiler/stilt-cli/tests/release.rs`).

## The release toolchain

<a id="builds.release-toolchain"></a>
A release build lowers the program to C, which clang compiles. Each version of `stilt` names one release of clang. It holds a manifest of the archive of each host whose archive is published: its URL and the SHA-256 of its bytes. An archive is a POSIX tar compressed by gzip that holds `bin/clang` and what it loads, and nothing else. What a target's builds link is in the toolchain beside `stilt`: its runtime library and, for WebAssembly, its C library and binaryen. A release build reads nothing but the program, the toolchain and the environment variables that this chapter names. Its C includes no system header and links no library of clang's, and the build links as a debug build links.

Checked by: the toolchain's tests of fetching (`compiler/stilt-pkg/src/toolchain/tests.rs`), and `just cross`, which builds release builds for each target.

<a id="builds.finding-clang"></a>
A release build's clang is the first of:

- the one that `STILT_CC` names ([builds.another-compiler](#builds.another-compiler));
- the toolchain's own, `clang/bin/clang` in the toolchain that `STILT_TOOLCHAIN` names, or, without it, in `stilt-toolchain` beside `stilt`. A build of `stilt` from source assembles that toolchain from the build machine's clang of the named release;
- the host's archive, which the first release build that needs it fetches ([builds.fetching-toolchain](#builds.fetching-toolchain)).

A host whose archive isn't published builds release builds with `STILT_CC`, or with a toolchain that holds clang.

Checked by: the toolchain's tests of fetching (`compiler/stilt-pkg/src/toolchain/tests.rs`).

<a id="builds.fetching-toolchain"></a>
The host's archive is fetched over HTTPS, or from a `file://` URL, into `toolchains/` in the cache of [packages.fetching](04-programs.md#packages.fetching). That cache is the directory that `STILT_HOME` names, or `.stilt` in the directory that `HOME` names. The archive is checked against its hash and unpacked there, where every later build finds it. It is unpacked apart and moved into place whole, so an interrupted fetch leaves nothing that a build would use. An archive whose unpacking isn't whole is fetched again. A fetch that fails, or an archive whose hash differs from the manifest's, is an error that names the URL, and, for the hash, both hashes. Nothing is then built. Such an error, as every failure of the toolchain, ends the command with status 2 and its message on stderr. The line that reports a fetch goes to stderr too.

Checked by: the toolchain's tests of fetching: from `file://` archives, a corrupt one, one left unpacked in part, an entry that would land outside the toolchain, and a URL that doesn't answer (`compiler/stilt-pkg/src/toolchain/tests.rs`).

<a id="builds.same-bytes"></a>
Two release builds give the same executable, byte for byte, when these are the same: the source, the version of `stilt`, the clang, the host, the target and the executable's name. This holds at any number of threads, from any directory and cache, and on any machine. The program's profile, if it has one, counts as source ([builds.profile-use](#builds.profile-use)). The name counts, since the ad hoc signature of a macOS executable holds it. No path of the machine counts.

Checked by: the toolchain's tests of release builds, two builds from two directories with two caches (`compiler/stilt-cli/tests/release.rs`).

<a id="builds.another-compiler"></a>
`STILT_CC`, when set, names a clang to use instead of the toolchain's. [builds.same-bytes](#builds.same-bytes) then doesn't hold. A clang that can't be run, or that rejects the code or its flags, is an error that names it.

Checked by: the toolchain's tests of release builds, a compiler that can't run (`compiler/stilt-cli/tests/release.rs`).

## Specialization

<a id="builds.specialization"></a>
A release build compiles each generic function once for each **instantiation** that the program reaches from its roots. The roots are `main` for an executable, and the exported functions for a library ([c.static-library](#c.static-library)). An instantiation is a list of the function's type arguments, its value arguments and the types it reflects on ([meta.reflects](16-meta.md#meta.reflects)). A debug build passes a generic function a **dictionary** of each bound's methods, its value parameters, and a description of each type it reflects on. An instantiation instead calls the instance's own methods directly, holds each value parameter as its number and knows each type. So a bound test, `T.shape()` and `comptime` code are decided while the program is built ([meta.bound-tests](16-meta.md#meta.bound-tests), [meta.erasure](16-meta.md#meta.erasure)). A static expression that panics still panics where the run reaches it ([meta.erasure](16-meta.md#meta.erasure)). Instantiations whose code is the same are one function.

Checked by: the costs suite, whose `FOR` and `ONCE` annotations its tests check (`compiler/stilt-cli/tests/costs.rs`), the toolchain's tests of libraries, whose instantiations are reached from their exported functions (`compiler/stilt-cli/tests/library.rs`), and `just run`, which builds the run tests of `generics/`, `staging/`, `reflection/`, `json/`, `polymorphism/`, `variadics/` and `parameters/` as release builds.

<a id="builds.what-stays-generic"></a>
Two kinds of code keep their dictionaries in a release build, as in a debug build:

- every function of a recursive group in which a call passes type arguments other than the group's own ([polymorphism.recursion](07-types.md#polymorphism.recursion)), whose instantiations could grow without end;
- a polymorphic argument, a value of a type `fn<T: B>(…)`, called through its dictionaries at each call ([polymorphism.arguments](07-types.md#polymorphism.arguments)), since its callee isn't known where it is called.

Every such call is listed in the performance report ([builds.performance-report](#builds.performance-report)).

Checked by: the costs suite, whose `DICTIONARIES` and `DICTIONARY` annotations its tests check (`compiler/stilt-cli/tests/costs.rs`).

<a id="builds.no-specialization-hints"></a>
A program asks for no specialization and forbids none: a release build decides it all, and no attribute, hint or annotation exists for it.

Checked by: the grammar, which has no form for it ([syntax.grammar](03-syntax.md#syntax.grammar)).

## Profiles

<a id="builds.profiles"></a>
`stilt run --profile` and `stilt test --profile` count how often these happen as the program runs in its debug build:

- each body is entered;
- each arm of an `if` or a `match` is taken;
- each loop's body runs;
- each call through a function value or a dictionary reaches each function that has an address ([edits.paths](19-tools.md#edits.paths)).

A closure and a structural impl have no address, and calls that reach them aren't counted. At the end of a run, each count is added to the program's **profile**. The profile is `default.profile` at the root of a directory program, beside its manifest, or `NAME.profile` beside a program of one file `NAME.lt`. A run that ends with status 134 writes nothing. A run that panics, with status 101, writes them.

Checked by: the toolchain's tests of profiles (`compiler/stilt-cli/tests/profiles.rs`).

<a id="builds.profile-form"></a>
A profile is text, one line for each count that isn't 0, `ADDRESS HASH KIND LINE:COL [CALLEE] COUNT`. The lines are sorted by address, hash, place, kind and callee, so that a change of the profile reads as a diff. The fields are these:

- `ADDRESS` is the body's address and `HASH` its hash ([edits.body-addresses](19-tools.md#edits.body-addresses), [edits.hash](19-tools.md#edits.hash));
- `KIND` is `entry`, `arm`, `loop` or `call`;
- `LINE:COL` is the place of what the line counts. Its line is counted from the body's first line, that of its declaration, so an edit above the body moves none of its lines. A body's entry is at its `{`. An arm of an `if` is at its condition, or at its pattern for `if let`. Its `else` is at what follows `else`, or at the `if` when it has none. An arm of a `match` or a `catch` is at its pattern, a loop at its keyword, and a call at the call;
- `CALLEE` is the address of the function that a `call` reaches;
- `COUNT` is the count rounded down to a power of two.

Merging adds counts and rounds the sum down again. A line that isn't of this form is E0610, *malformed profile*, at the line, including a blank line and a line whose count isn't a power of two. `check` reports it, and a profiled run and a release build refuse the program.

Checked by: the toolchain's tests of profiles, two runs whose counts add, a malformed line, and the same runs writing the same file (`compiler/stilt-cli/tests/profiles.rs`), since the command-line protocol gives no file beside a program.

<a id="builds.profile-use"></a>
A release build reads the program's profile when there is one. It drops each line whose hash differs from its body's, which the performance report lists. A profile tells the C compiler which branches are likely, which functions are hot and which are cold. It changes nothing that the program does.

Checked by: the toolchain's tests of profiles, a release build with a profile and without one printing the same, an edited function's lines dropped and listed, and an edit above a function keeping its lines (`compiler/stilt-cli/tests/profiles.rs`).

## The performance report

<a id="builds.performance-report"></a>
`stilt show --release ADDRESS [PATH]` prints, for each function at the address that the release build compiles:

- the instantiations it is compiled for;
- each call left on a dictionary, with its reason ([builds.what-stays-generic](#builds.what-stays-generic));
- the reference-count operations that its code still performs, and the copies among them ([modes.copies](13-modes.md#modes.copies)), each at its line;
- the checks that verification proves, which the build drops, and those it keeps, by kind and line ([builds.dropped-checks](#builds.dropped-checks));
- the lines of the profile that it drops ([builds.profile-use](#builds.profile-use)).

`--json` gives the same as records.

Checked by: the costs suite (`tests/costs/`), whose instantiations, dictionaries, checks and profile lines are derived from this chapter's rules, while where the counting of references falls is the compiler's own, so the suite pins those counts as reviewed snapshots, as diagnostics' renderings are pinned (`compiler/stilt-cli/tests/costs.rs`).

## Exporting functions to C

<a id="c.exported-functions"></a>
A top-level `pub fn` of a module of the program's own package may be written `pub extern fn`, with its body. It is then **exported**: a C program linked with the program's library calls it by its name. `extern` stands only in two places. It stands after `pub` before a module's function with a body, and before a module's function with no body, which declares a foreign function ([c.foreign-functions](#c.foreign-functions)). Anywhere else, it is E0100, *syntax error* ([syntax.extern-functions](03-syntax.md#syntax.extern-functions)), as before a method, a type, a local function, or a function with a body without `pub`. A dependency's exported functions are exported only by a library built from that package itself.

Tests: [export/accepted.lt](../conformance/export/accepted.lt), [export/on_a_local_function.lt](../conformance/export/on_a_local_function.lt), [export/on_a_method.lt](../conformance/export/on_a_method.lt), [export/on_a_type.lt](../conformance/export/on_a_type.lt), [export/without_pub.lt](../conformance/export/without_pub.lt), [program/syntax_error_in_exported_function.lt](../conformance/program/syntax_error_in_exported_function.lt).

<a id="c.exported-signatures"></a>
An exported function takes and returns only these types, each passed as C passes the type beside it:

- `i8`, `i16`, `i32` and `i64` as `int8_t` to `int64_t`;
- `u8` to `u64` as `uint8_t` to `uint64_t`;
- `f32` and `f64` as `float` and `double`;
- `bool` as `bool`;
- `()`, as a result only, as `void`.

It has no type, value or effect-row parameter, no `inout` or `escaping` parameter, and no result of type `Never`. Its row has no `raise<E>`, no `async` and no user-defined effect. It may perform `io` and its capabilities ([facts.capabilities](15-facts.md#facts.capabilities)). Any other signature is E0352, *exported function C can't call*, once for each part that C can't take. It is reported at the name of an `inout` or `escaping` parameter, at the type of another parameter or of the result, at a generic, and at an element of the row.

Tests: [export/accepted.lt](../conformance/export/accepted.lt), [export/signatures.lt](../conformance/export/signatures.lt).

<a id="c.exported-names"></a>
An exported function's name is its C symbol, as written, so it must be one that no other code of the C program can mean. Two exported functions of a package with one name, in any modules, are E0219, *exported name used twice*. It is reported at the second's name, in the order of [c.library-header](#c.library-header). These names are E0352 at the name:

- a name that [c-names.txt](c-names.txt) lists;
- a keyword of C11, C23 or C++23;
- `main`;
- a name that POSIX.1-2024's headers declare, C17's library among them;
- a name beginning with `_`, `stilt_`, `lt_`, `f_` or `m_`.

Tests: [export/names.lt](../conformance/export/names.lt), [export/twice/main.lt](../conformance/export/twice/main.lt).

<a id="c.calls-from-c"></a>
A call from C runs the function as a call from Stilt does, on the calling thread and its stack. The first call makes the runtime ready. Calls from several C threads may run at once, as tasks run under `task.threads()` ([tasks.std-task](14-tasks.md#tasks.std-task)). The function's output goes where a program's goes, a line at a time, and what it wrote has reached the file when it returns. `cli.args()` is the empty list, and `cli.env` reads the process's environment ([std.cli](17-std.md#std.cli)). A panic in the function writes its output, prints its report and ends the process with status 101, as in a program ([program.exit-statuses](04-programs.md#program.exit-statuses), [program.panic-report](04-programs.md#program.panic-report)). So no panic crosses into C. The depth of [program.recursion-depth](04-programs.md#program.recursion-depth) holds on a thread whose stack has 8 MiB free. The library installs no signal handler, so a stack overflow ends the process as the C program's own does.

Checked by: the toolchain's tests of libraries, which call each type from a C program that they build and link, from two threads at once, 10,000 calls deep, and into a panic (`compiler/stilt-cli/tests/library.rs`), since no Stilt program calls from C.

<a id="c.static-library"></a>
`stilt build --lib PATH`, with or without `--release`, writes a static library and a header. The library holds the program's exported functions and everything they reach, the runtime among it. With `-o DIR/NAME`, they are `DIR/libNAME.a` and `DIR/NAME.h`. Without `-o`, they are written in the current directory, and `NAME` is the program's name. A program built with `--lib` needs no `main`, and its `main`, if it has one, isn't exported. The archive holds its members in a fixed order, each with the time 0, the owner 0 and the mode 644. So [builds.same-bytes](#builds.same-bytes) holds of a release build's library as of its executable. The library defines `stilt_runtime_once`, so the linker of a C program that links two Stilt libraries rejects it. A C program links it with its C library, and on Linux with the math library too, `-lm`, which glibc keeps apart from it.

Checked by: the toolchain's tests of libraries, the bytes of two release libraries built in different directories, and two libraries that don't link together (`compiler/stilt-cli/tests/library.rs`).

<a id="c.library-header"></a>
The header is C11 and C++ alike. It holds these:

- a guard `NAME_H`, with `NAME` in capitals and every byte but letters and digits written `_`. A `_` comes before it when it starts with a digit, as no C name does;
- `<stdbool.h>` and `<stdint.h>`;
- the declarations, inside `extern "C"` when `__cplusplus` is defined.

Each exported function is declared in the order of its modules' paths, compared as bytes, and of the functions in each module. Each declaration follows its doc comment's first paragraph, written as `//` lines. It names each parameter after its type, except one whose name [c.exported-names](#c.exported-names) rejects, which C might mean otherwise. It writes `(void)` for no parameters.

Checked by: the toolchain's tests of libraries, a header of functions in two modules compiled as C11 and as C++ (`compiler/stilt-cli/tests/library.rs`), and guards of names that hold other bytes or start with a digit (`compiler/stilt-cli/src/library/header.rs`).

<a id="c.exported-fact"></a>
An exported function's inferred facts are its own, and `stilt show` prints `exported` in its bracket ([facts.visibility](15-facts.md#facts.visibility)). Whether a function is exported is no part of its package's API ([versions.facts-in-api](21-versions.md#versions.facts-in-api)), whose callers are Stilt code.

Checked by: the toolchain's tests of libraries (`compiler/stilt-cli/tests/library.rs`).

## Foreign functions

<a id="c.foreign-functions"></a>
A top-level `extern fn` with no body, `pub` or not, declares a **foreign function**, which C gives. It is written `pub? extern fn name(params) -> T`, with an optional row `/ io`, and its name is its C symbol. Its head ends the item, or a `without` clause after it does ([c.effects](#c.effects)), so a `where` clause or `= ?` after it is E0100, *syntax error* ([syntax.extern-functions](03-syntax.md#syntax.extern-functions)). It has no generics, no `self`, no `inout` or `escaping` parameter and no row element but `io`. Each of these is E0353, at the generic's name, at `self`, at the parameter's name and at the row's element. `parse --sexp` prints a foreign function as a function without a body inside `(extern …)`, and inside `(pub (extern …))` when it is `pub` ([syntax.tree-form](03-syntax.md#syntax.tree-form)). Foreign functions are part of the systems tier ([c.systems-tier](#c.systems-tier)).

Tests: [foreign/body_without_pub.lt](../conformance/foreign/body_without_pub.lt), [foreign/signatures.lt](../conformance/foreign/signatures.lt), [foreign/types.lt](../conformance/foreign/types.lt), [foreign/where.lt](../conformance/foreign/where.lt), [program/syntax_error_in_exported_function.lt](../conformance/program/syntax_error_in_exported_function.lt).

<a id="c.types-c-takes"></a>
A foreign function's parameters and result have the types of [c.exported-signatures](#c.exported-signatures), or one of three more:

- `c.Ptr<T>`, from the module `std.c` ([c.module-std-c](#c.module-std-c)), an address that C reads or writes, for `T` one of those types, `()` for `void`, or another `c.Ptr`;
- `c.Str`, from `std.c`, a NUL-terminated string, C's `const char *`;
- `()`, as a result only.

Any other type is E0353, *type C can't take*, at the type.

Tests: [foreign/broken_pointee.lt](../conformance/foreign/broken_pointee.lt), [foreign/signatures.lt](../conformance/foreign/signatures.lt), [foreign/types.lt](../conformance/foreign/types.lt).

<a id="c.effects"></a>
A foreign function's code is outside what inference reads, so a call of it adds what any C code may do: the implicit effects `panic`, `alloc` and `div`, and, when its row holds `io`, every capability: `fs`, `net`, `clock`, `env`, `console`, `rand`, `spawn` and `exec` ([facts.inferred-facts](15-facts.md#facts.inferred-facts)). It adds no `overflow`, `copy` or `locks`, which count operations that Stilt's own code performs on its values. So a function that wraps a call of C in an `unsafe` block has these facts, and so has each of its callers: `without alloc` or `without net` rejects a call of such a wrapper as it rejects one of a native that allocates.

A foreign function's declaration may end with a `without` clause, which names what its C code doesn't do. A call of it adds none of the facts and capabilities that the clause names. No check reads C code, so the clause is a statement that the program makes, as the reason of an `unsafe` block is ([c.unsafe-because](#c.unsafe-because)). A name that a call wouldn't add anyway, such as `overflow`, or a capability of a function without `io`, is allowed, and changes nothing. A limit that holds only because of such a clause is **trusted**, which `stilt show` says ([c.unsafe-and-foreign](#c.unsafe-and-foreign)).

Tests: [foreign/types.lt](../conformance/foreign/types.lt), [foreign/c_facts.lt](../conformance/foreign/c_facts.lt), [foreign/c_trusted.lt](../conformance/foreign/c_trusted.lt).

## Unsafe code

<a id="c.unsafe-operations"></a>
These operations are **unsafe**. They stand only inside an `unsafe` block, or they are E0436, *unsafe operation outside `unsafe`*, at the call, or at the name of a function used as a value:

- a call of a foreign function, or a use of one as a value;
- `p.read()`, `p.write(v)` and `p.read_list(n)` on a `c.Ptr<T>`, which read or write `T`s at its address, and a use of one of these as a value;
- `s.to_str()` on a `c.Str`, which copies its bytes up to the NUL, and a use of it as a value.

Test bodies and doc examples are code like any other: an unsafe operation in one needs a block too. This is part of the systems tier.

Tests: [foreign/outside.lt](../conformance/foreign/outside.lt).

<a id="c.unsafe-because"></a>
`unsafe because "reason" { … }` is a block expression, whose value is its block's (the `primary` production, [syntax.expressions](03-syntax.md#syntax.expressions)). The reason is a string literal with no interpolation and at least one character that isn't whitespace ([lexical.whitespace](02-lexical.md#lexical.whitespace)). A reason with no such character is E0437, *`unsafe` with no reason*, at the reason. `unsafe` without `because` is E0100, *syntax error*. Like a block, the form stands in no head ([expressions.heads](08-expressions.md#expressions.heads)). `because` there is a contextual keyword ([lexical.contextual-keywords](02-lexical.md#lexical.contextual-keywords)), and `parse --sexp` prints the form as `(unsafe "reason" BLOCK)`. A closure literal inside the block is inside it, so the closure given to `with_ptr` may call a foreign function. So is a block inside it: `unsafe` blocks nest. This is part of the systems tier.

Tests: [foreign/lending.lt](../conformance/foreign/lending.lt), [foreign/reasons.lt](../conformance/foreign/reasons.lt), [foreign/without_because.lt](../conformance/foreign/without_because.lt).

<a id="c.module-std-c"></a>
The module `std.c` declares the native types `Ptr<T>` and `Str` ([declarations.native-items](10-declarations.md#declarations.native-items)), each held as one word, an address. It declares the operations on them, none of which is in the prelude. Its safe operations, which may be written anywhere, are these:

- `c.null()`, a `c.Ptr<T>` whose address is 0, its `T` inferred;
- `p.is_null()` and `s.is_null()`, whether a `c.Ptr` or a `c.Str` is 0;
- `p.offset(n)`, which moves an address by `n` elements of `T`, wrapping as a `u64` does;
- `p.address()`, its value as a `u64`.

Tests: [foreign/lending.lt](../conformance/foreign/lending.lt), [foreign/memory.lt](../conformance/foreign/memory.lt).

<a id="c.element-types"></a>
`read`, `write`, `read_list` and `offset` take a `c.Ptr<T>` whose `T` is a type of [c.exported-signatures](#c.exported-signatures) other than `()`, or a `c.Ptr`. They read and write each `T` as C holds it. An integer or a float is held in its width, `bool` in one byte, 0 or 1, and a `c.Ptr` in the width of the target's addresses. With any other `T`, a type parameter among them, the call is E0353, at the call. `p.read_list(n)` reads `n` elements one after another from the address of `p`, and gives `[]` when `n <= 0`. `s.to_str()` replaces each maximal subpart of an invalid UTF-8 sequence with one U+FFFD, as `read_line` does ([std.read-line](17-std.md#std.read-line)).

Tests: [foreign/elements.lt](../conformance/foreign/elements.lt), [foreign/lending.lt](../conformance/foreign/lending.lt), [foreign/memory.lt](../conformance/foreign/memory.lt).

<a id="c.lending-buffer"></a>
For a list whose elements are of a type that `read` takes ([c.element-types](#c.element-types)), and for a `str`, these methods lend C a buffer:

- `xs.with_ptr(f)` calls `f` with the address of the list's first element, a `c.Ptr<T>`, and returns what `f` returns. The list stays alive and unmoved until `f` returns. An empty list lends an address that isn't 0 and that C may not read.
- `xs.with_mut_ptr(f)`, with `xs` taken `inout`, lends an address that C may write through, and the list holds what C wrote when `f` returns. The list is made unique first, as any write makes it ([facts.own-storage](15-facts.md#facts.own-storage)).
- `s.with_c_str(f)` on a `str` calls `f` with a NUL-terminated copy, a `c.Str` that lives until `f` returns. A `str` that holds a NUL panics at the call with the kind `nul-in-string` ([effects.panic-kinds](12-effects.md#effects.panic-kinds)), which counts against `without panic`. The detail is `the string holds a NUL at byte N`, where `N` is the first NUL's offset.

With a list of any other type, `with_ptr` and `with_mut_ptr` are E0353, at the call. An address kept after `f` returns dangles, and only unsafe code can read through it.

Tests: [foreign/elements.lt](../conformance/foreign/elements.lt), [foreign/lending.lt](../conformance/foreign/lending.lt), [foreign/memory.lt](../conformance/foreign/memory.lt), [foreign/nul.lt](../conformance/foreign/nul.lt).

<a id="c.lending-methods"></a>
`with_ptr` and `with_mut_ptr` are methods of `List<T>`, and `with_c_str` a method of `str`. They are declared in the prelude, their types' home module ([traits.impl-blocks](11-traits.md#traits.impl-blocks)). `with_c_str` panics and allocates. `with_mut_ptr` allocates, as a native whose `inout` parameter names `List` does ([facts.native-allocation](15-facts.md#facts.native-allocation)). `with_ptr` does neither. Calling them leaves a module in its tier ([c.systems-tier](#c.systems-tier)).

Tests: [foreign/nul.lt](../conformance/foreign/nul.lt).

Checked by: also the facts suite, whose `tests/facts/foreign.lt` gives a call of `with_c_str` `PANIC` and `ALLOC`, which `just facts` checks.

## The facts of unsafe code

<a id="c.unsafe-and-foreign"></a>
A function or method whose own code holds an `unsafe` block, a closure literal's body included, has the inferred fact `unsafe`. The foreign functions that its own code names are its fact `foreign` ([facts.inferred-facts](15-facts.md#facts.inferred-facts)). Neither fact is inherited: a caller of a function that wraps a call of C in an `unsafe` block has neither. `stilt show` prints `unsafe` and `foreign: NAME, …` last in the bracket after the signature, with the foreign functions in the order the body first names them. The line of each block's `unsafe` ends with the comment `` // unsafe because "REASON" ``. Each line that names a foreign function ends with `` // `NAME` is C code ``, and with `` // `NAME` is C code, trusted without LIMITS `` when its declaration has a `without` clause, `LIMITS` the clause's names in the order of the `limit` production ([syntax.programs](03-syntax.md#syntax.programs); [c.effects](#c.effects)). `show --json` gives each function two lists. `unsafe` lists each block, with its `line` and its `cause`. `foreign` lists each line that names a foreign function, with its `line`, its `name` and its `cause`.

Checked by: the facts suite, whose `UNSAFE` annotations, at the line of each block's `unsafe`, and `FOREIGN name` annotations, at each line that names a foreign function, `just facts` checks, and the toolchain's tests of `stilt show` (`compiler/stilt-cli/tests/foreign.rs`).

<a id="c.without-unsafe"></a>
`unsafe` is a limit ([facts.without](15-facts.md#facts.without)). A module's or a function's `without unsafe` makes each `unsafe` block of its own code E0204, *fact beyond a `without` limit*, at its `unsafe`. It limits its own code alone, since the fact isn't inherited. Test bodies and doc examples are exempt, as they are from every limit. In a `without` clause, `unsafe` is a reserved word ([lexical.reserved-words](02-lexical.md#lexical.reserved-words)), so it is no contextual keyword.

Tests: [foreign/limits.lt](../conformance/foreign/limits.lt), [foreign/module_limit.lt](../conformance/foreign/module_limit.lt).

<a id="c.systems-tier"></a>
A module is in the systems tier ([program.module-tier](04-programs.md#program.module-tier)) when it declares a foreign function, writes an `unsafe` block or names `std.c` with `use`. A module that only calls `with_ptr`, `with_mut_ptr` or `with_c_str` stays in its tier. So does a function whose signature names the types of `std.c`, as one that names `std.par` does ([par.core-tier](14-tasks.md#par.core-tier)).

Checked by: the facts suite, whose `tests/facts/foreign.lt` carries `//~ tier: systems`, which `just facts` checks.

<a id="c.unsafe-in-api"></a>
`unsafe` and `foreign` are no limitable facts of a package's API, since no caller inherits them ([versions.limitable-facts](21-versions.md#versions.limitable-facts)). A `pub` foreign function is part of the API with its signature. Whether the package's own code holds an `unsafe` block is part of the API, as whether it performs `io` is. It is counted as [packages.own-effects](04-programs.md#packages.own-effects) counts calls: test bodies, doc examples and bodies with errors hold none. A version that starts to hold one needs a new major version, and one that stops needs a new minor version ([versions.change-needed](21-versions.md#versions.change-needed)).

Tests: [foreign/ungranted/main.lt](../conformance/foreign/ungranted/main.lt).

Checked by: also the toolchain's tests of versions (`compiler/stilt-cli/tests/versions.rs`).

## Packages that call C

<a id="c.granting-unsafe"></a>
A dependency whose own code holds an `unsafe` block, counted as [c.unsafe-in-api](#c.unsafe-in-api) counts it, needs `"unsafe"` in its entry's `may`, as an effect does ([packages.grants](04-programs.md#packages.grants), [facts.capability-grants](15-facts.md#facts.capability-grants)). Without it, the dependency is E0608, *effect that the manifest doesn't grant*, at its entry. The message names the first function that holds a block, by its address, with the block's line. So no dependency runs C code that its user didn't grant, and a root package needs no grant for its own. `io` doesn't grant `unsafe`, and `"unsafe"` listed twice is E0600, *malformed manifest*. When a manifest doesn't grant a dependency `unsafe`, `run` treats each function of that dependency whose own code holds an `unsafe` block as code with an error ([packages.running-with-ungranted-effect](04-programs.md#packages.running-with-ungranted-effect)).

Tests: [foreign/granted/main.lt](../conformance/foreign/granted/main.lt), [foreign/io_grant/main.lt](../conformance/foreign/io_grant/main.lt), [foreign/link_names/main.lt](../conformance/foreign/link_names/main.lt), [foreign/ungranted/main.lt](../conformance/foreign/ungranted/main.lt).

<a id="c.linking"></a>
`[package]` takes a key `link`, a list of the names of the C libraries that the package's foreign functions need, as `link = ["z"]`. Each is a library that the system's linker finds as `-lz` ([packages.package-table](04-programs.md#packages.package-table)). A name that isn't a string of one or more letters, digits, `_`, `-` and `.` is E0600, *malformed manifest*, at the string.

Tests: [foreign/link_names/main.lt](../conformance/foreign/link_names/main.lt).

<a id="c.finding-libraries"></a>
Every command that checks a program looks for each library of each of its packages as the system's dynamic loader finds one, by the bare name: `libz.dylib` on macOS and `libz.so` elsewhere. It looks without loading the library, so no code of it runs until the program does. A library that isn't found is E0611, *C library that isn't found*, at its string.

Tests: [foreign/missing_library/main.lt](../conformance/foreign/missing_library/main.lt).

<a id="c.loading-libraries"></a>
`run` and `test` load the libraries of every package of the program when the program starts, before any of its code runs. So does an executable that `stilt build` writes for a target whose executables load shared libraries. The libraries load in the order of the packages: the root first, then each dependency of a manifest in the order of its entries, depth first, each package once. That is how `stilt build` links them: the executable names its libraries, and loads them as `run` does.

Tests: [foreign/zlib/main.lt](../conformance/foreign/zlib/main.lt).

<a id="c.build-targets"></a>
A program whose packages link a library builds only for the host's own target, the one that `stilt build` writes without `--target`. It builds only when that target's executables load shared libraries, as aarch64 macOS's do. A Linux executable, x86-64 or aarch64, is static, and a WebAssembly module loads no library. A build for any other target is E0612, *C libraries for another target*, at the first library in the order of [c.loading-libraries](#c.loading-libraries). A program whose packages link no library may call a function of the target's C library on any target, such as `strlen`, which the build takes from that library. That C library is musl's for x86-64 Linux, and WASI's for `wasm32-wasip1`.

Checked by: the toolchain's tests of foreign functions, E0612 for x86-64 Linux and for WebAssembly, and `strlen` called from a module built for `wasm32-wasip1` (`compiler/stilt-cli/tests/foreign.rs`), since the command-line protocol gives no target.

## Calls into C

<a id="c.calls"></a>
A foreign call runs on the calling thread, with C's calling convention for the target, and blocks the thread until C returns. A call inside a `par` or a task runs on its worker's thread. No panic crosses C, and what C code that calls back into Stilt does is not defined. Compile-time code performs nothing ([macros.procedural-bodies](16-meta.md#macros.procedural-bodies)), and C's code is outside what a macro's run can reach. A run that calls a foreign function, `with_ptr`, `with_mut_ptr`, `with_c_str` or a native of `std.c` stops there, as one that takes too many steps does. E0226, *macro that didn't finish*, then gives the reason `it reached C through NAME`, with the function's name ([macros.step-limits](16-meta.md#macros.step-limits)).

Tests: [foreign/compile_time/main.lt](../conformance/foreign/compile_time/main.lt), [foreign/types.lt](../conformance/foreign/types.lt), [foreign/zlib/main.lt](../conformance/foreign/zlib/main.lt).

<a id="c.finding-functions"></a>
Under `run` and `test`, and on a target whose executables load libraries, a foreign function is found by its name. It is the function of that name in the C library or in the libraries of [c.linking](#c.linking). It is found at its first call. A name that none of them defines ends the program at that call, with `fatal: no C function NAME` on stderr and status 134, as running out of memory does ([program.exit-statuses](04-programs.md#program.exit-statuses)).

Tests: [foreign/missing.lt](../conformance/foreign/missing.lt), [foreign/zlib/main.lt](../conformance/foreign/zlib/main.lt).

<a id="c.both-implementations"></a>
The reference interpreter calls C as the compiler does, through the platform's foreign-function interface. It copies a lent list into a C buffer and, for `with_mut_ptr`, back into the list when the closure returns. So a program that calls C means the same under both, and the conformance tests of this chapter run under both.

Tests: [foreign/granted/main.lt](../conformance/foreign/granted/main.lt), [foreign/lending.lt](../conformance/foreign/lending.lt), [foreign/memory.lt](../conformance/foreign/memory.lt), [foreign/missing.lt](../conformance/foreign/missing.lt), [foreign/nul.lt](../conformance/foreign/nul.lt), [foreign/types.lt](../conformance/foreign/types.lt), [foreign/zlib/main.lt](../conformance/foreign/zlib/main.lt), [foreign/c_trusted.lt](../conformance/foreign/c_trusted.lt).

## WebAssembly

<a id="wasm.target"></a>
`stilt build --target wasm32-wasip1`, with or without `--release`, writes a WebAssembly module, `NAME.wasm`. The module is a WASI command that imports only WASI preview 1's `wasi_snapshot_preview1` functions. Both builds are made through C, as a release build is ([builds.release-toolchain](#builds.release-toolchain)), so every target has builds from either host. Without `--release`, the module keeps every check, which changes nothing that it does. `--lib` with this target is an error that names the target.

Checked by: the toolchain's tests of WebAssembly: both builds, a module's name and imports, and `--lib` refused (`compiler/stilt-cli/tests/wasm.rs`), since the command-line protocol gives no target.

<a id="wasm.same-meaning"></a>
A program built for `wasm32-wasip1` means what it means on every other target ([builds.same-meaning](#builds.same-meaning)). Its output, its status and its panics' reports are the same, except the statuses of [wasm.exit-statuses](#wasm.exit-statuses). The runtime that the module runs in gives it its arguments, environment, files and console. The transcendental functions of `std.math` are within the tolerance of [std.math](17-std.md#std.math), as on every target. The target's **reference runtime** is wasmtime, at the version that the conformance runs pin. The paragraphs below that depend on a runtime's choices are stated for it.

Checked by: `just cross`, which runs the conformance suite's run tests as `wasm32-wasip1` modules under wasmtime.

<a id="wasm.what-std-reads"></a>
Every native of `std` works through WASI preview 1. That covers the environment and arguments, the clocks, randomness, standard input with `io.poll_line`, standard output and error, and files. Files are reached through the directories that the runtime grants, which are the only ones a program reaches there. A path names a file of the module's own tree, in which the runtime places each directory it grants. wasmtime's `--dir DIR` places `DIR` at the path `DIR`, and `--dir .` at the root, which is the working directory too. So `/etc/hosts` then names the granted directory's `etc/hosts`. A path in no granted directory raises `PermissionDenied`. A path in a granted directory that holds nothing there raises `NotFound` ([std.io-errors](17-std.md#std.io-errors)). WASI preview 1 runs no other program and opens no socket. So on this target, every command of `std.process` raises `PermissionDenied` with its program ([std.process-starting](17-std.md#std.process-starting)). `net.lookup` raises it with its host, and `net.connect` and `net.listen` with their `host:port` ([std.net-listeners](17-std.md#std.net-listeners)).

Checked by: the toolchain's tests of WebAssembly: a granted file, a file outside the granted directories, a file of a directory granted as `.` named from the root, the arguments, environment, clock and randomness, and standard input polled (`compiler/stilt-cli/tests/wasm.rs`).

<a id="wasm.tasks-in-order"></a>
On this target, `task.threads()` runs each task and each scope's function in order, where `spawn` starts it, as `task.sequential()` does. `std.par` runs its closures in order on one thread. Both give the sequential run, which is the program's meaning ([tasks.sequential-run](14-tasks.md#tasks.sequential-run), [par.sequential-meaning](14-tasks.md#par.sequential-meaning)). `when` blocks run in that order too ([shared.when](14-tasks.md#shared.when)).

Checked by: `just cross`, which runs the conformance suite's tests of tasks, scopes, `std.par` and `when` as modules.

<a id="wasm.handlers-that-resume"></a>
A handler that resumes runs on a stack of its own, as on every target ([handlers.resuming](12-effects.md#handlers.resuming)). The cost of making that stack falls only on the bodies of handlers that resume. They are the only functions of the program on such a stack when it switches, since a body calls `resume` itself. No other function pays the cost, whatever its row.

Checked by: `just cross`, which runs the conformance suite's tests of handlers that resume as modules, and the toolchain's tests of WebAssembly (`compiler/stilt-cli/tests/wasm.rs`).

<a id="wasm.limits"></a>
A module's memory is at most 4 GiB. Its own stack is 8 MiB. The depth of [program.recursion-depth](04-programs.md#program.recursion-depth) holds when the runtime gives its code 4 MiB of stack, as wasmtime does with `-W max-wasm-stack=4194304`. A stack overflow and running out of memory end the program with status 134, as on every target ([program.exit-statuses](04-programs.md#program.exit-statuses)). The program ends after `fatal: <reason>` when the module finds the failure, and after the runtime's own report when the runtime's stack runs out first.

Checked by: the toolchain's tests of WebAssembly: a recursion 10,000 calls deep, a deeper one, a stack frame past the module's stack and memory past 4 GiB (`compiler/stilt-cli/tests/wasm.rs`).

<a id="wasm.exit-statuses"></a>
WASI preview 1's `proc_exit` takes a status only below 126. So under the reference runtime, a program that calls `exit(code)` with a code from 126 to 255, other than 134, ends with status 1. It ends after everything it wrote, and then the runtime's report of the status on stderr. The module gives 134 by a trap, after which the runtime reports the trap.

Checked by: the toolchain's tests of WebAssembly, `exit` with 125, 126, 134 and 255 (`compiler/stilt-cli/tests/wasm.rs`).

<a id="wasm.conformance-runs"></a>
The conformance suite's run tests run as `wasm32-wasip1` release builds under the reference runtime. They run with the stack of [wasm.limits](#wasm.limits), and with the test's directory and `/tmp` granted. The tests of `std.process`, `std.net` and `std.http`, in `conformance/process/`, `conformance/net/` and `conformance/http/`, are left out. They need the programs and the sockets that WASI preview 1 lacks ([wasm.what-std-reads](#wasm.what-std-reads)).

Checked by: `just cross`.
