# Rationale: Builds, C and WebAssembly

A debug build compiles in milliseconds and keeps every check, so an edit is soon running. A release build spends its compile time on the program's speed instead, and aims to run within a fifth of the same program in Rust. It must mean exactly what the debug build means. The bridges to C and to WebAssembly follow the same rule. What crosses them is visible in the source and in the tools, and a program means the same on every target.

## Release builds

A release build is a flag of `stilt build` ([builds.release-builds](../20-builds.md#builds.release-builds)), with no command or dialect of its own. It differs from a debug build in speed and memory only ([builds.same-meaning](../20-builds.md#builds.same-meaning)). The alternative is a release build that keeps fewer checks, as Rust's release profile wraps on overflow. The two builds would then mean different things, and a bug would show in one and hide in the other. A release build may drop only what can't fail, the checks that verification proves ([builds.dropped-checks](../20-builds.md#builds.dropped-checks)). The reference interpreter, debug builds and release builds are compared on the conformance suite's run tests and on generated programs. A difference between them is a bug of the toolchain.

The depth at which the stack overflows may differ, since a call in tail position may become a jump. In either build, it is at least the depth that every implementation supports. A release build refuses a program with a hole ([builds.what-it-refuses](../20-builds.md#builds.what-it-refuses)), since a hole is unfinished code, and a release is meant to run. Its line tables keep its panics and profilers pointed at the program's lines ([builds.line-tables](../20-builds.md#builds.line-tables)), while its locals may be optimized away. The debug build is the one made for a debugger.

**How release builds are made.** None of this is part of the language.

- The program is lowered after reference counting, as for a debug build, to one C file per module. One more file, `program.c`, holds the code that no module holds: the constants' cells and C's `main`. A function that no other file names is `static`, so that clang sees every call of it.
- The files are compiled at `-O2` across the machine's cores, with no optimization across them. Each object is kept in the cache under the hash of its file's name, its C, the clang and the flags. So a build compiles again only the files whose C changed, and an object unused for a week goes.
- The runtime's fast paths are a header that clang inlines: counting references, reading and writing an element, pushing, popping and testing that a value is unique. The header starts with the runtime's layout constants, written from the runtime's own definitions. It ends with `_Static_assert`s of what the fast paths take for granted of them. Every other operation calls the runtime's library, the same one a debug build links.
- A list's length and the address of its elements stay in C locals across stores to its elements. They are read again after anything that may change them: an assignment to the place or local that holds the list, a call, an append, a pop, or a runtime function that makes a value unique.
- The C never reaches C's undefined behaviour. Overflow goes through checked builtins, and wrapping arithmetic through unsigned types. A shift checks its amount, and a division its divisor and `MIN / -1`. A float converted to an integer checks its range. Loops are labels and jumps, since C lets a compiler assume that a loop ends.
- The code compiles with `-std=c11 -O2 -ffreestanding -fwrapv -fno-strict-aliasing -ffp-contract=off -fno-math-errno -fno-stack-protector -w`. `-ffp-contract=off` keeps clang from fusing a multiply and an add into one rounding. `-fno-math-errno` keeps it from calling a library's `sqrt` for `errno`.
- `-fstack-clash-protection` probes each page of a large frame, so that a stack overflow still faults in the guard page and ends with status 134.
- Line tables come from `#line` directives relative to the build's directory (`-gline-tables-only -fdebug-compilation-dir=.`).
- On aarch64, clang's pairing of neighbouring loads and stores is turned off, since it stalls a load on a field stored just before.

## The release toolchain

The compiler lowers the program to C and has clang compile it ([builds.release-toolchain](../20-builds.md#builds.release-toolchain)), as Lean, Nim and Koka do. The C compiler's optimizer, profile-guided, is decades of work that no new back end would match, and every target that a C compiler reaches comes with it. The C is freestanding and links as a debug build links. So a release build needs no SDK and no system headers, and builds for every target from either host. These alternatives are rejected:

- **The system's C compiler.** A release build would need one installed, against the rule that one `stilt` binary needs nothing else. The same source would build differently on each machine, with each version of clang or GCC. The same holds of a Linux distribution's clang on a host whose archive isn't published: its version isn't the one named. So `STILT_CC` names it, and gives up identical bytes knowingly ([builds.another-compiler](../20-builds.md#builds.another-compiler)).
- **`zig cc`.** It is a compiler before its first stable release, moving clang out of its binary, and without the runtime that profile-guided builds need. Each of its releases would become a dependency.
- **LLVM inside `stilt`.** It would add more than 100 MB to every user's binary, used only by release builds, and an LLVM build to the compiler's own.
- **LLVM IR as the output.** The runtime would have to ship as bitcode of clang's version to be inlined. Lean's LLVM back end lost to its C back end on exactly that.
- **Link-time optimization across Rust and C.** It needs rustc's LLVM and clang's to be the same version, so every Rust update would force a new toolchain. The header's fast paths already inline what matters.
- **Link-time optimization across the program's files, or one C file for the program.** The linker's LLVM isn't clang's. One file would compile again in full after every edit, and on one core, where the files of a 100,000-line project compile in a third of the time across ten. A function that only its module calls stays `static`, which gives clang the calls that matter. The benchmark suite's programs run as fast as from one file.

The clang is fetched the first time a release build needs it, pinned by `stilt`'s own version and checked against a hash ([builds.finding-clang](../20-builds.md#builds.finding-clang), [builds.fetching-toolchain](../20-builds.md#builds.fetching-toolchain)). So one binary needs nothing else installed, and the same source gives the same executable on every machine ([builds.same-bytes](../20-builds.md#builds.same-bytes)). A machine without the network builds no release build until its cache holds the toolchain, which can be copied in. Debug builds need nothing fetched. Release builds are slower to make: they spend seconds where debug builds spend milliseconds.

## Specialization

A debug build compiles a generic function once for each layout of its type arguments, and a function that reflects once for every type. It passes the function its bounds' dictionaries, its value parameters and a description of each type it reflects on. An edit of a type then compiles nothing again but the functions it changes.

A release build has no edit to patch, so it specializes ([builds.specialization](../20-builds.md#builds.specialization)). The C compiler sees each call's types and values. It folds a `Mod<7>`'s modulus into its arithmetic, and reads a reflected record's fields without a description.

A release build specializes every instantiation that the program reaches, as Rust and MLton do. The alternative is to specialize only what profiles show to be hot, and to share the rest by layout. A new program has no profile, and a profile goes stale with each edit. The cut between hot and cold is a threshold that no suite pins, and the counters would slow debug builds. Go's dictionaries shared by layout run measurably slower than its specialized code. MLton's whole-program specialization grows code by at most about 30%. Merging instantiations whose code is the same keeps the growth down, and the report keeps it visible.

Code that would grow without end keeps its dictionaries ([builds.what-stays-generic](../20-builds.md#builds.what-stays-generic)). That is polymorphic recursion, whose instantiations have no bound, and polymorphic arguments, whose callee isn't known where they are called. The report lists every such call, so no cost is hidden.

A program asks for nothing ([builds.no-specialization-hints](../20-builds.md#builds.no-specialization-hints)). Specialization hints in the source, as Swift's `@_specialize`, are rejected. A release build specializes everything a hint could ask for, and a hint would be a declaration that changes nothing a program does.

**How instantiations are made.** None of this is part of the language. Instantiations are made from the debug build's code after reference counting. Each dictionary, value parameter and type description is replaced by what the instance knows, and the code is simplified before the C is written.

## Profiles

Profiles still help the C compiler choose which branches are likely and which functions are hot ([builds.profiles](../20-builds.md#builds.profiles), [builds.profile-use](../20-builds.md#builds.profile-use)). They are counts that debug runs take on request. They are kept as text beside the manifest, and committed and reviewed as code is, so builds stay reproducible ([builds.profile-form](../20-builds.md#builds.profile-form)).

Each line names a body by its address and hash, and a place by a line counted from the body's first. So an edit above a function keeps its lines, and an edit of the function drops only its own. Counts are rounded down to powers of two, so two runs that differ a little write the same file, and a diff shows only real changes. Two alternatives are rejected:

- **clang's own profiles,** `.profdata`. The format is binary and changes with LLVM's version. It keys each function by a hash of the C, which changes with every change of the compiler. A profile kept in the program's own terms survives all three.
- **Counting in every debug run.** The counters would cost every run, for a profile that most runs don't need.

A run that aborts writes nothing, since its counts may be half written. A run that panics writes them, since its counts are whole, and a test that panics still ran its code.

## The performance report

Every cost that a release build can't remove has a line in the report ([builds.performance-report](../20-builds.md#builds.performance-report)): a generic call left on a dictionary, a reference count, a copy and a check kept. A reader sees where a function pays, and why, without reading the C.

A suite of programs whose costs are known checks the report. What it compiles, what keeps dictionaries, and which checks it drops follow from the rules of this chapter and of verification. Where reference counts fall is the compiler's own choice, so those counts are pinned as reviewed snapshots.

## Exporting functions to C

A program in C, or in any language that calls C, should be able to call a Stilt function: a checksum, a parser's inner loop, a pricing rule. Calling Stilt from C breaks none of the language's guarantees, since the Stilt side is checked as any code is. So exporting needs no `unsafe` ([c.exported-functions](../20-builds.md#c.exported-functions)). `extern` is reserved for this. A function written `pub extern fn` is exported under its own name, so the C side reads as the Stilt side does.

Only numbers and `bool` cross ([c.exported-signatures](../20-builds.md#c.exported-signatures)), so a Stilt function whose values are numbers serves C code with no wrapper. The alternative is strings, lists and records across the boundary. A C caller can't keep the reference counts or the value semantics of a `str` or a `List`. An exported function has no effect but `io`, since C couldn't see a raise or a handler.

An exported function's name is its C symbol ([c.exported-names](../20-builds.md#c.exported-names)). The alternative is a mangled name, such as one built from the module's path. C has one namespace, and the name that the user wrote is the one the C side should call. A clash is an error that the user fixes by renaming. The names that are refused are those that other code of the C program can mean. C++23's keywords are among them, since the header is C++ too. A name beginning with `_` is reserved by C for its implementation, and the prefixes `stilt_`, `lt_`, `f_` and `m_` are the ones that the library's own code uses.

A panic ends the process ([c.calls-from-c](../20-builds.md#c.calls-from-c)). The alternative is returning panics to C as an error code. Every exported function would then need an error channel that its signature doesn't show. A panic is a bug, which ends the process as in Stilt.

The library is static and holds the runtime ([c.static-library](../20-builds.md#c.static-library), [c.library-header](../20-builds.md#c.library-header)). Two alternatives are rejected: a shared library, and one object with only the exported names global, so that a C program could link several Stilt libraries. A static library needs no loader and no versioning. The linker that builds use can't link objects into one. Only numbers cross the boundary, so one program that depends on every package it needs loses nothing. A C program links one Stilt library, which its linker enforces, since two would hold two runtimes under one runtime's names.

Exporting a function changes nothing in its package's API ([c.exported-fact](../20-builds.md#c.exported-fact)), whose callers are Stilt code.

## Foreign functions

Without a way to call C, every library would have to be written again in Stilt or added to the runtime. No user of systems code accepts a language that is a closed world. Stilt's bridge is the smallest one that reaches real C libraries:

- functions of numbers, pointers and strings ([c.foreign-functions](../20-builds.md#c.foreign-functions), [c.types-c-takes](../20-builds.md#c.types-c-takes));
- a buffer lent for one call;
- a block that says why the call is sound.

The alternative is importing only functions of numbers, the mirror of exports. Almost no C library is usable without pointers and strings. Headers imported through libclang, callbacks from C, structs passed by value and variadic functions are rejected too, since each needs layout rules for types that this bridge avoids.

A foreign call adds what any C code may do: `panic`, `alloc` and `div`, and every capability when it performs `io` ([c.effects](../20-builds.md#c.effects)). Inference can't read C. The alternative, counting nothing, would make `without alloc` a promise about the Stilt code alone: a function under it could call a wrapper whose C code allocates, and a reader of its signature couldn't tell. Counting the worst case keeps each limit whole. Where C code is known to do less, its declaration says so, as `extern fn labs(n: i64) -> i64 without panic, alloc, div`, once for every call, since what a C function does doesn't depend on who calls it. No check reads that statement, so `stilt show` marks it trusted at each call, and a review finds every limit that rests on one. A statement on each `unsafe` block instead would repeat it at every call, and two calls could disagree. `overflow`, `copy` and `locks` count operations that Stilt's own code performs on its values, which C code doesn't perform on them, so a foreign call adds none of them.

## Unsafe code

A foreign call can break memory safety and every promise of `without`, so it stands only in an `unsafe` block ([c.unsafe-operations](../20-builds.md#c.unsafe-operations)). The block's reason says why the code is sound ([c.unsafe-because](../20-builds.md#c.unsafe-because)). The alternative is `unsafe` without a reason, as Rust's. The reason is where an author says why the call is sound, and `show` prints it, as `because` on a catch-all says why an error can be dropped.

`std.c` holds the pointer and string types and their operations ([c.module-std-c](../20-builds.md#c.module-std-c), [c.element-types](../20-builds.md#c.element-types)). Reading or writing through an address is unsafe. Making, testing and moving one is safe, since an address alone harms nothing. A list or a string is lent to C for one call ([c.lending-buffer](../20-builds.md#c.lending-buffer), [c.lending-methods](../20-builds.md#c.lending-methods)), and stays alive and unmoved until the call returns. So the common case, C reading or filling a buffer, needs no address that outlives the call.

## The facts of unsafe code

`unsafe` and `foreign` are facts of a function's own code ([c.unsafe-and-foreign](../20-builds.md#c.unsafe-and-foreign)). The alternative is an inherited `unsafe`. Every caller of a safe wrapper would show it, up to `main`, and `without unsafe` would forbid using any library that wraps C. A caller of a wrapper has neither fact, as a caller of Rust's safe wrappers has none. The grant of a dependency keeps C out of dependencies instead.

`without unsafe` ([c.without-unsafe](../20-builds.md#c.without-unsafe)) keeps C out of code that must stay checked. It is a limit on an inferred fact, and no tier, so a module that only calls a wrapper keeps its tier ([c.systems-tier](../20-builds.md#c.systems-tier)). Whether a package holds an `unsafe` block is part of its API ([c.unsafe-in-api](../20-builds.md#c.unsafe-in-api)), since a dependent's manifest grants it. So a version that starts to hold one breaks that grant.

## Packages that call C

A dependency whose own code holds an `unsafe` block needs the grant `unsafe` ([c.granting-unsafe](../20-builds.md#c.granting-unsafe)), so no dependency runs C code that its user didn't grant. `io` doesn't grant it. `io` says what a package may reach, while `unsafe` says that the package's code steps outside the checks.

A package names the C libraries it needs in its manifest ([c.linking](../20-builds.md#c.linking)). Every command looks for them ([c.finding-libraries](../20-builds.md#c.finding-libraries)), and the program loads them when it starts ([c.loading-libraries](../20-builds.md#c.loading-libraries)). The alternative is linking each library into the executable, as `-lz` on the linker's command line does. A macOS executable built without the system's SDK names, for each symbol it imports, the library that defines it. The build can't tell which library that is without the SDK's stubs. Loading the libraries when the program starts finds every symbol as `run` does. So a program that links C libraries builds only for a host whose executables load shared libraries ([c.build-targets](../20-builds.md#c.build-targets)), and the C library of each target stays reachable from every program.

## Calls into C

A foreign call runs on the calling thread and blocks it ([c.calls](../20-builds.md#c.calls)), as C expects. A function that C doesn't define ends the program where it is first called ([c.finding-functions](../20-builds.md#c.finding-functions)), as the platform's loader would. Compile-time code performs nothing, so a macro's run that reaches C stops. The reference interpreter calls C through the platform's foreign-function interface ([c.both-implementations](../20-builds.md#c.both-implementations)), libffi, which macOS's SDK holds and Linux's `libffi-dev` gives. So both implementations run the same tests.

## WebAssembly

WebAssembly runs a program in a sandbox, on a server, at the edge or in a browser, from one file. `wasm32-wasip1` is a module that WASI's first preview gives files, the environment, clocks, randomness and the console: everything the natives of `std` read ([wasm.what-std-reads](../20-builds.md#wasm.what-std-reads)). Every runtime runs it: wasmtime, wasmer, Node and the browsers' shims ([wasm.target](../20-builds.md#wasm.target)). The alternative is a component of WASI's component model. Preview 1 runs everywhere, gives everything `std` reads, and becomes a component through wasmtime's adapter. WASI preview 1 reactors as libraries are rejected for the same reason: the component model gives WebAssembly libraries typed exports, which a reactor's would only approximate.

Both builds go through C, since Cranelift doesn't write WebAssembly. The alternative is refusing debug builds for this target. A program would then build for every target but this one without a flag, and the C back end's build means what a debug build means. So builds for this target take a release build's time, and an edit isn't patched into a running module.

A program means the same here ([wasm.same-meaning](../20-builds.md#wasm.same-meaning)). Threads are the first gap: wasi-threads is a proposal that runtimes are abandoning, and its successor has no implementation. Tasks and `std.par` run in order ([wasm.tasks-in-order](../20-builds.md#wasm.tasks-in-order)), which means the same, since a program's meaning is its sequential run. A parallel program is correct here, and slower than on a native target.

A handler that resumes is the second gap. It needs a stack of its own, which WebAssembly's stack switching would give, but no browser ships it ([wasm.handlers-that-resume](../20-builds.md#wasm.handlers-that-resume)). These alternatives are rejected:

- **Rejecting such handlers on this target.** A program's validity would depend on its target, which no other part of the language allows.
- **Instrumenting the whole module.** binaryen's Asyncify gives the stack, and its cost falls only on the bodies of handlers that resume. A program that runs 100,000 `with`s whose handler resumes grows by 3%, and runs in 20 ms, against 17 to 23 ms as a native release build. Instrumenting the whole module would make it 3.55 times as large.
- **WebAssembly's stack switching.** No browser ships it and clang doesn't emit it. Asyncify gives the same meaning everywhere, and stack switching would change only speed.

The limits ([wasm.limits](../20-builds.md#wasm.limits)) are WebAssembly's. A handler's body that has resumed and waits for the rest of its `with` holds its own stack, about 1.2 MiB of the module's memory. So about 3,400 wait at once in 4 GiB, while a native target's stacks are reserved and touched only as they are used. A program that keeps more waiting runs out of memory here.

WASI preview 1 passes on an exit status only below 126 ([wasm.exit-statuses](../20-builds.md#wasm.exit-statuses)). So a script that tells a program's endings apart by statuses from 126 up can, on this target, tell only 134 from the rest. The conformance suite runs on this target under wasmtime ([wasm.conformance-runs](../20-builds.md#wasm.conformance-runs)), so a difference from the native targets is found as any bug is.

**How modules are made.** None of this is part of the language.

- The C is compiled by the release toolchain's clang for `wasm32-wasip1` with wasi-libc, which the toolchain holds with binaryen. The runtime's library is built for the same target.
- The stack lies first in memory, so an overflow of it traps. Each function's entry checks the stack pointer against the stack's end, so the runtime reports the overflow and traps.
- WASI's `proc_exit` takes a status only below 126. On Unix, wasmtime ends with 1 for a larger one, and with 134 for a module that traps, so a status of 134 is a trap.
- Asyncify instruments only the functions on a body's frames when it switches. These are the runtime's own, the same in every program, and the bodies that call `resume`, listed by name, since each calls `resume` in its own C.
