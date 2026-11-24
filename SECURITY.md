# Security

## Reporting a vulnerability

Report it privately, through GitHub's security advisories: open the [Security tab](https://github.com/stilt-lang/stilt/security) of the repository and choose "Report a vulnerability", or go to <https://github.com/stilt-lang/stilt/security/advisories/new>. Please don't open a public issue or pull request for it.

A report is most useful with the version (`stilt --version`), the operating system, and the smallest program or command that shows the problem.

You get an answer within five working days. We keep you informed while the problem is confirmed, fixed and released, agree a date with you for publishing the advisory, and credit you in it if you wish. We ask that you don't publish details before the fix is released, and we aim to release it within ninety days of the report.

## What is in scope

- **The compiler**, `stilt`, and what it writes: a program or a package that makes the compiler read or write memory it shouldn't, run code at check time that no `comptime` or macro asked for, or fetch or write files outside what its manifest and the command ask for.
- **The runtime** linked into every executable that `stilt build` writes: memory errors, and the failure of a guarantee that the Reference states and the runtime upholds.
- **The sandbox of compile-time code**: code that runs at compile time, in staged code and in procedural macros, performs nothing ([macros.procedural-bodies](reference/16-meta.md#macros.procedural-bodies)), and stays within its steps, its memory and the size of its expansions; [its threat model](docs/design/compile-time-sandbox.md) states each boundary, and a way around one is in scope.
- **The engine**, the process that `stilt` starts to keep a program's checks warm: how it is started, found and stopped, and what a local user or another program can make it do.
- **The installer**, `install.sh`, and the toolchain archives it installs: what it downloads, how it verifies it, and what it writes.

## What is not in scope

- A mistake in a program written in Stilt, including one that the language is documented not to prevent, such as an `unsafe because` block or a call into C that the program makes.
- A program that was given a capability, such as the network or the file system, using it.
- Problems in a package that isn't in this repository, or in an editor, a shell or an operating system.
- A wrong or confusing diagnostic, or a divergence between the compiler and the reference interpreter. These are bugs; report them in the [issue tracker](https://github.com/stilt-lang/stilt/issues/new/choose).

## Supported versions

The latest release receives fixes. A release is named by its calendar version, as in `2027.1.0`.
