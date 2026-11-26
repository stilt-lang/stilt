# Contributing to Stilt

Thank you for helping. This page tells you how to set up, how to make a first change, what the tests expect, the style the code follows, how AI tools are treated, and how issues are triaged. [GOVERNANCE.md](GOVERNANCE.md) says who decides what.

Stilt is built interpreter first. The [Reference](reference/) defines the language, the reference interpreter implements it as simply as possible, and every other implementation is tested against the interpreter. A change is welcome when it keeps those three in agreement.

## Set up

You need [rustup](https://rustup.rs), [opam](https://opam.ocaml.org) 2.2 or later, [elan](https://github.com/leanprover/elan), [uv](https://docs.astral.sh/uv/), [just](https://github.com/casey/just), a C compiler, and on macOS Homebrew's LLVM (`brew install llvm`) for the playground. The clang of release builds is fetched by `just toolchain`, the release that `stilt` pins. [README.md](README.md) lists the libraries. Then:

```sh
git clone https://github.com/stilt-lang/stilt
cd stilt
just setup
```

`just setup` checks that the tools are there, creates the repository's opam switch, fetches the pinned Rust and Lean toolchains, and builds everything. The first build is the long part; later ones are incremental. Docker is needed only for `just sanitizers`, `just debuggers` and `just cross`.

`just` alone lists every recipe, grouped by what it does. `just ci` runs everything the pull-request checks run; run it before you call a change done. In a git worktree, which has no opam switch of its own, set `STILT_SWITCH` to the main checkout's path.

## Make a first change

A good first change is small and has a test. Some places to start: an issue labelled `good first issue`; a diagnostic that confused you, whose message you can improve; a program of your own that exposes a bug, which becomes a conformance test; a paragraph of the guide that taught you less than it could.

1. Make a branch from `main`.
2. Make the change, and its tests (see below). For a change to the language, start with the next section.
3. Run the recipes your change touches, then `just fmt` and `just ci`. For a change to a message, `just diagnostics` and `just diagnostics-tokens`; to the guide, `just guide`; to the compiler's behaviour, `just conformance`, `just check` and `just run`.
4. Add a change file: a short file in [`changes/`](changes/), named for the change, saying what it does for a user ([its README](changes/README.md)). A change with no effect on users, such as a refactoring or a test, takes the label `no-changes-file` instead.
5. Open a pull request. Say what changed and why. Each commit does one thing, and its message starts with a short summary in the imperative mood, such as "Lex format specs", followed by a blank line and an explanation of why the change is needed.

A maintainer reviews it ([GOVERNANCE.md](GOVERNANCE.md)). Review is a conversation; a request for changes is not a rejection.

## Changing the language

A change to the language is decided in an [RFC](https://github.com/stilt-lang/stilt-rfcs), a document that starts with a plain example and ends with the error messages the feature needs. Write or comment on one there before you write code; the RFC repository says what needs one. An accepted RFC is then implemented in this repository in this order:

1. **Change the Reference.** Amend or add the paragraphs that state the rule, in [`reference/`](reference/), each precise enough to test, and say why in the chapter's rationale. A paragraph's ID never changes and is never given to another rule ([Paragraph IDs](reference/README.md#paragraph-ids)).
2. **Update the documents** in the same change, so they describe the language exactly as the Reference states it.
3. **Write the tests** the paragraphs need, and link them from each paragraph's `Tests:` line. Expected output is derived from the Reference by reasoning, never by running an implementation.
4. **Implement the rule** in the reference interpreter, then in the compiler.

A clarification that changes no program's meaning needs no RFC; it is a pull request.

## Diagnostics

Every diagnostic code is registered in [`reference/errors.toml`](reference/errors.toml), with the paragraph that defines it, its home. Codes are never reused. Each entry gives the help printed under the code's diagnostics, and examples of the mistake and of its fix, unless one file can't show it. `cargo run -p stilt-registry` generates from the registry the codes of both implementations, the language server's links to the error index, the list of codes that the coverage report expects, and the [error index](docs/errors/) itself, which shows each code's examples and the renderings of its snapshots; `just diagnostics` and `just coverage` fail when one of them isn't current, and `just guide` checks the examples.

## Tests

- **Conformance tests** are `.lt` files under `conformance/`, annotated as [Conformance](reference/01-conformance.md) defines. Each cites the paragraphs it covers, such as `//~ rule: numbers.integer-panics`. Drafts go in `conformance/_pending/`, which the runner skips until `just approve` moves them out; it moves only drafts that cite paragraphs of the Reference. Every paragraph of the Reference has a test, and every paragraph that rejects programs has an accepted and a rejected one; `just coverage` reports the gaps.
- **Unit tests** live next to the code: `ppx_expect` tests in `interpreter/test/`, and `#[test]` functions in each Rust crate.
- **Formatter tests** are pairs of files under `tests/format/`: an input, and the output that the canonical format ([syntax.format](reference/03-syntax.md#syntax.format)) gives it, derived from the Reference by hand, never by running the formatter ([its README](tests/format/README.md)).
- **Diagnostics snapshots** are programs under `tests/diagnostics/`, each with the rendering of its one diagnostic. A changed message is drafted in `tests/diagnostics/_pending/` with `just snapshots-draft`, which writes the compiler's rendering; you review it line by line, as a person reading the message for the first time would, and accept it with `just snapshots-accept` ([its README](tests/diagnostics/README.md)). A snapshot is the one expected output that comes from an implementation, and the review is what makes it expected.
- **Never edit a test's expectation to make it pass** without citing the paragraph of the Reference that justifies the new expectation.

## Code

- **Formatting.** `just fmt` formats everything. CI rejects unformatted code.
- **Lints.** Rust code passes `clippy::pedantic` with no warnings, and `unsafe` is forbidden outside the runtime, the Cranelift back end and the meter, a tool that reads a process's counts.
- **Dependencies.** A crate the workspace depends on comes from crates.io, under a licence that [deny.toml](deny.toml) allows, and in one version unless the file names the crate that holds the other; `just lint` checks this with [cargo-deny](https://github.com/EmbarkStudios/cargo-deny) where it is installed, and CI also checks the dependencies against the RustSec advisories.
- **Size.** A source file stays under 500 lines and aims at 400. A function stays within 60 lines; in OCaml, a top-level definition does, counted with its local helpers. Split by concern, so that each file holds the one thing its name says. `just lint` checks both limits. They bind the implementations' code, not Stilt modules, since a Stilt file is a module ([program.forms](reference/04-programs.md#program.forms)).
- **Modules.** A Rust module with submodules is `name.rs` beside a `name/` directory, never `mod.rs`. A new OCaml module is named after the module it comes from and its concern, such as `check_patterns.ml`.
- **No placeholders.** Code is either finished or absent: no `todo!`, `unimplemented!` or `failwith "TODO"` outside tests.
- **Comments** say why, not what. A comment cites a paragraph of the Reference where the rule isn't plain from the code. A paragraph that justifies a workaround usually means the code should change instead.
- **Interfaces.** Every OCaml module has an `.mli` that documents what it exports.
- **Describe things as they are.** Code, comments and documents say what the language and its tools do, in the present tense, not how they came to be so.

## Writing

Every page of the documentation, from the tour to a doc comment in the standard library, follows [docs/writing.md](docs/writing.md): what kind of page you are writing, plain words and short sentences, one term for each idea, and examples that the tests run.

## AI tools

AI tools are welcome here, and Stilt was itself written with them: one person decides the design, agents write much of the code, and the Reference, the reference interpreter and the conformance suite judge every line. The rules are the same as for everyone's code:

- **You are responsible for every line** you submit, whoever or whatever wrote it. You can explain it, you have run it, and you accept the maintainers' questions about it.
- **A large generated change says so** in its pull request: which tool, what it was asked, and what you checked yourself. A reviewer is entitled to read a generated change with the care that its size asks for, or to ask for it in smaller parts.
- **The review bar is the same.** Generated code that doesn't follow the style above, or whose tests only repeat what it does, is sent back like any other.
- **Expected output still comes from the Reference.** A test whose expectation was copied from an implementation's output proves nothing.
- Don't send automated comments, issues or reviews that no person has read.

[AGENTS.md](AGENTS.md) gives the commands and rules that such a tool needs.

## Triage

How maintainers treat what you report:

- **A divergence is a bug.** If the compiler and the reference interpreter disagree on a program, one of them is wrong, or the Reference is silent, and the Reference is fixed. Report it with the divergence template.
- **An internal error is a bug of the highest priority**, whatever the program: a panic of the compiler, a crash, a hang, or a message that says the tool itself failed. The report doesn't need to say why.
- **A confusing message is a bug.** A diagnostic that made you stop and wonder what to do is worth an issue; it doesn't matter that it is correct.
- **A feature idea goes to the [RFC repository](https://github.com/stilt-lang/stilt-rfcs)**, where it is discussed until it can become an RFC. Issues here that ask for a feature are moved there.
- **A security problem is reported privately**, as [SECURITY.md](SECURITY.md) says.
- An issue with a program that reproduces it is looked at first. Labels say the area and whether more information is needed; an issue waiting for information for a month is closed, and reopens when it arrives.

## Licence

Code and the conformance suite are under the MIT and Apache 2.0 licences, at your option; the prose of the guide, the design documents and the Reference is under CC BY 4.0 ([README.md](README.md#license) lists the paths). There is no contributor licence agreement: you contribute under the licence of the files you change, and keep your copyright.
