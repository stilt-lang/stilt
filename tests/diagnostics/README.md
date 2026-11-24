# Diagnostics snapshots

Each program here makes the compiler report one diagnostic, of the code its name starts with, and the `.stderr` file beside it is the rendering of `stilt check`, reviewed before it was accepted. They test the wording and the form of messages, which conformance tests never compare ([conformance.diagnostic-text](../../reference/01-conformance.md#conformance.diagnostic-text)), for the requirements on error messages ([Goals](../../docs/design/goals.md), `one-diagnostic-shape` to `working-fixes`, `closest-candidates` and `mismatch-diffs`).

A program is a `.lt` file, or a directory that holds one, as in the conformance suite. The program of a refusal of an edit (E07xx, [edits.refusals](../../reference/19-tools.md#edits.refusals)) has an `edits` file of the same name beside it, which holds the edits of its command, an address on one line and the new text on the next for each. `stilt check --edit` on the program is refused with the code, which no diagnostic of the program accompanies, and its stderr is the snapshot. `E0208_name_defined_twice.lt` is checked against `E0208_name_defined_twice.stderr`. The program of an error about fetched dependencies (E0602, E0604, E0605 and E0607, [packages.fetch-failures](../../reference/04-programs.md#packages.fetch-failures)) has a fixture of the same name with the extension `repos` beside it: a directory for each git repository it fetches from, whose directories, each named by a version such as `1.4.0`, hold the trees that the repository tags `v1.4.0`. The program's manifests name a repository `R` as `file:///repos/R`. The harness builds the repositories, with the git writer of the toolchain's tests, in a directory of the run's own under the system's temporary directory, so that runs at once share nothing, and checks a copy of the program whose manifests give their URLs there. In what the copy renders, it spells those URLs `file:///repos/R` again, and wraps each paragraph of prose that holds one as the renderer wraps it, so that a snapshot reads the same on every machine; a span that follows a URL on its line would move, so no fixture's program has one. It checks the program with an empty cache of its own, once to fetch, then for the rendering, which reports nothing fetched. The program of a stale doc (W0002, [docs.stale](../../reference/04-programs.md#docs.stale)) is a package whose `docs.lock` pins the doc to an older signature, and applying its fix through `check --edit` pins the doc again in the copy. A code has more programs when its message takes another form worth seeing, as `E0211_misspelled_name.lt` shows the fix that names the closest candidate.

## What is checked

`just diagnostics`, part of `just test`, checks that:

- each program reports exactly one diagnostic, of the code its name starts with, and the program of a refusal is refused with its code instead;
- that diagnostic has the shape of `one-diagnostic-shape` in `check --json`: a message, a title, one primary span, and at most two fixes, each with a title and its edits, objects `{at, new}` of parts ([edits.json-form](../../reference/19-tools.md#edits.json-form)), which a fix that changes text outside every part lacks;
- each fix it offers, applied to a copy of the program, leaves the copy without any diagnostic, so the fix removes its diagnostic and causes no other (`working-fixes`). A fix with `edits` is applied through `check --edit`. A fix that changes text outside every part, such as a `use` line, a module header or an impl's header, or in a part whose path names two parts, has no `edits` in the JSON ([edits.fixes-as-edits](../../reference/19-tools.md#edits.fixes-as-edits)), since an edit addresses a part; the harness applies it through the change its rendering shows, which the diagnostic holds as spans of its file;
- its rendering is byte for byte its snapshot;
- every code of the `core` tier that isn't retired has a program.

`just diagnostics-tokens`, part of `just ci`, checks `short-messages`: each diagnostic's message and the texts of its labels make fewer than 40 tokens on every tokenizer of the basket, so what a case needs beyond that goes in the diagnostic's own help. It needs [uv](https://docs.astral.sh/uv/).

## Changing a message

A snapshot is the compiler's own output, so it is never written by hand, and it is reviewed before it is accepted (`reviewed-messages`):

1. Put the program in `_pending/`: a new one, or the one whose rendering changes, moved there with its snapshot.
2. Run `just snapshots-draft`, which writes the rendering of every program in `_pending/` beside it, through the harness of `just diagnostics`, which builds each fixture's repositories.
3. Review the drafts, then run `just snapshots-accept`, which moves each program and snapshot out of `_pending/`, in place of any older one, and writes the renderings into the [error index](../../docs/errors/), whose page for each code shows them.

Drafts are checked like accepted snapshots, so a draft whose rendering has changed since it was written fails until it is drafted again.
