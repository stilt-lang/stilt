# Change files

Every pull request that changes what a user of Stilt sees adds one file here, and the release notes are collected from them. A reviewer reads the file with the change; when the release is made, the files are gathered into its notes and removed.

## Writing one

Name the file for the change, in lowercase words joined by hyphens: `changes/let-else-in-closures.md`. It starts with a header of `key: value` lines, then a blank line, then the text:

```
kind: fix
rfc: 0007

`stilt fmt` no longer moves a comment that follows a closing brace onto the next line.
```

- **`kind`** is one of `language` (a change to the language, which changes the Reference), `library` (the standard library), `tools` (the compiler, the formatter, the editor support, the installer and the other commands), `fix` (a bug fixed), or `docs` (the guide and the other documents).
- **`rfc`** is optional: the number of the [RFC](https://github.com/stilt-lang/stilt-rfcs) that decided a language change.
- **The text** says in a sentence or two what changed for the user, in the present tense and in the user's terms: what they can now write or see, not how the code changed. It may use backticks and links. A breaking change says what breaks and what to write instead.

A change with no effect on users, such as a refactoring, a test or a change to the build, adds no file; its pull request takes the label `no-changes-file`.

## Collecting them

```sh
uv run tools/release/notes.py --check     # every file is well formed
uv run tools/release/notes.py             # the notes of the next release, on the standard output
uv run tools/release/notes.py --remove    # delete the files, once the release is published
```

The notes group the entries by kind, and the release workflow publishes them with the release ([RELEASING.md](../RELEASING.md)).
