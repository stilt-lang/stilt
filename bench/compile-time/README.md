# The compile-time benchmark

A program heavy in compile-time code, and a baseline that writes the same program by hand (Goals, Workloads, "Compile-time benchmark"; `compile-time-code-rebuilds`, `editors-see-expansions`, `visible-expansion-size`, `compile-time-errors-at-user-code`). The program is `logscan`, a log analyzer: it reads a service's log from standard input, a line of text or of JSON per entry, and prints what it found: the entries of each topic, level and host, their pace, histograms, what the requests, logins, cache and jobs did, the deploys and settings changed, the alerts, the errors by kind, the first entry of each kind as it reads back from its JSON, and a summary as JSON. Its options keep some entries and leave out the others, or print the entries kept as JSON instead of the report: `logscan [--host HOST]... [--topic TOPIC]... [--level LEVEL] [--since HH:MM] [--until HH:MM] [--export] < LOG`.

| Path | Contents |
| --- | --- |
| [`meta/`](meta/) | The benchmark: 2,752 lines in 30 files |
| [`baseline/`](baseline/) | Its baseline, written without compile-time code: 3,788 lines in 30 files, 14 of them the benchmark's, byte for byte |
| [`log.txt`](log.txt) | A log of 266 lines: entries of every topic, lines of JSON, and lines that hold no entry |
| [`log.out`](log.out) | What both versions print given that log |
| [`edits.txt`](edits.txt) | The edit script: 32 edits a person makes while working on the program, each made to both versions |

`just examples` runs the tests of both versions, and each version given the log, under the reference interpreter and under the compiler, whose output must be `log.out`. `just latency` replays the edit script on both versions, each held by an engine of the compiler, as `stilt build` is answered while a person works, and times each edit, and then its undoing, from the change of the files until the debug executable is written again: the benchmark must rebuild within 1.2 times its baseline's time (`compile-time-code-rebuilds`). Before the replay, it reports the lines of the benchmark's functions as `stilt show` prints them, as written and with each macro use's expansion in its place, and whether those are at most twice these (`visible-expansion-size`, proposed, which it doesn't fail on). `stilt-latency compile-time --only baseline` replays the script on the baseline alone, which measures no target.

The language server's test of the benchmark, [`lsp_compile_time.rs`](../../compiler/stilt-cli/tests/lsp_compile_time.rs), run by `just test`, opens each file as an editor does and checks that the server publishes no diagnostic, that a hover over each macro use shows its expansion, over a name of each `comptime` form what checking gave it, and over each reflective call the function it calls, and that it finds as many of each as the list below gives (`editors-see-expansions`). Two snapshots of [`tests/diagnostics/`](../../tests/diagnostics/) show errors in the benchmark's compile-time code at the user's tokens, naming the macro (`compile-time-errors-at-user-code`): `E0225_unclosed_group_in_a_regex_pattern`, a `regex!` use of `rx.lt` and `matcher.lt`, copied, whose pattern leaves a group open, and `E0311_mismatched_type_in_a_macro_use`, where an expression given to a macro has a type its expansion can't take, which no `regex!` use can show, since `regex!` takes only a string.

## The two versions

Each version holds the same modules, of the same names: what the versions share is the same file in both, and where they differ, the baseline writes by hand what the benchmark computes at compile time.

| Concern | The benchmark | The baseline |
| --- | --- | --- |
| Patterns of the log's lines | `rx.lt` declares `regex!`, a procedural macro ([macros.procedural-declarations](../../reference/16-meta.md#macros.procedural-declarations)) that parses its pattern while the program is checked, raising E0225 at the pattern's first character that can't stand where it is, and writes its matcher from the steps of `matcher.lt`; `patterns.lt` uses it 13 times | `patterns.lt` writes the 13 matchers from the same steps |
| The twenty types of events, in `events/` | Written and read as JSON by `json.to_text` and `json.from_text`, from their shapes ([std.json](../../reference/17-std.md#std.json)) | Each implements `json.ToJson` and `json.FromJson`, reading through `decode.lt`, which gives the errors reading from a shape gives |
| Entries as `path=value` pairs | `flat.lt` reads them from their types' shapes ([meta.shapes](../../reference/16-meta.md#meta.shapes)) | `flat.lt` writes out the leaves of each type |
| Tables of the report | `table.lt` takes its columns from the fields of its rows' type | `table.lt` declares a trait `Row`, implemented for each row of `rows.lt` |
| Histograms and windows | `Histogram<n>` and `Window<n>` take their size as a value parameter ([generics.value-parameters](../../reference/07-types.md#generics.value-parameters)), and loop over it with `comptime for` and `comptime if` ([meta.staged-loops](../../reference/16-meta.md#meta.staged-loops)) | `Histogram` and `Window` take their size when made, and loop over it at run time |
| The summary's JSON | `json.to_text` and `json.from_text` | `Summary`, `Charts` and `Histogram` implement the traits |

## What the measurements count

These are the benchmark's uses of compile-time code, which the language server must expand and run (`editors-see-expansions`), whose expansions `stilt show --expanded` measures (`visible-expansion-size`), and whose errors must point at the user's tokens (`compile-time-errors-at-user-code`):

- **`regex!` uses**, 13, in `patterns.lt`: `line`, `http`, `slow`, `login`, `lookup`, `evict`, `job`, `disk`, `deploy`, `setting`, `crash`, `retry` and `clock`, each `rx.regex!("…")`. The macro's module, `rx.lt`, writes 17 quotes.
- **`comptime` forms**, 21: in `histogram.lt`, a `comptime for` in `add`, `total`, `peak`, `median` and `lines`, and a `comptime if` in `lines`; in `window.lt`, a `comptime for` in `mean` and `most`; in `timeline.lt`, two `comptime for` over `entry.TOPICS`; in `flat.lt`, a `comptime match` in `leaves` and `payload`, and four `comptime for`; in `table.lt`, a `comptime match` in `columns`, `cells` and `cell`, and two `comptime for`.
- **Types with value arguments**, 6: the five histograms of `charts.lt`, `Histogram<8>`, `<6>`, `<5>`, `<12>` and `<5>`, and the windows of `spikes.lt`, `Window<6>`.
- **Reflective calls**, 20, of the functions that reflect on a type's shape ([meta.reflects](../../reference/16-meta.md#meta.reflects)): `flat.pairs`, called once in `report.lt`, and `table.render`, called 15 times in `report.lt`, `requests.lt`, `people.lt`, `operations.lt`, `objectives.lt`, `errors.lt` and `pace.lt`, which reach the functions that name `T.shape()`, `T.name()` or a bound test, `flat.leaves`, `flat.payload`, `table.columns`, `table.cells` and `table.cell`; and `std.json`'s, `json.to_text` and `json.from_text`, each called twice, in `codec.lt` and `summary.lt`.

## The edit script

`edits.txt` holds 32 edits, of six kinds: 4 fields added to a type, 2 variants added, 8 patterns changed, 11 bodies edited, 5 sizes changed, of histograms and of the window, and 2 items added. The replay makes each edit, then undoes it, so a field added is then taken away. Each edit is the same in both versions where they share code, and the matching one where they don't: a field added to an event's type is also added, in the baseline, to its JSON and its leaves; a pattern changed in a `regex!` use is changed, in the baseline, in its matcher; a histogram's size changed in its type is changed, in the baseline, where it is made. The file's head gives its format, and `stilt-latency`'s tests check that every edit applies to both versions.
