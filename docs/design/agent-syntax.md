# Agent syntax

An agent-first syntax should minimize tokens per solved task, not tokens per file. In the most careful 2026 measurement, the final source file accounted for only 4.5–8.4% of the output tokens agents spent ([Wu et al.](https://arxiv.org/abs/2607.22807)). The rest went to fixing compile errors, re-checking code that already passed, and exploring.

So Stilt's syntax is familiar first and dense second. The parts designed for agents target the three places tokens actually go: the error loop, the edit loop and the context window. On one measured program, Stilt still needs 23% fewer tokens than Python and 33% fewer than Rust.

## What goes wrong in AI-driven development

Eight problems recur across 2025–2026 research. Most are about context and correctness, not code length.

| Problem | Evidence | Stilt's answer |
| --- | --- | --- |
| Tokens go to the fix loop, not the file | Agents used 1.28–1.69x more output tokens in OCaml than in Python on the same problems. For one model, 92% of failed OCaml attempts were compile errors ([Wu et al.](https://arxiv.org/abs/2607.22807)). | Familiar syntax; errors that carry their fix; a "done" verdict |
| Long context degrades models | All 18 models Chroma tested got less reliable as input grew, even on simple tasks ([Chroma, via Hamel Husain](https://hamel.dev/notes/llm/rag/p6-context_rot.html)). | Skeleton view; holes that report only the context that fits them |
| Repository context files cost more than they help | LLM-generated AGENTS.md files lowered success in 5 of 8 settings and raised cost 20–23% ([ETH Zurich](https://arxiv.org/pdf/2602.11988)). | Docs live in code, structured and checked |
| Formatting is mostly overhead for models | Removing formatting cut input tokens by 24.5% on average with no meaningful accuracy loss ([Pan et al.](https://arxiv.org/html/2508.13666v1)). | A dense canonical format |
| Edits land in the wrong place | After a one-line shift, line-range edits silently corrupted 99.1% of files. Edits addressed by function name hit the wrong function 12.7% of the time, because of duplicate names ([Althoubi](https://arxiv.org/pdf/2609.11957)). | Path-and-hash edits over unique names |
| Comments mislead | Models treat comments as authoritative even when they contradict the code ([CodeCrash](https://arxiv.org/pdf/2504.14119)). Defective commented-out code pushed the rate of defective output as high as 58% ([Comment Traps](https://papers.cool/arxiv/2512.20334)). | Pinned docs; no commented-out code |
| Invented packages | Across 576,000 samples, 16 models invented 205,474 distinct package names. Open models did so in 21.7% of samples, commercial ones in 5.2% ([BankInfoSecurity](https://www.bankinfosecurity.com/ais-phantom-packages-invite-slopsquatting-supply-chain-risk-a-28059)). | Imports pinned in the manifest, no install on import |
| Duplication and swallowed errors | Across 623 million changes, code duplication rose 81% and error masking 47% in the AI era ([LeadDev on GitClear](https://leaddev.com/?p=34362)). Agents also tend to catch everything ([Armin Ronacher](https://lucumr.pocoo.org/2026/2/9/a-language-for-agents/)). | Duplicate detection from typed bodies; catch-alls that drop the error must give a reason |

## Design rules

Six rules follow from the evidence. When they conflict, the first rule wins.

1. **Count tokens per solved task.** Keywords and symbols come from languages already in the models' training data: Rust, TypeScript and Swift. A shorter syntax that agents must learn costs more in failed attempts than it saves in characters. Grammar-only compressions such as SimPy (10–14% fewer tokens) and Token Sugar (up to 15%) needed fine-tuning before models could use them ([SimPy](https://arxiv.org/abs/2404.16333v2), [Token Sugar](https://arxiv.org/abs/2512.08266)).
2. **Dense by default, nothing left to strip.** Braces instead of significant whitespace. The formatter keeps short blocks on one line and never aligns columns. The canonical file is already close to its minimum.
3. **Every name has exactly one home.** No overloading, no re-exports, no import aliases. Calls are written qualified (`fs.read`); only a small, fixed prelude (`print`, `Option`, `List`, …) is used unqualified. Every definition is then greppable and addressable by a unique path.
4. **Types shown where they matter.** Signatures are always written; bodies are inferred. `stilt show` prints inferred types and facts on demand, so nobody needs a language server to read them.
5. **Docs are data, checked like code.** Each doc has a summary line, executable examples, and a pin that detects when the code has moved on without the doc.
6. **One command, one verdict.** `stilt test` checks the code, runs the affected tests, then answers with a single machine-readable result.

## The syntax at a glance

Six constructs exist mainly for agents. Each is borrowed from a language models already know. Here is the measured program, plus one executable example line:

```stilt
use std.cli
use std.fs

/// One validated row of the orders file.
type Order = { customer: str, qty: i64, price: f64 }

/// Parses one `customer,qty,price` row.
/// ex: try parse_line(2, "ana,3,2.5") == Order { customer: "ana", qty: 3, price: 2.5 }
fn parse_line(n: i64, text: str) -> Order / raise<str> {
  let [customer, q, p] = text.split(",") else raise "line {n}: expected 3 fields"
  let qty = q.to_i64() else raise "line {n}: bad qty {q}"
  let price = p.to_f64() else raise "line {n}: bad price {p}"
  if qty <= 0 { raise "line {n}: qty must be positive" }
  Order { customer, qty, price }
}

/// Revenue per customer, largest first.
fn totals(orders: List<Order>) -> List<(str, f64)> {
  var sums = Map.with_default(0.0)
  for o in orders { sums[o.customer] += o.qty.to_f64() * o.price }
  sums.entries().sorted_desc_by(.1)
}

fn main() / {io, raise<str>} {
  let path = cli.arg(0) else raise "usage: orders <file>"
  let lines = try fs.read_lines(path) catch _ => raise "cannot read {path}"
  let orders = try lines.skip(1).enumerate(2).map(|(n, l)| parse_line(n, l))
  for (c, t) in totals(orders).take(3) { print("{c}: {t:.2}") }
}
```

A raise that escapes `main` prints `error: …` and exits with status 1, so `main` needs no handler of its own. The single `try` in front of `lines.skip(1)…` marks both `map` and the `parse_line` call inside its callback.

| Construct | Example | Borrowed from |
| --- | --- | --- |
| Destructure or fail | `let [a, b, c] = xs else raise …` | Rust's let-else |
| Fallback on an optional value | `q.to_i64() else raise …` | Swift's guard, as an expression |
| Key paths for one-argument lambdas | `sorted_desc_by(.1)`, `filter(.paid)` | Swift key paths, Kotlin's `it` |
| Field punning | `Order { customer, qty, price }` | Rust, JavaScript |
| Short blocks stay on one line | `if qty <= 0 { raise … }` | Formatter policy |
| Examples are tests | `/// ex: …` | Rust doctests, Python doctest |

An agent reads the skeleton view, `stilt show main`, to use the module: shown whole, a module prints only its signatures and doc summaries, in 100 tokens instead of 338. `stilt show main.totals` prints one function with its inferred types and facts written in, such as `[panic, alloc]` after the signature of `totals`.

```text
use std.cli; use std.fs
/// One validated row of the orders file.
type Order = { customer: str, qty: i64, price: f64 }
/// Parses one `customer,qty,price` row.
fn parse_line(n: i64, text: str) -> Order / raise<str>
/// Revenue per customer, largest first.
fn totals(orders: List<Order>) -> List<(str, f64)>
fn main() / {io, raise<str>}
```

## Token cost

The program above, measured with the `o200k_base` tokenizer on 27 Oct 2026:

| Version | Tokens | Stilt's saving |
| --- | --- | --- |
| Stilt | 338 | |
| Stilt without the six constructs | 403 | 16% |
| Python | 437 | 23% |
| TypeScript | 471 | 28% |
| Rust | 502 | 33% |

- **Tokenizer.** The ranking is the same with `cl100k_base`.
- **Behaviour.** The Python, TypeScript and Rust versions produce identical output on every test input.
- **Where the savings come from.** The six constructs save 65 tokens in total. Destructure-or-fail and the `else` fallback, which replace `match`, account for 48 of them. Field punning, key paths and one-line blocks add the other 17.
- **Method.** One person wrote every version, so treat the gaps as directional.

The programs, inputs and counting script are in [measurements/token-cost](../../tools/measurements/token-cost/).

## Features not found in other languages

Eleven features target the edit loop, the context window and the error loop. Each has a precedent somewhere, but as far as this research found, no mainstream language ships any of them as part of the language and its compiler.

| Feature | Problem it fixes | Closest precedent |
| --- | --- | --- |
| **Path-and-hash edits**: an edit of `main.totals/body#a91f` is refused if the content has changed or the new text doesn't parse | Edits landing in the wrong place; quoting old code costs tokens | Unison's hashed definitions; HTTP ETags; SWE-agent's linter gate |
| **Pinned docs**: each doc is pinned in its package's `docs.lock` to the hash of its declaration's signature, without the body, beside its own; a doc left untouched after its signature changes is flagged stale, and the commands that write source pin new and changed docs | Comments that contradict the code | Rust doctests check examples, not prose |
| **No commented-out code**: a comment that parses as code gets a warning | Defective commented-out code steering generation | None in a compiler |
| **Reasons on catch-alls**: a catch-all arm must raise, use the error it binds, or give a reason with `because "…"` | Swallowed errors | Lint suppressions with reasons |
| **Typed holes as context**: a `?` checks with a warning, runs until it is reached, and reports what fits, in the order Hazel measured | Agents planning in comments; context rot | Agda, Idris and Haskell typed holes; Hazel |
| **Prefix checking**: a body cut off at any token either can still become well typed or is rejected at the token that rules it out, and the grammar is published for constrained decoding | Compile errors that decoding could have prevented | MoonBit's sampler; type-constrained decoding |
| **Admissible alternatives**: a diagnostic lists what would fit where it points | Repair loops that guess | Elm's hints; rustc's suggestions |
| **Properties from signatures**: a `/// prop:` line is a property whose generators come from the signature, and a failure returns a shrunk counterexample | Tests that check only the cases an agent thought of | QuickCheck; Hypothesis |
| **Duplicate warnings**: two functions with the same typed body of 20 tokens or more, whatever their locals' names, are flagged at the later one, which names the first and is offered a call of it | Duplication up 81% | Separate clone detectors |
| **Hash-pinned imports**: a package imports only the dependencies its manifest pins by content hash, and an unknown one is a compile error that lists the real names; nothing installs on import, and a name that doesn't resolve fails when `stilt check` first fetches it | Invented package names | Go's checksum database; Zig's and Roc's content-hashed packages |
| **Programs with errors run**: code with an error panics with `check-error` only where it is reached, and the run exits with status 2 | Commenting out broken code to try the rest | Roc; Hazel's marked lambda calculus |

Three of these change how code is written. An address with a hash is an edit: `stilt check` or `stilt test` takes `--edit ADDRESS TEXT`, applies it if the hash still matches and the text parses as the part, and answers with the verdict that follows. In 0.1 an address names a declaration or its body, and `-` in place of the text reads it from standard input. `stilt show main.totals --json` gives the address with its hash and the text it covers.

```text
$ stilt show main.totals --json
{"at": "main.totals#77e0", "text": "fn totals(orders: List<Order>) -> … { … }", "body": "main.totals/body#a91f", …}
$ stilt check --edit 'main.totals/body#a91f' '{ orders.map(.qty) }'
applied main.totals/body#a91f -> #c40d

$ stilt check --edit 'main.totals/body#a91f' '{ orders.map(.price) }'
── STALE ADDRESS ──────────────────────────────────────── main.lt:12:52  [E0703]

`main.totals/body` changed since #a91f, and is now #c40d:
…
```

Several `--edit` options make one change: every edit is checked against the files as they are before any applies, and if one is refused, none does, no file changes, and the command exits with status 2 with no verdict. The hash covers the part's canonical text, the text `stilt fmt` writes for it, so formatting a file or moving a method between blocks never invalidates an address, while a comment added inside the part does.

```stilt
// A catch-all has to say why it is safe to swallow the error
fn port(text: str) -> u16 {
  try parse_port(text) catch _ because "old configs omit the port" => 8080
}

// A typed hole: checks with a warning, panics if reached, and release builds reject it
fn totals(orders: List<Order>) -> List<(str, f64)> = ?
```

`stilt show --json 'main.totals/body'` reports the hole's context in the order Hazel measured: the expected type and effects first, then the definitions of the types they name, then the bindings in scope, and last the headers of at most 10 functions whose result fits, each as code calls it. Headers tripled GPT-4's test performance once types were present ([Blinn et al.](https://arxiv.org/html/2409.00921v1)). A function fits when its result can be the expected type, called on a binding in scope if it is a method, and when the hole may perform its effects; the module's own functions come first, then what the bindings in scope make, then the imported modules' functions and the expected type's own, and last what a binding of the expected type makes of another. Here the expected type names no declared type, so `types` is empty; one that named `Order` would hold its definition. Without `--json`, the context follows the part's text, one line per entry.

```json
{"at": "main.totals/body#a91f", "text": "= ?", …,
 "holes": [{"line": 12, "col": 54, "expects": "List<(str, f64)>", "effects": [], "without": [],
            "types": [], "in_scope": [{"name": "orders", "type": "List<Order>"}],
            "headers": ["List.map<U>(self, f: fn(T) -> U) -> List<U>",
                        "List.filter_map<U>(self, f: fn(T) -> Option<U>) -> List<U>", …]}]}
```

A cut-off body works the same way. Cut a body at any token, put `?` in place of the rest and close its braces, and `show` gives the expected type at the cut and the classes of token that can come next. Every prefix of a correct body passes, so a decoder constrained by it never blocks a program that would have been accepted ([Goals](goals.md), `prefix-decidable-checking`).

A search/replace edit has to quote the code it replaces. A path-and-hash edit replaces that quote with an address of a few tokens, so the saving grows with the size of the code being replaced. [declarations.unique-names](../../reference/10-declarations.md#declarations.unique-names) makes every address unique, and the hash makes a stale address fail cleanly instead of silently.

## Diagnostics built for agents

An agent should get one short, final answer per check. Every error in it is addressed by path, and every fix is ready to apply.

- **One verdict.** `stilt test --json` checks the code, runs the tests and doc examples affected by the change, reuses cached results for the rest, then returns a single object. Agents get confused when type checks, lints and tests can disagree ([Armin Ronacher](https://lucumr.pocoo.org/2026/2/9/a-language-for-agents/)).
- **Root causes only.** Errors caused by earlier errors are never reported.
- **Short by default, long on request.** Each message stays under about 40 tokens. `stilt show E0404` prints the full explanation when an agent asks for it.
- **Fixes as path-and-hash edits.** Each fix of a diagnostic has its `edits`, objects `{"at", "new"}` that `--edit` takes as they are, and is safely refused if the code has moved.
- **Alternatives, not guesses.** Wherever the checker can enumerate them, a diagnostic lists the admissible alternatives: bindings of the expected type, missing variants, effects the row allows, methods with a close name. In one agent loop, feedback with alternatives raised success from 28% to 72%, and almost all of the gain came from the alternatives ([Ray & Goyal](https://arxiv.org/abs/2607.14167)).
- **Counterexamples, not "assertion failed".** A failing `/// prop:` property comes back with a shrunk counterexample and its seed, the same on every run, so the verdict stays cacheable.
- **A done signal.** When everything passes, the verdict says `done: true`, and a harness can stop on that flag. Agents keep polishing code that already passes, and smaller models often never run the provided tests ([Wu et al.](https://arxiv.org/abs/2607.22807)).
- **A repeat signal.** When the submission, the contents of the program's files, is identical to an earlier one whose verdict wasn't done, the verdict says `repeat: true`, so a harness can tell an agent that resubmits failing code unchanged to try something else ([Goals](goals.md), `repeated-failures-flagged`). The program's engine remembers the hashes of the failing submissions it has seen, until it stops.

```json
{"done": false, "repeat": false,
 "diagnostics": [{"code": "E0404", "file": "src/cart.lt", "line": 14,
   "at": "cart.prune/body#91ad", "message": "cart changed while the loop reads cart.items",
   "fixes": [{"title": "use retain",
              "edits": [{"at": "cart.prune/body#91ad",
                         "new": "{ cart.items.retain(|i| !i.expired()) }"}]}],
   "alternatives": []}],
 "tests": []}
```

A diagnostic's `at` is the address, with its hash, of the smallest part that holds its primary span: the body when the span lies in one, and otherwise the declaration. A diagnostic in a `use` declaration, a module header or an impl's header has none. A fix that changes text outside every part has no `edits`, and its message still shows the change.

Tests run only once the code checks, so this verdict lists none. The same object, minus the agent fields `done`, `repeat`, `at`, `fixes` and `alternatives`, and the `kind`, `name` and `why` of each test, is what the conformance suite reads from every implementation.

## Trade-offs and open questions

The biggest open question is whether agents write correct code in this syntax as reliably as in the languages it borrows from. File size can't answer that.

- **Every new form must be learned.** Key paths and the expression-level `else` are familiar from other languages, but not in this combination. Only a study of agents can answer it, measuring task success and output tokens per solved task, as Wu et al. did, not file size.
- **Addresses stop at bodies.** An edit resends the whole body, and a fix carries the whole text of the body or declaration it changes, so a verdict grows with the size of the bodies it fixes. Paths to statements would shrink it, and wait until agents need them.
- **Pins can nag.** A signature change that keeps the meaning still flags its doc. The warning's fix, an edit that sends the declaration back as it is, pins the doc again in one step.
- **Constraints can hurt reasoning.** Constrained decoding applies to code blocks only, never to the reasoning around them, since over-strict constraints cost up to 10 points on reasoning tasks ([CRANE](https://arxiv.org/html/2502.09061v3)). Whether it helps frontier closed models on multi-file tasks is untested, so the agent study runs with it and without it.
- **Tokenizers change.** Budgets and benchmarks are measured on a basket of public tokenizers and re-run each year.
- **One program is not a benchmark.** The next step is porting 100 small tasks to every language and running agents on them.
- **Packing barely helps.** A packed view with one line per declaration saves only 2% more (330 tokens instead of 338), because the dense formatter already removes most formatting. It isn't worth a separate format unless a larger suite shows otherwise.
