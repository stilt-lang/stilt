# Token cost of one program

This directory holds the measurement cited in [Agent syntax](../../../docs/design/agent-syntax.md). The same program, a CSV report of revenue per customer, is written in several languages, and a script counts the tokens in each version.

## Contents

| Path | Contents |
| --- | --- |
| `programs/orders.lt` | Stilt |
| `programs/orders.plain.lt` | The same Stilt program without the six agent-oriented constructs: let-else, the `else` fallback, key paths, field punning, one-line blocks and `/// ex:` examples |
| `programs/orders.py`, `orders.ts`, `orders.rs` | Python, TypeScript and Rust versions with identical behaviour |
| `programs/orders.packed.txt` | The Stilt program with one line per declaration. It is a view for counting tokens, not valid source, since each `///` comment runs to the end of its line |
| `programs/orders.skeleton.txt` | The skeleton view of the Stilt module, as `stilt show main` prints it. Its signatures have no bodies, so it is a view, not valid source |
| `inputs/` | Inputs used to check that the versions behave identically |
| `measure.py` | Counts tokens. With `--check`, it also runs the Python, TypeScript and Rust versions on every input and compares their stdout, stderr and exit status |

## Method

- **Tokenizers.** Counts use the `o200k_base` and `cl100k_base` encodings from `tiktoken`.
- **Stilt examples.** `/// ex:` lines are excluded, because they are tests and the other versions have none.
- **Authorship.** One author wrote every version, aiming for idiomatic code in each language. Treat the differences as directional, not as a benchmark.
- **The Stilt versions** use the core standard library defined in the standard library of the Reference. They can't run until a Stilt implementation exists.

## Results (27 Oct 2026)

| Version | o200k_base | cl100k_base |
| --- | --- | --- |
| Stilt | 338 | 338 |
| Stilt without the six constructs | 403 | 403 |
| Python | 437 | 427 |
| TypeScript | 471 | 466 |
| Rust | 502 | 499 |
| Stilt, one line per declaration | 330 | 329 |
| Stilt skeleton view | 100 | 101 |

To reproduce:

```sh
uv run measure.py --check
```
