# The edit loop

Measured on 2026-11-24 07:48 UTC, on Apple M4, 4 performance and 6 efficiency cores, macOS 27.2.1. Each version is a project of 250 modules of a record type and 20 functions, each module calling the one before it. A clean step runs 3 times from no cache, and each warm measurement makes 10 edits to the middle module; a cell is the median, with the least and the most below it.

| | Stilt | Rust | Go | OCaml | Swift |
| --- | ---: | ---: | ---: | ---: | ---: |
| Lines | 46286 | 47283 | 51792 | 40781 | 47042 |
| Clean check | 120 ms<br>120 ms–142 ms | 1.10 s<br>1.10 s–1.10 s | 2.91 s<br>2.88 s–2.91 s | 4.20 s<br>4.18 s–4.21 s | 6.36 s<br>6.26 s–7.99 s |
| Clean debug build | 652 ms<br>640 ms–654 ms | 1.74 s<br>1.74 s–1.75 s | 2.92 s<br>2.92 s–2.94 s | 6.19 s<br>6.04 s–6.34 s | 6.34 s<br>6.29 s–6.38 s |
| Edit to diagnostics, a type error | 9 ms<br>8 ms–10 ms | 187 ms<br>185 ms–197 ms | 72 ms<br>71 ms–73 ms | 91 ms<br>90 ms–92 ms | 1.03 s<br>1.02 s–1.04 s |
| Edit to diagnostics, the error fixed | 9 ms<br>8 ms–9 ms | 207 ms<br>203 ms–211 ms | 178 ms<br>176 ms–179 ms | 98 ms<br>97 ms–102 ms | 1.61 s<br>1.60 s–1.61 s |
| Edit to the running program | 82 ms<br>54 ms–90 ms | 719 ms<br>686 ms–741 ms | 392 ms<br>376 ms–400 ms | 609 ms<br>579 ms–615 ms | 1.82 s<br>1.80 s–1.83 s |

Stilt's edit to the running program is `stilt run`'s: the program runs on, and each edit is patched into it. Every other language's is an incremental debug build and a start of the program, to its first line. Go and Swift have no command that only checks, so their check is their build.

## Tools

| Language | Version | Check | Build |
| --- | --- | --- | --- |
| Stilt | stilt 2027.1.0 (1e1320782 2026-11-24) | `stilt check .` | `stilt build -o program .` |
| Rust | cargo 1.99.1 (5f94df478 2026-08-27) | `cargo check --quiet` | `cargo build --quiet` |
| Go | go version go1.27.4 darwin/arm64 | `go build -o program .` | `go build -o program .` |
| OCaml | dune 3.24.2 | `dune build --root . @check` | `dune build --root . ./main.exe` |
| Swift | Swift version 6.4.2 (swiftlang-6.4.2.1.9 clang-2100.4.1.1) | `swift build --quiet` | `swift build --quiet` |
