# Stilt against other languages

Measured on 2026-11-24 07:45 UTC. The machine: Apple M4, 4 performance and 6 efficiency cores, 24 GiB of memory, macOS 27.2.1. Its load average over 1, 5 and 15 minutes was 2.30, 5.04, 9.47 before the first build and 1.90, 2.81, 5.05 after the last run.

A time is the mean of a version's timed runs, after one untimed run: the cycles its threads ran on the performance cores, taken at the reference clock of 4.0 GHz, or its wall time where that is less, as for work spread over several threads, by the Timing rule of the project's goals. ± is the standard deviation of the runs' times over their mean. Each version runs at least 5 times, and as many more as its runs take to add up to 1 s. Other programs on the machine change the times by what they contend for, and leave the instructions nearly as they are. Instructions are the mean of the runs', and peak memory the least of the runs' peak resident memory. Every version printed what its suite's reference prints, the Rust version or jq, unless its cell says otherwise.

## The Perceus paper's programs

### Time

| Program | Stilt | Rust | Koka | OCaml | Haskell | Swift | Java |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| binarytrees | 4.108 s ±21.0% | 9.976 s ±0.3% | 2.993 s ±0.7% | 3.238 s ±0.4% | 2.582 s ±0.8% | 16.355 s ±0.6% | 1.600 s ±2.9% |
| cfold | 0.105 s ±1.1% | 0.186 s ±2.8% | 0.050 s ±1.1% | 0.206 s ±0.5% | 0.148 s ±0.5% | 0.519 s ±0.7% | 0.162 s ±1.2% |
| deriv | 0.450 s ±0.4% | 0.905 s ±3.3% | 0.378 s ±0.8% | 0.673 s ±0.6% | 0.846 s ±0.5% | 1.074 s ±0.8% | 0.486 s ±1.4% |
| nqueens | 0.469 s ±0.3% | 0.470 s ±0.5% | 0.423 s ±0.6% | 0.671 s ±0.2% | 0.851 s ±0.5% | 1.130 s ±0.3% | 0.519 s ±0.2% |
| rbtree | 0.487 s ±0.7% | 0.941 s ±2.3% | 0.304 s ±0.6% | 0.517 s ±0.5% | 0.705 s ±0.1% | 5.856 s ±0.5% | 1.209 s ±0.2% |
| rbtree_ck | 0.970 s ±0.6% | 3.535 s ±1.3% | 0.629 s ±0.3% | 1.288 s ±0.3% | 1.794 s ±0.1% | 5.894 s ±0.4% | 1.403 s ±0.5% |
| Geometric mean against Rust | 0.50 | 1.00 | 0.35 | 0.65 | 0.71 | 2.27 | 0.59 |

### Instructions, in billions

| Program | Stilt | Rust | Koka | OCaml | Haskell | Swift | Java |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| binarytrees | 57.83 | 242.87 | 63.64 | 82.39 | 55.25 | 374.80 | 48.21 |
| cfold | 1.11 | 2.38 | 0.63 | 4.06 | 3.06 | 8.30 | 4.21 |
| deriv | 8.83 | 18.80 | 7.24 | 12.64 | 14.38 | 24.68 | 25.76 |
| nqueens | 4.44 | 5.00 | 3.91 | 9.95 | 15.60 | 19.52 | 7.52 |
| rbtree | 11.41 | 22.06 | 5.73 | 10.02 | 15.67 | 116.49 | 28.53 |
| rbtree_ck | 18.11 | 78.32 | 10.50 | 24.43 | 44.59 | 113.79 | 41.80 |

### Peak memory, in MiB

| Program | Stilt | Rust | Koka | OCaml | Haskell | Swift | Java |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| binarytrees | 130 | 130 | 226 | 141 | 253 | 259 | 2023 |
| cfold | 135 | 215 | 123 | 192 | 125 | 274 | 270 |
| deriv | 563 | 979 | 456 | 420 | 616 | 652 | 568 |
| nqueens | 150 | 151 | 96 | 167 | 243 | 156 | 163 |
| rbtree | 226 | 131 | 132 | 198 | 330 | 259 | 2581 |
| rbtree_ck | 1592 | 1363 | 1149 | 1372 | 2514 | 1822 | 3185 |

## The benchmark suite

### Time

| Program | Stilt | Rust | OCaml | Swift | Go |
| --- | ---: | ---: | ---: | ---: | ---: |
| binary_trees | 0.074 s ±24.2% | 0.467 s ±2.4% | 0.049 s ±1.3% | 0.400 s ±0.4% | 0.135 s ±0.9% |
| fannkuch | 0.196 s ±0.3% | 0.203 s ±0.9% | 0.243 s ±0.4% | 0.296 s ±0.9% | 0.175 s ±0.7% |
| fasta | 0.024 s ±0.9% | 0.024 s ±1.0% | 0.025 s ±0.7% | 0.014 s ±0.9% | 0.012 s ±0.8% |
| json | 0.017 s ±0.8% | 0.021 s ±3.9% | 0.036 s ±0.5% | 0.041 s ±2.7% | 0.019 s ±2.1% |
| life | 0.013 s ±0.7% | 0.016 s ±0.3% | 0.091 s ±0.4% | 0.027 s ±0.6% | 0.036 s ±0.9% |
| mandelbrot | 0.015 s ±1.2% | 0.015 s ±1.4% | 0.023 s ±0.9% | 0.015 s ±1.0% | 0.016 s ±1.3% |
| map_heavy | 0.030 s ±1.0% | 0.028 s ±2.7% | 0.075 s ±1.7% | 0.030 s ±2.4% | 0.029 s ±1.1% |
| matmul | 0.014 s ±0.6% | 0.013 s ±0.5% | 0.023 s ±0.4% | 0.019 s ±0.4% | 0.014 s ±0.6% |
| nbody | 0.036 s ±0.1% | 0.026 s ±0.2% | 0.038 s ±0.3% | 0.043 s ±0.8% | 0.034 s ±0.1% |
| nsieve | 0.045 s ±1.0% | 0.048 s ±0.7% | 0.359 s ±2.2% | 0.047 s ±0.6% | 0.043 s ±2.2% |
| pipeline | 0.033 s ±0.8% | 0.050 s ±3.8% | 0.182 s ±0.2% | 0.047 s ±0.3% | 0.184 s ±0.7% |
| sort | 0.040 s ±0.8% | 0.031 s ±1.1% | 0.173 s ±1.1% | 0.067 s ±0.4% | 0.074 s ±0.6% |
| spectral_norm | 0.027 s ±0.2% | 0.026 s ±0.3% | 0.081 s ±9.7% | 0.032 s ±0.2% | 0.036 s ±0.3% |
| string_heavy | 0.010 s ±0.9% | 0.016 s ±3.7% | 0.052 s ±0.7% | 0.054 s ±1.9% | 0.022 s ±8.5% |
| vm | 0.028 s ±7.3% | 0.023 s ±0.9% | 0.153 s ±1.1% | 0.064 s ±2.4% | 0.078 s ±1.9% |
| Geometric mean against Rust | 0.86 | 1.00 | 2.20 | 1.40 | 1.22 |

### Instructions, in billions

| Program | Stilt | Rust | OCaml | Swift | Go |
| --- | ---: | ---: | ---: | ---: | ---: |
| binary_trees | 1.44 | 11.46 | 1.24 | 9.25 | 6.48 |
| fannkuch | 3.00 | 2.76 | 4.18 | 5.63 | 2.39 |
| fasta | 0.26 | 0.25 | 0.22 | 0.15 | 0.07 |
| json | 0.42 | 0.45 | 0.82 | 0.89 | 0.52 |
| life | 0.31 | 0.31 | 1.99 | 0.51 | 0.83 |
| mandelbrot | 0.17 | 0.16 | 0.27 | 0.17 | 0.16 |
| map_heavy | 0.50 | 0.53 | 1.21 | 0.45 | 0.48 |
| matmul | 0.32 | 0.29 | 0.44 | 0.22 | 0.29 |
| nbody | 0.66 | 0.35 | 0.83 | 0.60 | 0.60 |
| nsieve | 0.69 | 0.80 | 1.21 | 0.74 | 0.56 |
| pipeline | 0.62 | 1.02 | 3.45 | 0.50 | 3.33 |
| sort | 0.38 | 0.22 | 3.29 | 0.61 | 0.73 |
| spectral_norm | 0.86 | 0.44 | 2.30 | 0.90 | 0.58 |
| string_heavy | 0.16 | 0.32 | 1.33 | 1.34 | 0.41 |
| vm | 0.73 | 0.67 | 3.86 | 1.21 | 0.71 |

### Peak memory, in MiB

| Program | Stilt | Rust | OCaml | Swift | Go |
| --- | ---: | ---: | ---: | ---: | ---: |
| binary_trees | 6 | 10 | 10 | 10 | 15 |
| fannkuch | 2 | 2 | 5 | 2 | 10 |
| fasta | 2 | 2 | 5 | 2 | 5 |
| json | 26 | 34 | 31 | 35 | 25 |
| life | 2 | 2 | 5 | 2 | 8 |
| mandelbrot | 2 | 2 | 3 | 2 | 4 |
| map_heavy | 9 | 6 | 10 | 6 | 9 |
| matmul | 3 | 3 | 6 | 7 | 6 |
| nbody | 2 | 2 | 5 | 5 | 4 |
| nsieve | 25 | 21 | 140 | 20 | 22 |
| pipeline | 19 | 22 | 29 | 16 | 33 |
| sort | 26 | 19 | 19 | 20 | 17 |
| spectral_norm | 2 | 2 | 5 | 5 | 4 |
| string_heavy | 11 | 19 | 24 | 30 | 15 |
| vm | 2 | 2 | 5 | 2 | 4 |

## `std.par` against Rayon, on each number of threads

### Time

| Program | Stilt | Rust |
| --- | ---: | ---: |
| mandelbrot, 1 thread | 0.593 s ±0.2% | 0.589 s ±1.0% |
| mandelbrot, 2 threads | 0.306 s ±0.2% | 0.307 s ±0.3% |
| mandelbrot, 3 threads | 0.209 s ±0.1% | 0.210 s ±0.3% |
| mandelbrot, 4 threads | 0.160 s ±0.5% | 0.158 s ±0.2% |
| mandelbrot, 5 threads | 0.144 s ±1.4% | 0.145 s ±4.0% |
| mandelbrot, 6 threads | 0.132 s ±1.6% | 0.131 s ±2.1% |
| mandelbrot, 7 threads | 0.120 s ±0.7% | 0.119 s ±0.2% |
| mandelbrot, 8 threads | 0.113 s ±1.4% | 0.110 s ±0.5% |
| mandelbrot, 9 threads | 0.105 s ±1.3% | 0.103 s ±1.3% |
| mandelbrot, 10 threads | 0.100 s ±1.3% | 0.099 s ±4.4% |
| primes, 1 thread | 0.828 s ±0.2% | 0.800 s ±0.1% |
| primes, 2 threads | 0.449 s ±0.1% | 0.409 s ±0.0% |
| primes, 3 threads | 0.312 s ±0.6% | 0.277 s ±0.1% |
| primes, 4 threads | 0.239 s ±1.0% | 0.211 s ±1.0% |
| primes, 5 threads | 0.218 s ±1.1% | 0.200 s ±0.4% |
| primes, 6 threads | 0.207 s ±2.7% | 0.190 s ±0.2% |
| primes, 7 threads | 0.198 s ±1.6% | 0.184 s ±0.8% |
| primes, 8 threads | 0.191 s ±2.7% | 0.176 s ±0.3% |
| primes, 9 threads | 0.182 s ±1.1% | 0.169 s ±0.6% |
| primes, 10 threads | 0.179 s ±1.0% | 0.165 s ±1.2% |
| states, 1 thread | 1.082 s ±2.0% | 1.057 s ±1.9% |
| states, 2 threads | 0.552 s ±0.3% | 0.534 s ±0.3% |
| states, 3 threads | 0.381 s ±0.2% | 0.382 s ±1.0% |
| states, 4 threads | 0.293 s ±0.2% | 0.285 s ±0.3% |
| states, 5 threads | 0.242 s ±0.4% | 0.238 s ±0.4% |
| states, 6 threads | 0.211 s ±0.4% | 0.205 s ±1.0% |
| states, 7 threads | 0.186 s ±0.7% | 0.181 s ±1.5% |
| states, 8 threads | 0.166 s ±0.5% | 0.161 s ±0.2% |
| states, 9 threads | 0.152 s ±1.0% | 0.145 s ±0.6% |
| states, 10 threads | 0.148 s ±3.2% | 0.135 s ±2.6% |
| Geometric mean against Rust | 1.04 | 1.00 |

### Instructions, in billions

| Program | Stilt | Rust |
| --- | ---: | ---: |
| mandelbrot, 1 thread | 6.89 | 6.49 |
| mandelbrot, 2 threads | 6.89 | 6.49 |
| mandelbrot, 3 threads | 6.89 | 6.49 |
| mandelbrot, 4 threads | 6.89 | 6.49 |
| mandelbrot, 5 threads | 6.89 | 6.49 |
| mandelbrot, 6 threads | 6.89 | 6.49 |
| mandelbrot, 7 threads | 6.89 | 6.49 |
| mandelbrot, 8 threads | 6.90 | 6.49 |
| mandelbrot, 9 threads | 6.90 | 6.49 |
| mandelbrot, 10 threads | 6.90 | 6.50 |
| primes, 1 thread | 15.32 | 10.25 |
| primes, 2 threads | 15.32 | 10.25 |
| primes, 3 threads | 15.32 | 10.25 |
| primes, 4 threads | 15.32 | 10.25 |
| primes, 5 threads | 15.33 | 10.25 |
| primes, 6 threads | 15.33 | 10.25 |
| primes, 7 threads | 15.33 | 10.25 |
| primes, 8 threads | 15.33 | 10.25 |
| primes, 9 threads | 15.33 | 10.26 |
| primes, 10 threads | 15.33 | 10.26 |
| states, 1 thread | 3.55 | 3.25 |
| states, 2 threads | 3.55 | 3.25 |
| states, 3 threads | 3.55 | 3.25 |
| states, 4 threads | 3.56 | 3.25 |
| states, 5 threads | 3.56 | 3.25 |
| states, 6 threads | 3.56 | 3.25 |
| states, 7 threads | 3.56 | 3.25 |
| states, 8 threads | 3.56 | 3.25 |
| states, 9 threads | 3.56 | 3.25 |
| states, 10 threads | 3.56 | 3.26 |

### Peak memory, in MiB

| Program | Stilt | Rust |
| --- | ---: | ---: |
| mandelbrot, 1 thread | 2 | 2 |
| mandelbrot, 2 threads | 2 | 2 |
| mandelbrot, 3 threads | 2 | 2 |
| mandelbrot, 4 threads | 2 | 2 |
| mandelbrot, 5 threads | 2 | 2 |
| mandelbrot, 6 threads | 2 | 2 |
| mandelbrot, 7 threads | 2 | 2 |
| mandelbrot, 8 threads | 3 | 2 |
| mandelbrot, 9 threads | 3 | 2 |
| mandelbrot, 10 threads | 3 | 2 |
| primes, 1 thread | 2 | 2 |
| primes, 2 threads | 2 | 2 |
| primes, 3 threads | 2 | 2 |
| primes, 4 threads | 2 | 2 |
| primes, 5 threads | 2 | 2 |
| primes, 6 threads | 2 | 2 |
| primes, 7 threads | 2 | 2 |
| primes, 8 threads | 2 | 2 |
| primes, 9 threads | 3 | 2 |
| primes, 10 threads | 3 | 2 |
| states, 1 thread | 25 | 17 |
| states, 2 threads | 25 | 17 |
| states, 3 threads | 25 | 17 |
| states, 4 threads | 25 | 17 |
| states, 5 threads | 26 | 17 |
| states, 6 threads | 26 | 17 |
| states, 7 threads | 26 | 18 |
| states, 8 threads | 26 | 18 |
| states, 9 threads | 26 | 18 |
| states, 10 threads | 26 | 18 |

## The programs that allocate most, against Rust with mimalloc

### Time

| Program | Stilt | Rust |
| --- | ---: | ---: |
| binary_trees | 0.074 s ±25.6% | 0.177 s ±0.4% |
| binarytrees | 3.918 s ±17.0% | 4.087 s ±0.3% |
| cfold | 0.104 s ±0.8% | 0.144 s ±1.0% |
| deriv | 0.450 s ±0.6% | 0.534 s ±0.9% |
| nqueens | 0.467 s ±0.3% | 0.424 s ±0.1% |
| rbtree | 0.486 s ±0.7% | 0.533 s ±1.5% |
| rbtree_ck | 0.971 s ±0.5% | 2.236 s ±1.2% |
| Geometric mean against Rust | 0.73 | 1.00 |

### Instructions, in billions

| Program | Stilt | Rust |
| --- | ---: | ---: |
| binary_trees | 1.44 | 3.32 |
| binarytrees | 57.83 | 76.60 |
| cfold | 1.11 | 1.09 |
| deriv | 8.83 | 8.64 |
| nqueens | 4.44 | 3.69 |
| rbtree | 11.41 | 9.23 |
| rbtree_ck | 18.11 | 44.59 |

### Peak memory, in MiB

| Program | Stilt | Rust |
| --- | ---: | ---: |
| binary_trees | 6 | 10 |
| binarytrees | 130 | 160 |
| cfold | 135 | 210 |
| deriv | 563 | 976 |
| nqueens | 147 | 150 |
| rbtree | 226 | 131 |
| rbtree_ck | 1589 | 1808 |

## `examples/pick` against jq and jaq

### Time

| Program | Stilt | jq | jaq |
| --- | ---: | ---: | ---: |
| pick, `.books[] \| select(.price < 10 and .stock > 0) \| {title, year}` | 0.418 s ±1.4% | 1.206 s ±0.4% | 0.529 s ±0.3% |
| pick, `[.books[] \| .year] \| sort \| unique \| length` | 0.706 s ±0.7% | 1.502 s ±1.0% | 0.381 s ±0.3% |
| pick, `.books \| map(.author.name) \| unique` | 0.452 s ±1.2% | 1.514 s ±0.7% | 0.490 s ±0.4% |
| pick, `.books \| sort_by(.price) \| first \| .title` | 0.809 s ±0.6% | 1.590 s ±0.5% | 0.769 s ±0.6% |
| pick, `[.books[] \| .tags[]] \| length` | 0.279 s ±0.2% | 1.182 s ±0.3% | 0.418 s ±1.6% |
| pick, `.books \| map(select(.author.born < 1900)) \| length` | 0.307 s ±0.8% | 1.172 s ±0.2% | 0.476 s ±0.2% |
| Geometric mean against jq | 0.34 | 1.00 | 0.37 |

### Instructions, in billions

| Program | Stilt | jq | jaq |
| --- | ---: | ---: | ---: |
| pick, `.books[] \| select(.price < 10 and .stock > 0) \| {title, year}` | 8.95 | 22.46 | 9.30 |
| pick, `[.books[] \| .year] \| sort \| unique \| length` | 15.37 | 25.07 | 6.93 |
| pick, `.books \| map(.author.name) \| unique` | 10.15 | 26.89 | 7.53 |
| pick, `.books \| sort_by(.price) \| first \| .title` | 13.66 | 26.54 | 9.13 |
| pick, `[.books[] \| .tags[]] \| length` | 6.65 | 20.88 | 7.14 |
| pick, `.books \| map(select(.author.born < 1900)) \| length` | 7.57 | 21.38 | 8.20 |

### Peak memory, in MiB

| Program | Stilt | jq | jaq |
| --- | ---: | ---: | ---: |
| pick, `.books[] \| select(.price < 10 and .stock > 0) \| {title, year}` | 354 | 570 | 635 |
| pick, `[.books[] \| .year] \| sort \| unique \| length` | 373 | 590 | 636 |
| pick, `.books \| map(.author.name) \| unique` | 365 | 590 | 672 |
| pick, `.books \| sort_by(.price) \| first \| .title` | 408 | 594 | 663 |
| pick, `[.books[] \| .tags[]] \| length` | 369 | 605 | 664 |
| pick, `.books \| map(select(.author.born < 1900)) \| length` | 353 | 569 | 638 |

## Toolchains

| Language | Version | Built with | Run as |
| --- | --- | --- | --- |
| Stilt | stilt 2027.1.0 (1e1320782 2026-11-24) | `stilt build --release` | its executable |
| Rust | rustc 1.99.1 (58cf8f9c3 2026-10-13) | `rustc --edition 2024 -C opt-level=3 -C link-arg=-Wl,-stack_size,0x20000000` | its executable |
| Koka | Koka 3.2.9 | `koka -O2 --stack=512M` | its executable |
| OCaml | OCaml 5.5.2 | `ocamlopt` | its executable |
| Haskell | GHC 9.12.2 | `ghc -O2` | its executable |
| Swift | Apple Swift version 6.4.2 (swiftlang-6.4.2.1.9 clang-2100.4.1.1) | `swiftc -O -wmo -Xlinker -stack_size -Xlinker 0x20000000` | its executable |
| Java | openjdk 27.0.1.0.3 2026-10-24 | `javac` | `java -Xss512m -cp . Main` |
| Go | go1.27.4 darwin/arm64 | `go build` | its executable |
| jq | jq-1.7.1-apple | `jq` | its executable |
| jaq | jaq 3.1.2 | `jaq` | its executable |
