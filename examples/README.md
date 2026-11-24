# Examples

Nine programs written in Stilt, each a directory program with its tests and doc examples, and samples of its use: the arguments in `samples/NAME.args`, one to a line, and the output they give in `samples/NAME.out`. `just examples` runs each program's tests, and runs each sample under the compiler and the reference interpreter, from the program's directory.

| Program | Does | Shows |
| --- | --- | --- |
| [`csvq/`](csvq/) | Filters, groups, sorts and prints the rows of a CSV file | `std.fs` and `std.cli`, maps, grouping and sorting, `raise` across modules |
| [`calc/`](calc/) | Runs a small language of integers, booleans and functions, a line at a time | Variant types, `match`, recursion, `Result` |
| [`flags/`](flags/) | Reads command-line options into a record from the record's type alone | Reflection with `std.meta`, `comptime match` and `comptime for`, anonymous records, E0350 at a call that gives a type without a shape |
| [`kv/`](kv/) | Serves a key-value store over HTTP/1.1, keeping its keys in a file | `std.http` and `std.net`, a task for each connection under `task.threads()`, one store in a `sync.Shared` reached in `when`, `without panic` on the handler of requests |
| [`life/`](life/) | Runs Conway's Game of Life in the terminal | Editing a program while it runs: `stilt run` patches each edit of its rule into the running board |
| [`markdown/`](markdown/) | Writes the HTML of a Markdown document | Strings |
| [`pick/`](pick/) | Runs a query, in a part of jq's language, on a JSON document | `std.json`, a recursive variant type and its parser, queries that give lists of values, views and iterators |
| [`rays/`](rays/) | Renders spheres on a checkered floor, with shadows and reflections, as a PPM image | Records stored inline, `without alloc, panic` on the tracer, `par.map` over rows, release builds |
| [`vm/`](vm/) | Assembles and runs programs for a small stack machine | Variant types and `match`, `without panic` proved by the tests the machine needs to report faults, bounds checks that release builds drop |

Run one with `stilt run DIR ARGS…`, as `stilt run examples/calc examples/calc/samples/demo.calc`, and its tests with `stilt test DIR`.

## csvq

```text
csvq FILE [--where COLUMN=VALUE]... [--group COLUMN [--count] [--sum COLUMN]... [--mean COLUMN]...
     [--min COLUMN]... [--max COLUMN]...] [--sort COLUMN [--desc]] [--limit N] [--columns A,B,...]
```

It reads the file as RFC 4180 lays CSV out, the first record naming the columns, then filters the rows, groups them, sorts them, keeps the first `N` and keeps the columns named, in that order, and prints the table with its columns aligned. A filter compares with `=`, `!=`, `<`, `<=`, `>` or `>=`, as numbers when both sides are numbers and as text otherwise, and so does sorting, which keeps the order of equal rows. An aggregate leaves out empty fields.

```text
$ stilt run examples/csvq examples/csvq/samples/orders.csv --group city --sum qty --mean price --sort 'sum(qty)' --desc
city   sum(qty)  mean(price)
-----  --------  -----------
Paris        13         6.58
Lyon         11         6.06
Nice          5         7.62
```

## calc

Each line of the program is a definition, `let NAME = EXPR`, or an expression, whose value is printed. Expressions are integers, `true` and `false`, names, the operators `+ - * / %`, `== != < <= > >=`, `&& || !` and unary `-`, `if C then A else B`, `let NAME = A in B`, functions `fn(A, B) => BODY` and calls `f(x, y)`. A function sees the local names around it where it is made, and the global names when it runs, so global functions can call themselves and one another. `#` starts a comment. Arithmetic that overflows, a division by zero, a call nested more than 400 deep and a value of the wrong type are errors, reported with the line, which the program then skips, exiting with status 1 at the end.

```text
$ printf 'let fact = fn(n) => if n <= 1 then 1 else n * fact(n - 1)\nfact(20)\nfact(21)\n' | stilt run examples/calc
2432902008176640000
line 3: 21 * 2432902008176640000 overflows
```

## flags

```text
thumbs [OPTIONS] [TEXT...]
```

`flags.lt` is a library that reads command-line options into a record from the record's type alone, as a derive would, with nothing declared on the type: `std.meta` gives the type's fields, and each field's type says what its option takes. `main.lt` uses it for the options of a made-up image tool and prints the record they give, or, with `--help`, the usage that `flags.usage` writes from the same type.

A field `keep_metadata` is the option `--keep-metadata`. A `bool` is a flag, set by `--keep-metadata` and cleared by `--no-keep-metadata`; an integer, a float and a `str` take a value, as `--width 320` or `--width=320`, an integer one that its type holds; an `Option` takes its element's value; a `List` takes one each time its option is given; and a variant type takes the name of one of its variants, none with a payload, in lower case with `-` between words. The field named `rest`, a `List`, takes the arguments that aren't options. An unknown option is an error that names the nearest known one.

Its functions match on the type's shape with `comptime match` and loop over its fields with `comptime for`, so a release build specializes them for each record type and unrolls the loops. A field whose type no option can give, as a tuple, is an error as soon as parsing starts, and a type with no shape at all, as a field that holds a function, is E0350 at the call of `flags.parse`, which the editor shows as the call is written.

```text
$ stilt run examples/flags --width 320 --fit cover --no-keep-metadata x.png
Options { width: 320, height: None, quality: 85, scale: 1.0, fit: Cover, keep_metadata: false, tags: [], rest: ["x.png"] }
```

## kv

```text
kv serve [--port N] [--data FILE] [--max N]
kv replay FILE
```

`serve` answers HTTP/1.1 on `127.0.0.1`, port 8080 unless `--port` says otherwise: `GET /` lists the keys, `GET /stats` gives the number of keys and of writes as JSON, and `GET`, `PUT` and `DELETE` on `/k/NAME` read, set and remove a key, the value being the request's body. Each connection is answered by a task of its own, under `task.threads()`, and the tasks share the store through a `sync.Shared`, which each reaches inside `when`, so no two change it at once and the store's file, given by `--data`, is written in the order of the writes. `--max N` stops after `N` connections. `replay` runs the requests of a file through the same store with no network, one to a line as `METHOD TARGET [BODY]`, and prints each response, which is how its samples test it. `stilt show main.answer` prints the facts of a connection's task: `locks`, and the capabilities `fs`, `net` and `console` below `io`.

```text
$ stilt run examples/kv serve --data keys.json &
kv: listening on http://127.0.0.1:8080/
$ curl -X PUT --data 'hello, world' http://127.0.0.1:8080/k/greeting
$ curl http://127.0.0.1:8080/k/greeting
hello, world
```

## life

```text
life [--size WxH] [--steps N] [--delay MS] [PATTERN]
```

It runs Conway's Game of Life on a board that wraps around at its edges, 40 by 20 cells unless `--size` says otherwise, from a pattern in the plaintext format, rows of `.` and `O` with `!` starting a comment, or from the R-pentomino. It draws each generation in the terminal, a cell coloured by how long it has lived, pausing `--delay` milliseconds between two, 100 unless told otherwise, until it is stopped; with `--steps N`, it prints the board as a pattern after `N` generations and stops.

The rule and the colours are in `rules.lt`. Under `stilt run`, each saved edit of a program's files is patched into the running program, so changing `born` to `n == 3 || n == 6` turns the running board into HighLife, and changing `look` recolours it, while the board and its generation go on.

```text
$ stilt run examples/life examples/life/samples/gosper.cells
```

## markdown

It reads a subset of [CommonMark](https://spec.commonmark.org) and writes HTML as CommonMark's reference renderer lays it out: ATX headings, paragraphs and hard line breaks, fenced code blocks, block quotes, bullet and numbered lists, tight or loose and nested, thematic breaks, emphasis, code spans, links, images, `<…>` links and backslash escapes. It escapes raw HTML rather than passing it through, and it reads neither setext headings, nor indented code blocks, nor tabs as indentation.

## pick

```text
pick [-c] [-r] QUERY [FILE]
```

It reads one JSON value from the file, or from standard input, runs the query on it and prints each value the query gives, indented as jq indents it, on one line with `-c`, and strings without their quotes with `-r`. A query is written in a part of jq's language, and means what it means in jq: `.`, `.name`, `."name"`, `.[N]`, from the end when `N` is negative, the slices `.[N:M]`, `.[N:]` and `.[:M]` of arrays and strings, taken through views, and `.[]`; `|` and `,`; the comparisons `==`, `!=`, `<`, `<=`, `>` and `>=`, in jq's order of values, and `and`, `or` and `not`; arrays `[…]` and objects `{key: …, key}`; literals; and the functions `length`, `keys`, `type`, `empty`, `first`, `last`, `reverse`, `sort`, `unique`, `min`, `max`, `to_entries`, `select(f)`, `map(f)`, `sort_by(f)`, `has(k)`, `join(s)`, `first(f)` and `last(f)`. Numbers keep the text they were written with, and there is no arithmetic. An error stops the query before it prints anything. Its samples' output is jq 1.7's.

```text
$ stilt run examples/pick -c '.books[] | select(.price < 10 and .stock > 0) | {title, year}' examples/pick/samples/books.json
{"title":"The Left Hand of Darkness","year":1969}
{"title":"The Dispossessed","year":1974}
{"title":"Invisible Cities","year":1972}
```

## rays

```text
rays [WIDTH] [HEIGHT]
```

It renders a scene of four spheres, one a mirror, on a checkered floor under two lights, with shadows, highlights and reflections followed three bounces deep, and prints it as a plain PPM image, 320 by 180 by default. Each row is a task of `par.map`. The tracer's functions are limited by `without alloc, panic`, so the check proves that no ray allocates or can panic, and their vectors and hits are records stored inline. A release build renders 960 by 540 in about a third of a second on an M4:

```text
$ stilt build --release examples/rays -o rays && ./rays 960 540 > rays.ppm
```

Its sample's image was computed by an independent Python version of the same algorithm, which gives the same bytes.

## vm

```text
vm FILE [ARGUMENT]...
```

It assembles a program for a small stack machine and runs it, its arguments the parameters of the program's function `main`, and prints each value the program prints. A line of the program holds a label, `NAME:`, a function's header, `fn NAME PARAMETERS`, or an instruction, and `;` starts a comment:

| Instruction | Does |
| --- | --- |
| `push N` | Pushes the integer `N` |
| `load K`, `store K` | Pushes slot `K` of the call's frame, or pops a value into it; the parameters are the first slots |
| `add`, `sub`, `mul`, `div`, `mod` | Pops two values and pushes their sum, difference, product, quotient or remainder |
| `lt`, `le`, `eq`, `not` | Pops two values, or one for `not`, and pushes 1 when the comparison holds and 0 otherwise |
| `jump L`, `jumpz L` | Goes on at the label `L`, or pops a value and goes there when it is 0 |
| `call F`, `ret` | Calls the function `F`, its parameters taken from the stack, or returns the value on top of the stack |
| `print`, `dup`, `drop`, `halt` | Pops a value and prints it, pushes the top value again, pops it, or stops |

Every mistake of a program, as an overflow, a division by zero, a value taken from an empty stack or a slot outside its frame, is a fault, reported with its line. The machine's `run` is limited by `without panic`, and the check proves it: the loop's test, `pc >= 0 && pc < p.code.len()`, guards the read of each instruction, and the tests that report a slot outside its frame guard each read and write of a slot. A release build drops the checks those tests make redundant, as `stilt show --release machine.run examples/vm` reports.

```text
$ stilt run examples/vm examples/vm/samples/collatz.vm 30
27
112
```

The samples' output was computed by Python from the programs' definitions.
