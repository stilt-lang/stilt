# Rationale: The standard library

Conformance tests can compare a program's output only when the library's behaviour and printed forms are fixed. Programs need the everyday operations of text, collections, numbers, files and time to be one call each, named as the libraries that people and agents already know name them. The standard library answers both. Its shape follows from one constraint: every native function is a place where two implementations can disagree.

## Modules

The library is a prelude and a set of modules ([std.modules](../17-std.md#std.modules)). The prelude holds what nearly every program uses. It is a fixed list, so a library can't extend it: an extension would be a re-export by another name. Everything else is imported and written through its module, as `fs.read`, so every name has one home.

In a module that imports it, a module's name can't also name a local. So the modules take names that programs rarely give a variable: `clock` over `time`, `hashing` over `hash`, and `random` and `collections`. There is no `std.path`, since the modules that handle paths would want `path` for their locals. The path functions live in `std.fs`, beside the functions they serve. Dates and durations live in `std.clock` too, beside the clocks they read.

The library declares six traits, the four of the prelude and the two of `std.json`. The prelude's traits are the ones that operators and structural impls stand behind. `ToJson` and `FromJson` let a type that needs JSON of its own give it, and the reader and writer of `std.json` then use it at any depth.

## Principles

A native function is written once per implementation. So the native set holds only three kinds of function ([std.natives](../17-std.md#std.natives)):

- what Stilt can't express;
- what a body written in Stilt would make slower, or would give an effect where nothing can fail;
- what every program would pay for, since every implementation checks the library's bodies with each program it checks.

Everything else is written in Stilt, and every implementation shares it. Its source decides what the Reference leaves open, including raises, panics and calls of callbacks.

Library functions don't panic by default ([std.no-panics-by-default](../17-std.md#std.no-panics-by-default)). A missing value is an `Option` and a failure is a raise, so the caller handles it. `unwrap` and `expect` exist anyway. Leaving them out is the alternative. Code that knows a value is there, as a test or a short script does, would then write `opt else panic("…")` each time. An agent would write `unwrap` all the same, as other languages spell it. Their panic has a kind of its own, so `without panic` rejects them as it rejects indexing, and `else` and `match` stay the way to handle a missing value.

The order of callback calls is specified ([std.callbacks](../17-std.md#std.callbacks)). A callback may raise or perform effects that pass through to the caller, and the caller sees them in that order. Only the comparisons of sorting are unspecified, so implementations may sort as they choose.

A method's name says whether it changes its receiver ([std.method-names](../17-std.md#std.method-names)). Swift's `sort` and `sorted` and Python's `list.sort` and `sorted` split them the same way. The alternative is verbs that return copies, so that `xs.sort()` returns a sorted list. On a `var`, `xs.sort()` would then read as sorting the list while leaving it as it was. The fix for the unused value, `let _ = xs.sort()`, would hide the mistake.

## Numbers

The float methods are the operations that IEEE 754 defines exactly ([std.floats](../17-std.md#std.floats)), so tests compare their bits. Transcendental functions can't be compared bit for bit across platforms. So they live in `std.math`, whose results are specified within 4 ulps and whose special values are exact ([std.math](../17-std.md#std.math), [std.math-special-values](../17-std.md#std.math-special-values)). A program that needs the same output everywhere prints them with a precision.

The integer methods are native ([std.integers](../17-std.md#std.integers)). Written in Stilt, each would be written eight times, once per integer type, and checked with every program. They are exact operations, which implementations implement identically anyway.

`pow` takes a `u32`. A negative exponent has no integer result, so an `i64` exponent would add a panic that the type rules out. The exponents that programs write are literals, which take their type from the parameter, as in Rust. `pow` panics on overflow whatever order an implementation multiplies in. So an implementation that squares can't panic on an intermediate product that a naive loop wouldn't reach.

`clamp` and `sum` are written once per numeric type ([std.clamp-and-sum](../17-std.md#std.clamp-and-sum)). A numeric trait that wrote them once would need functions without `self`. A list's sum as `xs.sum()` would need an inherent block specialized to `List<i64>`. Neither is in core, so the sum of a list is `i64.sum(xs)`.

## Strings

Lengths and offsets count bytes, while widths count scalar values ([std.bytes-and-scalars](../17-std.md#std.bytes-and-scalars)). A string is UTF-8, and slicing by byte offset takes constant time. A width measures what a reader sees.

Case mapping, trimming and classifying handle ASCII only. Unicode-aware versions need large tables in every implementation, and such tables are a classic source of disagreement between implementations. `std.text` holds them once, in Stilt ([Unicode text](#unicode-text)).

There is no `char` type. Strings of one scalar value, the classifying methods and `code_points` cover what programs do with characters. A `char` type would give every text operation two forms.

The string functions are native ([std.str](../17-std.md#std.str)). Written in Stilt, each would cut its result with `slice`, and so carry the implicit `panic` effect where nothing can panic. It would also allocate a list of bytes on every call.

Their edges are fixed where libraries differ, so that tests can compare them. `split` keeps empty pieces, `lines` gives none for `""` ([std.str-splitting](../17-std.md#std.str-splitting)), and an empty pattern matches at every boundary between scalar values ([std.str-search](../17-std.md#std.str-search), [std.str-building](../17-std.md#std.str-building)). Invalid UTF-8 from outside the program becomes U+FFFD as the Unicode Standard recommends ([std.code-points](../17-std.md#std.code-points)). That is the one replacement that every implementation can make identically.

## Lists

Lists are the currency of every operation, and their methods are eager: each method that returns a list builds it ([std.lists](../17-std.md#std.lists), [std.list-functions](../17-std.md#std.list-functions)). Lazy iterators, which chain without building a list at each step, live with the views they read from. The list methods keep returning lists, so neither form changes the other.

`scan` includes its initial value, as Kotlin's `scan`, Haskell's `scanl` and Python's `accumulate` with `initial` do. It gives prefix sums one longer than the list, the form that range sums need. Rust's adapter, which leaves the initial value out, is the alternative.

Functions that take a count clamp it ([std.list-slicing](../17-std.md#std.list-slicing)), since a count past the end has one clear meaning. `chunks` and `windows` panic on a size below 1, which has none.

Sorting is stable ([std.list-sorting](../17-std.md#std.list-sorting)), so sorting by a second key and then a first gives the order of both. `sorted_with` names its algorithm, so a comparison with effects is called the same way everywhere.

## Maps

A map iterates in insertion order ([std.maps](../17-std.md#std.maps)), so its output is the same in every implementation and every run, whatever its hashes are. A map's default makes counting and summing one line, `m[k] += 1`. `get` ignores the default, so a program can still ask whether a key is present.

The calls of `hash` and `eq` that finding a key makes are specified ([std.finding-keys](../17-std.md#std.finding-keys)), since a written `Eq` or `Hash` can observe them. Which keys share a hash is unspecified, so implementations choose their hash functions.

The bound `K: Eq + Hash` is required where a key is found ([std.map-key-bounds](../17-std.md#std.map-key-bounds)). The alternative is a map type that is valid only with a bounded key. A type's parameters take no bounds, so a generic record could then never hold a map, as `type Cache<K, V> = { entries: Map<K, V> }` does. Generic code that finds keys needs the bound anyway, since the key's `Hash` reaches it as a dictionary. Iterating and showing find no key, so a map of float keys can still be shown.

An assignment through a map element reads and stores the element ([std.map-element-places](../17-std.md#std.map-element-places)), as a compound assignment does. So `m[k].f = v` panics on a missing key exactly where `m[k]` would, and starts from the default where there is one.

## Sets

`Set` is a prelude type ([std.sets](../17-std.md#std.sets)). The alternative is a module, as `collections.Set`. A set is as common as a map, and Python, Swift and Kotlin give it the same standing as their maps. The rarer double-ended queue and heap live in `std.collections`.

A set is a record over a map, so it keeps insertion order and shows its elements as a list does, `Set([1, 2])`. Braces, as `{1, 2}`, would show an empty set as `{}`, as an empty map shows.

`insert` and `remove` return `()`. Rust's return whether they changed the set. A result that isn't `()` can't stand as a statement, so every call would need `let _ =`, and `contains` answers the question when it matters. A set's `Hash` adds its elements' hashes ([std.set-impls](../17-std.md#std.set-impls)), so two equal sets built in different orders hash equally.

## `Option`, `Result` and `Ordering`

The order in which the prelude declares their variants is their structural order ([std.option-result-and-ordering](../17-std.md#std.option-result-and-ordering)). So `None < Some(0)` and an `Ok` sorts before an `Err`, with no impl written for them. Converting between raising and `Result` is one call each way, `get` and `Result.of`. `Ordering.then` orders by a second key ([std.option-result-functions](../17-std.md#std.option-result-functions)), which `sorted_with` uses for several keys.

## Showing and formatting

Every type's printed form is fixed ([std.show-output](../17-std.md#std.show-output), [std.show-names-and-escapes](../17-std.md#std.show-names-and-escapes)), because conformance tests compare output exactly. Names are printed unqualified, so the output doesn't depend on where a type is declared. Nested strings are quoted and escaped, so a list of strings reads back as one.

A format spec's alignment follows the splice's type where it is written ([std.width-fill-and-alignment](../17-std.md#std.width-fill-and-alignment)). So a generic function formats the same way for every type it is given.

A spec never decides the type of a literal ([std.invalid-specs](../17-std.md#std.invalid-specs)): `{x:.2}` doesn't make `x` a float. A literal's type comes from the code that computes with it, as every other literal's does, and adding a spec to an interpolation changes no type.

Precision rounds the exact binary value half to even ([std.precision](../17-std.md#std.precision)), as C's `printf` does, which every implementation can match exactly. Integer kinds print negative values as their two's complement ([std.integer-kinds](../17-std.md#std.integer-kinds)), as programs that print bit patterns expect.

## Input and output

`cli.args()` leaves out the program's name ([std.cli](../17-std.md#std.cli)). Its path differs between the reference interpreter and a built executable, so output that printed it wouldn't be deterministic. `IoError` lives in `std.io` ([std.io-errors](../17-std.md#std.io-errors)), since standard input and every other I/O fail in the same ways as files do.

`poll_line` reads a line only when one is waiting ([std.io](../17-std.md#std.io)). The alternative is a blocking read alone. A program that works while it waits for a command, as a chess engine waits for `stop`, would then need threads, which core doesn't have. Reads write out stdout first, so a prompt written with `write` shows before the program waits for its answer.

## Time

The clocks are three natives that give numbers ([std.clock](../17-std.md#std.clock)). The types of durations, instants and dates are written in Stilt on them ([std.durations](../17-std.md#std.durations), [std.instants](../17-std.md#std.instants), [std.date-times](../17-std.md#std.date-times)), so the calendar's arithmetic is one source that every implementation shares.

A duration is a count of nanoseconds in an `i64`, as Go's is. It spans 292 years, which covers what programs measure and the dates around them, and its order and equality are its record's.

A date is UTC in the Gregorian calendar with no leap seconds, as Unix time counts. Time zones need a database of rules that changes every year, which every implementation would have to ship and agree on. An offset is read and turned into UTC.

RFC 3339 is the one text format of times ([std.rfc-3339](../17-std.md#std.rfc-3339)), since it is what logs, JSON and the network exchange. It is written with a fraction only when there is one.

## Running programs and the network

Running another program is a capability of its own, `exec` ([facts.capabilities](../15-facts.md#facts.capabilities)). A program that is run can reach anything, so `exec` could have meant every capability at once. As a capability of its own, `without exec` is the promise that code runs nothing, and `fs` keeps saying what the code's own source reaches.

Commands are records built with functions that return new ones ([std.process-commands](../17-std.md#std.process-commands)), so a command is a value that can be kept and run again. A program whose name holds no `/` is looked up in the `PATH` that the command itself runs with, as Rust's `Command` does. So both implementations find the same file, whatever their platform's `execvp` does.

`wait` reads what is left of a child's output before it waits ([std.children](../17-std.md#std.children)). A child that fills its pipe then never waits on a parent that waits on it, and nothing it wrote is lost.

Processes and sockets fail as files do, with an `io.IoError` that names what failed ([std.process-starting](../17-std.md#std.process-starting), [std.net-listeners](../17-std.md#std.net-listeners)). A type of error per module would make every program that reads a file and a socket catch two types for the same few failures. Reads of a child's output and of a connection give `None` at their end, as `io.read_line` does, and a read that fails ends them. So a protocol written on them handles one case, and a message cut short is the protocol's error, as `std.http`'s `Message("body")` is.

`std.http` is written in Stilt on `std.net` ([std.http](../17-std.md#std.http)), so its parsing is one source that both implementations share. Each connection carries one request, so the server needs no tasks and the client no pool.

`std.http` speaks no TLS. A client of `https://` needs a TLS library and a store of certificates in every implementation, which both would have to agree on. A program reaches HTTPS through a program that speaks it, such as a proxy or `curl`, which `std.process` runs.

The client and the server are split into the halves of an exchange: `write_request`, `read_request`, `write_response` and `read_response`. One program can then be both ends of a connection, as the conformance suite's tests are. A program's sequential run can't both wait for an answer and give it.

## Random numbers

`Rng` is SplitMix64, specified to the bit and written in Stilt ([std.random](../17-std.md#std.random), [std.random-numbers](../17-std.md#std.random-numbers), [std.shuffling](../17-std.md#std.shuffling)). So a seed gives the same numbers in every implementation, and a test can rely on them. A cryptographically secure generator is the alternative, and doesn't fit `Rng`, whose point is a sequence that a seed reproduces. `entropy()` gives unpredictable numbers.

A draw changes the generator, so its methods take it `inout`. A closure can't change what it captures, so code that draws inside `map` or `generate` draws in a loop instead.

## Collections

`Deque` and `Heap` are written in Stilt on lists ([std.deque](../17-std.md#std.deque), [std.heap](../17-std.md#std.heap)), so they need no native code. Their impls work on `to_list()`, so two collections with the same elements compare, hash and show the same however they were built.

## Encodings and hashes

Base64, hexadecimal, UTF-8 with its errors and the hashes are written in Stilt ([std.encoding](../17-std.md#std.encoding), [std.hashing](../17-std.md#std.hashing)). They are exact operations on bytes, which a native in each implementation would only repeat, and their standards fix their results, which the tests compare.

A reader of base64 or hexadecimal gives an `Option`, as the number parsers do. `encoding.from_utf8` raises where the bytes go wrong ([std.utf8-errors](../17-std.md#std.utf8-errors)). It says whether they end inside a character or hold one that isn't UTF-8, so that a reader of a stream can tell the two apart. `str.from_utf8`, which says only whether the bytes are UTF-8, stays in the prelude.

FNV-1a is the fast hash. A hash that a program stores must be the same in every implementation, and FNV-1a is short enough to be checked by reading it, while faster hashes have longer definitions. Its values are the same everywhere, but it resists no attacker, so nothing cryptographic relies on it: SHA-256 and its HMAC are the hashes for that.

## Unicode text

Unicode's case mappings and properties are tables in Stilt ([std.text](../17-std.md#std.text)). As natives, they would come from OCaml's and Rust's Unicode data, of different versions, and the two implementations would disagree. The tables are written from Rust's `char`, whose version the toolchain pins, and a test fails when they fall behind it.

The mappings are those without context, as Rust's `char::to_uppercase` gives them. The conditional ones of SpecialCasing.txt depend on the language of the text or on the scalar values around one, which a function of a scalar value can't see. The tests of properties take a text, as the ASCII tests of `str` do, since a scalar value is a one-character string ([lexical.no-characters](../02-lexical.md#lexical.no-characters)). They hold of no empty text.

## Regular expressions

Regular expressions are matched by a Pike machine over a compiled program ([std.regex](../17-std.md#std.regex)), as RE2, Go and Rust match them. Perl, Python and JavaScript backtrack. A backtracking matcher takes exponential time on patterns such as `(a*)*b`, which has taken services down when a text met a pattern written without that case in mind. A reader can rely on a promise of linear time without studying the pattern.

The price is what a linear matcher can't do: backreferences and lookaround, which the syntax leaves out ([std.regex-syntax](../17-std.md#std.regex-syntax)). A program writes them as code around a match.

Matches are leftmost-first, preferring alternatives and repetitions in the order written, as every widely used engine does. POSIX's leftmost-longest is the alternative. With leftmost-first, a pattern means what it means elsewhere.

The module is written in Stilt, so both implementations share one matcher and its results. Offsets count bytes, as every offset of `str` does. Counts are bounded at 1,000 and programs at 100,000 instructions, so compiling a pattern is bounded too.

## JSON

`std.json` is a derive written as a library function ([std.json](../17-std.md#std.json)). It reflects on its type, so no type gains an API from compile-time code and nothing is generated per type. These alternatives are rejected:

- **A `derive` declaration that generates impls of `ToJson` and `FromJson`,** as serde's. A type would gain an API from compile-time code, and the generated code would cost compile time for every type.
- **Attributes on fields,** as serde's `rename` and `skip`. A type that needs other JSON implements `ToJson` and `FromJson`, which the derive uses at any depth.
- **Unknown members as an error** ([std.json-reading](../17-std.md#std.json-reading)). JSON read from elsewhere often gains fields, and serde ignores them by default too.
- **A variant as `{"type": "Name", …}`** ([std.json-writing](../17-std.md#std.json-writing)). It needs a payload whose fields have names that code uses, and a payload's names are documentation only.
- **`NaN` and the infinities as `null`.** They would read back as another value, or not at all, so writing one panics with its path.

A read error names the path and the expected type ([std.json-read-errors](../17-std.md#std.json-read-errors)), so a program can tell its user which member was wrong. Parsing fixes its limit of nesting, 512 levels, and the place of each syntax error, including a lone surrogate's ([std.json-parsing](../17-std.md#std.json-parsing)). So every implementation accepts the same documents and reports the same position.

## The library's own tests

Every function has an example in its doc comment ([std.examples](../17-std.md#std.examples)), which documents it where it is declared and is its test. No program's `stilt test` runs them, as it never runs a dependency's tests. A program's verdict then depends only on its own code, and each implementation runs the library's examples in its own test suite.
