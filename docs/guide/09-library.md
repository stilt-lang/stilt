# The standard library

This program writes a roster to a file, reads it back, and prints the names in order:

```stilt
use std.fs
use std.io

fn main() / {io, raise<io.IoError>} {
  try fs.write("roster.txt", "Mossling\nTidepup\nEmbercat\n")
  let names = try fs.read_lines("roster.txt")
  print("{names.len()} creatures: {", ".join(names.sorted())}")
}
```

```output
3 creatures: Embercat, Mossling, Tidepup
```

The standard library has two parts. The methods of the built-in types, such as `len`, `sorted` and `join`, belong to the prelude, which every module sees without a `use`. Everything else is in modules such as `std.fs`, which a program imports with `use` and names through the module: `fs.write`, `fs.read_lines`, `io.IoError` ([Importing modules with `use`](08-programs.md#importing-modules-with-use)).

This chapter shows the common jobs for each type and module, with an example each. The library's pages list every function with its signature, its facts and an example: `stilt doc --std` writes them ([docs.std](../../reference/04-programs.md#docs.std)), and the website publishes them. [The standard library](../../reference/17-std.md) chapter of the Reference states what each function guarantees.

These are the modules this chapter covers:

| Module | What it holds |
| --- | --- |
| `std.io` | Standard input and output, and `IoError` |
| `std.fs` | Files, directories and paths |
| `std.cli` | Command-line arguments and environment variables |
| `std.math` | `sin`, `log`, `pow` and the other transcendental functions |
| `std.clock` | Clocks, waiting, durations, and dates in UTC |
| `std.process` | Other programs |
| `std.net`, `std.http` | TCP, UDP and HTTP/1.1 |
| `std.random` | Random numbers that a seed reproduces |
| `std.encoding`, `std.hashing` | Base64, hexadecimal, UTF-8, SHA-256 and FNV-1a |
| `std.text`, `std.regex` | Unicode case and character classes, and regular expressions |
| `std.collections` | `Deque` and `Heap` |
| `std.lazy` | Values computed on first use |

Other modules have chapters of their own: `std.view` in [Views and iterators](11-views.md), `std.task`, `std.sync` and `std.par` in [Effects, tasks and parallelism](17-effects.md), and `std.json` in the [cookbook](cookbook.md).

## How library functions behave

A few rules hold across the whole library, and they tell you what a call can do before you look it up.

**No panics by default.** If a value can be missing, a function returns an `Option`, as `xs.get(9)` does. If an operation can fail, it raises, as `fs.read` does. A library function panics only on an index out of range, on a precondition its documentation states, and in `unwrap` and `expect` ([std.no-panics-by-default](../../reference/17-std.md#std.no-panics-by-default)).

**Verbs change, participles copy.** A method named by a verb, such as `push`, `sort` or `reverse`, changes its receiver through `inout self`, so it needs a `var`. A method named by a participle, such as `sorted` or `reversed`, returns a new value and leaves the receiver as it was:

```stilt
fn main() / io {
  var hps = [34, 30, 32]
  let ordered = hps.sorted()
  print("{hps} {ordered}")
  hps.sort()
  hps.reverse()
  print("{hps}")
}
```

```output
[34, 30, 32] [30, 32, 34]
[34, 32, 30]
```

When a method has both forms, the verb does what assigning the participle would do: `xs.sort()` leaves `xs` as `xs = xs.sorted()` would. A participle alone on a line, such as `hps.sorted()`, is E0322, *unused value*. Methods whose names other languages share, such as `map`, `filter`, `fold`, `zip`, `take`, `skip` and `concat`, keep those names, though they return new values. So does every method of `str` ([std.method-names](../../reference/17-std.md#std.method-names)).

**Callbacks run in order.** A method that takes a callback calls it once per element, from first to last. `any`, `all`, `find`, `find_index`, `take_while` and `skip_while` stop at the first element that decides the result. A callback's effects pass through to the caller, so a callback that raises makes the whole call need a `try` ([Effects that pass through](05-errors.md#effects-that-pass-through)).

**The sources decide.** Part of the library is **native**: each implementation provides it. The rest is written in Stilt, in [`std/`](../../std/), and every implementation runs that same code. Where the Reference says less than a function's source, the source decides ([std.natives](../../reference/17-std.md#std.natives)).

Every function has at least one `/// ex:` example in its doc comment. These examples are the library's own tests, so `stilt test` on your program never runs them ([std.examples](../../reference/17-std.md#std.examples)).

## The prelude

The prelude holds the primitive types, `Option`, `Result`, `List`, `Map`, `Set`, `Ordering` and their variants, the traits `Eq`, `Ord`, `Hash` and `Show`, and five functions ([The prelude](08-programs.md#the-prelude)):

| Function | What it does |
| --- | --- |
| `print(s: str) / io`, `eprint(s: str) / io` | Writes `s` and a newline to stdout, or to stderr |
| `panic(msg: str) -> Never` | Panics with the kind `explicit` and the detail `msg` |
| `unreachable() -> Never` | Panics with the kind `unreachable` |
| `exit(code: u8) -> Never / io` | Writes out both streams, and ends the process with status `code` |

Each line that `print` or `eprint` writes reaches its stream when the call returns. Everything the program has written reaches its stream before the process exits:

```stilt exit:3
fn main() / io {
  print("loading the roster")
  eprint("no roster file")
  exit(3)
}
```

```output
loading the roster
```

```stderr
no roster file
```

## Numbers

Every integer type, from `i8` to `u64`, has methods for the jobs that the operators don't do. In this table `T` is the integer type:

| Item | What it's for |
| --- | --- |
| `T.MIN`, `T.MAX` | The smallest and the largest value, as in `i64.MAX` |
| `abs`, `min`, `max`, `clamp` | The absolute value, the smaller or larger of two, and a value kept within a range |
| `checked_add`, `checked_sub`, `checked_mul` | Arithmetic that gives `None` instead of overflowing |
| `saturating_add`, `saturating_sub` | Arithmetic that stops at `T.MIN` or `T.MAX` |
| `pow`, `div_euclid`, `rem_euclid`, `gcd`, `lcm` | Powers, division whose remainder is never negative, and the common divisor and multiple |
| `count_ones`, `leading_zeros`, `trailing_zeros` | Counts of bits |
| `T.sum(xs: List<T>) -> T` | The sum of a list |
| `to_U(self) -> U`, `to_U(self) -> Option<U>`, `wrap_to_U(self) -> U` | Conversion to another integer type `U`, or its low bits |
| `to_f32(self) -> f32`, `to_f64(self) -> f64` | The nearest float |

A conversion to a type `U` that holds every value of `T` returns a `U`, as `u8.to_i64()` does. Any other conversion returns an `Option<U>`, as `i64.to_u8()` does ([Conversions](02-values.md#conversions)):

```stilt
fn main() / io {
  let hp = 30
  let damage = 45
  print("{(hp - damage).max(0)} {(hp - damage).abs()} {damage.clamp(0, 40)} {i64.sum([30, 34, 32])}")
  let big: u8 = 250
  print("{big.checked_add(10)} {big.saturating_add(10)} {big.to_i64()} {hp.to_u8()} {(-1).to_u8()}")
  print("{(-7).div_euclid(2)} {(-7).rem_euclid(2)} {i64.pow(2, 10)} {i64.gcd(12, 18)} {i64.count_ones(255)}")
}
```

```output
0 15 40 96
None 255 250 Some(30) None
-4 1 1024 6 8
```

`abs`, `pow`, `gcd`, `lcm` and `sum` panic with `overflow` when the exact result doesn't fit, as `+` and `*` do. `pow` takes a `u32` exponent, because a negative one has no integer result. `div_euclid` and `rem_euclid` panic on a zero divisor, as `/` does. A divisor written as a nonzero literal, as in `i.rem_euclid(7)`, adds no `panic` ([std.integers](../../reference/17-std.md#std.integers)). A list's sum is written `i64.sum(xs)`, since an `impl` block can't be specialized to `List<i64>`.

`f32` and `f64` have these constants and methods:

| Item | What it's for |
| --- | --- |
| `T.PI`, `T.E`, `T.NAN`, `T.INFINITY` | π, e, a NaN and positive infinity |
| `T.MAX`, `T.MIN`, `T.EPSILON`, `T.MIN_POSITIVE` | The largest and the smallest finite value, the gap after 1.0, and the smallest positive normal value |
| `sqrt`, `abs`, `floor`, `ceil`, `trunc`, `round` | The square root, the absolute value, and rounding |
| `min`, `max`, `clamp` | The smaller or larger of two, and a value kept within a range |
| `is_nan`, `is_finite`, `is_infinite` | Whether a value is a NaN, finite, or an infinity |
| `to_U(self) -> Option<U>` | The value truncated toward zero, as the integer type `U`, or `None` when it doesn't fit |

These methods are the operations that IEEE 754 defines exactly, so every implementation computes the same bits. `round` rounds halves away from zero. `min` and `max` give NaN when either operand is NaN, and treat `-0.0` as less than `0.0` ([std.floats](../../reference/17-std.md#std.floats)).

`std.math` holds `pow`, `exp`, `log`, `log2`, `log10`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `sinh`, `cosh`, `tanh`, `cbrt` and `hypot`, each on `f64`. They come from each platform's math library, so a result is only guaranteed within 4 ulps of the exact value. Print their results with a precision when the output must be the same everywhere ([std.math](../../reference/17-std.md#std.math)):

```stilt
use std.math

fn main() / io {
  let x = -2.5
  print("{x.round()} {x.floor()} {x.ceil()} {x.trunc()} {x.abs()} {(2.0).sqrt()}")
  print("{(1.0).max(f64.NAN)} {(1.5).clamp(0.0, 1.0)} {(-0.5).to_u8()} {(1e300).to_i64()} {f64.EPSILON}")
  print("{math.sin(f64.PI / 6.0):.4} {math.pow(2.0, 0.5):.6} {math.hypot(3.0, 4.0):.1} {math.log(0.0)}")
}
```

```output
-3.0 -3.0 -2.0 -2.0 2.5 1.4142135623730951
nan 1.0 Some(0) None 2.220446049250313e-16
0.5000 1.414214 5.0 -inf
```

Special values are exact everywhere, so `math.log(0.0)` is always `-inf` ([std.math-special-values](../../reference/17-std.md#std.math-special-values)). How floats compare and sort is in [Traits and generics](06-traits.md#floats).

## Strings

A `str` never changes, so every method of `str` returns a new value. These are the methods, by job:

| Method | What it's for |
| --- | --- |
| `len`, `is_empty`, `char_count` | The length in bytes, whether it is zero, and the number of Unicode scalar values |
| `contains`, `starts_with`, `ends_with`, `find`, `rfind`, `count` | Search for a substring |
| `split`, `split_once`, `rsplit_once`, `split_whitespace`, `lines`, `chars`, `bytes` | Cut into pieces |
| `trim`, `trim_start`, `trim_end`, `strip_prefix`, `strip_suffix`, `slice` | Cut off the ends, or take a part |
| `replace`, `replace_first`, `repeat`, `reversed`, `pad_start`, `pad_end`, `join` | Build a new string |
| `ascii_upper`, `ascii_lower`, `eq_ignore_ascii_case` | Change or ignore the case of ASCII letters |
| `is_ascii`, `is_ascii_digit`, `is_ascii_alpha`, `is_ascii_alphanumeric`, `is_ascii_whitespace`, `is_ascii_upper`, `is_ascii_lower` | Classify ASCII characters |
| `code_points`, `str.from_code_point`, `str.from_code_points`, `str.from_utf8`, `str.from_utf8_lossy` | Convert to and from numbers and bytes |
| `to_T(self) -> Option<T>` | Parse a number of the numeric type `T` |

Here a line of a roster is taken apart:

```stilt
fn main() / io {
  let line = "  Embercat = 30  "
  let (name, value) = line.trim().split_once(" = ") else return
  let hp = value.to_i64() else 0
  print("{name} has {hp} HP")
  print("{"Root Snare".ascii_upper()} {"Fire,,Plant".split(",")} {"7".pad_start(3, "0")} {"Bubble Jet".replace(" ", "-")}")
  print("{"Flame Pounce".starts_with("Flame")} {"Flame Pounce".find("P")} {" a  b ".split_whitespace()}")
}
```

```output
Embercat has 30 HP
ROOT SNARE ["Fire", "", "Plant"] 007 Bubble-Jet
true Some(6) ["a", "b"]
```

`split_once` gives an `Option`, so `else return` handles a line without ` = `. `split` keeps the empty piece between two commas. `split_whitespace` drops empty pieces, and `lines` splits on `\n` and drops a `\r` at the end of each line ([std.str-splitting](../../reference/17-std.md#std.str-splitting)).

Lengths and offsets count bytes, and `é` takes two:

```stilt
fn main() / io {
  let word = "héllo"
  print("{word.len()} {word.char_count()} {word.find("l")}")
  print(word.slice(0, 3))
}
```

```output
6 5 Some(3)
hé
```

`slice` panics with `bounds` when an offset is outside the string, and with `utf8-boundary` when it falls inside a character. The `é` runs from offset 1 to 3, so this program panics and exits with status 101:

```stilt exit:101
fn main() / io { print("héllo".slice(0, 2)) }
```

`trim`, `ascii_upper`, `ascii_lower` and the classifying methods look at ASCII only. For Unicode case and character classes, use `std.text` ([Unicode text](#unicode-text)). Every method's exact result, such as what `split("")` gives, is in [Strings](../../reference/17-std.md#strings).

### Parsing numbers

`s.to_i64()`, `s.to_f64()` and the other `to_T` methods give `None` unless the whole string is a number of that type. An integer is digits, with a `-` before them for a signed type. A float can also have a fraction and an exponent, as in `2.5e3`. A `+`, whitespace, `_`, a radix prefix, `inf` and `nan` are all rejected ([numbers.parsing](../../reference/06-numbers.md#numbers.parsing)):

```stilt
fn main() / io {
  print("{"42".to_i64()} {"007".to_u8()} {"300".to_u8()} {"-1".to_u8()} {" 42".to_i64()}")
  print("{"2.5e3".to_f64()} {"1.".to_f64()} {"inf".to_f64()}")
}
```

```output
Some(42) Some(7) None None None
Some(2500.0) None None
```

Trim a string first if it can hold spaces, as in `line.trim().to_i64()`.

### Unicode text

`std.text` does for all of Unicode what the ASCII methods of `str` do for ASCII. It holds tables of Unicode 17.0.0, written in Stilt, so it gives the same results everywhere:

| Function | What it's for |
| --- | --- |
| `text.upper`, `text.lower` | Change case, where one character can become several |
| `text.is_letter`, `text.is_upper`, `text.is_lower`, `text.is_numeric`, `text.is_alphanumeric`, `text.is_whitespace` | Whether a string isn't empty and each character is in the class |
| `text.unicode_version` | The version of Unicode the tables hold |

```stilt
use std.text

fn main() / io {
  print("{text.upper("Straße")} {text.lower("ΟΔΟΣ")} {"Straße".ascii_upper()}")
  print("{text.is_letter("ñandú")} {text.is_numeric("٣½")} {text.is_whitespace("\u{3000}")}")
}
```

```output
STRASSE οδοσ STRAßE
true true true
```

`text.upper` leaves out the mappings that depend on the language or the surrounding text, so every final `Σ` lowercases to `σ` ([std.text](../../reference/17-std.md#std.text)).

### Regular expressions

`std.regex` compiles a pattern once, and then matches it in time linear in the length of the text, whatever the pattern and the text hold:

```stilt
use std.regex

fn main() / io {
  let log = "Embercat hits Mossling for 16. Mossling hits Embercat for 3."
  let hit = try regex.compile("(\\w+) hits (\\w+) for (\\d+)") catch e => { print("bad pattern: {e}"); return }
  print("{hit.is_match(log)} {hit.find_all(log).len()}")
  let groups = hit.captures(log) else return
  print("{groups.filter_map(|g| g.text)}")
  print(hit.replace(log, "$2 takes $3"))
  print("{Result.of(|| try regex.compile("(a"))}")
}
```

```output
true 2
["Embercat hits Mossling for 16", "Embercat", "Mossling", "16"]
Mossling takes 16. Embercat takes 3.
Err(Unclosed(0))
```

`regex.compile` raises a `regex.Error` that names the mistake and its byte offset, here an unclosed `(` at offset 0. `captures` gives the whole match, then each group, as an `Option` for a group that took no part. In `replace`, `$1` stands for group 1, and `$$` for a `$`.

| Function | What it's for |
| --- | --- |
| `regex.compile`, `regex.escape` | Compile a pattern, and make a pattern that matches a text exactly |
| `is_match`, `find`, `find_all`, `captures` | Find matches, each a `Match { start, end, text }` with byte offsets |
| `replace`, `replace_first`, `split` | Replace matches, or split the text at them |

The syntax is the common one: `.`, classes such as `[a-z]` and `[^,]`, `\d`, `\w`, `\s`, `^`, `$`, `\b`, groups `(…)` and `(?:…)`, `|`, and the quantifiers `*`, `+`, `?` and `{n,m}`, made lazy by a `?` after them ([std.regex-syntax](../../reference/17-std.md#std.regex-syntax)). In a string literal a `{` starts an interpolation, so write a count as `\{4}`: `regex.compile("\\d\{4}")` matches four digits.

## Lists

These are the methods of `List<T>`, by job:

| Function | What it's for |
| --- | --- |
| `List.new`, `List.repeat`, `List.generate` | Build a list. A literal such as `[a, b]` builds one too |
| `len`, `is_empty`, `get`, `first`, `last` | Read the length or an element. `xs[i]` reads one and panics out of range |
| `push`, `pop`, `insert`, `remove`, `swap`, `extend`, `clear`, `truncate`, `retain`, `dedup` | Change the list in place |
| `map`, `filter`, `filter_map`, `flat_map`, `fold`, `scan`, `reduce` | Transform the elements |
| `any`, `all`, `find`, `find_index`, `index_of`, `contains`, `count` | Search |
| `min`, `max`, `min_by`, `max_by` | The smallest or largest element |
| `sorted`, `sorted_desc`, `sorted_by`, `sorted_desc_by`, `sorted_with`, `is_sorted`, `binary_search`, `partition_point` | Order, and search a sorted list |
| `sort`, `sort_desc`, `sort_by`, `sort_desc_by`, `sort_with`, `reverse` | Order the list in place |
| `take`, `skip`, `take_last`, `skip_last`, `take_while`, `skip_while`, `split_at`, `slice`, `chunks`, `windows` | Cut out a part |
| `partition`, `group_by`, `count_by`, `distinct`, `deduped` | Group the elements |
| `concat`, `zip`, `enumerate`, `reversed`, `List.flatten`, `List.unzip` | Combine and rearrange |

Some methods need more of the element type. `contains`, `index_of`, `dedup` and `deduped` need `Eq`, `distinct` needs `Eq` and `Hash`, and `sorted`, `min`, `max` and `binary_search` need `Ord`. A key path such as `.hp` can stand for a callback that reads a field ([Key paths](03-expressions.md#key-paths)):

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn main() / io {
  let roster = [
    Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 },
    Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 },
    Creature { name: "Tidepup", element: Water, hp: 32, attack: 7 },
  ]
  print("{roster.sorted_desc_by(.hp).map(.name)}")
  print("{roster.filter(|c| c.attack > 6).map(.name)} {roster.any(|c| c.hp < 31)}")
  print("{i64.sum(roster.map(.hp))} {roster.max_by(.attack).name}")
}
```

```output
["Mossling", "Tidepup", "Embercat"]
["Embercat", "Tidepup"] true
96 Some("Embercat")
```

`max_by` gives an `Option`, which is `None` for an empty list, and `.name` reads the field through it ([Fields through options](03-expressions.md#fields-through-options)).

These methods cut and group a list of hits:

```stilt
fn main() / io {
  let hits = [16, 3, 16, 3, 16]
  print("{hits.count(|h| h > 10)} {hits.distinct()} {hits.scan(0, |total, h| total + h)}")
  print("{hits.chunks(2)} {hits.partition(|h| h > 10)} {hits.take(2)} {hits.enumerate(1).take(2)}")
  print("{["Fire", "Water", "Fire", "Plant"].count_by(|e| e)}")
}
```

```output
3 [16, 3] [0, 16, 19, 35, 38, 54]
[[16, 3], [16, 3], [16]] ([16, 16, 16], [3, 3]) [16, 3] [(1, 16), (2, 3)]
{"Fire": 2, "Water": 1, "Plant": 1}
```

`take`, `skip` and the other cutting methods clamp their count to the list's length, so they never panic. `chunks` and `windows` panic when their size is less than 1 ([std.list-slicing](../../reference/17-std.md#std.list-slicing)).

Every sort is stable: elements with equal keys keep their order. So `sorted_desc_by` isn't `sorted_by` reversed:

```stilt
fn main() / io {
  let hp = [("Embercat", 30), ("Mossling", 34), ("Tidepup", 30)]
  print("{hp.sorted_by(.1)}")
  print("{hp.sorted_desc_by(.1)}")
  print("{["b", "B", "a"].sorted()} {[Some(2), None].sorted()}")
}
```

```output
[("Embercat", 30), ("Tidepup", 30), ("Mossling", 34)]
[("Mossling", 34), ("Embercat", 30), ("Tidepup", 30)]
["B", "a", "b"] [None, Some(2)]
```

`sorted` orders values through `Ord`: tuples element by element, strings by their bytes, and variants in the order they are declared ([Structural impls](06-traits.md#structural-impls)). To sort by several keys, give `sorted_with` a comparison, and combine keys with `Ordering.then` ([std.list-sorting](../../reference/17-std.md#std.list-sorting)).

Each list method that returns a list builds it whole. To chain steps without building a list at each one, use the iterators of `std.view` ([Iterators](11-views.md#iterators)).

## Maps

A `Map<K, V>` keeps its entries in the order their keys were first inserted, and every loop and `Show` follows that order. These are its methods, by job:

| Function | What it's for |
| --- | --- |
| `Map.new`, `Map.with_default`, `Map.from_entries` | Build a map, with or without a default value |
| `len`, `is_empty`, `contains`, `get`, `get_or` | Read. `m[k]` reads a value too |
| `insert`, `remove`, `get_or_insert`, `retain`, `extend`, `clear` | Change the map in place. `m[k] = v` inserts too |
| `entries`, `keys`, `values` | The entries, keys or values as lists, in order |
| `filter`, `map_values`, `merged` | Make a new map |

The key type must implement `Eq` and `Hash`, so a float can't be a key (E0318). `m[k]` panics with `missing-key` when `k` has no entry, unless the map was made by `Map.with_default`, which gives the default instead. `get` gives `None` for a missing key, with or without a default:

```stilt
fn main() / io {
  var damage = Map.with_default(0)
  for (name, hit) in [("Mossling", 16), ("Embercat", 3), ("Mossling", 16)] { damage[name] += hit }
  print("{damage} {damage["Tidepup"]} {damage.get("Tidepup")} {damage.len()}")
  let removed = damage.remove("Mossling")
  damage["Mossling"] = 0
  print("{removed} {damage} {damage.get_or("Tidepup", -1)}")
}
```

```output
{"Mossling": 32, "Embercat": 3} 0 None 2
Some(32) {"Embercat": 3, "Mossling": 0} -1
```

`damage[name] += hit` reads the default for a new name, then stores the sum. Reading `damage["Tidepup"]` inserts nothing, so the map still has two entries. A key that is inserted again keeps its place, but one that was removed goes to the end, as `Mossling` does here ([std.maps](../../reference/17-std.md#std.maps)).

Whether a map has a default is known only when the program runs, so every `m[k]` counts as an operation that can panic. So does an assignment through an element, such as `m[k].hp = 0`, which reads `m[k]` first ([std.map-element-places](../../reference/17-std.md#std.map-element-places)). Under `without panic`, read with `get` ([Limits](05-errors.md#limits)). Two maps are equal when they hold the same entries, in any order and whatever their defaults ([traits.map-equality](../../reference/11-traits.md#traits.map-equality)).

## Sets

A `Set<T>` holds each element once, in the order the elements were first inserted. Its elements need `Eq` and `Hash`, as a map's keys do:

| Function | What it's for |
| --- | --- |
| `Set.new`, `Set.from_list` | Build a set |
| `len`, `is_empty`, `contains`, `to_list` | Read |
| `insert`, `remove` | Change the set in place |
| `union`, `intersection`, `difference`, `symmetric_difference` | Combine two sets |
| `is_subset`, `is_superset`, `is_disjoint` | Compare two sets |
| `filter`, `map` | Make a new set |

```stilt
fn main() / io {
  var fainted = Set.new()
  for name in ["Mossling", "Tidepup", "Mossling"] { fainted.insert(name) }
  let roster = Set.from_list(["Embercat", "Mossling", "Tidepup"])
  print("{fainted} {fainted.contains("Embercat")} {roster.difference(fainted)}")
  print("{fainted.is_subset(roster)} {Set.from_list([1, 2]) == Set.from_list([2, 1])}")
}
```

```output
Set(["Mossling", "Tidepup"]) false Set(["Embercat"])
true true
```

A `for` loop can't iterate over a set directly, so loop over its `to_list()`. Two sets are equal when they hold the same elements, in any order. A set can be a map key, but it has no `Ord` ([std.sets](../../reference/17-std.md#std.sets)).

## Deques and heaps

`std.collections` holds two more collections. A `Deque<T>` is a double-ended queue, which adds and removes at both ends in constant time on average. A `Heap<T>` is a priority queue, whose `pop` gives the smallest element first:

| Function | What it's for |
| --- | --- |
| `Deque.new`, `Deque.from_list`, `push_front`, `push_back`, `pop_front`, `pop_back`, `front`, `back` | Build a deque, and use either end |
| `Heap.new`, `Heap.from_list`, `push`, `pop`, `peek` | Build a heap, add an element, and take or see the smallest |
| `len`, `is_empty`, `to_list` | Read either one. A heap lists its elements in ascending order |

Here a deque holds the order of turns, and a heap finds the creature with the fewest HP:

```stilt
use std.collections

fn main() / io {
  var turns = collections.Deque.from_list(["Embercat", "Mossling"])
  turns.push_back("Tidepup")
  let first = turns.pop_front() else return
  turns.push_back(first)
  print("{turns} {turns.front()}")
  var weakest = collections.Heap.new()
  weakest.push((30, "Embercat"))
  weakest.push((34, "Mossling"))
  weakest.push((32, "Tidepup"))
  print("{weakest.pop()} {weakest.peek()} {weakest}")
}
```

```output
Deque(["Mossling", "Tidepup", "Embercat"]) Some("Mossling")
Some((30, "Embercat")) Some((32, "Tidepup")) Heap([(32, "Tidepup"), (34, "Mossling")])
```

A heap's elements need `Ord`. To take the largest element first, store elements that order in reverse, such as negated numbers ([std.heap](../../reference/17-std.md#std.heap)).

## Option, Result and Ordering

The prelude declares `Option`, `Result` and `Ordering` as variant types, and [`Option` and `Result`](05-errors.md#option-and-result) shows how to use them for errors. Their methods do these jobs:

| Function | What it's for |
| --- | --- |
| `is_some`, `is_none`, `is_some_and` | Ask whether an `Option` holds a value |
| `unwrap_or`, `or`, `ok_or`, `to_list` | Replace a `None`, or turn an `Option` into a `Result` or a list |
| `map`, `filter`, `zip` | Change or combine the values inside |
| `is_ok`, `is_err`, `ok`, `err`, `map_err`, `get` | Read a `Result`, and raise its error with `get` |
| `Option.all`, `Result.all`, `Result.partition` | Collect a list of options or results |
| `Result.of` | Call a function, and turn its raise into an `Err` |
| `unwrap`, `expect` | The value, or a panic when there is none |
| `reversed`, `then` | Reverse an `Ordering`, or break a tie with a second one |

```stilt
fn main() / io {
  let hp = "30".to_i64()
  let missing = "thirty".to_i64()
  print("{hp.map(|x| x * 2)} {missing.unwrap_or(0)} {missing.or(Some(1))} {hp.is_some_and(|x| x > 25)}")
  let parsed = missing.ok_or("not a number")
  print("{parsed} {parsed.is_err()} {Result.all(["1", "x"].map(|s| s.to_i64().ok_or(s)))}")
  print("{None < Some(0)} {Less.then(Greater)} {Equal.then(Greater)}")
}
```

```output
Some(60) 0 Some(1) true
Err("not a number") true Err("x")
true Less Greater
```

`opt else d` does what `opt.unwrap_or(d)` does, but evaluates `d` only for a `None`, and `d` can be `return`, `raise` or `break` ([The `else` fallback](03-expressions.md#the-else-fallback)). `unwrap` and `expect` panic on a `None` or an `Err`, so use them only where the value must be there, as in a test. Code under `without panic` can't call them. The order of declaration fixes how the variants compare, so `None < Some(0)` and `Ok(1) < Err(0)` ([std.option-result-and-ordering](../../reference/17-std.md#std.option-result-and-ordering)).

## How values show

Interpolation shows a value through its `Show` impl ([Showing values](06-traits.md#showing-values)). The built-in and structural impls show values this way:

| Type | Shown as |
| --- | --- |
| Integers and floats | `-3`, `1.0`, `1e-7`, `nan`, as [Printed numbers](02-values.md#printed-numbers) describes |
| `bool`, `()` | `true`, `false`, `()` |
| `str` | `ana` alone, and `"ana"` inside another value |
| Tuples, `List`, `Map` | `(1, "a")`, `(1,)`, `[1, 2]`, `{"a": 1}` |
| Variants and records | `Some(3)`, `None`, `Move { name: "Root Snare", element: Plant, power: 30 }` |
| `Set`, `Deque`, `Heap` | `Set([1, 2])`, `Deque([1, 2])`, `Heap([1, 2])` |

```stilt
type Element = | Fire | Water | Plant

type Move = { name: str, element: Element, power: i64 }

fn main() / io {
  let move = Move { name: "Bubble Jet", element: Water, power: 35 }
  print("{move} {(1, "a")} {(1,)} {[Some(1.5), None]}")
  print("{["she said \"hi\"\n", "\u{1b}"]}")
}
```

```output
Move { name: "Bubble Jet", element: Water, power: 35 } (1, "a") (1,) [Some(1.5), None]
["she said \"hi\"\n", "\u{1b}"]
```

A name is shown without its module, so an `io.NotFound("x.txt")` shows as `NotFound("x.txt")`. A string inside another value is escaped, and control characters are written as `\u{…}` ([std.show-names-and-escapes](../../reference/17-std.md#std.show-names-and-escapes)).

### Format specs

A format spec after a colon changes how one interpolation shows its value. It sets a width, a fill and an alignment, a float's precision, or an integer's base ([Format specs](03-expressions.md#format-specs)):

```stilt
fn main() / io {
  let rate = 2.5
  print("[{"Embercat":<10}] [{30:>4}] [{30:0>4}] [{"hp":*^6}]")
  print("{rate:.2} {rate:.0} {12345.0:.2e} {255:x} {255:b}")
}
```

```output
[Embercat  ] [  30] [0030] [**hp**]
2.50 2 1.23e4 ff 11111111
```

`{rate:.0}` prints `2`, because a precision rounds a tie to even, while `rate.round()` gives `3.0`. A spec that doesn't fit the value's type is E0325, *invalid format spec*. A precision applies only to floats. A literal's type comes from the rest of the body, never from the spec, so `hp` here is an `i64`:

```stilt E0325:3
fn main() / io {
  let hp = 30
  print("{hp:.2}")
}
```

Every spec's exact output is in [Showing and formatting](../../reference/17-std.md#showing-and-formatting).

## Read and write files

`std.fs` reads and writes whole files. Each function that touches a file performs `io`, and each that can fail raises an `io.IoError`. So `fs.read` is `fs.read(path: str) -> str / {io, raise<io.IoError>}`:

| Function | What it's for |
| --- | --- |
| `fs.read`, `fs.read_lines`, `fs.read_bytes` | Read a whole file as text, as lines, or as bytes |
| `fs.write`, `fs.write_bytes`, `fs.append` | Create or replace a file, or add to its end |
| `fs.exists`, `fs.is_file`, `fs.is_dir` | Whether something is at a path |
| `fs.list_dir`, `fs.create_dir`, `fs.remove`, `fs.remove_all`, `fs.rename`, `fs.copy` | Work with directories, and move or copy files |
| `fs.join`, `fs.file_name`, `fs.parent`, `fs.extension` | Take paths apart and put them together, as text, touching no file |

An `IoError` says what went wrong, with the path:

| Variant | Meaning |
| --- | --- |
| `NotFound(path: str)` | The file, or a directory on its path, doesn't exist |
| `PermissionDenied(path: str)` | Access was refused |
| `InvalidUtf8(path: str)` | `read` or `read_lines` found bytes that aren't UTF-8 |
| `Other(path: str)` | Any other failure, such as a path that names a directory |

A `catch` can handle one variant and pass the rest on:

```stilt
use std.fs
use std.io

fn main() / {io, raise<io.IoError>} {
  try fs.write("roster.txt", "Embercat\nMossling\n")
  try fs.append("roster.txt", "Tidepup\n")
  print("{try fs.read_lines("roster.txt")}")
  let saved = try fs.read("save.txt") catch {
    io.NotFound(path) => "no file {path}, so a new tournament starts"
    error => raise error
  }
  print(saved)
}
```

```output
["Embercat", "Mossling", "Tidepup"]
no file save.txt, so a new tournament starts
```

An error that escapes `main` is printed after `error: `, and the program exits with status 1:

```stilt exit:1
use std.fs
use std.io

fn main() / {io, raise<io.IoError>} { print(try fs.read("save.txt")) }
```

```stderr
error: NotFound("save.txt")
```

`fs.create_dir` creates every missing directory on the path, and `fs.remove_all` removes a directory with everything in it. `fs.list_dir` gives the names of the entries, sorted:

```stilt
use std.fs
use std.io

fn main() / {io, raise<io.IoError>} {
  let dir = fs.join("tournaments", "2026")
  try fs.create_dir(dir)
  try fs.write(fs.join(dir, "final.txt"), "Embercat wins")
  print("{try fs.list_dir("tournaments")} {fs.is_dir(dir)} {fs.extension("final.txt")}")
  print("{fs.file_name("tournaments/2026/final.txt")} {fs.parent("tournaments/2026/final.txt")}")
  try fs.remove_all("tournaments")
  print("{fs.exists("tournaments")}")
}
```

```output
["2026"] true Some("txt")
final.txt tournaments/2026
false
```

Which error each function raises, and how the path functions treat a trailing `/`, is in [std.fs](../../reference/17-std.md#std.fs) and the paragraphs after it.

## Read input and write output

`std.io` reads standard input and writes without a newline:

| Function | What it does |
| --- | --- |
| `io.read_line() -> Option<str> / io` | Reads one line, without its line ending, or gives `None` at the end of the input |
| `io.read_lines() -> List<str> / io` | Reads every line that is left |
| `io.read_all() -> str / io` | Reads everything that is left |
| `io.poll_line() -> Option<str> / io` | Reads a line if one is waiting, and otherwise gives `None` at once |
| `io.write(s: str) / io`, `io.ewrite(s: str) / io` | Writes `s` to stdout, or to stderr, with no newline |
| `io.flush() / io` | Writes out what is waiting for stdout |

Text that `io.write` writes after its last newline waits. It goes out at the next newline, at `io.flush()`, at a read of stdin, or when the program ends. Every read writes out stdout first, so a prompt shows before the program waits for its answer. Run with no input, this program prints:

```stilt
use std.io

fn main() / io {
  io.write("Name your creature: ")
  let name = io.read_line() else "Embercat"
  print("{name} enters the arena")
  print("{io.read_lines().len()} more lines")
}
```

```output
Name your creature: Embercat enters the arena
0 more lines
```

`io.poll_line` lets a program check for a command between steps of its work, without waiting. Here a tournament checks for `stop` between rounds. With no input, no line ever waits, so it plays all three:

```stilt
use std.io

fn main() / io {
  var round = 1
  loop {
    print("round {round} done")
    if round == 3 || io.poll_line() == Some("stop") { break }
    round += 1
  }
  print("tournament over")
}
```

```output
round 1 done
round 2 done
round 3 done
tournament over
```

The reads share one stream, so a line that one of them reads is never read again by another. Bytes that aren't UTF-8 become U+FFFD ([std.io](../../reference/17-std.md#std.io)).

## Read the command line

`std.cli` gives a program its arguments and its environment:

| Function | What it gives |
| --- | --- |
| `cli.args() -> List<str> / io` | The arguments, without the program's name |
| `cli.arg(i: i64) -> Option<str> / io` | Argument `i`, counting from 0 |
| `cli.env(name: str) -> Option<str> / io` | The value of an environment variable, or `None` when it isn't set |

Run with no arguments, this program uses its default:

```stilt
use std.cli

fn main() / io {
  let name = cli.arg(0) else "Embercat"
  print("{name} enters the arena, with {cli.args().len()} arguments")
}
```

```output
Embercat enters the arena, with 0 arguments
```

The program's name is left out because its path differs between `stilt run` and a built executable ([std.cli](../../reference/17-std.md#std.cli)). [Parse creature stats from the command line](cookbook.md#parse-creature-stats-from-the-command-line) shows a program that parses flags.

## Time and dates

`std.clock` measures time, waits, and reads the date. Its module is named `clock`, so `time` stays free for your own variables:

| Function | What it's for |
| --- | --- |
| `clock.now`, `elapsed`, `since` | Measure how long something takes, with an `Instant` |
| `clock.sleep`, `clock.sleep_ms` | Wait for at least a duration |
| `Duration.from_ns`, `from_us`, `from_ms`, `from_seconds`, `from_minutes`, `from_hours` | Make a `Duration` |
| `whole_ms`, `whole_seconds`, `seconds`, `plus`, `minus` | Read and add durations |
| `DateTime.now`, `DateTime.of`, `DateTime.from_unix_seconds`, `DateTime.from_unix_ms`, `unix_seconds`, `unix_ms`, `weekday` | Dates and times in UTC |
| `to_rfc3339`, `DateTime.from_rfc3339` | Write and read RFC 3339 text, such as `2026-03-01T14:00:00Z` |
| `clock.unix_ms`, `clock.monotonic_ns` | The raw clocks |

An `Instant` reads a clock that never goes back, so use it to measure durations. A `DateTime` is a date and a time of day in UTC:

```stilt
use std.clock

fn main() / io {
  let start = clock.now()
  clock.sleep(clock.Duration.from_ms(15))
  print("{start.elapsed() >= clock.Duration.from_ms(15)}")
  let final = clock.DateTime.of(2026, 3, 1, 14, 0, 0) else return
  let lunch = clock.DateTime.from_rfc3339("2026-03-01T12:30:00+01:00") else return
  print("{final} {final.weekday()} {final.since(lunch)} {lunch.plus(clock.Duration.from_minutes(90))}")
  print("{clock.Duration.from_ms(1500)} {clock.Duration.from_us(250)} {clock.DateTime.from_rfc3339("yesterday")}")
}
```

```output
true
2026-03-01T14:00:00Z 7 9000s 2026-03-01T13:00:00Z
1.5s 250µs None
```

`DateTime.of` and `DateTime.from_rfc3339` give `None` for a date that doesn't exist or text they can't read. `from_rfc3339` converts an offset such as `+01:00` to UTC. `weekday` counts from 1 for Monday to 7 for Sunday. A duration shows in the largest unit it reaches, and durations and times compare in the order of time ([Time](../../reference/17-std.md#time)).

## Run other programs

`std.process` runs other programs. `process.run` runs one to its end and gives what it wrote:

| Function | What it's for |
| --- | --- |
| `process.run(program: str, args: List<str>) -> process.Output / {io, raise<io.IoError>}` | Run a program to its end, and capture its status and output |
| `Command.new`, `with_arg`, `with_args`, `with_env`, `without_env`, `with_dir`, `with_input` | Build a `Command`: the program, its arguments, environment, directory and input |
| `output`, `status`, `spawn` | Run a command: capture its output, let it write to the program's own output, or start it beside the program |
| `write`, `close_input`, `read_line`, `read_all`, `wait`, `kill` | Talk to a `Child`, a program started by `spawn` |

```stilt
use std.io
use std.process

fn main() / {io, raise<io.IoError>} {
  let out = try process.run("sh", ["-c", "echo found; echo warned >&2; exit 3"])
  print("{out.status} {out.stdout.trim()} {out.stderr.trim()}")
  let sorted = try process.Command.new("sort").with_input("Tidepup\nEmbercat\n").output()
  print(", ".join(sorted.stdout.lines()))
  let missing = try process.run("no-such-tool", []) catch {
    io.NotFound(name) => process.Output { status: 127, stdout: "", stderr: "no {name}" }
    error => raise error
  }
  print("{missing.status} {missing.stderr}")
}
```

```output
3 found warned
Embercat, Tidepup
127 no no-such-tool
```

A **status** is the code the program exited with, from 0 to 255, or `-n` when signal `n` ended it. A program name without a `/` is looked up in `PATH`. A program that can't start raises an `IoError`, such as `NotFound` with its name ([std.process-starting](../../reference/17-std.md#std.process-starting)).

A `Child` runs beside the program that started it, and its methods take it `inout`. `wait` closes its input, waits for it to end and gives its status, and keeps the rest of its output for later reads:

```stilt
use std.io
use std.process

fn main() / {io, raise<io.IoError>} {
  let script = "while read line; do echo \"got $line\"; done"
  var echo = try process.Command.new("sh").with_args(["-c", script]).spawn()
  try echo.write("first\n")
  print("{echo.read_line()}")
  try echo.write("second\nthird\n")
  print("{echo.wait()} {echo.read_line()} {echo.read_all().trim()}")
}
```

```output
Some("got first")
0 Some("got second") got third
```

Many programs hold their output back until a buffer fills when they write to a pipe. A `read_line` on such a child waits until the buffer fills or the child ends. Every function that runs a program has the capability `exec` ([Capabilities](05-errors.md#capabilities)).

## Connect over the network

`std.net` connects over TCP and sends datagrams over UDP. `std.http`, written on it, speaks HTTP/1.1. Every function that reaches the network performs `io` and has the capability `net`.

### TCP and UDP

A **listener** waits for connections on a port, and a **stream** is one connection:

| Function | What it's for |
| --- | --- |
| `net.connect`, `net.listen`, `net.lookup` | Connect to a host, listen on a port, and find a host's addresses |
| `accept`, `port`, `close` | Take a listener's next connection, read its port, and close it |
| `write`, `write_bytes`, `read_line`, `read_bytes`, `read_all`, `set_timeout`, `close_write` | Write to and read from a stream |
| `net.socket`, `send_to`, `receive` | Send and receive UDP datagrams |

A failed connect, listen or write raises an `IoError` that names the address, such as `Other("127.0.0.1:8080")` for a refused connection. A read gives `None` or the text so far at the end of the connection, and the same when it fails or times out. The system holds what a stream writes until the other end reads it, so one program can be both ends:

```stilt
use std.io
use std.net

fn main() / {io, raise<io.IoError>} {
  var listener = try net.listen("127.0.0.1", 0)
  var client = try net.connect("127.0.0.1", listener.port())
  try client.write("Embercat\n")
  var server = try listener.accept()
  let name = server.read_line() else "nobody"
  try server.write("{name} enters the arena\n")
  print("{client.read_line()}")
}
```

```output
Some("Embercat enters the arena")
```

Port 0 asks the system for a free port, which `port()` then gives. A UDP socket sends and receives datagrams, each whole or not at all. UDP doesn't promise that a datagram arrives, so set a timeout before `receive`:

```stilt
use std.io
use std.net

fn main() / {io, raise<io.IoError>} {
  var a = try net.socket("127.0.0.1", 0)
  var b = try net.socket("127.0.0.1", 0)
  try a.send_to("ping".bytes(), "127.0.0.1", b.port())
  b.set_timeout(1000)
  let got = b.receive() else {
    print("nothing arrived")
    return
  }
  print("{got.bytes.len()} bytes, from this machine: {got.from.starts_with("127.0.0.1:")}")
}
```

```output
4 bytes, from this machine: true
```

`receive` gives a `Datagram { bytes, from }`, where `from` is the sender's `ip:port` ([std.net-datagrams](../../reference/17-std.md#std.net-datagrams)).

### HTTP

`std.http` declares `Request`, `Response` and `Error`, and has a client and a server:

| Function | What it's for |
| --- | --- |
| `http.get(url: str) -> http.Response / {io, raise<http.Error>}` | Fetch a URL |
| `http.post(url: str, content_type: str, body: str) -> http.Response / {io, raise<http.Error>}` | Send a body to a URL |
| `http.send(request: http.Request, url: str) -> http.Response / {io, raise<http.Error>}` | Send a request you built |
| `Request.new`, `Response.new`, `with_header`, `with_body`, `header` | Build a message, and read a header in any case |
| `http.serve(inout listener: net.Listener, handle: fn(http.Request) -> http.Response) -> Never / io` | Answer every connection with `handle`, for as long as the program runs |
| `http.serve_one`, `read_request`, `write_response`, `write_request`, `read_response` | Serve one connection, or do each half of an exchange yourself |

A client and a server, each a program of its own:

```stilt
use std.http
use std.io

fn main() / {io, raise<http.Error>} {
  let r = try http.get("http://127.0.0.1:8080/roster")
  print("{r.status} {r.header("content-type")} {r.body}")
}
```

```stilt
use std.http
use std.io
use std.net

fn main() / {io, raise<io.IoError>} {
  var listener = try net.listen("127.0.0.1", 8080)
  http.serve(inout listener, |r| {
    if r.target == "/roster" { http.Response.new(200, "Embercat, Mossling, Tidepup").with_header("Content-Type", "text/plain") }
    else { http.Response.new(404, "") }
  })
}
```

An `http.Error` is `Io` for a connection that failed, `Url` for a URL the client can't fetch, or `Message` for a message that isn't HTTP/1.1. The client speaks no TLS, so it fetches `http://` URLs only, and an `https://` URL raises `Url`. Each connection carries one request and closes after the answer, so `serve` answers one client at a time ([std.http](../../reference/17-std.md#std.http)).

## Random numbers

`std.random` declares `Rng`, a generator written in Stilt, so a seed gives the same numbers in every implementation:

| Function | What it's for |
| --- | --- |
| `Rng.seeded`, `Rng.from_entropy` | Make a generator from a seed, or from the system's randomness |
| `below`, `range`, `float`, `chance`, `next_u64` | Draw a number |
| `shuffle`, `shuffled`, `pick` | Shuffle a list, or pick one element |

```stilt
use std.random

fn main() / io {
  var rng = random.Rng.seeded(7)
  var damage: List<i64> = []
  for _ in 0..3 { damage.push(rng.range(5, 9)) }
  let order = rng.shuffled(["Embercat", "Mossling", "Tidepup"])
  print("{damage} {order} {rng.pick(["Flame Pounce", "Root Snare", "Bubble Jet"])} {rng.chance(0.5)}")
}
```

```output
[8, 5, 7] ["Mossling", "Tidepup", "Embercat"] Some("Flame Pounce") true
```

`range(5, 9)` draws from 5 up to 8, each equally likely, and `below(n)` from 0 up to `n - 1`. Both panic when the range is empty. Every draw changes the generator, so its methods take `inout self`. A closure can't change what it captures, so draw numbers in a loop, as here, instead of in `map` ([std.random-numbers](../../reference/17-std.md#std.random-numbers)).

## Encodings and hashes

`std.encoding` writes bytes as text and reads them back, and `std.hashing` hashes bytes. Both are written in Stilt, and none of their functions performs `io` or panics:

| Function | What it's for |
| --- | --- |
| `encoding.to_base64`, `encoding.from_base64`, `encoding.to_base64_url`, `encoding.from_base64_url` | Base64, and its form for URLs |
| `encoding.to_hex`, `encoding.from_hex` | Two hexadecimal digits for each byte |
| `encoding.from_utf8` | Text from bytes, or a raise that says where they stop being UTF-8 |
| `hashing.sha256`, `hashing.hmac_sha256` | SHA-256 and its HMAC, 32 bytes each |
| `hashing.fnv1a` | FNV-1a, a fast 64-bit hash that is the same everywhere, with no cryptographic strength |

`from_base64`, `from_base64_url` and `from_hex` give `None` for text that their writer can't produce:

```stilt
use std.encoding
use std.hashing

fn main() / io {
  let token = encoding.to_base64("user:pass".bytes())
  print("{token} {encoding.from_base64(token) == Some("user:pass".bytes())}")
  print("{encoding.to_hex(hashing.sha256("abc".bytes())).slice(0, 16)} {hashing.fnv1a("abc".bytes()):x}")
  print("{Result.of(|| try encoding.from_utf8([104, 105, 226, 130]))} {encoding.from_hex("zz")}")
}
```

```output
dXNlcjpwYXNz true
ba7816bf8f01cfea e71fa2190541574b
Err(Truncated(2)) None
```

`str.from_utf8` says only whether bytes are UTF-8. `encoding.from_utf8` raises `Truncated(offset)` when the bytes end inside a character, as a stream cut short does, and `Invalid(offset)` for any other bad sequence ([std.utf8-errors](../../reference/17-std.md#std.utf8-errors)).

## Lazy values

`std.lazy` declares `Lazy<T>`, a value computed the first time it is read. `Lazy.new(f)` keeps a function that performs no effects, and `get` returns its value, computed once for the `Lazy` and all its copies. It belongs to the `advanced` tier ([Polymorphic arguments and lazy values](14-polymorphism.md#lazy-values)):

```stilt
use std.lazy

fn main() / io {
  let total = lazy.Lazy.new(|| i64.sum([30, 34, 32]))
  print("{total.get()} {total.get() * 2}")
}
```

```output
96 192
```
