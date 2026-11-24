# Cookbook

Each recipe is a short, whole program for one everyday job, using only the standard library. The guide's tests run every one of them. [The standard library](09-library.md) describes the modules they use, and `stilt doc --std` writes a page for each module, with every function's signature, facts and examples.

## Read a file line by line

If a program keeps its data in a text file, such as a roster of creatures, read it with `fs.read_lines`:

```stilt
use std.fs
use std.io

fn main() / {io, raise<io.IoError>} {
  try fs.write("roster.txt", "Embercat 30\nMossling 34\n\nTidepup 32\n")
  let lines = try fs.read_lines("roster.txt")
  print("{lines.len()} lines")
  for line in lines {
    let fields = line.split_whitespace()
    if fields.is_empty() { continue }
    print("{fields[0]} has {fields[1]} HP")
  }
  try fs.remove("roster.txt")
}
```

```output
4 lines
Embercat has 30 HP
Mossling has 34 HP
Tidepup has 32 HP
```

`fs.read_lines` splits the text on `\n`, as `str.lines` does. The blank line in the middle is a line, and the final newline doesn't start an empty one. `fs.read` gives the whole text instead, and `fs.append` adds to the end of a file. Each function of `std.fs` raises an `io.IoError` that names the path, so `main` declares it in its row ([Read and write files](09-library.md#read-and-write-files)).

## Read a file that may be missing

If a missing file means "start fresh", catch `NotFound` and pass every other error on:

```stilt
use std.fs
use std.io

/// The text of the file at `path`, or `""` when there is none.
fn read_or_empty(path: str) -> str / {io, raise<io.IoError>} {
  try fs.read(path) catch {
    NotFound(_) => ""
    e => raise e
  }
}

fn main() / {io, raise<io.IoError>} {
  let saved = try read_or_empty("save.txt")
  if saved.is_empty() { print("No save file, so a new tournament starts.") }
}
```

```output
No save file, so a new tournament starts.
```

An `io.IoError` is a variant type, so `catch` matches its variants as `match` does. The arm `e => raise e` raises the other errors again ([Handling errors with `catch`](05-errors.md#handling-errors-with-catch)).

## Keep files in a directory

If a program writes one file per battle, put them in a directory with `fs.create_dir`, and build each path with `fs.join`:

```stilt
use std.fs
use std.io

fn main() / {io, raise<io.IoError>} {
  try fs.create_dir("logs")
  try fs.write(fs.join("logs", "round-2.log"), "Mossling wins")
  try fs.write(fs.join("logs", "round-1.log"), "Embercat wins")
  for name in try fs.list_dir("logs") {
    print("{name}: {try fs.read(fs.join("logs", name))}")
  }
  try fs.remove_all("logs")
}
```

```output
round-1.log: Embercat wins
round-2.log: Mossling wins
```

`fs.list_dir` gives the names of the entries, sorted, and `fs.remove_all` removes a directory with everything in it ([Read and write files](09-library.md#read-and-write-files)).

## Parse creature stats from the command line

If a program takes options, parse `cli.args()` in a function of its own, so tests can call it with any list of arguments:

```stilt pass:34 pass:39 pass:44
use std.cli

/// What the command line asks for.
type Options = { hp: i64, verbose: bool, names: List<str> }

/// Reads `-v`, `--hp N` and creature names, in any order.
fn parse(args: List<str>) -> Options / raise<str> {
  var options = Options { hp: 30, verbose: false, names: [] }
  var i = 0
  while i < args.len() {
    let arg = args[i]
    if arg == "-v" {
      options.verbose = true
    } else if arg == "--hp" {
      let n = args.get(i + 1) else raise "--hp needs a number"
      options.hp = n.to_i64() else raise "--hp needs a number, not {n}"
      i += 1
    } else if arg.starts_with("-") {
      raise "unknown option {arg}"
    } else {
      options.names.push(arg)
    }
    i += 1
  }
  options
}

fn main() / {io, raise<str>} {
  let options = try parse(cli.args())
  for name in options.names { print("{name} enters with {options.hp} HP") }
  if options.verbose { print("{options.names.len()} creatures") }
}

test "options and names mix" {
  let options = Result.of(|| try parse(["Embercat", "--hp", "40", "-v", "Mossling"]))
  assert options == Ok(Options { hp: 40, verbose: true, names: ["Embercat", "Mossling"] })
}

test "--hp needs a number" {
  assert Result.of(|| try parse(["--hp"])) == Err("--hp needs a number")
  assert Result.of(|| try parse(["--hp", "lots"])) == Err("--hp needs a number, not lots")
}

test "an unknown option is refused" {
  assert Result.of(|| try parse(["--all"])) == Err("unknown option --all")
}
```

`cli.args()` gives the arguments without the program's own name ([Read the command line](09-library.md#read-the-command-line)). `args.get(i + 1)` gives an `Option`, and `else raise` raises when it is `None`. `Result.of` turns a raise into an `Err`, so a test can compare it ([`Option` and `Result`](05-errors.md#option-and-result)).

In a package, `stilt run` passes every argument after the program's path on to the program:

```console
$ stilt run . -v --hp 40 Embercat Mossling
Embercat enters with 40 HP
Mossling enters with 40 HP
2 creatures
$ stilt run . --all
error: unknown option --all
```

The program [`examples/flags`](../../examples/flags/) reads options from a record's type instead, by reflection.

## Save results as JSON

If a program saves its results for another program, write them with `json.to_text`. Any value whose type is built from records, variants, lists, maps, options and the basic types has JSON, with nothing declared on the type:

```stilt
use std.fs
use std.io
use std.json

type Element = | Fire | Water | Plant

/// How a creature did in a tournament.
type Standing = { name: str, element: Element, wins: i64, title: Option<str> }

fn main() / {io, raise<io.IoError>} {
  let standings = [
    Standing { name: "Embercat", element: Fire, wins: 2, title: Some("champion") },
    Standing { name: "Mossling", element: Plant, wins: 1, title: None },
  ]
  try fs.write("standings.json", json.to_text(standings))
  print(try fs.read("standings.json"))
  try fs.remove("standings.json")
}
```

```output
[{"name":"Embercat","element":"Fire","wins":2,"title":"champion"},{"name":"Mossling","element":"Plant","wins":1,"title":null}]
```

A record writes an object, a variant without a payload writes its name, and `None` writes `null` ([JSON](18-compile-time.md#json), [std.json-writing](../../reference/17-std.md#std.json-writing)).

## Load a roster from JSON

If a function reads a file of JSON, it meets two error types, `io.IoError` and `json.Error`. A row holds one error type, so the function turns both into its own ([One error type per row](05-errors.md#one-error-type-per-row)):

```stilt exit:1
use std.fs
use std.json

type Element = | Fire | Water | Plant
type Creature = { name: str, element: Element, hp: i64, attack: i64 }

/// The roster saved in the file at `path`.
fn load(path: str) -> List<Creature> / {io, raise<str>} {
  let text = try fs.read(path) catch _ => raise "can't read {path}"
  try json.from_text(text) catch e => raise "{path}: {e}"
}

fn main() / {io, raise<str>} {
  let saved = "[\{\"name\": \"Mossling\", \"element\": \"Plant\", \"hp\": 34.5, \"attack\": 6}]"
  try fs.write("roster.json", saved) catch _ => raise "can't write roster.json"
  let roster = try load("roster.json")
  print("{roster.len()} creatures")
}
```

```stderr
error: roster.json: Mismatch("$[0].hp", "i64", "34.5")
```

The return type of `load` tells `json.from_text` which type to read. `34.5` is no `i64`, so the error says where it was found, `$[0].hp`, what was expected, and what was there. A field of type `Option<T>` that the JSON leaves out reads as `None`, and members that no field names are ignored ([std.json-reading](../../reference/17-std.md#std.json-reading)). A literal brace in a string is written `\{`, because `{` starts an interpolation.

## Read JSON of unknown shape

If you don't know the shape of the JSON in advance, `json.parse` gives a `json.Value`, a variant type to match on:

```stilt
use std.json

/// What kind of JSON value `v` is.
fn kind(v: json.Value) -> str {
  match v {
    Null => "null"
    Bool(_) => "a bool"
    Number(n) => "the number {n}"
    Text(_) => "text"
    Array(xs) => "an array of {xs.len()}"
    Object(members) => "an object of {members.len()}"
  }
}

fn main() / {io, raise<json.Error>} {
  let v = try json.parse("\{\"name\": \"Tidepup\", \"hp\": 32, \"moves\": [\"Bubble Jet\"], \"trainer\": null}")
  let Object(members) = v else return
  for (name, member) in members { print("{name}: {kind(member)}") }
}
```

```output
name: text
hp: the number 32
moves: an array of 1
trainer: null
```

An object keeps its members in order, and a number keeps its text. `let Object(members) = v else return` takes the members out, or returns when `v` isn't an object ([`let` and let-else](04-declarations.md#let-and-let-else)).

## Simulate battles in parallel

If you run many independent battles, `par.map` runs them on every core. Here every creature fights every other one:

```stilt
use std.par

type Element = | Fire | Water | Plant
type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn effectiveness(attacker: Element, defender: Element) -> i64 {
  match (attacker, defender) {
    (Fire, Plant) | (Water, Fire) | (Plant, Water) => 200
    (Fire, Water) | (Water, Plant) | (Plant, Fire) => 50
    _ => 100
  }
}

/// The name of the winner when `a` and `b` fight, `a` hitting first.
fn battle(a: Creature, b: Creature) -> str {
  var a = a
  var b = b
  loop {
    b.hp -= a.attack * effectiveness(a.element, b.element) / 100
    if b.hp <= 0 { return a.name }
    a.hp -= b.attack * effectiveness(b.element, a.element) / 100
    if a.hp <= 0 { return b.name }
  }
}

fn main() / io {
  let roster = [
    Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 },
    Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 },
    Creature { name: "Tidepup", element: Water, hp: 32, attack: 7 },
  ]
  let matchups = roster.flat_map(|a| roster.filter(|b| b.name != a.name).map(|b| (a, b)))
  let winners = par.map(matchups, |m| battle(m.0, m.1))
  print("{winners}")
  print("{winners.count_by(|w| w)}")
}
```

```output
["Embercat", "Tidepup", "Embercat", "Mossling", "Tidepup", "Mossling"]
{"Embercat": 2, "Tidepup": 2, "Mossling": 2}
```

The closure given to `par.map` performs no effect, so the result is the one a loop gives, in the same order, on any number of cores. A closure that prints or raises doesn't compile. `par.each`, `par.fold` and `par.both` change a list in place, combine one, and run two computations ([Parallel loops](17-effects.md#parallel-loops)).

## Test with properties

If a function has a rule that holds for every input, write it as a property, and `stilt test` looks for an input that breaks it:

```stilt pass:5 pass:6 fail:7 pass:10
type Element = | Fire | Water | Plant
type Creature = { name: str, element: Element, hp: i64, attack: i64 }

/// The creatures of `roster`, the most hit points first.
/// prop: |roster: List<Creature>| rank(roster).len() == roster.len()
/// prop: |roster: List<Creature>| rank(roster).map(.hp).reversed().is_sorted()
/// prop: |roster: List<Creature>| rank(roster).map(.name) == roster.map(.name).sorted()
fn rank(roster: List<Creature>) -> List<Creature> { roster.sorted_desc_by(.hp) }

test "an empty roster ranks empty" {
  assert rank([]) == []
}
```

A property is a doc line that starts with `prop:`, holding a closure whose parameters have their types written. `stilt test` generates values of those types, here whole rosters, and runs the closure on each. The first two properties hold. The third is wrong, because `rank` orders by hit points. `stilt test` reports a roster that breaks it, shrunk to two creatures: one named `""` with 0 HP, then one named `"a"` with 1 HP.

A property that holds only for some inputs states its condition first, with `||`. A property that starts `hp < 0 || damage < 0 || …` passes every case with a negative value without running the rest. Each run tries the same cases, and a property can't perform `io` ([Properties](08-programs.md#properties)).
