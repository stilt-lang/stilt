# Stilt for Go programmers

Here is the tour's `hit` function in Go:

```go
func hit(attacker Creature, defender *Creature) string {
    defender.HP = max(defender.HP-attacker.Attack, 0)
    return fmt.Sprintf("%s hits %s. %s has %d HP left.", attacker.Name, defender.Name, defender.Name, defender.HP)
}
```

And here it is in Stilt:

```stilt
type Element = | Fire | Water | Plant

type Creature = { name: str, element: Element, hp: i64, attack: i64 }

fn hit(attacker: Creature, inout defender: Creature) -> str {
  defender.hp = (defender.hp - attacker.attack).max(0)
  "{attacker.name} hits {defender.name}. {defender.name} has {defender.hp} HP left."
}

fn main() / io {
  let embercat = Creature { name: "Embercat", element: Fire, hp: 30, attack: 8 }
  var mossling = Creature { name: "Mossling", element: Plant, hp: 34, attack: 6 }
  print(hit(embercat, inout mossling))
}
```

```output
Embercat hits Mossling. Mossling has 26 HP left.
```

As in Go, `attacker` is the function's own copy. Where Go passes a pointer, Stilt marks the parameter `inout`, and the call marks the argument the same way, as `&mossling` does. An `inout` parameter can't be `nil`, and the function can't keep it after it returns. A string literal interpolates any expression between braces. `/ io` says that `main` prints: a function's signature lists what it does to the outside world.

## At a glance

These are the Go forms you know, with what Stilt writes instead:

| Go | Stilt |
| --- | --- |
| `go mod init`, `go run .`, `go test`, `go build` | `stilt new`, `stilt run`, `stilt test`, `stilt build --release` |
| `go vet`, `gofmt`, `go doc`, gopls | `stilt check`, `stilt fmt`, `stilt doc`, `stilt lsp` |
| `go.mod`, `go.sum` | `stilt.toml` |
| `x := 1`, `var x = 1` | `let x = 1`, which can't change, or `var x = 1`, which can |
| `struct` | a record, `type Point = { x: f64, y: f64 }` |
| a pointer parameter | an `inout` parameter |
| methods on a type | functions in `impl Point { … }` |
| `interface` | `trait`, implemented with `impl Trait for Type` |
| `iota` constants, type switches | variant types and `match` |
| `nil` | `Option<T>`: `Some(x)` or `None` |
| `(T, error)` and `if err != nil` | `raise<E>` in the row, and `try` before each call that can raise |
| `panic`, `recover` | `panic`, which nothing catches |
| slices, maps | `List<T>`, `Map<K, V>`, which keeps insertion order |
| goroutines and `sync.WaitGroup` | `task.spawn` inside `with task.threads() { … }` |
| `sync.Mutex` | `sync.Shared<T>`, reached with `when` |
| `fmt.Printf("%5.2f\n", x)` | `print("{x:5.2}")` |

## Values and copies

A Go slice shares its backing array, so appending to one slice can change another:

```go
roster := []string{"Embercat", "Mossling"}
team := roster[:1]
team = append(team, "Tidepup")
fmt.Println(roster, team) // [Embercat Tidepup] [Embercat Tidepup]
```

Every Stilt value is independent. Assigning or passing it makes a copy, so changing one value never changes another:

```stilt
fn main() / io {
  let roster = ["Embercat", "Mossling"]
  var team = roster.take(1)
  team.push("Tidepup")
  print("{roster} {team}")
}
```

```output
["Embercat", "Mossling"] ["Embercat", "Tidepup"]
```

The compiler keeps copies cheap: a copy shares its storage until one side changes. It frees a value when its last use ends, by counting references, so there is no garbage collector ([how copies stay cheap](../../reference/rationale/05-values.md#value-semantics)). Two `inout` arguments of one call can't overlap, so `swap(inout xs[0], inout xs[1])` doesn't compile ([Parameter modes](07-modes.md)).

## Numbers

Every integer type has its size in its name, as Go's `int64` does: `i8` to `i64` and `u8` to `u64`, with `f32` and `f64` for floats. There is no `int`. Lengths and indices are `i64`. As in Go, nothing converts implicitly, and integer `/` truncates toward zero.

Integer overflow panics, where Go wraps silently. `+%`, `-%` and `*%` wrap on purpose ([Integer arithmetic](02-values.md#integer-arithmetic)).

## Errors

A Go function that can fail returns an `error` beside its result, and the caller checks `err != nil`. A Stilt function names its error type in its **row**, after `/`, and returns the plain value:

```stilt
type HpError = | NotANumber(text: str) | NotPositive(hp: i64)

/// The hit points written in `text`.
fn parse_hp(text: str) -> i64 / raise<HpError> {
  let hp = text.to_i64() else raise NotANumber(text)
  if hp <= 0 { raise NotPositive(hp) }
  hp
}

fn main() / io {
  let hp = try parse_hp("x") catch {
    NotANumber(_) => 1
    NotPositive(_) => 1
  }
  print("{hp} {Result.of(|| try parse_hp("30"))} {Result.of(|| try parse_hp("-5"))}")
}
```

```output
1 Ok(30) Err(NotPositive(-5))
```

A caller writes `try` before each call that can raise, or the program doesn't compile, so no error goes unchecked. `catch` handles the error, and because `HpError` is a variant type, it knows every case. `Result.of` gives the error as a value. The compiler returns a raised error as an ordinary value, as Go does ([how raising is compiled](../../reference/rationale/12-effects.md#raising-and-marking), [Errors and effects](05-errors.md)).

## Variant types and `Option`

Go writes a closed set of cases as constants, or as types behind an interface, and doesn't check that a `switch` covers them all. A Stilt variant type carries data in each case, and `match` must cover every one:

```stilt
type Element = | Fire | Water | Plant

type Move = { name: str, element: Element, power: i64 }

/// What happened on one turn of a battle.
type Turn = | Hit(damage: i64) | Miss

fn main() / io {
  for turn in [Hit(16), Miss] {
    print(match turn {
      Hit(damage) => "hit for {damage}"
      Miss => "missed"
    })
  }
  let moves = [Move { name: "Flame Pounce", element: Fire, power: 40 }]
  let pounce = moves.find(|m| m.name == "Flame Pounce")
  let jet = moves.find(|m| m.name == "Bubble Jet")
  print("{pounce.power else 0} {jet.power else 0}")
}
```

```output
hit for 16
missed
40 0
```

There is no `nil`. A value that can be missing is an `Option`, such as the result of `find`. A field read through an `Option` gives an `Option`, and `else` gives a fallback when it is `None` ([Fields through options](03-expressions.md#fields-through-options), [Variant types](04-declarations.md#variant-types)).

## Traits and generics

A Go type satisfies an interface by having its methods. A Stilt type implements a trait by saying so, with `impl`:

```stilt fragment
trait Label {
  fn label(self) -> str
}

impl Label for Move {
  fn label(self) -> str { "{self.name} ({self.power})" }
}

fn labels<T: Label>(xs: List<T>) -> List<str> { xs.map(|x| x.label()) }
```

A generic function names the traits it needs, as a Go type constraint does, and a call never names its type arguments. A record, a variant type or a tuple gets `==`, ordering, hashing and printing from its parts, with no method to write ([Structural impls](06-traits.md#structural-impls)).

## Tasks and parallel loops

`task.spawn` starts a task, as `go` does, and `t.await()` waits for its value. A `with task.threads() { … }` block runs its tasks on threads and waits for all of them before it ends, as a `WaitGroup` would. `par.map` runs a function over a list on every core.

A task captures its values by copy, so tasks share nothing by accident. State that tasks change together lives in a `sync.Shared<T>`, and only a `when` block reaches its value, so no access can forget the lock. There are no channels. A program prints the same under threads as when each task runs to its end in turn, and `par.map` gives the result a loop gives ([Effects, tasks and parallelism](17-effects.md)).

## Inferred facts and limits

The compiler infers **facts** about every function, such as `alloc` when it allocates, `panic` when it can panic and `overflow` when its arithmetic can overflow. `stilt show` prints them with the operation behind each, much as `go build -gcflags=-m` prints what escapes to the heap ([Ask what the compiler inferred](01-tour.md#ask-what-the-compiler-inferred)). A `without` clause turns facts into a **limit**, which the checker holds the body to. If you index a list in the tour's `fn damage(…) -> i64 without panic, alloc`, it stops compiling ([Limits](05-errors.md#limits)).

## Modules, packages and tests

A file is a module, where a Go package is a directory. `pub` marks what other modules see, as a capital letter does. `use std.fs` imports the module, and code names `fs.read`, as Go names `os.ReadFile` ([Programs](08-programs.md)).

Tests sit beside the code, in the same file: a `test "name" { … }` block is a test, and a doc comment holds examples, `/// ex:` lines, and properties, `/// prop:` lines. `stilt test` runs a property on generated values ([Tests](08-programs.md#tests)). `stilt fmt` has no options, as `gofmt` has none.
