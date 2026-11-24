# Pattern macros

A macro can turn a short table of creatures into the records it stands for:

```stilt
type Element = | Fire | Water | Plant
type Creature = { name: str, element: Element, hp: i64, attack: i64 }

syntax roster {
  [$($name: expr => $element: Name, $hp: expr, $attack: expr);+] => [$(
    Creature { name: $name, element: $element, hp: $hp, attack: $attack }
  ),+]
}

fn main() / io {
  let creatures = roster![
    "Embercat" => Fire, 30, 8;
    "Mossling" => Plant, 34, 6;
    "Tidepup" => Water, 32, 7
  ]
  for c in creatures { print("{c.name}: {c.hp} HP") }
}
```

```output
Embercat: 30 HP
Mossling: 34 HP
Tidepup: 32 HP
```

`roster!` writes three `Creature` literals, so the table stays readable and the compiler still checks every field. A **pattern macro** adds a form of your own, for code a function can't express: a table like this one, a block that runs only sometimes, or a name the caller chooses. A macro is matched and substituted, never run. Macros that compute code are procedural macros, in the `meta` tier ([procedural macros](18-compile-time.md#procedural-macros)).

Declaring a macro puts a module in the `advanced` tier. A module that only uses a macro declared elsewhere stays in its tier ([tiers](08-programs.md#module-headers-tiers-and-limits)).

## Arms and fragments

`syntax` declares a macro: a name, then arms, each a **pattern**, `=>` and a **template**. A use writes the name with `!`, as `roster![…]`, so every tool can tell a use from a call. The template of the first arm that matches replaces the use.

In a pattern, `$name: expr` is a **fragment**: it matches one expression and names it, and `$name` in the template puts it back. A fragment's kind is `expr`, `block`, `pattern`, `type`, `name` for a lowercase name such as `mossling`, or `Name` for an uppercase one such as `Fire` ([patterns](../../reference/16-meta.md#macros.patterns)).

A `$body: block` after the pattern's brackets matches a block written after the use, on the same line. A function's arguments are evaluated before the call, so only a macro can take a block that runs only sometimes:

```stilt
syntax unless {
  ($cond: expr) $body: block => if !($cond) $body
}

fn main() / io {
  let hp = 18
  unless!(hp == 0) { print("Mossling fights on with {hp} HP.") }
}
```

```output
Mossling fights on with 18 HP.
```

An `expr`, `pattern` or `type` fragment must be followed by `,`, `;`, `=>` or the end of its group, so that it can't run on into what follows. That is why `roster!` writes `=>` after the name. A fragment stays one form, as if it were in parentheses: a template `$x * 2` given `1 + 2` computes `(1 + 2) * 2` ([expansion](../../reference/16-meta.md#macros.expansion)).

## Repetitions

A **repetition**, `$( … ),*`, matches what it holds any number of times, separated by commas, and in the template repeats what it holds once for each match. `+` instead of `*` needs at least one match, and `;` or nothing can separate instead of `,`. In `roster!`, `$( … );+` matches each line of the table, and the template's `$( … ),+` writes one `Creature` for each.

The arms are tried in order, and the first one that matches is used:

```stilt
syntax count {
  () => "no creatures"
  ($x: expr) => "one creature: {$x}"
  ($($x: expr),+) => "{[$($x),+].len()} creatures"
}

fn main() / io {
  print(count!())
  print(count!("Embercat"))
  print(count!("Embercat", "Mossling", "Tidepup"))
}
```

```output
no creatures
one creature: Embercat
3 creatures
```

A use that no arm matches is E0222, *use that no arm matches*. The message says how far the closest arm got and what it expected there.

## Macros as items

A macro is an item: it can be `pub` and documented, and another module uses it by its path, as `tools.unless!(…)`. A macro whose templates are all patterns is used where a pattern goes, as `pair!(1, s) => …` in a `match` arm.

A template can use macros, its own among them. A use nested too deep in expansions is E0224, and one whose expansions grow too large is E0231 ([expansions](../../reference/16-meta.md#macros.nested-expansions)).

## Hygiene

A macro is **hygienic**: a template means what its author wrote, wherever it is used. The names a template binds are its own, and the caller's names are the caller's. Here the template's `tmp` and the caller's `tmp` are two different variables:

```stilt
syntax swap {
  ($a: name, $b: name) => {
    let tmp = $a
    $a = $b
    $b = tmp
  }
}

fn main() / io {
  var tmp = 30
  var hp = 34
  swap!(tmp, hp)
  print("{tmp} {hp}")
}
```

```output
34 30
```

Every other name a template writes is found where the macro is declared, among that module's items and imports, private ones included ([hygiene](../../reference/16-meta.md#macros.hygiene)). So `roster!` can name `Creature` in a module that doesn't import it, and a macro can call a helper that the modules using it never see.

The compiler checks each template where the macro is declared, before any use:

- A name the template writes that doesn't exist there is E0211.
- A template that names a fragment its pattern doesn't bind, or that is neither an expression nor a pattern, is E0221, *malformed macro template*.
- A pattern that names a fragment twice, or lets a fragment run on into what follows it, is E0220, *malformed macro pattern* ([pattern checks](../../reference/16-meta.md#macros.pattern-checks)).

An error in an expansion is reported where you wrote the code: in a fragment, at its tokens, and in the template, at the use, with a note that shows the template line.

The expansion is the using function's own code, so its effects and facts are inferred there, and that function's `without` limits them. `stilt fmt` and `stilt show` print uses as written. `stilt show --expanded` prints each expansion in its place, with each name the template binds followed by `#` and a number, as `tmp#1` ([showing expansions](../../reference/16-meta.md#macros.showing)).
