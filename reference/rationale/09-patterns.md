# 9. Patterns: rationale

Stilt promises that every `match` is exhaustive. It also gives `else` two meanings that look alike: the let-else of `let [customer, q, p] = text.split(",") else raise …`, and the `Option` fallback of `let qty = q.to_i64() else raise …`. The sections below say why the pattern forms are the ones they are, why refutability goes by syntax alone, and why exhaustiveness ignores guards and constants.

## Forms

The forms are those of ML and Rust, kept to what exhaustive matching needs ([patterns.pattern-forms](../09-patterns.md#patterns.pattern-forms)). Range patterns, `@` bindings and list patterns with elements after `..` are left out ([patterns.no-other-forms](../09-patterns.md#patterns.no-other-forms)). Each would be a form of its own, with its own case in the exhaustiveness check. A guard already tests a range, as `n if n >= 1 && n <= 9` does.

A payload is matched by position only, as it is built. Payload names in patterns would give each variant two pattern forms.

Float equality isn't reflexive, because NaN is unequal to itself. A float pattern could then fail to match a value equal to itself, so no literal and no constant that holds a float matches a float ([patterns.floats](../09-patterns.md#patterns.floats)). Whether a constant holds a float goes by its type, so whether it is a pattern never depends on its value.

The alternatives of an or-pattern bind the same names with the same types ([patterns.or-patterns](../09-patterns.md#patterns.or-patterns)), because the arm's body sees the same variables whichever alternative matched. A name that only some alternatives bind takes the error type, so one mistake gives one diagnostic.

## Constants

A constant pattern compares structurally ([patterns.constants](../09-patterns.md#patterns.constants)), while `==` calls the `eq` of each type. Where the program writes the `Eq` of a type, the two could disagree, so a constant whose type holds such a type isn't a pattern ([patterns.constants-with-written-eq](../09-patterns.md#patterns.constants-with-written-eq)). Rust rejects such constants for the same reason.

The other choice is to call the written `eq` while matching, so that the pattern and `==` agree. That hides a call inside a `match`, and the call could panic while the arms are tried.

The rule goes by the type, as the rule on floats does. So `const NOBODY: Option<Name> = None` is rejected, though its value holds no `Name`. A constant's value can then change without changing whether it is a pattern.

## Variants named by the matched type

A pattern names a variant of the type it matches without its module ([patterns.variants-by-type](../09-patterns.md#patterns.variants-by-type)). The matched type names one home for the variant, so the variant meant is never in doubt. With qualified variants in every pattern, as Rust needs for an enum it doesn't import, a walker over the syntax tree of another module repeats the module on most lines: `ebnf.Seq`, `ebnf.Alt` and `ebnf.Lit` on every arm.

Expressions still name the variants of another module with the module. The expected type of an expression is often not known where a constructor stands, so a bare name there would mean different things in code that looks alike. A constructor is also written once, where a pattern names it on every arm. So a search for `ebnf.Seq` still finds every place that builds one.

## Bindings

A binding is a copy ([patterns.bindings-are-copies](../09-patterns.md#patterns.bindings-are-copies)), as every value in core is ([values.independent-copies](../05-values.md#values.independent-copies)), so matching never makes an alias. Rust's `ref` and `ref mut` bindings have no counterpart. Bindings are immutable unless a `var` statement makes them ([patterns.var-bindings](../09-patterns.md#patterns.var-bindings)), and `var x = x` gives a mutable copy where one is needed.

## Refutability

Let-else and the `Option` fallback are told apart by whether the pattern is refutable ([patterns.else-after-pattern](../09-patterns.md#patterns.else-after-pattern)). Refutability depends on three things only: the pattern's syntax, which names resolve to variants and constants, and how many variants their types have ([patterns.irrefutable-positions](../09-patterns.md#patterns.irrefutable-positions)). It never depends on the exhaustiveness check.

If exhaustiveness decided refutability, `A(x) | B(x)` would be irrefutable only once the check had run. The meaning of an `else` after a pattern would then depend on that algorithm. Bare variant names are read against the type of the expression before `else`, so the two meanings are told apart as soon as that expression is checked, before the pattern is.

The `else` branch of a let-else has type `Never` ([patterns.let-else](../09-patterns.md#patterns.let-else)). Control never continues past a statement whose pattern didn't match, so the pattern's bindings can be in scope after it, as in Rust's `let … else`. `return`, `raise`, `break`, `continue`, `panic` and `exit` all have that type ([declarations.never](../10-declarations.md#declarations.never)).

## Matching

When the pattern of an arm holds or-patterns, its guard is tried with each way the pattern matches ([patterns.guards](../09-patterns.md#patterns.guards)). So `[x, ..] | [_, x, ..] if x > 10` means what it says. The order of the tries is fixed, the leftmost or-pattern varying slowest. A guard may run more than once, and without a fixed order its effects, such as a print, would differ between implementations.

Without an expected type, the first arm whose type isn't `Never` sets the type of the `match` ([patterns.arm-types](../09-patterns.md#patterns.arm-types)). A mistake is then reported in the arm that differs from the ones before it, and an arm that returns or raises never sets the type.

## Exhaustiveness

Exhaustiveness is checked with Maranget's usefulness algorithm ([patterns.algorithm](../09-patterns.md#patterns.algorithm)), which OCaml and Rust use too. Its witness is the missing case that the error message shows, as the messages of Elm do ([patterns.non-exhaustive-matches](../09-patterns.md#patterns.non-exhaustive-matches)).

Arms with guards and arms that hold constants cover nothing ([patterns.guards-and-constants](../09-patterns.md#patterns.guards-and-constants)), because the check never reasons about values. The other choice is to count a guard toward exhaustiveness when it can be proven to cover every case. Proving it needs reasoning about values, which belongs to verification, part of `stilt check` ([Inferred facts and limits](../15-facts.md)). A `_` arm says what the rest is.

A constructor that can't build a value doesn't count ([patterns.types-without-values](../09-patterns.md#patterns.types-without-values)). So a `match` on an `Option<Never>` needs no `Some` arm, and a `match` on a type with no values needs no arm at all ([patterns.empty-matches](../09-patterns.md#patterns.empty-matches)). The declared types with values are the smallest set that their constructors build. A recursive type such as `type Loop = | Loop(Loop)` has none, because each of its values would need one first.

A type that the program doesn't declare has values, as `List<Never>` has `[]` and `fn() -> Never` has a function that panics. Only `Never`, tuples and declared types can make a constructor count for nothing.

A pattern on a part whose type is the error type covers that part, and an arm that holds one is never unreachable ([patterns.unreachable-arms](../09-patterns.md#patterns.unreachable-arms)). A mistake in the declaration of a type then gives no further diagnostic in the matches on it.
