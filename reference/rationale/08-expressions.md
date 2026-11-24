# 8. Expressions: rationale

A recursive-descent parser meets four ambiguities in Stilt's expressions:

- in `if x == Leaf {`, `Leaf {` could be a struct literal or the start of the block;
- `|` can open a closure, be the bitwise or, or separate the alternatives of a pattern;
- `<` can mean less-than or open a list of type arguments;
- `else` can belong to an `if` or be the `Option` fallback.

A stated rule resolves each one. With the precedence table and the rule on struct literals, the grammar is LR(1), which Menhir checks mechanically.

## Statements and blocks

A block's value is the value of its last expression statement ([expressions.block-value](../08-expressions.md#expressions.block-value)), so a function's result needs no `return`. Any other expression statement must have type `()` or `Never` ([expressions.unused-values](../08-expressions.md#expressions.unused-values)). The alternative is to discard unused values silently, as Go does, and as Rust does for a type without `#[must_use]`. Then a method that returns a new value, such as `sorted`, does nothing when it is called for its effect. `let _ = e` says that a value is discarded on purpose.

## Operators and precedence

The bitwise operators bind more tightly than the comparisons, unlike in C, so `x & 1 == 0` tests whether `x` is even. The shifts bind more loosely than `+`, unlike in Go ([expressions.precedence](../08-expressions.md#expressions.precedence)). Comparisons don't chain, so the intent of `a < b < c` is spelled out as `a < b && b < c`.

`try`, `raise`, `return` and closure bodies take everything to their right ([expressions.open-ended-forms](../08-expressions.md#expressions.open-ended-forms)), and the operand of `try` stops before `catch`. So `let x = try a() catch _ because "…" => 0` parses as written. The operand of `try` is `a()`, and the body of the `catch` arm runs to the end of the statement. The arm is outside the operand, so a raising call inside it needs its own `try`.

Ranges are not values ([expressions.ranges](../08-expressions.md#expressions.ranges)). A first-class range would be an iterator, and an iterator holds stored references, which only views give ([views.making-iterator](../13-modes.md#views.making-iterator)). As the iterable of a `for`, a range needs no value at all.

## How an operation is checked

Two implementations that both follow the meaning of the operators could still report different codes, at different places, for one ordinary mistake, as `"total: " + n` or `x * 2.0`. The rules on checking an operation fix the order ([expressions.left-operand-first](../08-expressions.md#expressions.left-operand-first), [expressions.right-operand](../08-expressions.md#expressions.right-operand)). The left operand comes first, then the right one against what the operator requires of it. So an operator that the left operand's type doesn't have is reported once, with the fix that applies whatever the right operand is. A mismatch is reported at the operand that differs.

Interpolation builds strings ([expressions.no-string-plus](../08-expressions.md#expressions.no-string-plus)). The alternative, `+` on strings as in Java, Python and Rust, would be a second way to write the same string. So the error for it carries the interpolation as its fix.

## Struct literals and heads

`Name {` begins a struct literal only after an uppercase name, `Self` or a path that ends in one ([expressions.struct-literals](../08-expressions.md#expressions.struct-literals)). A head ends at the first `{` outside parentheses and brackets ([expressions.heads](../08-expressions.md#expressions.heads)). So `if x == None {` and `while n < MAX {` mean what they say, and a literal in a head is written in parentheses, as Rust also requires.

Every field of a struct literal is given once ([expressions.struct-literal-fields](../08-expressions.md#expressions.struct-literal-fields)). The form that copies the others from a base is update syntax ([records.update](../07-types.md#records.update)).

## Closures

A closure captures by copy, when it is created ([expressions.capture](../08-expressions.md#expressions.capture)), as every value in core is copied. It can't modify what it captures, so a closure never causes an exclusivity violation ([modes.closures](../13-modes.md#modes.closures)). It can't call itself ([expressions.closure-boundaries](../08-expressions.md#expressions.closure-boundaries)): a recursive function is declared with `fn`, whose signature is written.

A closure may take `inout` parameters ([expressions.inout-closure-parameters](../08-expressions.md#expressions.inout-closure-parameters)). The alternative is to let only named functions take them, which fits poorly with function types that have them. A table of closures that each update one state, as a generator's weighted choices are, would need a named function for each, numbered by hand.

## Key paths

A key path ([expressions.key-paths](../08-expressions.md#expressions.key-paths)) writes the most common closure, one that reads a field or calls a method of its argument, in one token: `items.map(.price)`. Swift has the same form as `\.price`. A key path stands only where a function type is expected, which gives its argument a type.

## Calls

Arguments are positional ([expressions.arguments](../08-expressions.md#expressions.arguments)). The alternative of variadic functions, as in C and Go, adds grammar and errors and passes nothing new. A list literal already passes any number of values of one type, as in `max([a, b, c])`, and arities that differ in type are the work of variadic generics ([variadics.packs](../07-types.md#variadics.packs)).

An `inout` argument is marked at the call ([expressions.inout-arguments](../08-expressions.md#expressions.inout-arguments)), so a reader sees where a caller's variable may change. Whether a callee consumes an argument or only reads it is a fact that is inferred ([facts.copy](../15-facts.md#facts.copy)), so nothing marks it ([expressions.consumed-arguments](../08-expressions.md#expressions.consumed-arguments)).

## The `else` fallback

`e₁ else e₂` unwraps an `Option` with a word ([expressions.option-fallback](../08-expressions.md#expressions.option-fallback)). Because `return`, `raise`, `break` and `continue` have type `Never`, it also leaves early. The alternative is the `?` operator of Rust, which returns `None` or an error from the function. In Stilt `?` is the hole, and `else return None` says it in words, at the place where the function leaves. A `Result` is converted with `.ok()` first, because `try` acts on the `raise` effect and never unwraps a `Result`.

## Control flow

`if let` ([expressions.if-let](../08-expressions.md#expressions.if-let)) matches one pattern. The alternative is a two-arm `match` with a wildcard, which writes an arm that does nothing, `match x { P => a, _ => {} }`, and programs need that shape often. There is no `while let` and no `&&` joined to a `let`, as Rust has. A loop writes `let P = e else break` inside `loop`, which says where the loop ends.

`break` and `continue` take no labels and no values ([expressions.break-and-continue](../08-expressions.md#expressions.break-and-continue)). A `loop` that only `return` leaves has type `Never` ([expressions.loop-types](../08-expressions.md#expressions.loop-types)), so it can end a function of any result type.

## Assignment and places

Assignment is a statement ([expressions.assignment](../08-expressions.md#expressions.assignment)). The alternative, assignment as an expression as in C, invites `if x = y` bugs and complicates the order of evaluation.

## Conditions

Every condition has type `bool` ([expressions.conditions](../08-expressions.md#expressions.conditions)). No other type stands in for one, as an integer does in C or any value does in Python. So `if count {` is an error, and `if count > 0 {` says what it means.

## Scope

A binding may hide another, an item included ([expressions.shadowing](../08-expressions.md#expressions.shadowing)). This is how a value changes mutability, as in `var n = n`, and how a parsed value replaces its text, as in `let qty = qty.to_i64() else 0`. A module's name is the exception, because `m.f` would otherwise be ambiguous.
