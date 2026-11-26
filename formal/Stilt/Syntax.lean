import Stilt.Syntax.Types

/-!
# Syntax

The syntax of the core calculus: types, effect rows, the built-in operations,
places and expressions. `Stilt.Operators` holds the kinds of operator the
operations name, and `Stilt.Declarations` the calculus's declarations.

The calculus is elaborated. Every binder carries its type, every construct
that needs an expected type carries it, every use of a function with row
variables carries their instantiation, implicit ones included, and every
method call is the call of the method it finds, so the model needs no
inference. The reference interpreter evaluates an elaborated program too.
-/

namespace Stilt

/-- A parameter of a function or a closure: `mode name: T` (declarations.parameters).

A parameter of a declared function whose type is a function type, and which is
neither `inout` nor written `escaping`, is non-escaping: its type stands for
the type written with an implicit row variable of its own added to its row, a
variable that the function's own row holds too (effects.non-escaping-parameters). The
elaborated parameter carries that variable in `implicit`, and its type holds
it. An `escaping` parameter, an `inout` one, a closure literal's, and one whose
type isn't a function type have none, so `implicit = none` on a parameter of
function type with no mode is the mark `escaping`: its type is the one written, whose row
holds no variable but those the signature writes (effects.escaping-parameters). -/
structure Param where
  mode : Mode
  name : Name
  type : Ty
  /-- The implicit row variable of a non-escaping parameter. -/
  implicit : Option Name

/-- The part of a parameter that belongs to the function's type (declarations.function-types). -/
def Param.sig (p : Param) : Mode × Ty := (p.mode, p.type)

/-- The operations on the world. `print(s)`, `eprint(s)`, `io.write(s)` and `io.ewrite(s)`
append `s` to the output, or to standard error when `err`, with a newline when `newline`;
`io.read_line()` and `io.poll_line()` take the next line of the input, as a list of none or
one line; `io.read_all()` takes the rest of it (std.io). `Shared.new(v)` at `Shared<type>`
puts `v` in a new cell of the store and gives its handle (shared.std-sync). -/
inductive WorldOp where
  | write (err newline : Bool)
  | readLine
  | readAll
  | sharedNew (type : Ty)
  deriving DecidableEq

/-- The operations built in to the language. Each evaluates its operands from
left to right (values.left-to-right), then computes its value from theirs. An
operator's types are those of the elaborated program: `a + b` on `i32` is
`arith .add .i32`. `&&` and `||` evaluate their right operand only when the
left one doesn't decide the result, so they are `if`s (values.left-to-right). -/
inductive Op where
  /-- `(e₁, …, eₙ)`, the tuple of its operands (declarations.tuples-and-unit). -/
  | tuple
  /-- `!` on a `bool`, logical not (numbers.bitwise-operators). -/
  | not
  /-- A float literal, `mantissa × 10^exponent` with the exponent's sign, of
  the float type its context expects (numbers.float-literals). -/
  | float (type : FloatTy) (mantissa : Nat) (negative : Bool) (exponent : Nat)
  /-- `-e` on a signed integer (numbers.integer-panics and numbers.unsigned-negation). -/
  | neg (type : IntTy)
  /-- `+`, `-`, `*`, `/` and `%` on an integer type (numbers.integer-panics and
  numbers.division-and-remainder). -/
  | arith (op : Arith) (type : IntTy)
  /-- `+%`, `-%` and `*%` (numbers.wrapping). -/
  | wrapping (op : Wrapping) (type : IntTy)
  /-- `<<` and `>>`, shifting a value of the first type by an amount of the
  second (numbers.shifts and numbers.shift-amounts). -/
  | shift (op : Shift) (type amount : IntTy)
  /-- `&`, `|` and `^` on an integer type (numbers.bitwise-operators). -/
  | bitwise (op : Bitwise) (type : IntTy)
  /-- `!` on an integer type, bit by bit (numbers.bitwise-operators). -/
  | complement (type : IntTy)
  /-- A comparison of two integers of a type (numbers.comparisons). -/
  | compare (op : Cmp) (type : IntTy)
  /-- `.to_T()` from an integer type each of whose values fits in `T`
  (numbers.conversions). -/
  | convert (source target : IntTy)
  /-- `.wrap_to_T()` (numbers.wrapping-conversions). -/
  | wrapTo (source target : IntTy)
  /-- `.to_f32()` and `.to_f64()` on an integer (numbers.conversions). -/
  | toFloat (source : IntTy) (target : FloatTy)
  /-- `.to_f32()` and `.to_f64()` on a float (numbers.conversions). -/
  | floatTo (source target : FloatTy)
  /-- `-e` on a float (numbers.ieee-754). -/
  | fneg (type : FloatTy)
  /-- `+`, `-`, `*` and `/` on a float type (numbers.ieee-754). -/
  | farith (op : Arith) (type : FloatTy)
  /-- A comparison of two floats of a type (numbers.comparisons and numbers.ieee-754). -/
  | fcompare (op : Cmp) (type : FloatTy)
  /-- A native method of a float type (std.floats). -/
  | fmethod (m : FloatMethod) (type : FloatTy)
  /-- `==`, `!=` and the ordering operators on `bool`, through its native `Eq`
  and `Ord`, with `false < true` (traits.operators and traits.built-in-impls). -/
  | bcompare (op : Cmp)
  /-- A string literal's text, its escapes read: the calculus starts after lexing. -/
  | str (text : String)
  /-- An interpolating string literal: its pieces joined, each interpolation
  shown (std.show-output). -/
  | concat
  /-- An integer shown in decimal, with a leading `-` when it is negative
  (numbers.printing-integers). -/
  | showInt (type : IntTy)
  /-- `true` or `false` (std.show-output). -/
  | showBool
  /-- A string padded with copies of a character to a width, by a format
  spec's fill, alignment and width (std.width-fill-and-alignment). -/
  | pad (fill : Char) (align : Align) (width : Nat)
  /-- An integer in base 16, 8 or 2, in uppercase when `upper` says so, by the
  kinds `x`, `X`, `o` and `b` (std.integer-kinds). -/
  | inBase (type : IntTy) (base : Nat) (upper : Bool)
  /-- A method of an integer type (std.integers). -/
  | intMethod (m : IntMethod) (type : IntTy)
  /-- Whether a string parses as an integer of the type (numbers.parsing). -/
  | parses (type : IntTy)
  /-- The integer a string parses as at the type, or 0 when it doesn't
  (numbers.parsing). -/
  | parsed (type : IntTy)
  /-- Whether `s.to_f()` gives `Some`, and the float it gives, at the float type
  (numbers.parsing). -/
  | fparses (type : FloatTy)
  | fparsed (type : FloatTy)
  /-- A float in fixed notation with a precision (std.precision). -/
  | fixed (type : FloatTy) (precision : Nat)
  /-- A float in scientific notation, by the kind `e` (std.scientific-notation). -/
  | scientific (type : FloatTy) (precision : Option Nat)
  /-- `s.len()`, the length in bytes (std.bytes-and-scalars and std.str). -/
  | len
  /-- `s.is_empty()` (std.str). -/
  | isEmpty
  /-- `s.slice(start, end)`, the bytes from `start` up to `end` (std.str). -/
  | slice
  /-- A native of `str` from a string to a string (std.str-splitting and
  std.str-building). -/
  | strMap (f : StrMap)
  /-- `s.replace(from, to)`, or `s.replace_first(from, to)` when `first` says so
  (std.str-building). -/
  | replace (first : Bool)
  /-- `s.char_count()`, the number of scalar values (std.str). -/
  | charCount
  /-- `s.count(sub)` (std.str-search). -/
  | count
  /-- `s.contains(sub)`, `s.starts_with(prefix)` and `s.ends_with(suffix)`
  (std.str-search). -/
  | search (op : Search)
  /-- `==`, `!=` and the ordering operators on `str`, through its native `Eq`
  and `Ord`: by bytes, the same order as by scalar values (traits.operators and
  traits.built-in-impls). -/
  | scompare (op : Cmp)
  /-- `s.is_ascii()` and the tests of a class of bytes (std.str-classes). -/
  | strClass (c : StrClass)
  /-- `s.pad_start(width, fill)`, or `s.pad_end(width, fill)` when not `start`
  (std.str-building). -/
  | padStr (start : Bool)
  /-- A value interpolated into a string, shown as the prelude's structural impls of
  `Show` show it (std.show-output and traits.show). -/
  | showValue
  /-- `==`, `!=` and the ordering operators through the prelude's structural
  impls of `Eq` and `Ord`, with the constructors of each variant type in
  declaration order (traits.operators, traits.structural-impls and
  traits.structural-calls). -/
  | structural (op : Cmp) (orders : List (Name × List Name))
  /-- Whether two handles name one cell, which the export tests where a `when` names several
  handles of one type, to hold one value for the names whose handles are equal
  (shared.names-that-may-be-one-place). No program writes it as `==`: `Shared<T>` implements
  no trait (shared.std-sync). -/
  | sameCell
  /-- The elements of a list, the second operand, sorted stably by their keys, the
  first: in ascending order of `Ord.compare` on the keys, or in descending order,
  through the prelude's structural impls of `Ord`, which is how `sorted_by(key)`
  and `sorted_desc_by(key)` order a list once `key` has given each element's key
  (std.lists). -/
  | sortedByKey (descending : Bool) (orders : List (Name × List Name))
  /-- `panic(msg)` and `unreachable()`: a panic of the kind, which the message
  doesn't change (effects.panic-kinds and program.prelude-functions). -/
  | panic (kind : PanicKind)
  /-- A function of lists (std.lists). -/
  | list (op : ListOp)
  /-- A function of maps (std.maps). -/
  | map (op : MapOp)
  /-- A function of sets (std.sets). -/
  | set (op : SetOp)
  /-- A view of its first operand: of the whole with no other operand,
  `View.all(source)`, and of the part from the second operand up to the third,
  `View.of(source, start, end)` and, of a view, `v.view(start, end)`
  (views.making-view). `Expr.view` applies it. -/
  | view
  /-- `v.copy()`, the part a view reads, as an owned value
  (views.functions-of-views). -/
  | copy
  /-- An operation on the world (std.io and shared.std-sync). -/
  | world (op : WorldOp)
  deriving DecidableEq

/-- The name of a tuple's field at a position, which `.0`, `.1`, … read
(types.field-access). -/
def tupleField (i : Nat) : Name := toString i

/-- Pairs each element of a list with the name of its position, counting
from `i`. -/
def positionsFrom {α : Type} : Nat → List α → List (Name × α)
  | _, [] => []
  | i, x :: xs => (tupleField i, x) :: positionsFrom (i + 1) xs

/-- Pairs each element of a tuple with the name of its position: a tuple is a
record whose fields are named `0`, `1`, … (types.field-access). -/
def positions {α : Type} (xs : List α) : List (Name × α) := positionsFrom 0 xs

/-- What a list pattern says of the elements after those it lists: that there
are none, `[p₁, …, pₙ]`; that there may be any, `[p₁, …, pₙ, ..]`; or that
there may be any, bound as a list to a name, `[p₁, …, pₙ, ..rest]`
(patterns.pattern-forms). -/
inductive ListRest where
  | exact
  | any
  | bind (name : Name)
  deriving DecidableEq, Repr

/-- The name a list pattern's rest binds, if it binds one. -/
def ListRest.binders : ListRest → List Name
  | .bind r => [r]
  | _ => []

/-- A pattern (patterns.pattern-forms), in elaborated form: a variant pattern
names its variant type, and a record pattern its record and the fields it
matches, a bare field `g` written `g: g`, as if it ended in `..`, since one that
doesn't names every field (patterns.pattern-types). Constants, and the guards
that a pattern's ways of matching meet, have a calculus of their own
(`Stilt.Guards`); patterns over other modules' names are outside the calculus. -/
inductive Pattern where
  /-- `_`, which matches anything and binds nothing. -/
  | wild
  /-- A name, which matches anything and binds it. -/
  | bind (name : Name)
  /-- An integer literal, optionally negative (numbers.negative-literals). -/
  | int (value : Int)
  | bool (value : Bool)
  /-- A string literal with no interpolation. -/
  | str (value : String)
  /-- `()`. -/
  | unit
  /-- `(p₁, …, pₙ)`, which matches a tuple element by element. -/
  | tuple (elems : List Pattern)
  /-- `R { f: p, …, .. }`, which matches the listed fields of a record of type `R`. -/
  | record (type : Name) (fields : List (Name × Pattern))
  /-- `C(p₁, …, pₙ)`, a variant of the variant type `type`, its payload
  matched by position. -/
  | variant (type : Name) (ctor : Name) (payload : List Pattern)
  /-- `p | q`, either alternative (patterns.or-patterns). -/
  | or (first second : Pattern)
  /-- `[p₁, …, pₙ]` and the forms with a rest, which match a list element by
  element from its first, a list with no more elements than listed, or as many
  more as the rest allows (patterns.pattern-forms). -/
  | list (elems : List Pattern) (rest : ListRest)

mutual

/-- The names a pattern binds, in the order they are written; an or-pattern's
are its first alternative's, which every alternative binds
(patterns.or-patterns). -/
def Pattern.binders : Pattern → List Name
  | .wild | .int _ | .bool _ | .str _ | .unit => []
  | .bind x => [x]
  | .tuple ps => patternsBinders ps
  | .record _ fields => fieldPatternsBinders fields
  | .variant _ _ ps => patternsBinders ps
  | .or p _ => p.binders
  | .list ps r => patternsBinders ps ++ r.binders

/-- The names a list of patterns binds, in order. -/
def patternsBinders : List Pattern → List Name
  | [] => []
  | p :: ps => p.binders ++ patternsBinders ps

/-- The names the field patterns of a record pattern bind, in order. -/
def fieldPatternsBinders : List (Name × Pattern) → List Name
  | [] => []
  | (_, p) :: fields => p.binders ++ fieldPatternsBinders fields

end

mutual

/-- Expressions, in elaborated form. Statements are expressions:
`letIn`, `varIn` and `seq` hold the rest of their block, and an assignment has
type `()`. -/
inductive Expr where
  /-- Reads a variable. -/
  | var (name : Name)
  /-- Reads a variable at its last use, which may hand its storage over to the
  binding or the parameter that receives the value (values.passing-values). The
  compiler infers it; `Stilt.Moves.Analysis` marks it. -/
  | move (name : Name)
  | int (value : Int)
  | bool (value : Bool)
  | unit
  /-- `R { f: e, … }`, with the fields in the order they are written (expressions.struct-literal-fields),
  and the type arguments that inference gives the record type, which the literal doesn't
  write (declarations.type-arguments). -/
  | record (type : Name) (args : List Ty) (fields : List (Name × Expr))
  /-- `C(e, …)`, a variant of the variant type `type`, at the type arguments that inference
  gives it (declarations.variant-types and declarations.type-arguments). -/
  | variant (type : Name) (args : List Ty) (ctor : Name) (payload : List Expr)
  /-- `[e, …]`, with its element type. -/
  | list (elem : Ty) (elems : List Expr)
  /-- A built-in operation applied to its operands, as `(e₁, …, eₙ)`. -/
  | op (op : Op) (operands : List Expr)
  /-- `View.all(source)`, `View.of(source, start, end)` and `v.view(start, end)`:
  `Op.view` applied to its operands, the source first. Its source is the place
  the first operand names when it names one, the sources of a view, and a
  temporary otherwise (views.making-view). -/
  | view (operands : List Expr)
  /-- `e.f`, and `e.0` on a tuple (types.field-access). -/
  | field (base : Expr) (name : Name)
  /-- `e[i]`. -/
  | index (base : Expr) (index : Expr)
  /-- A function declared at the top level, used as a value, with its type
  parameters and its row variables instantiated in order, afresh at each use
  (types.no-type-arguments and effects.inference). -/
  | fnRef (name : Name) (types : List Ty) (rows : List Row)
  /-- `Trait.m`, the method `m` of a trait at a type, as a function value whose
  first parameter is the receiver; a method call through a bound calls it
  (traits.method-resolution and traits.qualified-calls). -/
  | method (trait : Name) (name : Name) (type : Ty)
  /-- `|p, …| body`, with its whole type written out (expressions.closure-parameter-types). -/
  | closure (params : List Param) (result : Ty) (row : Row) (body : Expr)
  /-- `f(a, …)`, where `f` is any expression of function type, with the type of its result
  (expressions.arguments, expressions.inout-arguments and expressions.consumed-arguments). -/
  | call (callee : Expr) (args : List Arg) (result : Ty)
  /-- `let x: T = e`, followed by the rest of its block (values.let-and-var). -/
  | letIn (name : Name) (type : Ty) (init : Expr) (body : Expr)
  /-- `var x: T = e`, followed by the rest of its block (values.let-and-var). -/
  | varIn (name : Name) (type : Ty) (init : Expr) (body : Expr)
  /-- `place = e` (expressions.assignment). -/
  | assign (target : Place) (value : Expr)
  /-- A statement followed by the rest of its block (expressions.statements). Its value is
  the rest's, so a block has the value of its last statement, and a block whose last
  statement is no expression statement has `()` as its rest (expressions.block-value). -/
  | seq (first : Expr) (rest : Expr)
  /-- `if c { a } else { b }`, with the type of its branches (expressions.if). An `if` without `else` is one whose `else` branch is `()`. -/
  | «if» (cond : Expr) (type : Ty) (thenBranch : Expr) (elseBranch : Expr)
  /-- `match e { p => body, … }`, with the type of its arms (expressions.match
  and patterns.match). `if let p = e { a } else { b }` is
  `match e { p => a, _ => b }` (expressions.if-let). -/
  | «match» (scrutinee : Expr) (type : Ty) (arms : List Arm)
  /-- `for x in e { body }` over a list of `elem` (expressions.for-iterables). -/
  | «for» (name : Name) (elem : Ty) (iterable : Expr) (body : Expr)
  /-- `raise e` (effects.raise). -/
  | raise (error : Expr)
  /-- `try e`, which marks the raising calls in `e` (effects.marking). -/
  | «try» (body : Expr)
  /-- `try e catch x => handler`, where `e` raises errors of type `error`,
  with the common type of `e` and the handler (effects.catch). -/
  | tryCatch (body : Expr) (error : Ty) (name : Name) (handler : Expr)
      (type : Ty)
  /-- `while c { body }`, whose head is outside its body (expressions.loops and
  expressions.break-and-continue). -/
  | «while» (cond : Expr) (body : Expr)
  /-- `loop { body }`, of type `()` when a `break` exits it and `Never` otherwise
  (expressions.loops and expressions.loop-types). -/
  | «loop» (body : Expr)
  /-- `break`, which ends the innermost loop whose body holds it
  (expressions.break-and-continue). -/
  | «break»
  /-- `continue`, which goes on with the next turn of that loop
  (expressions.break-and-continue). -/
  | «continue»
  /-- `return e`, which ends the function or closure whose body holds it with
  `e`'s value (expressions.closure-boundaries). `return` without an operand is
  `return ()`. -/
  | «return» (value : Expr)
  /-- `E.op(e)`, a performance of the operation `op` on the value of its
  argument (handlers.performing-operation), or `resume(e)` in the body of an
  operation of a handler that takes control, a performance of
  `Operation.resume` (handlers.resuming). An operation's arguments are one
  value: `()` for none, a tuple for several. -/
  | perform (op : Operation) (arg : Expr)
  /-- `with h { block }`, the block run with the handler `h` installed for the
  effect `effect` (handlers.with). A handler is a record of closures, one for
  each operation of its effect, under the operation's name
  (handlers.handler-literals); `control` says whether it was written
  `handler E -> R { … }`, which takes control (handlers.resuming). -/
  | withH (effect : Name) (control : Bool) (handler : Expr) (block : Expr)
  /-- `when a, b { block }`: each name with the type of the value its handle reaches, the
  expressions of the handles, and the block, in which each name is a `var` of its value
  (shared.when). -/
  | held (names : List (Name × Ty)) (handles : List Expr) (body : Expr)

/-- An argument. An `inout` argument is marked at the call and is a place
(expressions.inout-arguments); any other argument is not marked (expressions.consumed-arguments). -/
inductive Arg where
  | value (expr : Expr)
  | inout (place : Place)

/-- A place: a variable followed by zero or more projections (modes.places). -/
structure Place where
  root : Name
  path : List Projection

/-- A projection of a place: `.f`, `.0` or `[i]` (modes.places). A tuple
field is the field named by its position. -/
inductive Projection where
  | field (name : Name)
  | index (index : Expr)

/-- A `match` arm `p => body` (patterns.match). Elaborated, it carries the
names its pattern binds, in order, as every binder carries its type; typing
checks that they are `pattern.binders`. Guards have a calculus of their own
(`Stilt.Guards`). -/
structure Arm where
  pattern : Pattern
  binders : List Name
  body : Expr

end

end Stilt
