import Stilt.Numbers
import Stilt.Declarations
import Stilt.Typing.Else
import Stilt.Typing.Tasks
import Stilt.Projections
import Stilt.Writable
import Lean.Data.Json

/-!
# Programs read from JSON

The calculus's syntax as data, so that a program the reference interpreter
exports runs in the model (`Stilt.Run.Main`). Each constructor is an array whose
first element names it and whose next elements are its fields in order, as
`["arith", "add", "i64"]` is `Op.arith .add .i64`; a constructor without fields
is its name alone, as `"bool"` is `Ty.bool`; an optional field is `null` or its
value, and a pair is an array of two.
-/

namespace Stilt.Run

open Lean (Json)

/-- A decoder: from JSON, a value or why there is none. -/
abbrev Decoder (α : Type) := Json → Except String α

/-- The constructor an array or a string names, with its fields. -/
def tagged (j : Json) : Except String (String × Array Json) :=
  match j with
  | .str s => pure (s, #[])
  | .arr a =>
    match a[0]? with
    | some (Json.str s) => pure (s, a.extract 1 a.size)
    | _ => throw s!"a constructor's name is a string: {j.compress}"
  | _ => throw s!"a constructor is a string or an array: {j.compress}"

def field (fs : Array Json) (i : Nat) : Except String Json :=
  match fs[i]? with
  | some f => pure f
  | none => throw s!"a constructor lacks its field {i}"

def str : Decoder String
  | .str s => pure s
  | j => throw s!"a string, not {j.compress}"

def nat : Decoder Nat
  | .num n => match n.mantissa.toNat, n.exponent with
    | m, 0 => if n.mantissa ≥ 0 then pure m else throw "a natural number"
    | _, _ => throw "a natural number"
  | j => throw s!"a natural number, not {j.compress}"

/-- An integer, written as a JSON string so that no width limits it. -/
def int : Decoder Int
  | .str s => match s.toInt? with
    | some n => pure n
    | none => throw s!"an integer, not {s}"
  | j => throw s!"an integer, written as a string, not {j.compress}"

def bool : Decoder Bool
  | .bool b => pure b
  | j => throw s!"a Boolean, not {j.compress}"

def list {α : Type} (d : Decoder α) : Decoder (List α)
  | .arr a => a.toList.mapM d
  | j => throw s!"an array, not {j.compress}"

def option {α : Type} (d : Decoder α) : Decoder (Option α)
  | .null => pure none
  | j => some <$> d j

def pair {α β : Type} (a : Decoder α) (b : Decoder β) : Decoder (α × β)
  | .arr #[x, y] => return (← a x, ← b y)
  | j => throw s!"a pair, not {j.compress}"

/-- A constructor without fields, by name. -/
def enum {α : Type} (what : String) (cases : List (String × α)) : Decoder α
  | .str s => match cases.lookup s with
    | some x => pure x
    | none => throw s!"no {what} is named {s}"
  | j => throw s!"a {what}, not {j.compress}"

def intTy : Decoder IntTy :=
  enum "integer type" [("i8", .i8), ("i16", .i16), ("i32", .i32), ("i64", .i64),
    ("u8", .u8), ("u16", .u16), ("u32", .u32), ("u64", .u64)]

def floatTy : Decoder FloatTy := enum "float type" [("f32", .f32), ("f64", .f64)]

def mode : Decoder Mode := enum "mode" [("let", .let), ("inout", .inout)]

def arith : Decoder Arith :=
  enum "operator" [("add", .add), ("sub", .sub), ("mul", .mul), ("div", .div), ("rem", .rem)]

def wrapping : Decoder Wrapping :=
  enum "operator" [("add", .add), ("sub", .sub), ("mul", .mul)]

def shift : Decoder Shift := enum "shift" [("left", .left), ("right", .right)]

def bitwise : Decoder Bitwise := enum "operator" [("and", .and), ("or", .or), ("xor", .xor)]

def cmp : Decoder Cmp :=
  enum "comparison" [("eq", .eq), ("ne", .ne), ("lt", .lt), ("le", .le), ("gt", .gt), ("ge", .ge)]

def search : Decoder Search :=
  enum "search" [("contains", .contains), ("startsWith", .startsWith), ("endsWith", .endsWith)]

def strClass : Decoder StrClass :=
  enum "string class" [("is_ascii", .ascii), ("is_ascii_digit", .digit),
    ("is_ascii_alpha", .alpha), ("is_ascii_alphanumeric", .alnum),
    ("is_ascii_whitespace", .whitespace), ("is_ascii_upper", .upper),
    ("is_ascii_lower", .lower)]

def listOp (j : Json) : Except String ListOp := do
  match ← tagged j with
  | ("len", _) => pure .len
  | ("isEmpty", _) => pure .isEmpty
  | ("push", _) => pure .push
  | ("join", _) => pure .join
  | ("slice", _) => pure .slice
  | ("insert", _) => pure .insert
  | ("removeAt", _) => pure .removeAt
  | ("chars", _) => pure .chars
  | ("bytes", _) => pure .bytes
  | ("codePoints", _) => pure .codePoints
  | ("nextLine", _) => pure .nextLine
  | ("find", _) => pure (.find false)
  | ("fromUtf8", _) => pure (.fromUtf8 false)
  | ("fromUtf8Lossy", _) => pure (.fromUtf8 true)
  | ("fromCodePoint", _) => pure .fromCodePoint
  | ("checked", fs) => do
    let o ← match ← field fs 0 >>= str with
      | "add" => pure Checked.add | "sub" => pure .sub | "mul" => pure .mul
      | o => throw s!"a checked operation, not {o}"
    let k ← field fs 1 >>= intTy
    return .checked o k.min k.max
  | ("narrow", fs) => do
    let k ← field fs 0 >>= intTy
    return .narrow k.min k.max
  | ("truncate", fs) => do
    let k ← field fs 0 >>= intTy
    return .truncate k.min k.max
  | ("rfind", _) => pure (.find true)
  | ("split", _) => pure .split
  | ("lines", _) => pure .lines
  | ("splitWhitespace", _) => pure .splitWhitespace
  | ("range", fs) => ListOp.range <$> (field fs 0 >>= bool)
  | (t, _) => throw s!"no list function is named {t}"

def mapOp : Decoder MapOp :=
  enum "map function" [("new", .new), ("withDefault", .withDefault), ("len", .len),
    ("isEmpty", .isEmpty), ("contains", .contains), ("index", .index), ("getOr", .getOr),
    ("insert", .insert), ("remove", .remove), ("keys", .keys), ("values", .values),
    ("entries", .entries), ("equal", .equal)]

def setOp (j : Json) : Except String SetOp := do
  let (tag, fs) ← tagged j
  match tag with
  | "combine" => SetOp.combine <$> (field fs 0 >>= enum "set combination"
      [("union", .union), ("intersection", .intersection), ("difference", .difference),
        ("symmetricDifference", .symmetricDifference)])
  | "relate" => SetOp.relate <$> (field fs 0 >>= enum "set relation"
      [("subset", .subset), ("superset", .superset), ("disjoint", .disjoint), ("equal", .equal)])
  | _ => enum "set function" [("new", .new), ("fromList", .fromList), ("len", .len),
      ("isEmpty", .isEmpty), ("contains", .contains), ("insert", .insert),
      ("remove", .remove), ("toList", .toList)] (.str tag)

mutual

/-- A declared type's arguments, its second field, which a type without them leaves out. -/
partial def typeArgs (fs : Array Json) : Except String (List Ty) :=
  match fs[1]? with
  | some a => list ty a
  | none => pure []

partial def ty (j : Json) : Except String Ty := do
  let (tag, fs) ← tagged j
  let f := field fs
  match tag with
  | "int" => .int <$> (f 0 >>= intTy)
  | "float" => .float <$> (f 0 >>= floatTy)
  | "bool" => pure .bool
  | "str" => pure .str
  | "unit" => pure .unit
  | "never" => pure .never
  | "record" => return .record (← f 0 >>= str) (← typeArgs fs)
  | "variant" => return .variant (← f 0 >>= str) (← typeArgs fs)
  | "list" => .list <$> (f 0 >>= ty)
  | "tuple" => .tuple <$> (f 0 >>= list ty)
  | "map" => return .map (← f 0 >>= ty) (← f 1 >>= ty)
  | "set" => .set <$> (f 0 >>= ty)
  | "view" => .view <$> (f 0 >>= ty)
  | "shared" => .shared <$> (f 0 >>= ty)
  | "param" => .param <$> (f 0 >>= str)
  | "fn" => return .fn (← f 0 >>= list (pair mode ty)) (← f 1 >>= ty) (← f 2 >>= row)
  | _ => throw s!"no type is named {tag}"

/-- A row: `[io, raise, vars, effects, resume]`, the last two optional. -/
partial def row : Decoder Row
  | .arr #[io, raise, vars] => return ⟨← bool io, ← option ty raise, ← list str vars, [], none⟩
  | .arr #[io, raise, vars, effects, resume] =>
    return ⟨← bool io, ← option ty raise, ← list str vars, ← list str effects,
      ← option (pair ty ty) resume⟩
  | j => throw s!"a row, not {j.compress}"

end

/-- An operation on the world: `["write", err, newline]`, `"readLine"`, `"readAll"` or
`["sharedNew", type]`. -/
def worldOp (fs : Array Json) : Except String WorldOp := do
  match ← field fs 0 >>= str with
  | "write" => return .write (← field fs 1 >>= bool) (← field fs 2 >>= bool)
  | "readLine" => pure .readLine
  | "readAll" => pure .readAll
  | "sharedNew" => .sharedNew <$> (field fs 1 >>= ty)
  | k => throw s!"an operation on the world, not {k}"

def op (j : Json) : Except String Op := do
  let (tag, fs) ← tagged j
  let f := field fs
  match tag with
  | "world" => .world <$> worldOp fs
  | "tuple" => pure .tuple
  | "not" => pure .not
  | "float" => do
    let m ← f 1 >>= int
    let e ← f 2 >>= int
    return .float (← f 0 >>= floatTy) m.toNat (e < 0) e.natAbs
  | "neg" => .neg <$> (f 0 >>= intTy)
  | "arith" => return .arith (← f 0 >>= arith) (← f 1 >>= intTy)
  | "wrapping" => return .wrapping (← f 0 >>= wrapping) (← f 1 >>= intTy)
  | "shift" => return .shift (← f 0 >>= shift) (← f 1 >>= intTy) (← f 2 >>= intTy)
  | "bitwise" => return .bitwise (← f 0 >>= bitwise) (← f 1 >>= intTy)
  | "complement" => .complement <$> (f 0 >>= intTy)
  | "compare" => return .compare (← f 0 >>= cmp) (← f 1 >>= intTy)
  | "convert" => return .convert (← f 0 >>= intTy) (← f 1 >>= intTy)
  | "wrapTo" => return .wrapTo (← f 0 >>= intTy) (← f 1 >>= intTy)
  | "toFloat" => return .toFloat (← f 0 >>= intTy) (← f 1 >>= floatTy)
  | "floatTo" => return .floatTo (← f 0 >>= floatTy) (← f 1 >>= floatTy)
  | "fneg" => .fneg <$> (f 0 >>= floatTy)
  | "farith" => return .farith (← f 0 >>= arith) (← f 1 >>= floatTy)
  | "fcompare" => return .fcompare (← f 0 >>= cmp) (← f 1 >>= floatTy)
  | "fmethod" => return .fmethod (← f 0 >>= enum "float method" [("sqrt", .sqrt), ("floor", .floor),
      ("ceil", .ceil), ("trunc", .trunc), ("abs", .abs), ("round", .round), ("min", .min), ("max", .max),
      ("is_nan", .isNan)]) (← f 1 >>= floatTy)
  | "bcompare" => .bcompare <$> (f 0 >>= cmp)
  | "str" => .str <$> (f 0 >>= str)
  | "concat" => pure .concat
  | "showInt" => .showInt <$> (f 0 >>= intTy)
  | "pad" => do
    let fill ← f 0 >>= str
    let some c := fill.toList.head? | throw "a pad without a fill"
    let a ← f 1 >>= str
    let align ← match a with
      | "<" => pure Align.left | "^" => pure .center | ">" => pure .right
      | _ => throw s!"an alignment, not {a}"
    return .pad c align (← f 2 >>= int).toNat
  | "inBase" => return .inBase (← f 0 >>= intTy) (← f 1 >>= int).toNat (← f 2 >>= bool)
  | "intMethod" => do
    let m ← f 0 >>= str
    let method ← match m with
      | "abs" => pure IntMethod.abs | "min" => pure .min | "max" => pure .max
      | "saturating_add" => pure .saturatingAdd | "saturating_sub" => pure .saturatingSub
      | "pow" => pure .pow | "div_euclid" => pure .divEuclid | "rem_euclid" => pure .remEuclid
      | "gcd" => pure .gcd | "lcm" => pure .lcm | "count_ones" => pure .countOnes
      | "leading_zeros" => pure .leadingZeros | "trailing_zeros" => pure .trailingZeros
      | _ => throw s!"an integer method, not {m}"
    return .intMethod method (← f 1 >>= intTy)
  | "parses" => .parses <$> (f 0 >>= intTy)
  | "parsed" => .parsed <$> (f 0 >>= intTy)
  | "fparses" => .fparses <$> (f 0 >>= floatTy)
  | "fparsed" => .fparsed <$> (f 0 >>= floatTy)
  | "fixed" => return .fixed (← f 0 >>= floatTy) (← f 1 >>= int).toNat
  | "scientific" => do
    let p ← f 1 >>= int
    return .scientific (← f 0 >>= floatTy) (if p < 0 then none else some p.toNat)
  | "showBool" => pure .showBool
  | "showValue" => pure .showValue
  | "sameCell" => pure .sameCell
  | "panic" => do
    match ← f 0 >>= str with
    | "explicit" => pure (.panic .explicit)
    | "unreachable" => pure (.panic .unreachable)
    | "unwrap" => pure (.panic .unwrap)
    | "assert" => pure (.panic .assert)
    | "deadlock" => pure (.panic .deadlock)
    | "checkError" => pure (.panic .checkError)
    | "hole" => pure (.panic .hole)
    | "bounds" => pure (.panic .bounds)
    | k => throw s!"a panic of a kind the export doesn't give, {k}"
  | "structural" =>
    return .structural (← f 0 >>= cmp) (← f 1 >>= list (pair str (list str)))
  | "sortedByKey" =>
    return .sortedByKey (← f 0 >>= bool) (← f 1 >>= list (pair str (list str)))
  | "len" => pure .len
  | "isEmpty" => pure .isEmpty
  | "slice" => pure .slice
  | "search" => .search <$> (f 0 >>= search)
  | "strClass" => .strClass <$> (f 0 >>= strClass)
  | "padStr" => .padStr <$> (f 0 >>= bool)
  | "strMap" => do
    let name ← f 0 >>= str
    let m ← match name with
      | "trim" => pure StrMap.trim | "trim_start" => pure .trimStart
      | "trim_end" => pure .trimEnd | "ascii_upper" => pure .asciiUpper
      | "ascii_lower" => pure .asciiLower | "reversed" => pure .reversed
      | "after_line" => pure .afterLine
      | _ => throw s!"a function of strings, not {name}"
    return .strMap m
  | "replace" => .replace <$> (f 0 >>= bool)
  | "charCount" => pure .charCount
  | "count" => pure .count
  | "scompare" => .scompare <$> (f 0 >>= cmp)
  | "list" => .list <$> (f 0 >>= listOp)
  | "map" => .map <$> (f 0 >>= mapOp)
  | "set" => .set <$> (f 0 >>= setOp)
  | "copy" => pure .copy
  | _ => throw s!"no operation is named {tag}"


/-- A parameter: `[mode, name, type, implicit]`. -/
def param : Decoder Param
  | .arr #[m, n, t, i] => return ⟨← mode m, ← str n, ← ty t, ← option str i⟩
  | j => throw s!"a parameter, not {j.compress}"

/-- A list pattern's rest: `"exact"`, `"any"`, or `["bind", name]`. -/
def listRest (j : Json) : Except String ListRest := do
  let (tag, fs) ← tagged j
  match tag with
  | "exact" => pure .exact
  | "any" => pure .any
  | "bind" => .bind <$> (field fs 0 >>= str)
  | _ => throw s!"no rest of a list pattern is named {tag}"

partial def pattern (j : Json) : Except String Pattern := do
  let (tag, fs) ← tagged j
  let f := field fs
  match tag with
  | "wild" => pure .wild
  | "bind" => .bind <$> (f 0 >>= str)
  | "int" => .int <$> (f 0 >>= int)
  | "bool" => .bool <$> (f 0 >>= bool)
  | "str" => .str <$> (f 0 >>= str)
  | "unit" => pure .unit
  | "tuple" => .tuple <$> (f 0 >>= list pattern)
  | "record" => return .record (← f 0 >>= str) (← f 1 >>= list (pair str pattern))
  | "variant" => return .variant (← f 0 >>= str) (← f 1 >>= str) (← f 2 >>= list pattern)
  | "or" => return .or (← f 0 >>= pattern) (← f 1 >>= pattern)
  | "list" => return .list (← f 0 >>= list pattern) (← f 1 >>= listRest)
  | "const" => return .const (← f 0 >>= str) (← f 1 >>= pattern)
  | _ => throw s!"no pattern is named {tag}"

mutual

partial def expr (j : Json) : Except String Expr := do
  let (tag, fs) ← tagged j
  let f := field fs
  match tag with
  | "var" => .var <$> (f 0 >>= str)
  | "move" => .move <$> (f 0 >>= str)
  | "int" => .int <$> (f 0 >>= int)
  | "bool" => .bool <$> (f 0 >>= bool)
  | "unit" => pure .unit
  | "record" =>
    if fs.size < 3 then return .record (← f 0 >>= str) [] (← f 1 >>= list (pair str expr))
    else return .record (← f 0 >>= str) (← f 1 >>= list ty) (← f 2 >>= list (pair str expr))
  | "variant" =>
    if fs.size < 4 then return .variant (← f 0 >>= str) [] (← f 1 >>= str) (← f 2 >>= list expr)
    else
      return .variant (← f 0 >>= str) (← f 1 >>= list ty) (← f 2 >>= str) (← f 3 >>= list expr)
  | "list" => return .list (← f 0 >>= ty) (← f 1 >>= list expr)
  | "op" => return .op (← f 0 >>= op) (← f 1 >>= list expr)
  | "view" => return .view (← f 0 >>= list expr)
  | "field" => return .field (← f 0 >>= expr) (← f 1 >>= str)
  | "index" => return .index (← f 0 >>= expr) (← f 1 >>= expr)
  | "fnRef" => return .fnRef (← f 0 >>= str) (← f 1 >>= list ty) (← f 2 >>= list row)
  | "method" => return .method (← f 0 >>= str) (← f 1 >>= str) (← f 2 >>= ty)
  | "closure" =>
    return .closure (← f 0 >>= list param) (← f 1 >>= ty) (← f 2 >>= row) (← f 3 >>= expr)
  | "call" => return .call (← f 0 >>= expr) (← f 1 >>= list arg) (← f 2 >>= ty)
  | "letIn" => return .letIn (← f 0 >>= str) (← f 1 >>= ty) (← f 2 >>= expr) (← f 3 >>= expr)
  | "varIn" => return .varIn (← f 0 >>= str) (← f 1 >>= ty) (← f 2 >>= expr) (← f 3 >>= expr)
  | "assign" => return .assign (← f 0 >>= place) (← f 1 >>= expr)
  | "seq" => return .seq (← f 0 >>= expr) (← f 1 >>= expr)
  | "if" => return .if (← f 0 >>= expr) (← f 1 >>= ty) (← f 2 >>= expr) (← f 3 >>= expr)
  | "match" => return .match (← f 0 >>= expr) (← f 1 >>= ty) (← f 2 >>= list arm)
  | "for" => return .for (← f 0 >>= str) (← f 1 >>= ty) (← f 2 >>= expr) (← f 3 >>= expr)
  | "raise" => .raise <$> (f 0 >>= expr)
  | "try" => .try <$> (f 0 >>= expr)
  | "tryCatch" =>
    return .tryCatch (← f 0 >>= expr) (← f 1 >>= ty) (← f 2 >>= str) (← f 3 >>= expr)
      (← f 4 >>= ty)
  | "while" => return .while (← f 0 >>= expr) (← f 1 >>= expr)
  | "loop" => .loop <$> (f 0 >>= expr)
  | "break" => pure .break
  | "continue" => pure .continue
  | "return" => .return <$> (f 0 >>= expr)
  | "perform" => return .perform ⟨← f 0 >>= str, ← f 1 >>= str⟩ (← f 2 >>= expr)
  | "with" => return .withH (← f 0 >>= str) (← f 1 >>= bool) (← f 2 >>= expr) (← f 3 >>= expr)
  | "held" => return .held (← f 0 >>= list (pair str ty)) (← f 1 >>= list expr) (← f 2 >>= expr)
  -- `["letElse", e, type, [P, binders, rest], x]`: `let P = e else x`, then the rest.
  | "letElse" =>
    let a ← f 2 >>= arm
    return .letElse a.pattern a.binders (← f 0 >>= expr) (← f 1 >>= ty) a.body (← f 3 >>= expr)
  -- `["orElse", e₁, type, option, name, e₂]`: `e₁ else e₂`, the `Option` named `option`.
  | "orElse" =>
    return .orElse (← f 2 >>= str) (← f 1 >>= ty) (← f 3 >>= str) (← f 0 >>= expr) (← f 4 >>= expr)
  -- `["compound", m]` and `["intFloat", m]`: `place op= e` and an integer literal at a float
  -- type, each written as what it means (`Form.Shaped`).
  | "compound" => .form .compound <$> (f 0 >>= expr)
  | "intFloat" => .form .intFloat <$> (f 0 >>= expr)
  -- `["optionField", m]`: `e.f` through an `Option`, written as the `match` it means.
  | "optionField" => .form .optionField <$> (f 0 >>= expr)
  -- `["update", m]`: `{ ..base, f: e }`, written as the bindings and record it means.
  | "update" => .form .update <$> (f 0 >>= expr)
  -- `["projection", res, type, body]`: a projection's body written for an access whose value
  -- has `type`, which keeps the access's values in `res` (`Expr.projectionBody`).
  | "projection" => return .projectionBody (← f 0 >>= str) (← f 1 >>= ty) (← f 2 >>= expr)
  -- `["yield", res, call]`: `yield p`, the call of the access with `p` `inout`, its value
  -- added to `res` (`Expr.yieldOf`).
  | "yield" =>
    let res ← f 0 >>= str
    return .form .yield (.assign ⟨res, []⟩ (.op (.list .push) [.var res, .try (← f 1 >>= expr)]))
  -- `["yielded", res]`: the access's value, which a projection's `return` gives.
  | "yielded" => return .yieldedOf (← f 0 >>= str)
  -- `["project", call]`: a call of a projection where a place is (`Expr.projectCall`).
  | "project" => return .form .project (← f 0 >>= expr)
  -- `["writes", call]`: a writable binding and the rest of its block, the call of a closure
  -- that takes its source `inout` (`Form.writes`).
  | "writes" => return .form .writes (← f 0 >>= expr)
  -- `["through", j, start, end, i]`: the index of a place through a writable binding whose
  -- part runs from `start` up to `end` of its source (`Expr.throughOf`).
  | "through" =>
    return .throughOf (← f 0 >>= str) (← f 1 >>= str) (← f 2 >>= str) (← f 3 >>= expr)
  -- The forms of tasks, scopes and lazy values (`Stilt.Typing.Tasks`): `["spawn", g, row, f,
  -- type]`, `["await", h, type, t]`, `["scope", error, f, type]`, `["scopeSpawn", r, error, s, g,
  -- row, f, type]`, `["asyncWith", h, block]`, `["lazyNew", type, f]` and `["lazyGet", h, type,
  -- l]`, where `type` is the value's type, that of a task's function's result or a lazy value's.
  | "spawn" =>
    return .spawnOf taskName (← f 0 >>= str) (← f 1 >>= row) (← f 2 >>= expr) (← f 3 >>= ty)
  | "await" => return .awaitOf taskName (← f 0 >>= str) (← f 1 >>= ty) (← f 2 >>= expr)
  | "scope" => return .scopeOf scopeName (← f 0 >>= ty) (← f 1 >>= expr) (← f 2 >>= ty)
  | "scopeSpawn" =>
    return .scopeSpawnOf scopeName (← f 0 >>= str) (← f 1 >>= ty) (← f 2 >>= expr) taskName
      (← f 3 >>= str) (← f 4 >>= row) (← f 5 >>= expr) (← f 6 >>= ty)
  | "asyncWith" => return .asyncWith (← f 0 >>= expr) (← f 1 >>= expr)
  | "lazyNew" => return .lazyNewOf lazyName (← f 0 >>= ty) (← f 1 >>= expr)
  | "lazyGet" => return .lazyGetOf lazyName (← f 0 >>= str) (← f 1 >>= ty) (← f 2 >>= expr)
  | _ => throw s!"no expression is named {tag}"

partial def arg (j : Json) : Except String Arg := do
  let (tag, fs) ← tagged j
  match tag with
  | "value" => .value <$> (field fs 0 >>= expr)
  | "inout" => .inout <$> (field fs 0 >>= place)
  | _ => throw s!"no argument is named {tag}"

/-- A place: `[root, projections]`. -/
partial def place : Decoder Place
  | .arr #[r, ps] => return ⟨← str r, ← list projection ps⟩
  | j => throw s!"a place, not {j.compress}"

partial def projection (j : Json) : Except String Projection := do
  let (tag, fs) ← tagged j
  match tag with
  | "field" => .field <$> (field fs 0 >>= str)
  | "index" => .index <$> (field fs 0 >>= expr)
  | _ => throw s!"no projection is named {tag}"

/-- An arm: `[pattern, binders, guard, body]`, its guard `null` when it has none, or
`[pattern, binders, body]` without a guard. -/
partial def arm : Decoder Arm
  | .arr #[p, bs, b] => return ⟨← pattern p, ← list str bs, none, ← expr b⟩
  | .arr #[p, bs, .null, b] => return ⟨← pattern p, ← list str bs, none, ← expr b⟩
  | .arr #[p, bs, g, b] => return ⟨← pattern p, ← list str bs, some (← expr g), ← expr b⟩
  | j => throw s!"an arm, not {j.compress}"

end

end Stilt.Run
