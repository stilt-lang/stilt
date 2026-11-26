import Stilt.StrNatives
import Stilt.Generics

/-!
# Maps and sets

The values of maps and sets, and what the functions of maps and sets that the
calculus holds compute (std.maps, std.map-functions and std.sets).

A map keeps its entries in insertion order (std.maps). Its value is a record,
which no declaration names, of its entries, each the list of its key and its
value, and of its default, a list of no value or one. A set's value is a
record of its elements, in insertion order: `Set<T>` is the prelude's record
`{ elements: Map<T, ()> }` (std.sets), and the value keeps that map's keys,
whose values are all `()`. So reading, writing and copying a value treats the
parts of a map or a set as those of a record and a list, as for tuples, and
only the functions of this file read them as entries.

A function finds a key as std.finding-keys says: the first stored key that
`eq` finds equal to it. The key types of the calculus are those whose `Eq` and
`Hash` are built in (traits.built-in-impls), which compare and hash values, so
which stored keys share a hash changes nothing, and the keys of a map, like
the elements of a set, are distinct.
-/

namespace Stilt

/-- The name of a map's record, which no declaration names. -/
def mapName : Name := "{:}"

/-- The name of a set's record, which no declaration names. -/
def setName : Name := "{,}"

/-- The field of a map's record that holds its entries. -/
def entriesField : Name := "entries"

/-- The field of a map's record that holds its default. -/
def defaultField : Name := "default"

/-- The field of a set's record that holds its elements. -/
def elementsField : Name := "elements"

/-- An entry of a map: the list of its key and its value. -/
def Value.entry (e : Value × Value) : Value := .list [e.1, e.2]

/-- A map of its entries, in insertion order, and of its default if it has one
(std.maps). -/
def Value.mapOf (es : List (Value × Value)) (d : Option Value) : Value :=
  .record mapName [(entriesField, .list (es.map Value.entry)), (defaultField, .list d.toList)]

/-- A set of its elements, in insertion order (std.sets). -/
def Value.setOf (ks : List Value) : Value := .record setName [(elementsField, .list ks)]

/-- A type whose values a map finds by their `Eq` and `Hash` part by part: an
integer type, `bool`, `str` or `()`, whose impls are built in (traits.built-in-impls
and std.map-key-bounds), and the tuples, lists, records and variant types whose
impls are the structural ones (traits.structural-impls), which compare their parts
in order. A use of a function of maps or sets asks more of a record or variant
type, that its parts be key types too and that the program write no `Eq` or `Hash`
for it (`Decls.Key`, in `HasType.op`). Keys of type parameters are outside the
calculus. -/
inductive Ty.Key : Ty → Prop
  | int (k : IntTy) : Ty.Key (.int k)
  | bool : Ty.Key .bool
  | str : Ty.Key .str
  | unit : Ty.Key .unit
  | tuple {κs : List Ty} : (∀ κ ∈ κs, Ty.Key κ) → Ty.Key (.tuple κs)
  | list {κ : Ty} : Ty.Key κ → Ty.Key (.list κ)
  /-- A record or a variant type at key types, whose parts `Decls.Key` checks: its values
  compare part by part. -/
  | record (R : Name) {args : List Ty} : (∀ κ ∈ args, Ty.Key κ) → Ty.Key (.record R args)
  | variant (T : Name) {args : List Ty} : (∀ κ ∈ args, Ty.Key κ) → Ty.Key (.variant T args)

/-! ## Reading maps and sets -/

namespace Value

/-- A list's elements. -/
def list? : Value → Option (List Value)
  | .list vs => some vs
  | _ => none

/-- An integer's value. -/
def int? : Value → Option Int
  | .int n => some n
  | _ => none

/-- An entry's key and value. -/
def entry? : Value → Option (Value × Value)
  | .list [k, v] => some (k, v)
  | _ => none

/-- The elements of a record's field that holds a list. -/
def listField? : Value → Name → Option (List Value)
  | .record _ fields, f => (fields.lookup f).bind list?
  | _, _ => none

/-- A map's entries and default. -/
def map? (v : Value) : Option (List (Value × Value) × Option Value) :=
  match v.listField? entriesField, v.listField? defaultField with
  | some es, some ds => (es.mapM entry?).map fun es => (es, ds.head?)
  | _, _ => none

/-- A set's elements. -/
def set? (v : Value) : Option (List Value) := v.listField? elementsField

/-- Whether two keys are equal, as the `Eq` of a key type finds them: integers,
Booleans and strings by their values, and `()` equal to itself
(traits.built-in-impls); tuples, records, variants and lists part by part, in
order, as their structural impls compare them (traits.structural-impls). -/
def keyEq : Value → Value → Bool
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .str a, .str b => a == b
  | .unit, .unit => true
  | .record R fs, .record S gs => R == S && fieldsKeyEq fs gs
  | .variant T C vs, .variant U D ws => T == U && C == D && payloadKeyEq vs ws
  | .list vs, .list ws => payloadKeyEq vs ws
  | _, _ => false
where
  /-- Whether two tuples' elements are equal keys, position by position. -/
  fieldsKeyEq : List (Name × Value) → List (Name × Value) → Bool
    | [], [] => true
    | (_, a) :: fs, (_, b) :: gs => keyEq a b && fieldsKeyEq fs gs
    | _, _ => false
  /-- Whether two variants' payloads are equal keys, position by position. -/
  payloadKeyEq : List Value → List Value → Bool
    | [], [] => true
    | a :: vs, b :: ws => keyEq a b && payloadKeyEq vs ws
    | _, _ => false

end Value

/-- What `f` computes from a map's entries and default. -/
def onMap (m : Value) (f : List (Value × Value) → Option Value → Except Fault Value) :
    Except Fault Value :=
  match m.map? with
  | some (es, d) => f es d
  | none => .error .stuck

/-- What `f` computes from a set's elements. -/
def onSet (s : Value) (f : List Value → Except Fault Value) : Except Fault Value :=
  match s.set? with
  | some ks => f ks
  | none => .error .stuck

/-- What `f` computes from a list's elements. -/
def onList (l : Value) (f : List Value → Except Fault Value) : Except Fault Value :=
  match l.list? with
  | some vs => f vs
  | none => .error .stuck

/-! ## Finding keys -/

namespace Entries

/-- The value of the entry whose key equals `k` (std.finding-keys). -/
def find (k : Value) (es : List (Value × Value)) : Option Value :=
  (es.find? fun e => k.keyEq e.1).map Prod.snd

/-- Whether an entry has a key equal to `k`. -/
def has (k : Value) (es : List (Value × Value)) : Bool := es.any fun e => k.keyEq e.1

/-- The entries with `v` the value of `k`: an entry that has the key keeps its
stored key and its position, and a new key goes at the end (std.maps and
std.finding-keys). -/
def insert (k v : Value) (es : List (Value × Value)) : List (Value × Value) :=
  if has k es then es.map fun e => if k.keyEq e.1 then (e.1, v) else e else es ++ [(k, v)]

/-- The entries without the one of `k`, the others in order (std.maps). -/
def remove (k : Value) (es : List (Value × Value)) : List (Value × Value) :=
  es.filter fun e => !k.keyEq e.1

/-- `m[k]`: the value of `k`, or for a missing key the default, which isn't
inserted, and otherwise a panic of the kind `missing-key` (std.maps). -/
def index (k : Value) (es : List (Value × Value)) (d : Option Value) : Except Fault Value :=
  match find k es, d with
  | some v, _ => .ok v
  | none, some v => .ok v
  | none, none => .error (.panic .missingKey)

/-- Whether two maps' entries are the same in any order: the same length, and each
key of the first, in order, found in the second with an equal value; values of a
key type, so `eq` is `keyEq` and stopping at the first difference shows nothing
(traits.structural-impls). -/
def equal (a b : List (Value × Value)) : Bool :=
  a.length == b.length && a.all fun e => match find e.1 b with
    | some v => e.2.keyEq v
    | none => false

end Entries

namespace Keys

/-- Whether an element equals `x`. -/
def has (x : Value) (ks : List Value) : Bool := ks.any x.keyEq

/-- The elements with `x` added at the end when it is absent (std.sets). -/
def insert (x : Value) (ks : List Value) : List Value := if has x ks then ks else ks ++ [x]

/-- The elements without the one equal to `x`, the others in order (std.sets). -/
def remove (x : Value) (ks : List Value) : List Value := ks.filter fun k => !x.keyEq k

/-- The elements, then each of `xs` that is absent, in order of first
appearance (std.sets). -/
def insertAll : List Value → List Value → List Value
  | ks, [] => ks
  | ks, x :: xs => insertAll (insert x ks) xs

end Keys

/-- The elements of a function of two sets, from theirs: `union` gives the
receiver's elements, then the other's that it lacks; `intersection` and
`difference` the receiver's that are, and that aren't, in the other, in order;
and `symmetric_difference` the receiver's that aren't in the other, then the
other's that aren't in the receiver (std.sets). -/
def SetCombine.run : SetCombine → List Value → List Value → List Value
  | .union, a, b => a ++ b.filter fun x => !Keys.has x a
  | .intersection, a, b => a.filter fun x => Keys.has x b
  | .difference, a, b => a.filter fun x => !Keys.has x b
  | .symmetricDifference, a, b =>
    a.filter (fun x => !Keys.has x b) ++ b.filter fun x => !Keys.has x a

/-- A test of two sets, from their elements. Two sets are equal when they hold
the same elements, in any order: the structural `Eq` of `Set` compares their
maps, which are unequal when their lengths differ and otherwise find each key
of the first in the second (std.set-impls and traits.map-equality). -/
def SetRelation.test : SetRelation → List Value → List Value → Bool
  | .subset, a, b => a.all fun x => Keys.has x b
  | .superset, a, b => b.all fun x => Keys.has x a
  | .disjoint, a, b => a.all fun x => !Keys.has x b
  | .equal, a, b => a.length == b.length && a.all fun x => Keys.has x b

/-! ## The functions -/

/-- What a function of maps computes from its operands' values, the map first.
Lengths are `i64`s (numbers.lengths-are-i64). -/
def MapOp.apply : MapOp → List Value → Except Fault Value
  | .new, [] => .ok (.mapOf [] none)
  | .withDefault, [d] => .ok (.mapOf [] (some d))
  | .len, [m] => onMap m fun es _ => .int <$> IntTy.i64.check es.length
  | .isEmpty, [m] => onMap m fun es _ => .ok (.bool es.isEmpty)
  | .contains, [m, k] => onMap m fun es _ => .ok (.bool (Entries.has k es))
  | .index, [m, k] => onMap m fun es d => Entries.index k es d
  | .getOr, [m, k, v] => onMap m fun es _ => .ok ((Entries.find k es).getD v)
  | .insert, [m, k, v] => onMap m fun es d => .ok (.mapOf (Entries.insert k v es) d)
  | .remove, [m, k] => onMap m fun es d => .ok (.mapOf (Entries.remove k es) d)
  | .keys, [m] => onMap m fun es _ => .ok (.list (es.map Prod.fst))
  | .values, [m] => onMap m fun es _ => .ok (.list (es.map Prod.snd))
  | .entries, [m] => onMap m fun es _ => .ok (.list (es.map fun e => .tuple [e.1, e.2]))
  | .equal, [m, n] => onMap m fun a _ => onMap n fun b _ => .ok (.bool (Entries.equal a b))
  | _, _ => .error .stuck

/-- What a function of sets computes from its operands' values, the set first. -/
def SetOp.apply : SetOp → List Value → Except Fault Value
  | .new, [] => .ok (.setOf [])
  | .fromList, [l] => onList l fun xs => .ok (.setOf (Keys.insertAll [] xs))
  | .len, [s] => onSet s fun ks => .int <$> IntTy.i64.check ks.length
  | .isEmpty, [s] => onSet s fun ks => .ok (.bool ks.isEmpty)
  | .contains, [s, x] => onSet s fun ks => .ok (.bool (Keys.has x ks))
  | .insert, [s, x] => onSet s fun ks => .ok (.setOf (Keys.insert x ks))
  | .remove, [s, x] => onSet s fun ks => .ok (.setOf (Keys.remove x ks))
  | .toList, [s] => onSet s fun ks => .ok (.list ks)
  | .combine c, [s, t] => onSet s fun a => onSet t fun b => .ok (.setOf (c.run a b))
  | .relate r, [s, t] => onSet s fun a => onSet t fun b => .ok (.bool (r.test a b))
  | _, _ => .error .stuck

/-- The integers from `a` up to `b`, which they include when `inclusive`. -/
def rangeValues (a b : Int) (inclusive : Bool) : List Value :=
  (List.range (if inclusive then b - a + 1 else b - a).toNat).map fun i : Nat => .int (a + i)

/-- The strings a list of values holds, if it holds only strings. -/
def strsOf : List Value → Option (List String)
  | [] => some []
  | .str s :: vs => (s :: ·) <$> strsOf vs
  | _ :: _ => none

/-- A list of strings as a value. -/
def strings (ss : List String) : Value := .list (ss.map Value.str)

/-- The integers a list holds, if it holds only integers. -/
def intsOf : List Value → Option (List Int)
  | [] => some []
  | .int n :: vs => (n :: ·) <$> intsOf vs
  | _ :: _ => none

/-- The integer `n`, as a list of one, when it is within the bounds, and an empty list
otherwise. -/
def fitting (lo hi n : Int) : Value := .list (if lo ≤ n ∧ n ≤ hi then [.int n] else [])

/-- A float's truncation when it fits in `lo` to `hi`, as a list of none or one integer. -/
def truncating (lo hi : Int) (x : FloatVal) : Value :=
  match x.truncated with
  | some n => fitting lo hi n
  | none => .list []

/-- A list of integers. -/
def ints (ns : List Nat) : Value := .list (ns.map fun (n : Nat) => Value.int n)

/-- What a function of lists computes from its operands' values, the list first.
Lengths are `i64`s (numbers.lengths-are-i64). -/
def ListOp.apply : ListOp → List Value → Except Fault Value
  | .len, [l] => onList l fun xs => .int <$> IntTy.i64.check xs.length
  | .isEmpty, [l] => onList l fun xs => .ok (.bool xs.isEmpty)
  | .push, [l, x] => onList l fun xs => .ok (.list (xs ++ [x]))
  | .range inclusive, [u, w] => match u.int?, w.int? with
    | some a, some b => .ok (.list (rangeValues a b inclusive))
    | _, _ => .error .stuck
  | .slice, [l, .int a, .int b] => onList l fun xs =>
    if 0 ≤ a ∧ a ≤ b ∧ b ≤ xs.length then .ok (.list ((xs.drop a.toNat).take (b - a).toNat))
    else .error (.panic .bounds)
  | .insert, [l, .int i, x] => onList l fun xs =>
    if 0 ≤ i ∧ i ≤ xs.length then .ok (.list (xs.take i.toNat ++ x :: xs.drop i.toNat))
    else .error (.panic .bounds)
  | .removeAt, [l, .int i] => onList l fun xs =>
    if 0 ≤ i ∧ i < xs.length then .ok (.list (xs.take i.toNat ++ xs.drop (i.toNat + 1)))
    else .error (.panic .bounds)
  | .chars, [.str s] => .ok (strings (Str.chars s))
  | .bytes, [.str s] => .ok (ints (s.toUTF8.toList.map UInt8.toNat))
  | .codePoints, [.str s] => .ok (ints (s.toList.map Char.toNat))
  | .nextLine, [.str s] => .ok (strings (Str.nextLine s))
  | .fromUtf8 lossy, [l] => onList l fun xs => match intsOf xs with
    | some ns =>
      let (s, ok) := Str.fromUtf8 ns
      .ok (if lossy then .str s else strings (if ok then [s] else []))
    | none => .error .stuck
  | .fromCodePoint, [.int p] => .ok (strings (Str.fromCodePoint p))
  | .checked o lo hi, [.int a, .int b] => .ok (fitting lo hi (o.exact a b))
  | .narrow lo hi, [.int n] => .ok (fitting lo hi n)
  | .truncate lo hi, [.float x] => .ok (truncating lo hi x)
  | .find last, [.str s, .str sub] => match Str.find last s sub with
    | none => .ok (.list [])
    | some n => (fun v : Int => Value.list [.int v]) <$> IntTy.i64.check n
  | .split, [.str s, .str sep] => .ok (strings (Str.split s sep))
  | .lines, [.str s] => .ok (strings (Str.lines s))
  | .splitWhitespace, [.str s] => .ok (strings (Str.splitWhitespace s))
  | .join, [.str sep, l] => onList l fun xs => match strsOf xs with
    | some ts => .ok (.str (sep.intercalate ts))
    | none => .error .stuck
  | _, _ => .error .stuck

/-! ## Signatures -/

/-- `ListOp.Sig op τs τ`: the function of lists takes operands of the types `τs`,
the list first, and gives a value of type `τ` (std.lists). -/
inductive ListOp.Sig : ListOp → List Ty → Ty → Prop
  | len {τ : Ty} : ListOp.Sig .len [.list τ] .i64
  | isEmpty {τ : Ty} : ListOp.Sig .isEmpty [.list τ] .bool
  | push {τ : Ty} : ListOp.Sig .push [.list τ, τ] (.list τ)
  | range {k : IntTy} {inclusive : Bool} :
      ListOp.Sig (.range inclusive) [.int k, .int k] (.list (.int k))
  | join : ListOp.Sig .join [.str, .list .str] .str
  | slice {τ : Ty} : ListOp.Sig .slice [.list τ, .i64, .i64] (.list τ)
  | insert {τ : Ty} : ListOp.Sig .insert [.list τ, .i64, τ] (.list τ)
  | removeAt {τ : Ty} : ListOp.Sig .removeAt [.list τ, .i64] (.list τ)
  | chars : ListOp.Sig .chars [.str] (.list .str)
  | bytes : ListOp.Sig .bytes [.str] (.list (.int .u8))
  | codePoints : ListOp.Sig .codePoints [.str] (.list (.int .u32))
  | nextLine : ListOp.Sig .nextLine [.str] (.list .str)
  | find {last : Bool} : ListOp.Sig (.find last) [.str, .str] (.list .i64)
  | fromUtf8 : ListOp.Sig (.fromUtf8 false) [.list (.int .u8)] (.list .str)
  | fromUtf8Lossy : ListOp.Sig (.fromUtf8 true) [.list (.int .u8)] .str
  | fromCodePoint : ListOp.Sig .fromCodePoint [.int .u32] (.list .str)
  | checked {o : Checked} {k : IntTy} :
      ListOp.Sig (.checked o k.min k.max) [.int k, .int k] (.list (.int k))
  | narrow {k k' : IntTy} : ListOp.Sig (.narrow k'.min k'.max) [.int k] (.list (.int k'))
  | truncate {f : FloatTy} {k : IntTy} : ListOp.Sig (.truncate k.min k.max) [.float f] (.list (.int k))
  | split : ListOp.Sig .split [.str, .str] (.list .str)
  | lines : ListOp.Sig .lines [.str] (.list .str)
  | splitWhitespace : ListOp.Sig .splitWhitespace [.str] (.list .str)

/-- `MapOp.Sig op τs τ`: the function of maps takes operands of the types `τs`,
the map first, and gives a value of type `τ`. Every function of a map finds
keys, so its key type implements `Eq` and `Hash` (std.map-key-bounds). -/
inductive MapOp.Sig : MapOp → List Ty → Ty → Prop
  | new {κ τ : Ty} : κ.Key → MapOp.Sig .new [] (.map κ τ)
  | withDefault {κ τ : Ty} : κ.Key → MapOp.Sig .withDefault [τ] (.map κ τ)
  | len {κ τ : Ty} : κ.Key → MapOp.Sig .len [.map κ τ] .i64
  | isEmpty {κ τ : Ty} : κ.Key → MapOp.Sig .isEmpty [.map κ τ] .bool
  | contains {κ τ : Ty} : κ.Key → MapOp.Sig .contains [.map κ τ, κ] .bool
  | index {κ τ : Ty} : κ.Key → MapOp.Sig .index [.map κ τ, κ] τ
  | getOr {κ τ : Ty} : κ.Key → MapOp.Sig .getOr [.map κ τ, κ, τ] τ
  | insert {κ τ : Ty} : κ.Key → MapOp.Sig .insert [.map κ τ, κ, τ] (.map κ τ)
  | remove {κ τ : Ty} : κ.Key → MapOp.Sig .remove [.map κ τ, κ] (.map κ τ)
  | keys {κ τ : Ty} : κ.Key → MapOp.Sig .keys [.map κ τ] (.list κ)
  | values {κ τ : Ty} : κ.Key → MapOp.Sig .values [.map κ τ] (.list τ)
  | entries {κ τ : Ty} : κ.Key → MapOp.Sig .entries [.map κ τ] (.list (.tuple [κ, τ]))
  | equal {κ τ : Ty} : κ.Key → τ.Key → MapOp.Sig .equal [.map κ τ, .map κ τ] .bool

/-- `SetOp.Sig op τs τ`: the function of sets takes operands of the types `τs`,
the set first, and gives a value of type `τ`. Its functions are in
`impl<T: Eq + Hash> Set<T>` (std.sets). -/
inductive SetOp.Sig : SetOp → List Ty → Ty → Prop
  | new {κ : Ty} : κ.Key → SetOp.Sig .new [] (.set κ)
  | fromList {κ : Ty} : κ.Key → SetOp.Sig .fromList [.list κ] (.set κ)
  | len {κ : Ty} : κ.Key → SetOp.Sig .len [.set κ] .i64
  | isEmpty {κ : Ty} : κ.Key → SetOp.Sig .isEmpty [.set κ] .bool
  | contains {κ : Ty} : κ.Key → SetOp.Sig .contains [.set κ, κ] .bool
  | insert {κ : Ty} : κ.Key → SetOp.Sig .insert [.set κ, κ] (.set κ)
  | remove {κ : Ty} : κ.Key → SetOp.Sig .remove [.set κ, κ] (.set κ)
  | toList {κ : Ty} : κ.Key → SetOp.Sig .toList [.set κ] (.list κ)
  | combine {c : SetCombine} {κ : Ty} : κ.Key → SetOp.Sig (.combine c) [.set κ, .set κ] (.set κ)
  | relate {r : SetRelation} {κ : Ty} : κ.Key → SetOp.Sig (.relate r) [.set κ, .set κ] .bool

/-- A key type names no type parameter, so an instance keeps it. -/
theorem Ty.Key.substTys {κ : Ty} (h : κ.Key) (s : TySubst) : κ.substTys s = κ := by
  induction h with
  | tuple _ ih =>
    simp only [Ty.substTys, substTyList_eq_map, Ty.tuple.injEq]
    exact (List.map_congr_left ih).trans (List.map_id _)
  | list _ ih => simp only [Ty.substTys, ih]
  | record _ _ ih =>
    simp only [Ty.substTys, substTyList_eq_map, Ty.record.injEq, true_and]
    exact (List.map_congr_left ih).trans (List.map_id _)
  | variant _ _ ih =>
    simp only [Ty.substTys, substTyList_eq_map, Ty.variant.injEq, true_and]
    exact (List.map_congr_left ih).trans (List.map_id _)
  | _ => rfl

/-! ## Key types of a program -/

/-- What a key type of the program is at its outermost type, given the types `S` its
parts must be: an integer type, `bool`, `str` or `()`, whose `Eq` and `Hash` are built
in (traits.built-in-impls); a tuple or a list of parts; or a record or variant type for
which the program writes no `Eq` or `Hash`, at key types, whose structural impls are those
of its fields or payloads at its arguments (traits.structural-impls). A float is none, since floats don't implement
`Hash` (std.map-key-bounds), and neither is a function type, which implements no trait
(traits.built-in-impls). -/
def Decls.KeyStep (D : Decls) (S : Ty → Prop) : Ty → Prop
  | .int _ | .bool | .str | .unit => True
  | .tuple κs => ∀ κ ∈ κs, S κ
  | .list κ => S κ
  | .record R args => (D.traitImpl? "Eq" (.record R)).isNone ∧
      (D.traitImpl? "Hash" (.record R)).isNone ∧ (∀ κ ∈ args, S κ) ∧
      ∃ r, D.record? R = some r ∧ ∀ f ∈ r.fieldsAt args, S f.2
  | .variant T args => (D.traitImpl? "Eq" (.variant T)).isNone ∧
      (D.traitImpl? "Hash" (.variant T)).isNone ∧ (∀ κ ∈ args, S κ) ∧
      ∃ t, D.variant? T = some t ∧ ∀ c ∈ t.ctorsAt args, ∀ τ ∈ c.2, S τ
  | _ => False

/-- A type that implements `Eq` and `Hash` in the program, part by part, as every
operation that finds a key requires (std.map-key-bounds and traits.structural-impls): some
set of types holds it, and each of them is a key type at its outermost type with its parts
in the set. A recursive type is a key type when its parts are. Its values are equal as
`Value.keyEq` finds them, by their parts. -/
def Decls.Key (D : Decls) (κ : Ty) : Prop :=
  ∃ S : Ty → Prop, S κ ∧ ∀ τ, S τ → D.KeyStep S τ

/-- The key types that a function of maps or sets finds keys of, as its signature gives
them: a map's or a set's key type, and for `==` on maps the value type too, which it
compares. Every other operation finds no key. -/
def Op.keyTypes : Op → List Ty → Ty → List Ty
  | .map .new, _, .map κ _ | .map .withDefault, _, .map κ _ => [κ]
  | .map .equal, .map κ υ :: _, _ => [κ, υ]
  | .map _, .map κ _ :: _, _ => [κ]
  | .set .new, _, .set κ | .set .fromList, _, .set κ => [κ]
  | .set _, .set κ :: _, _ => [κ]
  | _, _, _ => []

/-- The key types of an operation are key types of the program: a use whose key type
doesn't meet `Eq + Hash` is E0318 (std.map-key-bounds). -/
def Op.KeysIn (D : Decls) (o : Op) (τs : List Ty) (τ : Ty) : Prop :=
  ∀ κ ∈ o.keyTypes τs τ, D.Key κ

/-- An operation that finds no key needs no key type. -/
theorem Op.keysIn_of_nil {D : Decls} {o : Op} {τs : List Ty} {τ : Ty}
    (h : o.keyTypes τs τ = []) : o.KeysIn D τs τ :=
  fun _ hκ => by rw [h] at hκ; exact nomatch hκ

end Stilt
