import Stilt.Maps.Parts
import Stilt.Show
import Stilt.Structural
import Stilt.FormatSpec
import Stilt.World

/-!
# Built-in operations

The signatures of the operations built in to the language, and the value each
computes from its operands' values.

A tuple is a record whose fields are named by their positions, `0`, `1`, …, as
`.0` reads them (types.field-access), and whose type no declaration names
(declarations.tuples-and-unit). So reading and writing a tuple's field is
reading and writing a record's, and `.0` in a place is a field in its shape
(modes.places).
-/

namespace Stilt

/-- The viewable types: `str` and `List<U>` (views.viewable-types). -/
def Ty.viewable : Ty → Bool
  | .str | .list _ => true
  | _ => false

/-- `WorldOp.Sig op τs τ`: the operation on the world takes operands of the types `τs` and
gives a value of type `τ` (std.io): a write takes a string and gives `()`, a read of a line
gives the calculus's list of none or one line, and a read of the rest a string.
`Shared.new` takes a value of the cell's type and gives a handle (shared.std-sync); the
type has no row variable, since a cell's type is read with no instantiation of rows
(`Stilt.World`). -/
inductive WorldOp.Sig : WorldOp → List Ty → Ty → Prop
  | write {err newline : Bool} : WorldOp.Sig (.write err newline) [.str] .unit
  | readLine : WorldOp.Sig .readLine [] (.list .str)
  | readAll : WorldOp.Sig .readAll [] .str
  | sharedNew {u : Ty} : u.Closed → WorldOp.Sig (.sharedNew u) [u] (.shared u)

/-- `Op.Sig op τs τ`: the operation takes operands of the types `τs` and gives
a value of type `τ`. The two operands of an arithmetic, bitwise or comparison
operator have the same type, and a shift's amount may have any integer type
(numbers.no-implicit-conversions, numbers.shifts and numbers.comparisons). Arithmetic is
on integers and floats alone: `+` is not defined on `str` (expressions.no-string-plus). -/
inductive Op.Sig : Op → List Ty → Ty → Prop
  /-- A tuple has one element or more: `()` is the unit value
  (declarations.tuples-and-unit). -/
  | tuple {τs : List Ty} : τs ≠ [] → Op.Sig .tuple τs (.tuple τs)
  | not : Op.Sig .not [.bool] .bool
  /-- A float literal fits its type when it rounds to a finite value of that type, so
  `1e39` can't be an `f32` (E0320, numbers.float-literals). -/
  | float {k : FloatTy} {m : Nat} {s : Bool} {e : Nat} :
      (FloatVal.ofScientific k m s e).isInf = false → Op.Sig (.float k m s e) [] (.float k)
  /-- Unary `-` is defined on signed types only (numbers.unsigned-negation). -/
  | neg {k : IntTy} : k.signed = true → Op.Sig (.neg k) [.int k] (.int k)
  | arith {o : Arith} {k : IntTy} : Op.Sig (.arith o k) [.int k, .int k] (.int k)
  | wrapping {o : Wrapping} {k : IntTy} : Op.Sig (.wrapping o k) [.int k, .int k] (.int k)
  | shift {o : Shift} {k k' : IntTy} : Op.Sig (.shift o k k') [.int k, .int k'] (.int k)
  | bitwise {o : Bitwise} {k : IntTy} : Op.Sig (.bitwise o k) [.int k, .int k] (.int k)
  | complement {k : IntTy} : Op.Sig (.complement k) [.int k] (.int k)
  | compare {c : Cmp} {k : IntTy} : Op.Sig (.compare c k) [.int k, .int k] .bool
  /-- A conversion that returns `T` itself, when every value of the source
  type fits in `T` (numbers.conversions). -/
  | convert {k k' : IntTy} : k'.min ≤ k.min → k.max ≤ k'.max →
      Op.Sig (.convert k k') [.int k] (.int k')
  | wrapTo {k k' : IntTy} : Op.Sig (.wrapTo k k') [.int k] (.int k')
  | toFloat {k : IntTy} {f : FloatTy} : Op.Sig (.toFloat k f) [.int k] (.float f)
  | floatTo {f f' : FloatTy} : Op.Sig (.floatTo f f') [.float f] (.float f')
  | fneg {f : FloatTy} : Op.Sig (.fneg f) [.float f] (.float f)
  | farith {o : Arith} {f : FloatTy} : o ≠ .rem → Op.Sig (.farith o f) [.float f, .float f] (.float f)
  | fcompare {c : Cmp} {f : FloatTy} : Op.Sig (.fcompare c f) [.float f, .float f] .bool
  | funary {m : FloatMethod} {f : FloatTy} : m.binary = false → m ≠ .isNan →
      Op.Sig (.fmethod m f) [.float f] (.float f)
  | fbinary {m : FloatMethod} {f : FloatTy} : m.binary = true →
      Op.Sig (.fmethod m f) [.float f, .float f] (.float f)
  | fisNan {f : FloatTy} : Op.Sig (.fmethod .isNan f) [.float f] .bool
  | bcompare {c : Cmp} : Op.Sig (.bcompare c) [.bool, .bool] .bool
  | str {t : String} : Op.Sig (.str t) [] .str
  /-- An interpolating literal joins strings: its literal pieces and the
  interpolations shown. -/
  | concat {n : Nat} : Op.Sig .concat (List.replicate n .str) .str
  | showInt {k : IntTy} : Op.Sig (.showInt k) [.int k] .str
  | showBool : Op.Sig .showBool [.bool] .str
  | pad {c : Char} {a : Align} {w : Nat} : Op.Sig (.pad c a w) [.str] .str
  | inBase {k : IntTy} {base : Nat} {upper : Bool} : Op.Sig (.inBase k base upper) [.int k] .str
  | fixed {f : FloatTy} {p : Nat} : Op.Sig (.fixed f p) [.float f] .str
  | intMethod {m : IntMethod} {k : IntTy} :
      Op.Sig (.intMethod m k) (.int k :: ((m.second k).map Ty.int).toList) (.int (m.result k))
  | parses {k : IntTy} : Op.Sig (.parses k) [.str] .bool
  | parsed {k : IntTy} : Op.Sig (.parsed k) [.str] (.int k)
  | fparses {f : FloatTy} : Op.Sig (.fparses f) [.str] .bool
  | fparsed {f : FloatTy} : Op.Sig (.fparsed f) [.str] (.float f)
  | scientific {f : FloatTy} {p : Option Nat} : Op.Sig (.scientific f p) [.float f] .str
  | len : Op.Sig .len [.str] .i64
  | isEmpty : Op.Sig .isEmpty [.str] .bool
  /-- Offsets are `i64`s (numbers.lengths-are-i64). -/
  | slice : Op.Sig .slice [.str, .i64, .i64] .str
  | strMap {f : StrMap} : Op.Sig (.strMap f) [.str] .str
  | replace {first : Bool} : Op.Sig (.replace first) [.str, .str, .str] .str
  | charCount : Op.Sig .charCount [.str] .i64
  | count : Op.Sig .count [.str, .str] .i64
  | search {o : Search} : Op.Sig (.search o) [.str, .str] .bool
  | scompare {c : Cmp} : Op.Sig (.scompare c) [.str, .str] .bool
  | strClass {c : StrClass} : Op.Sig (.strClass c) [.str] .bool
  | padStr {start : Bool} : Op.Sig (.padStr start) [.str, .i64, .str] .str
  | showValue {τ : Ty} : Op.Sig .showValue [τ] .str
  | panic {k : PanicKind} {τs : List Ty} {τ : Ty} : Op.Sig (.panic k) τs τ
  | structural {c : Cmp} {orders : List (Name × List Name)} {τ : Ty} :
      Op.Sig (.structural c orders) [τ, τ] .bool
  | sameCell {τ : Ty} : Op.Sig .sameCell [.shared τ, .shared τ] .bool
  | sortedByKey {d : Bool} {orders : List (Name × List Name)} {κ τ : Ty} :
      Op.Sig (.sortedByKey d orders) [.list κ, .list τ] (.list τ)
  | list {l : ListOp} {τs : List Ty} {τ : Ty} : l.Sig τs τ → Op.Sig (.list l) τs τ
  | map {m : MapOp} {τs : List Ty} {τ : Ty} : m.Sig τs τ → Op.Sig (.map m) τs τ
  | set {m : SetOp} {τs : List Ty} {τ : Ty} : m.Sig τs τ → Op.Sig (.set m) τs τ
  /-- `View.all<T>(source: T) -> View<T>`, for a viewable `T`; any other `T` is E0420
  (views.viewable-types and views.making-view). -/
  | viewAll {τ : Ty} : τ.viewable = true → Op.Sig .view [τ] (.view τ)
  /-- `View.of<T>(source: T, start: i64, end: i64) -> View<T>` (views.making-view). -/
  | viewOf {τ : Ty} : τ.viewable = true → Op.Sig .view [τ, .i64, .i64] (.view τ)
  /-- `view(self, start: i64, end: i64) -> View<T>` (views.functions-of-views). -/
  | viewPart {τ : Ty} : τ.viewable = true → Op.Sig .view [.view τ, .i64, .i64] (.view τ)
  /-- `copy(self) -> T` (views.functions-of-views). -/
  | copy {τ : Ty} : Op.Sig .copy [.view τ] τ
  | world {k : WorldOp} {τs : List Ty} {τ : Ty} : k.Sig τs τ → Op.Sig (.world k) τs τ

/-- The operands and values of every operation but `tuple` and the functions
of maps and sets: numbers, Booleans and strings. -/
inductive Scalar where
  | int (n : Int)
  | float (x : FloatVal)
  | bool (b : Bool)
  | str (s : String)

/-- A scalar as a value. -/
def Scalar.value : Scalar → Value
  | .int n => .int n
  | .float x => .float x
  | .bool b => .bool b
  | .str s => .str s

/-- A value as a scalar, if it is one. -/
def Value.scalar? : Value → Option Scalar
  | .int n => some (.int n)
  | .float x => some (.float x)
  | .bool b => some (.bool b)
  | .str s => some (.str s)
  | _ => none

/-- A scalar's string, if it is one. -/
def Scalar.str? : Scalar → Option String
  | .str s => some s
  | _ => none

/-- A result, or `stuck`. -/
def orStuck {α : Type} : Option α → Except Fault α
  | some a => .ok a
  | none => .error .stuck

/-- What an operation on scalars computes from its operands. -/
def Op.compute : Op → List Scalar → Except Fault Scalar
  | .not, [.bool b] => .ok (.bool !b)
  | .float k m s e, [] => .ok (.float (FloatVal.ofScientific k m s e))
  | .neg k, [.int a] => .int <$> k.check (-a)
  | .arith o k, [.int a, .int b] => .int <$> k.arith o a b
  | .wrapping o k, [.int a, .int b] => .ok (.int (k.wrap (o.ints a b)))
  | .shift o k _, [.int a, .int b] => .int <$> k.shift o a b
  | .bitwise o k, [.int a, .int b] => .ok (.int (k.ofBits (o.bits (k.toBits a) (k.toBits b))))
  | .complement k, [.int a] => .ok (.int (k.ofBits (~~~(k.toBits a))))
  | .compare c _, [.int a, .int b] => .ok (.bool (c.ints a b))
  | .convert _ _, [.int a] => .ok (.int a)
  | .wrapTo _ k, [.int a] => .ok (.int (k.wrap a))
  | .toFloat _ f, [.int a] => .ok (.float (FloatVal.ofInt f a))
  | .floatTo _ f, [.float x] => .ok (.float (x.convert f))
  | .fneg _, [.float x] => .ok (.float x.neg)
  | .farith o _, [.float x, .float y] => .float <$> orStuck (FloatVal.arith o x y)
  | .fcompare c _, [.float x, .float y] => .bool <$> orStuck (FloatVal.compare c x y)
  | .fmethod .isNan _, [.float x] => .ok (.bool x.isNaN)
  | .fmethod .min _, [.float x, .float y] => .float <$> orStuck (FloatVal.extremum true x y)
  | .fmethod .max _, [.float x, .float y] => .float <$> orStuck (FloatVal.extremum false x y)
  | .fmethod m _, [.float x] => if m.binary then .error .stuck else .ok (.float (x.unary m))
  | .bcompare c, [.bool a, .bool b] => .ok (.bool (c.bools a b))
  | .str t, [] => .ok (.str t)
  | .concat, ss => (fun ts => .str (String.join ts)) <$> orStuck (ss.mapM Scalar.str?)
  | .showInt _, [.int n] => .ok (.str (toString n))
  | .pad c a w, [.str s] => .ok (.str (padText c a w s))
  | .inBase k base upper, [.int n] => .ok (.str (k.inBase base upper n))
  | .fixed _ p, [.float x] => .ok (.str (x.fixed p))
  | .intMethod m k, [.int a] => .int <$> k.method m a 0
  | .intMethod m k, [.int a, .int b] => .int <$> k.method m a b
  | .parses k, [.str s] => .ok (.bool (k.parse s).isSome)
  | .parsed k, [.str s] => .ok (.int (k.parsedOrZero s))
  | .fparses f, [.str s] => .ok (.bool (FloatVal.parse f s).isSome)
  | .fparsed f, [.str s] => .ok (.float (FloatVal.parsedOrZero f s))
  | .scientific _ p, [.float x] => .ok (.str (x.scientific p))
  | .showBool, [.bool b] => .ok (.str (toString b))
  | .len, [.str s] => .int <$> Str.len s
  | .isEmpty, [.str s] => .ok (.bool s.isEmpty)
  | .slice, [.str s, .int a, .int b] => .str <$> Str.slice s a b
  | .strMap f, [.str s] => .ok (.str (f.apply s))
  | .replace first, [.str s, .str a, .str b] => .ok (.str (Str.replace first s a b))
  | .charCount, [.str s] => .int <$> IntTy.i64.check s.length
  | .count, [.str s, .str t] => .int <$> IntTy.i64.check (Str.count s t)
  | .search o, [.str s, .str t] => .ok (.bool (o.test s t))
  | .scompare c, [.str s, .str t] => .ok (.bool (c.strs s t))
  | .strClass c, [.str s] => .ok (.bool (c.test s))
  | .padStr start, [.str s, .int w, .str f] => .ok (.str (Str.pad start s w f))
  | _, _ => .error .stuck

/-- Whether an operation reads numbers, Booleans and strings: every one but
`tuple`, `showValue`, the structural comparisons, `panic` and the functions of
lists, maps and sets. -/
def Op.scalar : Op → Bool
  | .tuple | .showValue | .structural .. | .sameCell | .sortedByKey .. | .panic _ | .list _
  | .map _ | .set _ | .view | .copy => false
  | _ => true

/-- What an operation on scalars computes from its operands' values. -/
def Op.applyScalars (o : Op) (vs : List Value) : Except Fault Value :=
  match vs.mapM Value.scalar? with
  | some ss => Scalar.value <$> o.compute ss
  | none => .error .stuck

/-- The value an operation computes from its operands' values: a tuple holds
them, the functions of lists, maps and sets read and build lists, maps and sets,
and every other operation reads numbers, Booleans and strings. -/
def Op.apply (o : Op) (vs : List Value) : Except Fault Value :=
  match o with
  | .tuple => .ok (.tuple vs)
  | .showValue => match vs with
    | [v] => .ok (.str (v.shown false))
    | _ => .error .stuck
  | .panic k => .error (.panic k)
  | .structural c orders => match vs with
    | [v, w] => .ok (.bool (c.values orders v w))
    | _ => .error .stuck
  | .sameCell => match vs with
    | [v, w] => .ok (.bool (v.same w))
    | _ => .error .stuck
  | .sortedByKey d orders => match vs with
    | [.list ks, .list xs] => .ok (.list (sortByKeys orders d ks xs))
    | _ => .error .stuck
  | .list l => l.apply vs
  | .map m => m.apply vs
  | .set m => m.apply vs
  -- A view is the part it reads, as the reference interpreter holds it: a view of the
  -- whole is its source's value, a view of a part is the part, which panics as `slice`
  -- does, and its copy is its value (views.what-view-is and views.making-view).
  | .view => match vs with
    | [v] => .ok v
    | [.str s, a, b] => Op.slice.applyScalars [.str s, a, b]
    | [v, a, b] => ListOp.slice.apply [v, a, b]
    | _ => .error .stuck
  | .copy => match vs with
    | [v] => .ok v
    | _ => .error .stuck
  | o => o.applyScalars vs

/-- Every operation is `tuple`, a function of lists, of maps or of sets, or one
on scalars. -/
theorem Op.cases_scalar (o : Op) :
    o = .tuple ∨ o = .showValue ∨ (∃ c orders, o = .structural c orders) ∨ o = .sameCell ∨
      (∃ d orders, o = .sortedByKey d orders) ∨ (∃ k, o = .panic k) ∨
      (∃ l, o = .list l) ∨ (∃ m, o = .map m) ∨ (∃ m, o = .set m) ∨ (o = .view ∨ o = .copy) ∨
      o.scalar = true := by
  cases o <;> simp [Op.scalar]

theorem Op.apply_of_scalar {o : Op} (ho : o.scalar = true) (vs : List Value) :
    o.apply vs = o.applyScalars vs := by
  cases o <;> first | rfl | cases ho

/-- An operation on scalars gives a scalar. -/
theorem Op.apply_scalar {o : Op} (ho : o.scalar = true) {vs : List Value} {w : Value}
    (h : o.apply vs = .ok w) : ∃ s : Scalar, w = s.value := by
  rw [Op.apply_of_scalar ho, Op.applyScalars] at h
  split at h
  · cases hc : o.compute _ with
    | error => rw [hc] at h; cases h
    | ok s => rw [hc] at h; cases h; exact ⟨s, rfl⟩
  · cases h

/-- A view's value is its operand's, or the part `slice` gives of a string or a list. -/
theorem Op.view_apply {vs : List Value} {w : Value} (h : Op.view.apply vs = .ok w) :
    vs = [w] ∨ Op.slice.apply vs = .ok w ∨ (Op.list .slice).apply vs = .ok w := by
  simp only [Op.apply] at h
  split at h
  · cases h; exact .inl rfl
  · exact .inr (.inl (by rw [Op.apply_of_scalar rfl]; exact h))
  · exact .inr (.inr h)
  · cases h

theorem mapM_scalar? : ∀ ss : List Scalar, (ss.map Scalar.value).mapM Value.scalar? = some ss
  | [] => rfl
  | s :: ss => by cases s <;> simp [Scalar.value, Value.scalar?, mapM_scalar? ss]

/-- An operation on scalars applied to scalars computes on them. -/
theorem Op.apply_scalars {o : Op} (ho : o.scalar = true) (ss : List Scalar) :
    o.apply (ss.map Scalar.value) = Scalar.value <$> o.compute ss := by
  simp only [Op.apply_of_scalar ho, Op.applyScalars, mapM_scalar?]

/-- An operation builds its value from its operands' values, numbers,
Booleans and strings, so a property that holds of those and passes through
records and lists holds of it. -/
theorem Op.apply_hereditary {P : Value → Prop} (hP : Value.Hereditary P) {o : Op}
    {vs : List Value} (hvs : ∀ v ∈ vs, P v) {w : Value} (h : o.apply vs = .ok w) : P w := by
  rcases o.cases_scalar with rfl | rfl | ⟨c, orders, rfl⟩ | rfl | ⟨d, orders, rfl⟩ | ⟨k, rfl⟩ |
    ⟨l, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | (rfl | rfl) | ho
  · cases h
    exact hP.tuple hvs
  · simp only [Op.apply] at h
    split at h
    · cases h; exact hP.str _
    · cases h
  · simp only [Op.apply] at h
    split at h
    · cases h; exact hP.bool _
    · cases h
  · simp only [Op.apply] at h
    split at h
    · cases h; exact hP.bool _
    · cases h
  · simp only [Op.apply] at h
    split at h
    · cases h
      rename_i _ xs
      have hxs := (hP.list xs).1 (hvs _ (by simp))
      exact (hP.list _).2 fun v hv => hxs v (mem_sortByKeys hv)
    · cases h
  · cases h
  · exact hP.listOp hvs h
  · exact hP.mapOp hvs h
  · exact hP.setOp hvs h
  all_goals try (simp only [Op.apply] at h; split at h
                 · cases h; exact hvs _ (by simp)
                 · cases h)
  · rcases Op.view_apply h with rfl | h | h
    · exact hvs _ (by simp)
    · obtain ⟨s, rfl⟩ := Op.apply_scalar rfl h
      cases s
      · exact hP.int _
      · exact hP.float _
      · exact hP.bool _
      · exact hP.str _
    · exact hP.listOp hvs h
  · obtain ⟨s, rfl⟩ := Op.apply_scalar ho h
    cases s
    · exact hP.int _
    · exact hP.float _
    · exact hP.bool _
    · exact hP.str _

/-! ## Operations in the world -/

/-- What an operation gives from its operands' values in a world, and the world it leaves:
an operation on the world reads and writes it (std.io), and every other one computes its
value and leaves the world as it is. -/
def Op.run (o : Op) (vs : List Value) (w : World) : Except Fault (Value × World) :=
  match o with
  | .world k => k.run vs w
  | o => (·, w) <$> o.apply vs

theorem Op.run_of_ne {o : Op} (h : ∀ k, o ≠ .world k) (vs : List Value) (w : World) :
    o.run vs w = (·, w) <$> o.apply vs := by
  cases o <;> first | rfl | exact absurd rfl (h _)

/-- The values an operation on the world gives: `()`, a string, a list of strings, or a
handle. -/
theorem WorldOp.run_value {k : WorldOp} {vs : List Value} {w w' : World} {v : Value}
    (h : k.run vs w = .ok (v, w')) :
    v = .unit ∨ (∃ s, v = .str s) ∨ (∃ ss : List String, v = .list (ss.map .str)) ∨
      ∃ u i, v = .handle u i := by
  unfold WorldOp.run at h
  split at h <;> (try cases h)
  · exact .inl rfl
  · exact .inl rfl
  · exact .inr (.inr (.inl ⟨_, rfl⟩))
  · exact .inr (.inl ⟨_, rfl⟩)
  · exact .inr (.inr (.inr ⟨_, _, rfl⟩))

/-- What a property that values inherit from their parts holds of operands, and of `()`, it
holds of the value an operation gives in any world. -/
theorem Op.run_hereditary {P : Value → Prop} (hP : Value.Hereditary P) (hu : P .unit) {o : Op}
    {vs : List Value} (hvs : ∀ v ∈ vs, P v) {w w' : World} {v : Value}
    (h : o.run vs w = .ok (v, w')) : P v := by
  cases o
  case world k =>
    rcases WorldOp.run_value h with rfl | ⟨s, rfl⟩ | ⟨ss, rfl⟩ | ⟨u, i, rfl⟩
    · exact hu
    · exact hP.str s
    · exact (hP.list _).2 fun u hu' => by
        obtain ⟨s, -, rfl⟩ := List.mem_map.1 hu'
        exact hP.str s
    · exact hP.handle u i
  all_goals
    simp only [Op.run] at h
    cases ha : Op.apply _ vs with
    | error e => rw [ha] at h; cases h
    | ok a =>
      rw [ha] at h; cases h
      exact Op.apply_hereditary hP hvs ha

/-- An operation on the world fails only by being stuck, and any other one as its value does. -/
theorem Op.run_error {o : Op} {vs : List Value} {w : World} {e : Fault}
    (h : o.run vs w = .error e) : e = .stuck ∨ o.apply vs = .error e := by
  cases o
  case world k =>
    left
    change k.run vs w = .error e at h
    unfold WorldOp.run at h
    split at h <;> cases h <;> rfl
  all_goals
    right
    simp only [Op.run] at h
    cases ha : Op.apply _ vs with
    | error e' => rw [ha] at h; cases h; rfl
    | ok a => rw [ha] at h; cases h

/-- An operation leaves the world as it is, unless it is one on the world. -/
theorem Op.run_world {o : Op} (h : ∀ k, o ≠ .world k) {vs : List Value} {w w' : World} {v : Value}
    (hr : o.run vs w = .ok (v, w')) : w' = w ∧ o.apply vs = .ok v := by
  rw [Op.run_of_ne h] at hr
  cases ha : o.apply vs with
  | error e => rw [ha] at hr; cases hr
  | ok a => rw [ha] at hr; cases hr; exact ⟨rfl, rfl⟩

/-! ## Positions -/

/-- Two lists of the same length whose elements a relation pairs, position by
position. -/
inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : Forall₂ R [] []
  | cons {x : α} {y : β} {xs : List α} {ys : List β} :
      R x y → Forall₂ R xs ys → Forall₂ R (x :: xs) (y :: ys)

section

variable {α β : Type}

theorem positionsFrom_names (i : Nat) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (positionsFrom i xs).map Prod.fst = (positionsFrom i ys).map Prod.fst
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [positionsFrom, List.map_cons, List.cons.injEq, true_and]
    exact positionsFrom_names (i + 1) xs ys (by simpa using h)
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

theorem positionsFrom_map (f : α → β) (i : Nat) :
    ∀ xs : List α, positionsFrom i (xs.map f) = (positionsFrom i xs).map fun (n, x) => (n, f x)
  | [] => rfl
  | x :: xs => by simp [positionsFrom, positionsFrom_map f (i + 1) xs]

/-- The element a position names, looked up through `f`. -/
theorem lookup_positionsFrom_map (f : α → β) (i : Nat) (n : Name) :
    ∀ xs : List α, (positionsFrom i (xs.map f)).lookup n = ((positionsFrom i xs).lookup n).map f
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, positionsFrom, List.lookup_cons]
    split <;> simp [lookup_positionsFrom_map f (i + 1) n xs]

/-- A position names, in two lists that a relation pairs, elements that it
pairs. -/
theorem lookup_positionsFrom_forall₂ {R : α → β → Prop} (i : Nat) (n : Name) :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → ∀ {y : β},
      (positionsFrom i ys).lookup n = some y →
        ∃ x, (positionsFrom i xs).lookup n = some x ∧ R x y
  | [], [], .nil, _, h => nomatch h
  | x :: _, _ :: _, .cons hxy hrest, y, h => by
    simp only [positionsFrom] at h ⊢
    by_cases hn : n = tupleField i
    · subst hn
      simp only [List.lookup_cons_self, Option.some.injEq] at h ⊢
      exact ⟨x, rfl, h ▸ hxy⟩
    · rw [lookup_cons_ne hn] at h ⊢
      exact lookup_positionsFrom_forall₂ (i + 1) n hrest h

/-- Writing the element a position names keeps a list of positions, with that
element replaced, and the relation with the other list when the new element is
paired with the old one's partner. -/
theorem assocSet_positionsFrom_forall₂ {R : α → β → Prop} (i : Nat) (n : Name) {x' : α} :
    ∀ {xs : List α} {ys : List β}, Forall₂ R xs ys → ∀ {y : β},
      (positionsFrom i ys).lookup n = some y → R x' y →
        ∃ xs', assocSet (positionsFrom i xs) n x' = positionsFrom i xs' ∧ Forall₂ R xs' ys
  | [], [], .nil, _, h, _ => nomatch h
  | x :: xs, _ :: _, .cons hxy hrest, y, h, hx' => by
    simp only [positionsFrom] at h ⊢
    by_cases hn : n = tupleField i
    · subst hn
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      subst h
      exact ⟨x' :: xs, by simp [positionsFrom, assocSet], .cons hx' hrest⟩
    · rw [lookup_cons_ne hn] at h
      obtain ⟨xs', h', hr⟩ := assocSet_positionsFrom_forall₂ (i + 1) n hrest h hx'
      exact ⟨x :: xs', by simp [positionsFrom, assocSet, hn, h'], .cons hxy hr⟩

end

end Stilt
