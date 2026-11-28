import Stilt.Soundness.Forms
import Stilt.Soundness.Maps
import Stilt.Soundness.Keys

/-!
# Built-in operations

An operation applied to values of the types its signature takes gives a value
of the type it gives, or panics; it is never stuck. A tuple holds its
operands, each at its position, and `.0` on a tuple reads the element at that
position (types.field-access).
-/

namespace Stilt

section

variable {D : Decls}

/-- Values of the types at their positions are a tuple's elements. -/
theorem ValuesAt.elems {η : REnv} :
    ∀ {vs : List Value} {τs : List Ty}, ValuesAt D η vs τs → Elems.Typed D vs (closeTys η τs)
  | _, _, .nil => .nil
  | _, _, .cons hv hvs => .cons hv hvs.elems

theorem IntOk.arith (k : IntTy) (o : Arith) {a b : Int} (ha : k.Contains a) (hb : k.Contains b) :
    IntOk k (k.arith o a b) := by
  cases o <;> simp only [IntTy.arith, IntTy.within, ha, hb, and_self, ↓reduceIte]
  · exact .check k _
  · exact .check k _
  · exact .check k _
  · split
    · exact .inr ⟨_, rfl⟩
    · exact .check k _
  · split
    · exact .inr ⟨_, rfl⟩
    · split
      · exact .inl ⟨_, rfl, IntTy.contains_tmod ha b⟩
      · exact .inr ⟨_, rfl⟩

theorem IntOk.shift (k : IntTy) (o : Shift) (a b : Int) : IntOk k (k.shift o a b) := by
  unfold IntTy.shift
  by_cases hb : b < 0 ∨ (k.bits : Int) ≤ b
  · simp only [hb, ↓reduceIte]
    exact .inr ⟨_, rfl⟩
  · simp only [hb, ↓reduceIte]
    exact .inl ⟨_, rfl, k.ofBits_contains _⟩

/-- An operation on scalars that computes a scalar of the type, or panics, is
sound. -/
theorem Applied.compute {o : Op} (ho : o.scalar = true) {ss : List Scalar} {σ : STy}
    (h : (∃ s, o.compute ss = .ok s ∧ Value.Typed D s.value σ) ∨
      ∃ k, o.compute ss = .error (.panic k)) :
    Applied D (o.apply (ss.map Scalar.value)) σ := by
  rw [Op.apply_scalars ho]
  rcases h with ⟨s, hs, ht⟩ | ⟨k, hk⟩
  · exact .inl ⟨_, by rw [hs]; rfl, ht⟩
  · exact .inr ⟨k, by rw [hk]; rfl⟩

theorem Applied.int {o : Op} (ho : o.scalar = true) {ss : List Scalar} {k : IntTy} {x : Except Fault Int}
    (hc : o.compute ss = .int <$> x) (h : IntOk k x) :
    Applied D (o.apply (ss.map Scalar.value)) (.int k) := by
  refine Applied.compute ho ?_
  rw [hc]
  rcases h with ⟨n, rfl, hn⟩ | ⟨p, rfl⟩
  · exact .inl ⟨.int n, rfl, .int hn⟩
  · exact .inr ⟨p, rfl⟩

theorem Applied.scalar {o : Op} (ho : o.scalar = true) {ss : List Scalar} {s : Scalar} {σ : STy}
    (hc : o.compute ss = .ok s) (h : Value.Typed D s.value σ) :
    Applied D (o.apply (ss.map Scalar.value)) σ :=
  Applied.compute ho (.inl ⟨s, hc, h⟩)

theorem Applied.float {o : Op} (ho : o.scalar = true) {ss : List Scalar} {x : FloatVal} {k : FloatTy}
    (hc : o.compute ss = .ok (.float x)) (h : x.type = k) :
    Applied D (o.apply (ss.map Scalar.value)) (.float k) :=
  Applied.scalar ho hc (h ▸ .float)

/-! ## Operands of each signature

Each lemma reads typed operands of one shape as scalars, so that an operation's
case only says what it computes from them. -/

variable {η : REnv} {vs : List Value} {o : Op} {σ : STy}

/-- A method of an integer type gives an integer of the type it gives, or panics. -/
theorem IntOk.euclid (k : IntTy) (a b r : Int) : IntOk k (k.euclid a b r) := by
  unfold IntTy.euclid
  split
  · exact .inr ⟨_, rfl⟩
  · split
    · exact .inr ⟨_, rfl⟩
    · exact .check _ _

theorem IntOk.method (k : IntTy) (m : IntMethod) {a b : Int} (ha : k.Contains a)
    (hb : m.second k = some k → k.Contains b) : IntOk (m.result k) (k.method m a b) := by
  cases m <;> simp only [IntTy.method, IntMethod.result] <;>
    first
    | exact .check _ _
    | (simp only [IntTy.within, ha, hb rfl, and_self, ↓reduceIte]
       first | exact .check _ _ | exact .euclid _ _ _ _)
    | exact .euclid _ _ _ _
    | (split
       · exact .check _ _
       · split
         · exact .inr ⟨_, rfl⟩
         · exact .check _ _)
    | (split
       · exact .inr ⟨_, rfl⟩
       · exact .check _ _)

/-- Two integer operands, each of its type. -/
theorem ints_apply {k k' : IntTy} (h : ValuesAt D η vs [.int k, .int k'])
    (f : ∀ a b, k.Contains a → k'.Contains b →
      Applied D (o.apply ([Scalar.int a, .int b].map Scalar.value)) σ) :
    Applied D (o.apply vs) σ := by
  obtain ⟨v, v', rfl, hv, hv'⟩ := h.two_inv
  obtain ⟨a, rfl, ha⟩ := hv.int_inv
  obtain ⟨b, rfl, hb⟩ := hv'.int_inv
  exact f a b ha hb

theorem int_apply {k : IntTy} (h : ValuesAt D η vs [.int k])
    (f : ∀ a, k.Contains a → Applied D (o.apply ([Scalar.int a].map Scalar.value)) σ) :
    Applied D (o.apply vs) σ := by
  obtain ⟨v, rfl, hv⟩ := h.one_inv
  obtain ⟨a, rfl, ha⟩ := hv.int_inv
  exact f a ha

theorem float_apply {k : FloatTy} (h : ValuesAt D η vs [.float k])
    (f : ∀ x, x.type = k → Applied D (o.apply ([Scalar.float x].map Scalar.value)) σ) :
    Applied D (o.apply vs) σ := by
  obtain ⟨v, rfl, hv⟩ := h.one_inv
  obtain ⟨x, rfl, hx⟩ := hv.float_inv
  exact f x hx

theorem floats_apply {k : FloatTy} (h : ValuesAt D η vs [.float k, .float k])
    (f : ∀ x y, x.type = k → y.type = k →
      Applied D (o.apply ([Scalar.float x, .float y].map Scalar.value)) σ) :
    Applied D (o.apply vs) σ := by
  obtain ⟨v, v', rfl, hv, hv'⟩ := h.two_inv
  obtain ⟨x, rfl, hx⟩ := hv.float_inv
  obtain ⟨y, rfl, hy⟩ := hv'.float_inv
  exact f x y hx hy

theorem bool_apply (h : ValuesAt D η vs [.bool])
    (f : ∀ a, Applied D (o.apply ([Scalar.bool a].map Scalar.value)) σ) :
    Applied D (o.apply vs) σ := by
  obtain ⟨v, rfl, hv⟩ := h.one_inv
  obtain ⟨a, rfl⟩ := hv.bool_inv
  exact f a

theorem bools_apply (h : ValuesAt D η vs [.bool, .bool])
    (f : ∀ a b, Applied D (o.apply ([Scalar.bool a, .bool b].map Scalar.value)) σ) :
    Applied D (o.apply vs) σ := by
  obtain ⟨v, v', rfl, hv, hv'⟩ := h.two_inv
  obtain ⟨a, rfl⟩ := hv.bool_inv
  obtain ⟨b, rfl⟩ := hv'.bool_inv
  exact f a b

theorem str_apply (h : ValuesAt D η vs [.str])
    (f : ∀ s, Applied D (o.apply ([Scalar.str s].map Scalar.value)) σ) :
    Applied D (o.apply vs) σ := by
  obtain ⟨v, rfl, hv⟩ := h.one_inv
  obtain ⟨s, rfl⟩ := hv.str_inv
  exact f s

theorem strs2_apply (h : ValuesAt D η vs [.str, .str])
    (f : ∀ s t, Applied D (o.apply ([Scalar.str s, .str t].map Scalar.value)) σ) :
    Applied D (o.apply vs) σ := by
  obtain ⟨v, v', rfl, hv, hv'⟩ := h.two_inv
  obtain ⟨s, rfl⟩ := hv.str_inv
  obtain ⟨t, rfl⟩ := hv'.str_inv
  exact f s t

theorem strs_inv : ∀ {vs : List Value} {n : Nat},
    ValuesAt D η vs (List.replicate n .str) → ∃ ts : List String, vs = (ts.map Scalar.str).map Scalar.value
  | [], 0, .nil => ⟨[], rfl⟩
  | _ :: _, _ + 1, .cons hv hvs => by
    obtain ⟨s, rfl⟩ := hv.str_inv
    obtain ⟨ts, rfl⟩ := strs_inv hvs
    exact ⟨s :: ts, rfl⟩

theorem mapM_str? : ∀ ts : List String, (ts.map Scalar.str).mapM Scalar.str? = some ts
  | [] => rfl
  | t :: ts => by simp [Scalar.str?, mapM_str? ts]

/-- A slice of a string is a string, or a panic. -/
theorem slice_ok (s : String) (a b : Int) :
    (∃ t, Str.slice s a b = .ok t) ∨ ∃ p, Str.slice s a b = .error (.panic p) := by
  unfold Str.slice
  split
  · exact .inr ⟨_, rfl⟩
  · split
    · exact .inl ⟨_, rfl⟩
    · exact .inr ⟨_, rfl⟩

/-! ## The operations whose cases take more than a line -/

theorem Applied.farith {a : Arith} (ha : a ≠ .rem) {k : FloatTy} (x y : FloatVal) (hx : x.type = k)
    (hy : y.type = k) :
    Applied D ((Op.farith a k).apply ([Scalar.float x, .float y].map Scalar.value)) (.float k) := by
  obtain ⟨z, hz, hzt⟩ := FloatVal.arith_some ha (hy.trans hx.symm)
  exact Applied.float rfl (by simp only [Op.compute, hz, orStuck]; rfl) (hzt.trans hx)

theorem Applied.fcompare (c : Cmp) {k : FloatTy} (x y : FloatVal) (hx : x.type = k)
    (hy : y.type = k) :
    Applied D ((Op.fcompare c k).apply ([Scalar.float x, .float y].map Scalar.value)) .bool := by
  obtain ⟨b, hb⟩ := FloatVal.compare_some c (hy.trans hx.symm)
  exact Applied.scalar (s := .bool b) rfl (by simp only [Op.compute, hb, orStuck]; rfl) .bool

theorem Applied.funary {m : FloatMethod} (hm : m.binary = false) (hn : m ≠ .isNan) {k : FloatTy}
    (x : FloatVal) (hx : x.type = k) :
    Applied D ((Op.fmethod m k).apply ([Scalar.float x].map Scalar.value)) (.float k) := by
  refine Applied.float (x := x.unary m) rfl ?_ ((FloatVal.type_unary m x).trans hx)
  cases m <;> simp_all [Op.compute, FloatMethod.binary]

theorem Applied.fbinary {m : FloatMethod} (hm : m.binary = true) {k : FloatTy} (x y : FloatVal)
    (hx : x.type = k) (hy : y.type = k) :
    Applied D ((Op.fmethod m k).apply ([Scalar.float x, .float y].map Scalar.value)) (.float k) := by
  cases m <;> simp only [FloatMethod.binary, Bool.false_eq_true] at hm
  · obtain ⟨z, hz, hzt⟩ := FloatVal.extremum_some true (hy.trans hx.symm)
    exact Applied.float rfl (by simp only [Op.compute, hz, orStuck]; rfl) (hzt.trans hx)
  · obtain ⟨z, hz, hzt⟩ := FloatVal.extremum_some false (hy.trans hx.symm)
    exact Applied.float rfl (by simp only [Op.compute, hz, orStuck]; rfl) (hzt.trans hx)

theorem Applied.concat {n : Nat} (h : ValuesAt D η vs (List.replicate n .str)) :
    Applied D (Op.concat.apply vs) .str := by
  obtain ⟨ts, rfl⟩ := strs_inv h
  exact Applied.scalar (s := .str (String.join ts)) rfl
    (by simp only [Op.compute, mapM_str?, orStuck]; rfl) .str

theorem Applied.slice (h : ValuesAt D η vs [.str, .i64, .i64]) :
    Applied D (Op.slice.apply vs) .str := by
  obtain ⟨v, rest, rfl, hv, hrest⟩ : ∃ v rest, vs = v :: rest ∧
      Value.Typed D v (Ty.str.close η) ∧ ValuesAt D η rest [.i64, .i64] := by
    cases h with
    | cons hv hrest => exact ⟨_, _, rfl, hv, hrest⟩
  obtain ⟨s, rfl⟩ := hv.str_inv
  obtain ⟨v, v', rfl, hv, hv'⟩ := hrest.two_inv
  obtain ⟨a, rfl, -⟩ := hv.int_inv
  obtain ⟨b, rfl, -⟩ := hv'.int_inv
  refine Applied.compute (ss := [.str s, .int a, .int b]) rfl ?_
  rcases slice_ok s a b with ⟨t, ht⟩ | ⟨p, hp⟩
  · exact .inl ⟨.str t, by simp only [Op.compute, ht]; rfl, .str⟩
  · exact .inr ⟨p, by simp only [Op.compute, hp]; rfl⟩

/-- A view of a part of a string or a list is the part `slice` gives
(views.making-view). -/
theorem Applied.view {τ : Ty} (hτ : τ.viewable = true) (h : ValuesAt D η vs [τ, .i64, .i64]) :
    Applied D (Op.view.apply vs) (τ.close η) := by
  cases τ <;> simp [Ty.viewable] at hτ
  · obtain ⟨u, a, b, rfl, hu, -, -⟩ := h.three_inv
    obtain ⟨s, rfl⟩ := hu.str_inv
    show Applied D (Op.slice.applyScalars _) _
    rw [← Op.apply_of_scalar rfl]
    exact Applied.slice h
  · obtain ⟨u, a, b, rfl, hu, -, -⟩ := h.three_inv
    obtain ⟨xs, rfl, -⟩ := hu.list_inv
    exact ListOp.Sig.slice.apply h

/-- `panic` panics, whatever its operands. -/
theorem Op.panic_apply {k : PanicKind} {σ : STy} : Applied D ((Op.panic k).apply vs) σ :=
  .inr ⟨k, rfl⟩

/-- An operation applied to operands of its signature's types gives a value of
the type it gives, or panics. -/
theorem Op.Sig.apply {τs : List Ty} {τ : Ty} (h : o.Sig τs τ) (hio : ∀ k, o ≠ .world k)
    (hvs : ValuesAt D η vs τs) (hkey : ∀ κ v, κ ∈ o.keyTypes τs τ →
      Value.Typed D v (κ.close η) → v.keyEq v = true) : Applied D (o.apply vs) (τ.close η) := by
  have ofBits := IntTy.ofBits_contains
  cases h with
  | world _ => exact absurd rfl (hio _)
  | tuple _ => exact .inl ⟨_, rfl, .tuple hvs.elems⟩
  | viewAll _ | copy =>
    cases hvs with
    | cons hv hnil => cases hnil; exact .inl ⟨_, rfl, hv⟩
  | @viewOf τ hτ => exact Applied.view (τ := τ) hτ hvs
  | @viewPart τ hτ =>
    cases hvs with
    | cons hv hrest => exact Applied.view (τ := τ) hτ (.cons hv hrest)
  | not => exact bool_apply hvs fun b => Applied.scalar (ss := [.bool b]) rfl rfl .bool
  | float =>
    rw [hvs.nil_inv]
    exact Applied.float (ss := []) rfl rfl (FloatVal.type_ofScientific ..)
  | neg _ => exact int_apply hvs fun _ _ => Applied.int rfl rfl (.check _ _)
  | arith => exact ints_apply hvs fun _ _ ha hb => Applied.int rfl rfl (.arith _ _ ha hb)
  | wrapping => exact ints_apply hvs fun _ _ _ _ => Applied.scalar rfl rfl (.int (ofBits _ _))
  | shift => exact ints_apply hvs fun _ _ _ _ => Applied.int rfl rfl (.shift _ _ _ _)
  | bitwise => exact ints_apply hvs fun _ _ _ _ => Applied.scalar rfl rfl (.int (ofBits _ _))
  | complement => exact int_apply hvs fun _ _ => Applied.scalar rfl rfl (.int (ofBits _ _))
  | compare => exact ints_apply hvs fun _ _ _ _ => Applied.scalar rfl rfl .bool
  | convert hmin hmax =>
    exact int_apply hvs fun _ ha => Applied.scalar rfl rfl
      (.int ⟨Int.le_trans hmin ha.1, Int.le_trans ha.2 hmax⟩)
  | wrapTo => exact int_apply hvs fun _ _ => Applied.scalar rfl rfl (.int (ofBits _ _))
  | toFloat => exact int_apply hvs fun _ _ => Applied.float rfl rfl (FloatVal.type_ofInt ..)
  | floatTo =>
    exact float_apply hvs fun _ _ => Applied.float rfl rfl (FloatVal.type_convert ..)
  | fneg =>
    exact float_apply hvs fun x hx => Applied.float rfl rfl ((FloatVal.type_neg x).trans hx)
  | farith ho => exact floats_apply hvs (Applied.farith ho)
  | fcompare => exact floats_apply hvs (Applied.fcompare _)
  | funary hm hn => exact float_apply hvs (Applied.funary hm hn)
  | fbinary hm => exact floats_apply hvs (Applied.fbinary hm)
  | fisNan => exact float_apply hvs fun _ _ => Applied.scalar rfl rfl .bool
  | bcompare => exact bools_apply hvs fun _ _ => Applied.scalar rfl rfl .bool
  | str =>
    rw [hvs.nil_inv]
    exact Applied.scalar (ss := []) rfl rfl .str
  | concat => exact Applied.concat hvs
  | showInt => exact int_apply hvs fun _ _ => Applied.scalar rfl rfl .str
  | showBool => exact bool_apply hvs fun b => Applied.scalar (ss := [.bool b]) rfl rfl .str
  | pad => exact str_apply hvs fun _ => Applied.scalar rfl rfl .str
  | inBase => exact int_apply hvs fun _ _ => Applied.scalar rfl rfl .str
  | fixed => exact float_apply hvs fun _ _ => Applied.scalar rfl rfl .str
  | @intMethod m k =>
    cases hs : m.second k with
    | none =>
      simp only [hs, Option.map_none, Option.toList_none] at hvs
      exact int_apply hvs fun a ha => Applied.int rfl rfl (.method k m ha fun h => by simp [hs] at h)
    | some k' =>
      simp only [hs, Option.map_some, Option.toList_some] at hvs
      exact ints_apply hvs fun a b ha hb => Applied.int rfl rfl (.method k m ha fun h => by
        rw [hs, Option.some.injEq] at h; exact h ▸ hb)
  | parses => exact str_apply hvs fun _ => Applied.scalar rfl rfl .bool
  | parsed => exact str_apply hvs fun s => Applied.scalar rfl rfl (.int (IntTy.contains_parsedOrZero _ s))
  | fparses => exact str_apply hvs fun _ => Applied.scalar rfl rfl .bool
  | fparsed => exact str_apply hvs fun _ => Applied.float rfl rfl (FloatVal.type_convert ..)
  | scientific => exact float_apply hvs fun _ _ => Applied.scalar rfl rfl .str
  | len => exact str_apply hvs fun _ => Applied.int rfl rfl (.check _ _)
  | isEmpty => exact str_apply hvs fun _ => Applied.scalar rfl rfl .bool
  | slice => exact Applied.slice hvs
  | strMap => exact str_apply hvs fun _ => Applied.scalar rfl rfl .str
  | replace =>
    obtain ⟨u, v, w, rfl, hu, hv, hw⟩ := hvs.three_inv
    obtain ⟨s, rfl⟩ := hu.str_inv
    obtain ⟨a, rfl⟩ := hv.str_inv
    obtain ⟨b, rfl⟩ := hw.str_inv
    exact Applied.scalar (ss := [.str s, .str a, .str b]) rfl rfl .str
  | charCount => exact str_apply hvs fun _ => Applied.int rfl rfl (.check _ _)
  | count => exact strs2_apply hvs fun _ _ => Applied.int rfl rfl (.check _ _)
  | search => exact strs2_apply hvs fun _ _ => Applied.scalar rfl rfl .bool
  | scompare => exact strs2_apply hvs fun _ _ => Applied.scalar rfl rfl .bool
  | strClass => exact str_apply hvs fun _ => Applied.scalar rfl rfl .bool
  | padStr =>
    obtain ⟨u, v, w, rfl, hu, hv, hw⟩ := hvs.three_inv
    obtain ⟨s, rfl⟩ := hu.str_inv
    obtain ⟨n, rfl, -⟩ := hv.int_inv
    obtain ⟨f, rfl⟩ := hw.str_inv
    exact Applied.scalar (ss := [.str s, .int n, .str f]) rfl rfl .str
  | showValue =>
    obtain ⟨v, rfl, -⟩ := hvs.one_inv
    exact .inl ⟨_, rfl, .str⟩
  | panic => exact Op.panic_apply
  | structural =>
    obtain ⟨v, w, rfl, -, -⟩ := hvs.two_inv
    exact .inl ⟨_, rfl, .bool⟩
  | sameCell =>
    obtain ⟨v, w, rfl, -, -⟩ := hvs.two_inv
    exact .inl ⟨_, rfl, .bool⟩
  | sortedByKey =>
    obtain ⟨u, w, rfl, hu, hw⟩ := hvs.two_inv
    obtain ⟨ks, rfl, -⟩ := hu.list_inv
    obtain ⟨xs, rfl, hxs⟩ := hw.list_inv
    exact .inl ⟨_, rfl, .list fun v hv => hxs v (mem_sortByKeys hv)⟩
  | list h => exact h.apply hvs
  | map h => exact h.apply hvs hkey
  | set h => exact h.apply hvs

/-- An operation on the world, on operands of its signature's types, gives a value of the
type it gives in every world, and keeps a typed world typed. -/
theorem WorldOp.Sig.run {k : WorldOp} {τs : List Ty} {τ : Ty} (h : k.Sig τs τ) (hvs : ValuesAt D η vs τs)
    {x : World} (hx : World.Typed D x) :
    ∃ v x', k.run vs x = .ok (v, x') ∧ Value.Typed D v (τ.close η) ∧ World.Typed D x' := by
  cases h with
  | @write err newline =>
    cases hvs with
    | cons hv hnil =>
      cases hnil
      obtain ⟨s, rfl⟩ := hv.str_inv
      cases err <;> exact ⟨_, _, rfl, .unit, hx⟩
  | readLine =>
    rw [hvs.nil_inv]
    exact ⟨_, _, rfl, .list fun v hv => by obtain ⟨s, -, rfl⟩ := List.mem_map.1 hv; exact .str, hx⟩
  | readAll =>
    rw [hvs.nil_inv]
    exact ⟨_, _, rfl, .str, hx⟩
  | @sharedNew u hu =>
    cases hvs with
    | cons hv hnil =>
      cases hnil
      have hc : u.close η = u.sem := Ty.close_closed η _ u hu
      refine ⟨_, _, rfl, .handle ?_, hx.push (hc ▸ hv)⟩
      show (STy.shared u.sem).Fits (.shared (u.close η))
      rw [hc]
      exact .refl _

/-- An operation applied to operands of its signature's types, in any typed world, gives a
value of the type it gives in a typed world, or panics. -/
theorem Op.Sig.run {τs : List Ty} {τ : Ty} (h : o.Sig τs τ) (hvs : ValuesAt D η vs τs) {x : World}
    (hkey : ∀ κ v, κ ∈ o.keyTypes τs τ → Value.Typed D v (κ.close η) → v.keyEq v = true)
    (hx : World.Typed D x) :
    (∃ v x', o.run vs x = .ok (v, x') ∧ Value.Typed D v (τ.close η) ∧ World.Typed D x') ∨
      ∃ k, o.run vs x = .error (.panic k) := by
  by_cases hio : ∃ k, o = .world k
  · obtain ⟨k, rfl⟩ := hio
    cases h with
    | world hk => exact .inl (hk.run hvs hx)
  · have ho : ∀ k, o ≠ .world k := fun k hk => hio ⟨k, hk⟩
    rw [Op.run_of_ne ho]
    rcases h.apply ho hvs hkey with ⟨a, ha, hat⟩ | ⟨k, hk⟩
    · exact .inl ⟨a, x, by rw [ha]; rfl, hat, hx⟩
    · exact .inr ⟨k, by rw [hk]; rfl⟩

/-- Reading and writing the world, which gives a value of `σ` in a typed world or panics in
every typed world, ends soundly. -/
theorem Eval.Ok.world {Γ : Ctx} {η : REnv} {X : Exits} {σ : STy}
    {f : World → Except Fault (Value × World)}
    (h : ∀ x, World.Typed D x → (∃ v x', f x = .ok (v, x') ∧ Value.Typed D v σ ∧ World.Typed D x') ∨
      ∃ k, f x = .error (.panic k)) :
    Eval.Ok D Γ η X (fun v => Value.Typed D v σ) (Eval.world Copy.memory f) := by
  rintro ⟨fr, x⟩ hγ
  rcases h x hγ.2 with ⟨v, x', hf, hv, hx'⟩ | ⟨k, hf⟩
  · rw [show Eval.world Copy.memory f (fr, x) = .done v (fr, x') from Eval.world_ok hf]
    exact ⟨hv, hγ.1, hx'⟩
  · rw [show Eval.world Copy.memory f (fr, x) = .fault (.panic k) (fr, x) from Eval.world_error hf]
    exact hγ

/-- A step that ends with a value, or a panic of any kind. -/
theorem Eval.Ok.ofExcept_panic {Γ : Ctx} {η : REnv} {X : Exits} {σ : STy}
    {x : Except Fault Value} (h : Applied D x σ) :
    Eval.Ok D Γ η X (fun v => Value.Typed D v σ) (Eval.ofExcept x) := by
  intro γ hγ
  rcases h with ⟨a, rfl, ha⟩ | ⟨k, rfl⟩
  · exact ⟨ha, hγ⟩
  · trivial

end

section

variable {D : Decls} {n : Nat} (hs : Sound D n) {scope : RowScope} {η : REnv}
  (hη : η.Respects scope) (θ : RowSubst) {Γ : Ctx} {fx : Effects}
include hs hη

/-- An operation that finds keys finds them of key types, whose values equal themselves. -/
theorem op_ok {o : Op} {es : List Expr} {τs : List Ty} {τ : Ty} (hD : D.WellFormed)
    (ho : o.Sig τs τ) (hes : ExprsFit D scope Γ fx es τs) (hk : o.KeysIn D τs τ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.op o es).substRows θ)) :=
  Eval.Ok.bind (ExprsFit.ok hs hη θ hes) fun _ hvs => Eval.Ok.world fun _ hx =>
    ho.run hvs (fun _ _ hκ hv => hv.keyEq_of_key hD (hk _ hκ)) hx

theorem view_ok {es : List Expr} {τs : List Ty} {τ : Ty} (ho : Op.view.Sig τs τ)
    (hes : ExprsFit D scope Γ fx es τs) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.view es).substRows θ)) :=
  Eval.Ok.bind (ExprsFit.ok hs hη θ hes) fun _ hvs => Eval.Ok.ofExcept_panic (ho.apply (fun _ h => by cases h) hvs
    fun _ _ h => by simp [Op.keyTypes] at h)

theorem elem_ok {e : Expr} {τs : List Ty} {f : Name} {τ : Ty}
    (he : HasType D scope Γ fx e (.tuple τs)) (hf : (positions τs).lookup f = some τ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
      (eval D Copy.memory (n + 1) ((Expr.field e f).substRows θ)) :=
  Eval.Ok.bind (hs he hη θ) fun _ hv =>
    Eval.Ok.ofExcept ((PathTyped.elem (closeTys_lookup η hf) .nil).get hv)

end

end Stilt
