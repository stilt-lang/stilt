import Stilt.Panics.Overflow

/-!
# Operations that overflow on no run

An operation that `Op.overflowFreeOn` keeps never panics with `overflow`
(effects.overflow-effect): whatever it computes from operands that fit their types, as a
well-typed program's do, fits its type, and operands that don't are stuck, which no
well-typed program is (`IntTy.within`). `n / 2` fits, since only `MIN / -1` overflows, a
shift by an amount below the width doesn't check its operand, `a.min(b)` is one of its
operands, and a remainder is below its divisor (`Op.apply_quiet`).
-/

namespace Stilt

namespace IntTy

/-- A quotient of an operand of the type by a divisor other than `0` and `-1`, not
negative on an unsigned type, fits the type: only `MIN / -1` overflows
(numbers.integer-panics). -/
theorem contains_tdiv {k : IntTy} {a b : Int} (ha : k.Contains a) (hb0 : b ≠ 0) (hb1 : b ≠ -1)
    (hu : k.signed = false → 0 ≤ b) : k.Contains (a.tdiv b) := by
  by_cases h1 : b.natAbs = 1
  · have : b = 1 := by omega
    subst this
    simpa using ha
  · have h2 : 2 ≤ b.natAbs := by omega
    have hlt : (a.tdiv b).natAbs ≤ a.natAbs / 2 := by
      rw [Int.natAbs_tdiv]; exact Nat.div_le_div_left h2 (by decide)
    obtain ⟨hlo, hhi⟩ := ha
    cases hs : k.signed
    · have h0 : 0 ≤ a := by simp only [min, hs, ↓reduceIte, Bool.false_eq_true] at hlo; omega
      have := Int.tdiv_nonneg h0 (hu hs)
      cases k <;> simp only [Contains, min, max, signed, bits, ↓reduceIte,
        Bool.false_eq_true] at hlo hhi hs ⊢ <;> omega
    · cases k <;> simp only [Contains, min, max, signed, bits, ↓reduceIte,
        Bool.false_eq_true] at hlo hhi hs ⊢ <;> omega

/-- So does the Euclidean quotient, which is the truncated one or one away from it. -/
theorem contains_ediv {k : IntTy} {a b : Int} (ha : k.Contains a) (hb0 : b ≠ 0) (hb1 : b ≠ -1)
    (hu : k.signed = false → 0 ≤ b) : k.Contains (a / b) := by
  by_cases h1 : b.natAbs = 1
  · have : b = 1 := by omega
    subst this
    simpa using ha
  · have h2 : 2 ≤ b.natAbs := by omega
    have hlt : (a.tdiv b).natAbs ≤ a.natAbs / 2 := by
      rw [Int.natAbs_tdiv]; exact Nat.div_le_div_left h2 (by decide)
    have he := @Int.tdiv_eq_ediv a b
    have hsg : b.sign = 1 ∨ b.sign = -1 := by
      rcases Int.lt_trichotomy b 0 with h | h | h
      · exact .inr (Int.sign_eq_neg_one_of_neg h)
      · exact absurd h hb0
      · exact .inl (Int.sign_eq_one_of_pos h)
    obtain ⟨hlo, hhi⟩ := ha
    cases hs : k.signed
    · have h0 : 0 ≤ a := by simp only [min, hs, ↓reduceIte, Bool.false_eq_true] at hlo; omega
      have := Int.ediv_nonneg h0 (hu hs)
      have := Int.ediv_le_self b h0
      cases k <;> simp only [Contains, min, max, signed, bits, ↓reduceIte,
        Bool.false_eq_true] at hlo hhi hs ⊢ <;> omega
    · split at he <;>
        cases k <;> simp only [Contains, min, max, signed, bits, ↓reduceIte,
          Bool.false_eq_true] at hlo hhi hs ⊢ <;> omega

/-- A Euclidean remainder lies below its divisor, so the divisor's type holds it. -/
theorem contains_emod {k : IntTy} {a b : Int} (hb : k.Contains b) (hb0 : b ≠ 0) :
    k.Contains (a % b) := by
  have h0 := Int.emod_nonneg a hb0
  have h1 := Int.emod_lt a hb0
  obtain ⟨hlo, hhi⟩ := hb
  cases k <;> simp only [Contains, min, max, signed, bits, ↓reduceIte,
    Bool.false_eq_true] at hlo hhi ⊢ <;> omega

/-- A saturated result fits its type. -/
theorem contains_saturate (k : IntTy) (x : Int) : k.Contains (Max.max k.min (Min.min k.max x)) := by
  unfold Contains min max
  cases k <;> simp [signed, bits] <;> omega

/-- A count of at most 64 bits fits `i64`. -/
theorem contains_small {n : Int} (h0 : 0 ≤ n) (h : n ≤ 64) : IntTy.i64.Contains n := by
  simp only [Contains, min, max, signed, bits, ↓reduceIte]
  omega

theorem contains_count {n : Nat} (h : n ≤ 64) : IntTy.i64.Contains n :=
  contains_small (by omega) (by omega)

theorem bits_le (k : IntTy) : k.bits ≤ 64 := by
  cases k <;> decide

end IntTy

/-- A result that is no panic of the kind `overflow`. -/
def NoOverflow {α : Type} (x : Except Fault α) : Prop :=
  ∀ k, x = .error (.panic k) → k ≠ .overflow

namespace NoOverflow

variable {α β : Type}

theorem ok (a : α) : NoOverflow (Except.ok a : Except Fault α) := fun _ h => by cases h

theorem stuck : NoOverflow (Except.error .stuck : Except Fault α) := fun _ h => by cases h

theorem panic {k : PanicKind} (hk : k ≠ .overflow) :
    NoOverflow (Except.error (.panic k) : Except Fault α) := fun _ h => by cases h; exact hk

theorem map {x : Except Fault α} (f : α → β) (h : NoOverflow x) : NoOverflow (f <$> x) :=
  fun k hk => by
    cases x with
    | ok a => cases hk
    | error e => exact h k (by simpa [Functor.map, Except.map] using hk)

theorem ite {c : Prop} [Decidable c] {x y : Except Fault α} (hx : NoOverflow x)
    (hy : NoOverflow y) : NoOverflow (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem orStuck (o : Option α) : NoOverflow (Stilt.orStuck o) := by
  cases o
  · exact stuck
  · exact ok _

theorem onList {l : Value} {f : List Value → Except Fault Value} (h : ∀ xs, NoOverflow (f xs)) :
    NoOverflow (Stilt.onList l f) := by
  unfold Stilt.onList; split
  · exact h _
  · exact stuck

theorem onMap {m : Value} {f : List (Value × Value) → Option Value → Except Fault Value}
    (h : ∀ es d, NoOverflow (f es d)) : NoOverflow (Stilt.onMap m f) := by
  unfold Stilt.onMap; split
  · exact h _ _
  · exact stuck

theorem onSet {s : Value} {f : List Value → Except Fault Value} (h : ∀ ks, NoOverflow (f ks)) :
    NoOverflow (Stilt.onSet s f) := by
  unfold Stilt.onSet; split
  · exact h _
  · exact stuck

theorem check {k : IntTy} {n : Int} (h : k.Contains n) : NoOverflow (k.check n) := by
  simp only [IntTy.check, h, ↓reduceIte]
  exact ok _

/-- An operation that can only overflow, and doesn't, can't panic. -/
theorem calm {x : Except Fault α} {ov : Bool} (hc : Calm x) (h : NoOverflow x) : Calm x ov :=
  fun k hk => absurd (hc k hk).1 (h k hk)

end NoOverflow

/-- Closes a goal `NoOverflow x` whose `x` is built of values, panics of other kinds and
matches on operands. -/
macro "noOverflow" : tactic => `(tactic| repeat (first
  | exact NoOverflow.ok _
  | exact NoOverflow.stuck
  | exact NoOverflow.panic (by decide)
  | exact NoOverflow.orStuck _
  | apply NoOverflow.map
  | (apply NoOverflow.onList; intro)
  | (apply NoOverflow.onMap; intro _ _)
  | (apply NoOverflow.onSet; intro)
  | split))

theorem ListOp.apply_noOverflow {l : ListOp} (hov : l.overflowFree = true) (vs : List Value) :
    NoOverflow (l.apply vs) := by
  unfold ListOp.apply
  split <;> first | (simp [ListOp.overflowFree] at hov; done) | noOverflow

theorem MapOp.apply_noOverflow {m : MapOp} (hov : m.overflowFree = true) (vs : List Value) :
    NoOverflow (m.apply vs) := by
  unfold MapOp.apply
  split <;> first
    | (simp [MapOp.overflowFree] at hov; done)
    | (unfold Entries.index; noOverflow)
    | noOverflow

theorem SetOp.apply_noOverflow {m : SetOp} (hov : m.overflowFree = true) (vs : List Value) :
    NoOverflow (m.apply vs) := by
  unfold SetOp.apply
  split <;> first | (simp [SetOp.overflowFree] at hov; done) | noOverflow

theorem Op.compute_noOverflow {o : Op} (hov : o.overflowFree = true) (ss : List Scalar) :
    NoOverflow (o.compute ss) := by
  unfold Op.compute
  split <;> first
    | (simp [Op.overflowFree] at hov; done)
    | (unfold Str.slice; noOverflow)
    | noOverflow

/-- An operation that can't overflow whatever its operands doesn't. -/
theorem Op.apply_noOverflow {o : Op} (hov : o.overflowFree = true) (vs : List Value) :
    NoOverflow (o.apply vs) := by
  unfold Op.apply
  split
  · exact NoOverflow.ok _
  · noOverflow
  · exact NoOverflow.panic (by simpa [Op.overflowFree] using hov)
  · noOverflow
  · noOverflow
  · noOverflow
  · exact ListOp.apply_noOverflow (by simpa [Op.overflowFree] using hov) vs
  · exact MapOp.apply_noOverflow (by simpa [Op.overflowFree] using hov) vs
  · exact SetOp.apply_noOverflow (by simpa [Op.overflowFree] using hov) vs
  · split
    · exact NoOverflow.ok _
    · unfold Op.applyScalars; split
      · exact NoOverflow.map _ (Op.compute_noOverflow (o := .slice) rfl _)
      · exact NoOverflow.stuck
    · exact ListOp.apply_noOverflow rfl _
    · exact NoOverflow.stuck
  · split
    · exact NoOverflow.ok _
    · exact NoOverflow.stuck
  · unfold Op.applyScalars
    split
    · exact NoOverflow.map _ (Op.compute_noOverflow hov _)
    · exact NoOverflow.stuck

/-! ## Operations whose result fits when their operands do -/

namespace IntTy

/-- `/` and `%` overflow only for `MIN` by `-1`, on a signed type. -/
theorem arith_quiet (k : IntTy) {o : Arith} (ho : o.divides = true) (x : Int) {y : Int}
    (hy : k.signed = true → y ≠ -1) : NoOverflow (k.arith o x y) := by
  have hdz : NoOverflow (Except.error (.panic .divideByZero) : Except Fault Int) :=
    NoOverflow.panic (by decide)
  cases o <;> simp only [Arith.divides, reduceCtorEq] at ho <;> simp only [IntTy.arith, IntTy.within]
  all_goals
    split
    · rename_i hc
      have hu : k.signed = false → 0 ≤ y := fun hs => by
        have := hc.2.1; simp only [min, hs, ↓reduceIte, Bool.false_eq_true] at this; exact this
      have hy' : y ≠ -1 := by
        cases hs : k.signed
        · have := hu hs; omega
        · exact hy hs
      split
      · exact hdz
      · rename_i h0
        have hq := contains_tdiv hc.1 h0 hy' hu
        first | exact NoOverflow.check hq | (simp only [hq, ↓reduceIte]; exact NoOverflow.ok _)
    · exact NoOverflow.stuck

/-- A shift by an amount from 0 to one below the width checks nothing. -/
theorem shift_quiet (k : IntTy) (o : Shift) (x : Int) {y : Int} (hy : 0 ≤ y ∧ y < k.bits) :
    NoOverflow (k.shift o x y) := by
  unfold IntTy.shift
  simp only [show ¬(y < 0 ∨ (k.bits : Int) ≤ y) by omega, ↓reduceIte]
  exact NoOverflow.ok _

/-- `min`, `max`, the saturating methods and the counts of bits fit their type, and so do
`div_euclid` and `rem_euclid` by a divisor other than `0` and `-1`. -/
theorem method_quiet (k : IntTy) {m : IntMethod} (x : Int) {y : Int}
    (h : m.bounded = true ∨ ((m = .divEuclid ∨ m = .remEuclid) ∧ y ≠ 0 ∧ y ≠ -1)) :
    NoOverflow (k.method m x y) := by
  have hb := k.bits_le
  cases m <;> simp only [IntMethod.bounded, reduceCtorEq, or_false, false_or, Bool.false_eq_true,
    true_and, false_and] at h <;> simp only [IntTy.method, IntTy.within]
  · split
    · rename_i hc; split <;> exact NoOverflow.check (by first | exact hc.1 | exact hc.2)
    · exact NoOverflow.stuck
  · split
    · rename_i hc; split <;> exact NoOverflow.check (by first | exact hc.1 | exact hc.2)
    · exact NoOverflow.stuck
  · exact NoOverflow.check (contains_saturate k _)
  · exact NoOverflow.check (contains_saturate k _)
  all_goals first
    | (split
       · rename_i hc
         have hu : k.signed = false → 0 ≤ y := fun hs => by
           have := hc.2.1; simp only [min, hs, ↓reduceIte, Bool.false_eq_true] at this; exact this
         simp only [IntTy.euclid, h.1, h.2, and_false, false_and, ↓reduceIte]
         first
           | exact NoOverflow.check (contains_ediv hc.1 h.1 h.2 hu)
           | exact NoOverflow.check (contains_emod hc.2 h.1)
       · exact NoOverflow.stuck)
    | (apply NoOverflow.check
       have := List.countP_le_length (p := (k.bitsOf x).testBit) (l := List.range k.bits)
       simp only [List.length_range] at this
       exact contains_count (by omega))
    | (apply NoOverflow.check
       split
       · exact contains_count hb
       · rename_i h0
         have hlt : (k.bitsOf x).log2 < k.bits := (Nat.log2_lt h0).2 (k.toBits x).isLt
         exact contains_small (by omega) (by omega))
    | (apply NoOverflow.check; apply contains_count
       cases hf : (List.range k.bits).find? (k.bitsOf x).testBit with
       | none => simpa using hb
       | some i =>
         have := List.mem_range.1 (List.mem_of_find?_eq_some hf)
         simp only [Option.getD_some]; omega)

end IntTy

/-- What an operation on scalars computes, when its operands are scalars, or stuck. -/
theorem Op.apply_cases {o : Op} (ho : o.scalar = true) (vs : List Value) :
    (∃ ss, vs = ss.map Scalar.value ∧ o.apply vs = Scalar.value <$> o.compute ss) ∨
      o.apply vs = .error .stuck := by
  rw [Op.apply_of_scalar ho, Op.applyScalars]
  split
  · rename_i ss hss
    refine .inl ⟨ss, ?_, rfl⟩
    induction vs generalizing ss with
    | nil => simp at hss; subst hss; rfl
    | cons v vs ih =>
      simp only [List.mapM_cons, bind, Option.bind] at hss
      cases hv : v.scalar? with
      | none => simp [hv] at hss
      | some s =>
        cases hr : vs.mapM Value.scalar? with
        | none => simp [hv, hr] at hss
        | some ss' =>
          simp [hv, hr] at hss; subst hss
          cases v <;> simp [Value.scalar?] at hv <;> subst hv <;> simp [Scalar.value, ih ss' hr]
  · exact .inr rfl

/-- An operation on scalars that overflows on none of the scalars its operands are doesn't. -/
theorem Op.apply_quiet_of {o : Op} (ho : o.scalar = true) {vs : List Value}
    (h : ∀ ss, vs = ss.map Scalar.value → NoOverflow (o.compute ss)) : NoOverflow (o.apply vs) := by
  rcases Op.apply_cases ho vs with ⟨ss, rfl, he⟩ | he
  · rw [he]; exact NoOverflow.map _ (h ss rfl)
  · rw [he]; exact NoOverflow.stuck

/-- Splits the scalars of an operation's operands into none, one, two, and more, of each
kind. -/
macro "scalars" ss:ident : tactic => `(tactic|
  rcases $ss:ident with _ | ⟨s₁, _ | ⟨s₂, _ | ⟨s₃, _⟩⟩⟩ <;>
    (try cases s₁) <;> (try cases s₂) <;> first | exact NoOverflow.stuck | skip)

/-- An operation that `Op.overflowFreeBy d` keeps, on operands whose second is the integer
`d` when `d` is one, doesn't overflow (effects.overflow-effect). -/
theorem Op.apply_quiet {o : Op} {d : Option Int} (h : o.overflowFreeBy d = true)
    {vs : List Value} (hd : ∀ n, d = some n → ∃ u, vs = [u, .int n]) : NoOverflow (o.apply vs) := by
  by_cases hf : o.overflowFree = true
  · exact Op.apply_noOverflow hf vs
  have hlast : ∀ n, d = some n → ∀ x y, vs = [.int x, .int y] → y = n := fun n hn x y hv => by
    obtain ⟨u, hu⟩ := hd n hn
    rw [hv] at hu; cases hu; rfl
  cases o <;> simp only [Op.overflowFree, Bool.not_eq_true, reduceCtorEq] at hf
  all_goals first
    | (simp [Op.overflowFreeBy, Op.overflowFree, hf] at h; done)
    | skip
  case arith a k =>
    cases a <;> simp only [Op.overflowFreeBy, Op.overflowFree, Bool.false_eq_true] at h
    all_goals
      refine Op.apply_quiet_of rfl fun ss hss => ?_
      scalars ss
      refine NoOverflow.map _ (IntTy.arith_quiet k rfl _ fun hs => ?_)
      cases d with
      | none => simp [hs] at h
      | some n =>
        have := hlast n rfl _ _ (by simpa [Scalar.value] using hss)
        simp only [hs, Bool.not_true, Option.isSome_some, bne_iff_ne, ne_eq, Option.some.injEq,
          Bool.true_and, Bool.false_or] at h
        omega
  case shift o k _ =>
    cases d with
    | none => simp [Op.overflowFreeBy, Op.overflowFree] at h
    | some n =>
      simp only [Op.overflowFreeBy, decide_eq_true_eq] at h
      refine Op.apply_quiet_of rfl fun ss hss => ?_
      scalars ss
      have := hlast n rfl _ _ (by simpa [Scalar.value] using hss)
      exact NoOverflow.map _ (IntTy.shift_quiet k o _ (by omega))
  case intMethod m k =>
    refine Op.apply_quiet_of rfl fun ss hss => ?_
    scalars ss
    · exact NoOverflow.map _ (IntTy.method_quiet k _ (by
        cases m <;> cases d <;> simp_all [Op.overflowFreeBy, IntMethod.bounded]))
    · exact NoOverflow.map _ (IntTy.method_quiet k _ (by
        have hl := fun n hn => hlast n hn _ _ (by simpa [Scalar.value] using hss)
        cases m <;> cases d <;> simp_all [Op.overflowFreeBy, IntMethod.bounded]))

end Stilt
