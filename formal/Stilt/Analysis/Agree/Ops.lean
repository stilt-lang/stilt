import Stilt.Analysis.Agree.Basic
import Stilt.Panics.Sites

/-!
# What an operation's facts mean

The facts `opValFacts` gives an operation's value hold of the value it computes (`opValFacts_holds`),
those `cmpFacts` gives a comparison hold where it gives that truth (`cmpFacts_holds`), and an
operation that `verifyOp` proves can't panic with that kind (`verifyOp_sound`).
-/

namespace Stilt

theorem neg_apply {k : IntTy} {x v : Value} (h : Op.apply (.neg k) [x] = .ok v) :
    ∃ a n, x = .int a ∧ k.check (-a) = .ok n ∧ v = .int n := by
  cases x <;>
    simp [Op.apply, Op.applyScalars, Value.scalar?, Op.compute, Functor.map, Except.map, Scalar.value] at h
  rename_i a
  cases hr : k.check (-a) with
  | error f => rw [hr] at h; simp at h
  | ok r => rw [hr] at h; simp at h; exact ⟨a, r, rfl, hr, h.symm⟩

theorem convert_apply {k k' : IntTy} {x v : Value} (h : Op.apply (.convert k k') [x] = .ok v) :
    ∃ a, x = .int a ∧ v = .int a := by
  cases x <;>
    simp [Op.apply, Op.applyScalars, Value.scalar?, Op.compute, Functor.map, Except.map, Scalar.value] at h
  exact ⟨_, rfl, h.symm⟩

theorem push_apply {l x v : Value} (h : Op.apply (.list .push) [l, x] = .ok v) :
    ∃ xs, l = .list xs ∧ v = .list (xs ++ [x]) := by
  cases l <;> simp [Op.apply, ListOp.apply, onList, Value.list?] at h
  exact ⟨_, rfl, h.symm⟩

theorem IntTy.check_ok {k : IntTy} {n m : Int} (h : k.check n = .ok m) : m = n ∧ k.Contains n := by
  simp only [IntTy.check] at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

theorem IntTy.interval_has {k : IntTy} {n : Int} (h : k.Contains n) : k.interval.Has n :=
  ⟨fun _ hl => by cases hl; exact h.1, fun _ hh => by cases hh; exact h.2⟩

theorem length_two {α : Type} {vs : List α} {a b : Option (Term × Int)}
    (h : vs.length = [a, b].length) : ∃ x y, vs = [x, y] := by
  rcases vs with _ | ⟨x, _ | ⟨y, _ | _⟩⟩ <;> simp at h
  exact ⟨x, y, rfl⟩

theorem length_one {α : Type} {vs : List α} {a : Option (Term × Int)} (h : vs.length = [a].length) :
    ∃ x, vs = [x] := by
  rcases vs with _ | ⟨x, _ | _⟩ <;> simp at h
  exact ⟨x, rfl⟩

variable {G H : Facts} {ν : Valuation}

theorem Holds.relateLin {i : Interval} {l : Option (Term × Int)} (h : H.Holds ν)
    (hl : ∀ t c, l = some (t, c) → i.Has (ν .res - ν t - c)) : (relateLin i l H).Holds ν := by
  cases l with
  | none => exact h
  | some p => obtain ⟨t, c⟩ := p; exact h.relate (hl t c rfl)

/-- What `opValFacts` says of an operation's value holds of the value it computes. -/
theorem opValFacts_holds {o : Op} {d : Nat} {lins : List (Option (Term × Int))} {vs : List Value}
    {r : Value} (hG : G.Holds ν) (hz : ν .zero = 0) (hlen : vs.length = lins.length)
    (hr : o.apply vs = .ok r) (hres : ν .res = r.intOr) (hreslen : ν .reslen = r.lenOr)
    (hops : ∀ i (h : i < vs.length), ν (.opnd (d + i)) = vs[i].intOr ∧
      ν (.opndLen (d + i)) = vs[i].lenOr) : (opValFacts o d lins G).Holds ν := by
  have ia := hG.interval hz (.opnd d)
  have ib := hG.interval hz (.opnd (d + 1))
  have two : ∀ x y, vs = [x, y] → ν (.opnd d) = x.intOr ∧ ν (.opnd (d + 1)) = y.intOr :=
    fun x y h => by subst h; exact ⟨by simpa using (hops 0 (by simp)).1, (hops 1 (by simp)).1⟩
  unfold opValFacts
  split
  · obtain ⟨x, y, rfl⟩ := length_two hlen
    obtain ⟨ha, hb⟩ := two x y rfl
    obtain ⟨a, b, n, rfl, rfl, hn, rfl⟩ := arith_apply hr
    obtain ⟨rfl, hc⟩ := IntTy.check_ok hn
    simp only [Value.intOr] at ha hb hres
    rw [ha] at ia; rw [hb] at ib
    refine Holds.relateLin (Holds.relateLin ((hG.relate ?_).relate ?_) ?_) ?_
    · rw [hres, hz]; simpa using Interval.Has.add ia ib
    · rw [hres, hz]; simpa using IntTy.interval_has hc
    · intro t c hl
      have := hG.linAt hl
      rw [show ν .res - ν t - c = b by omega]; exact ib
    · intro t c hl
      have := hG.linAt hl
      rw [show ν .res - ν t - c = a by omega]; exact ia
  · obtain ⟨x, y, rfl⟩ := length_two hlen
    obtain ⟨ha, hb⟩ := two x y rfl
    obtain ⟨a, b, n, rfl, rfl, hn, rfl⟩ := arith_apply hr
    obtain ⟨rfl, hc⟩ := IntTy.check_ok hn
    simp only [Value.intOr] at ha hb hres
    rw [ha] at ia; rw [hb] at ib
    refine Holds.relateLin ((hG.relate ?_).relate ?_) ?_
    · rw [hres, hz]; simpa using Interval.Has.sub ia ib
    · rw [hres, hz]; simpa using IntTy.interval_has hc
    · intro t c hl
      have := hG.linAt hl
      rw [show ν .res - ν t - c = -b by omega]; exact Interval.Has.neg ib
  · obtain ⟨x, y, rfl⟩ := length_two hlen
    obtain ⟨ha, hb⟩ := two x y rfl
    obtain ⟨a, b, n, rfl, rfl, hn, rfl⟩ := arith_apply hr
    obtain ⟨rfl, hc⟩ := IntTy.check_ok hn
    simp only [Value.intOr] at ha hb hres
    rw [ha] at ia; rw [hb] at ib
    refine (hG.relate ?_).relate ?_
    · rw [hres, hz]; simpa using Interval.Has.mul ia ib
    · rw [hres, hz]; simpa using IntTy.interval_has hc
  · obtain ⟨x, y, rfl⟩ := length_two hlen
    obtain ⟨a, b, n, rfl, rfl, hn, rfl⟩ := arith_apply hr
    simp only [Value.intOr] at hres
    simp only [IntTy.arith, IntTy.within] at hn
    split at hn
    · split at hn
      · cases hn
      · obtain ⟨rfl, hc⟩ := IntTy.check_ok hn
        exact hG.relate (by rw [hres, hz]; simpa using IntTy.interval_has hc)
    · cases hn
  · obtain ⟨x, y, rfl⟩ := length_two hlen
    obtain ⟨a, b, n, rfl, rfl, hn, rfl⟩ := arith_apply hr
    simp only [Value.intOr] at hres
    simp only [IntTy.arith, IntTy.within] at hn
    split at hn
    · rename_i hab
      split at hn
      · cases hn
      · split at hn
        · cases hn
          exact hG.relate (by rw [hres, hz]; simpa using IntTy.interval_has (IntTy.contains_tmod hab.1 b))
        · cases hn
    · cases hn
  · obtain ⟨x, rfl⟩ := length_one hlen
    have ha : ν (.opnd d) = x.intOr := by simpa using (hops 0 (by simp)).1
    obtain ⟨a, n, rfl, hn, rfl⟩ := neg_apply hr
    obtain ⟨rfl, hc⟩ := IntTy.check_ok hn
    simp only [Value.intOr] at ha hres
    rw [ha] at ia
    refine (hG.relate ?_).relate ?_
    · rw [hres, hz]; simpa using Interval.Has.neg ia
    · rw [hres, hz]; simpa using IntTy.interval_has hc
  · obtain ⟨x, rfl⟩ := length_one hlen
    have ha : ν (.opnd d) = x.intOr := by simpa using (hops 0 (by simp)).1
    obtain ⟨a, rfl, rfl⟩ := convert_apply hr
    simp only [Value.intOr] at ha hres
    exact hG.equate (by rw [hres, ha]; omega)
  · obtain ⟨x, rfl⟩ := length_one hlen
    have ha : ν (.opndLen d) = x.lenOr := by simpa using (hops 0 (by simp)).2
    obtain ⟨xs, rfl, rfl⟩ := len_apply hr
    simp only [Value.lenOr, Value.intOr] at ha hres
    exact hG.equate (by rw [hres, ha]; omega)
  · obtain ⟨x, y, rfl⟩ := length_two hlen
    have ha : ν (.opndLen d) = x.lenOr := by simpa using (hops 0 (by simp)).2
    obtain ⟨xs, rfl, rfl⟩ := push_apply hr
    simp only [Value.lenOr, List.length_append, List.length_singleton] at ha hreslen
    refine (hG.insert ?_).insert ?_ <;> simp only [Diff.Holds] <;> omega
  · exact hG

theorem nonzeroPick_holds {d i j : Nat} {lins : List (Option (Term × Int))} (hG : G.Holds ν)
    (h : H.Holds ν) (hz : ν .zero = 0) (hne : ν (.opnd (d + j)) = 0 → ν (.opnd (d + i)) ≠ 0) :
    (nonzeroPick G d i j lins H).Holds ν := by
  unfold nonzeroPick
  split
  · rename_i t hj hi
    have h0 := hG.linAt hj
    have h1 := hG.linAt hi
    rw [hz] at h0
    have := hne (by omega)
    exact (h.addNonzero (by omega)).addNonzero this
  · exact h

/-- What `cmpFacts` says where a comparison gives `truth` holds. -/
theorem cmpFacts_holds {c : Cmp} {d : Nat} {lins : List (Option (Term × Int))} {x y : Int}
    (hG : G.Holds ν) (hz : ν .zero = 0) (ha : ν (.opnd d) = x) (hb : ν (.opnd (d + 1)) = y)
    {truth : Bool} (ht : c.ints x y = truth) : (cmpFacts c d lins G truth).Holds ν := by
  cases c <;> cases truth <;> simp only [Cmp.ints, beq_iff_eq, bne_iff_ne, ne_eq,
    decide_eq_true_eq, decide_eq_false_iff_not, beq_eq_false_iff_ne,
    bne_eq_false_iff_eq] at ht <;> simp only [cmpFacts, nonzeroBy]
  all_goals first
    | exact hG.insert (by simp only [Diff.Holds]; omega)
    | exact (hG.insert (by simp only [Diff.Holds]; omega)).insert (by simp only [Diff.Holds]; omega)
    | exact nonzeroPick_holds hG (nonzeroPick_holds hG hG hz (by simp only [Nat.add_zero] at *; omega))
        hz (by simp only [Nat.add_zero] at *; omega)

theorem arith_apply_panic {o : Arith} {k : IntTy} {x y : Value} {p : PanicKind}
    (h : Op.apply (.arith o k) [x, y] = .error (.panic p)) :
    ∃ a b, x = .int a ∧ y = .int b ∧ k.arith o a b = .error (.panic p) := by
  cases x <;> cases y <;>
    simp [Op.apply, Op.applyScalars, Value.scalar?, Op.compute, Functor.map, Except.map, Scalar.value] at h
  rename_i a b
  cases hr : k.arith o a b with
  | error f => rw [hr] at h; simp at h; exact ⟨a, b, rfl, rfl, by rw [hr, h]⟩
  | ok r => rw [hr] at h; simp at h

theorem neg_apply_panic {k : IntTy} {x : Value} {p : PanicKind}
    (h : Op.apply (.neg k) [x] = .error (.panic p)) :
    ∃ a, x = .int a ∧ k.check (-a) = .error (.panic p) := by
  cases x <;>
    simp [Op.apply, Op.applyScalars, Value.scalar?, Op.compute, Functor.map, Except.map, Scalar.value] at h
  rename_i a
  cases hr : k.check (-a) with
  | error f => rw [hr] at h; simp at h; exact ⟨a, rfl, by rw [hr, h]⟩
  | ok r => rw [hr] at h; simp at h

theorem shift_apply_panic {o : Shift} {k k' : IntTy} {x y : Value} {p : PanicKind}
    (h : Op.apply (.shift o k k') [x, y] = .error (.panic p)) :
    ∃ a b, x = .int a ∧ y = .int b ∧ k.shift o a b = .error (.panic p) := by
  cases x <;> cases y <;>
    simp [Op.apply, Op.applyScalars, Value.scalar?, Op.compute, Functor.map, Except.map, Scalar.value] at h
  rename_i a b
  cases hr : k.shift o a b with
  | error f => rw [hr] at h; simp at h; exact ⟨a, b, rfl, rfl, by rw [hr, h]⟩
  | ok r => rw [hr] at h; simp at h

theorem IntTy.check_panic {k : IntTy} {n : Int} {p : PanicKind} (h : k.check n = .error (.panic p)) :
    p = .overflow ∧ ¬ k.Contains n := by
  simp only [IntTy.check] at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, by assumption⟩

/-- A division or remainder that panics: by zero, or with a quotient its type doesn't hold, of
operands it holds. -/
theorem IntTy.divides_panic {k : IntTy} {o : Arith} (ho : o = .div ∨ o = .rem) {a b : Int}
    {p : PanicKind} (h : k.arith o a b = .error (.panic p)) :
    (p = .divideByZero ∧ b = 0) ∨
      (p = .overflow ∧ k.Contains a ∧ k.Contains b ∧ b ≠ 0 ∧ ¬ k.Contains (a.tdiv b)) := by
  rcases ho with rfl | rfl <;> simp only [IntTy.arith, IntTy.within] at h <;> split at h
  · rename_i hab
    split at h
    · cases h; exact .inl ⟨rfl, by assumption⟩
    · obtain ⟨rfl, hc⟩ := IntTy.check_panic h
      exact .inr ⟨rfl, hab.1, hab.2, by assumption, hc⟩
  · cases h
  · rename_i hab
    split at h
    · cases h; exact .inl ⟨rfl, by assumption⟩
    · split at h
      · cases h
      · cases h; exact .inr ⟨rfl, hab.1, hab.2, by assumption, by assumption⟩
  · cases h

/-- A quotient of operands of the type, by a divisor other than zero, fits the type unless it
is signed, the dividend is the type's least value and the divisor −1. -/
theorem IntTy.contains_tdiv_of {k : IntTy} {a b : Int} (ha : k.Contains a) (hb : k.Contains b)
    (hb0 : b ≠ 0) (h : k.signed = false ∨ a ≠ k.min ∨ b ≠ -1) : k.Contains (a.tdiv b) := by
  by_cases hb1 : b = -1
  · subst hb1
    rw [Int.tdiv_neg, Int.tdiv_one]
    obtain ⟨hlo, hhi⟩ := ha
    obtain ⟨blo, bhi⟩ := hb
    rcases h with h | h | h
    · cases k <;> simp only [Contains, min, max, signed, bits, ↓reduceIte,
        Bool.false_eq_true, reduceCtorEq] at h blo ⊢ <;> omega
    · cases k <;> simp only [Contains, min, max, signed, bits, ↓reduceIte,
        Bool.false_eq_true] at h hlo hhi blo ⊢ <;> omega
    · exact absurd rfl h
  · refine IntTy.contains_tdiv ha hb0 hb1 fun hs => ?_
    have := hb.1
    simp only [min, hs, Bool.false_eq_true, ↓reduceIte] at this
    exact this

theorem nonzeroDivisor_sound {i : Nat} {l : Option (Term × Int)} (hv : nonzeroDivisor G i l = true)
    (hG : G.Holds ν) (hz : ν .zero = 0) : ν (.opnd i) ≠ 0 := by
  have hi := hG.interval hz (.opnd i)
  unfold nonzeroDivisor at hv
  simp only [Bool.or_eq_true, Option.any_eq_true, decide_eq_true_eq] at hv
  rcases hv with (⟨c, hc, h1⟩ | ⟨c, hc, h1⟩) | hv
  · have := hi.1 c hc; omega
  · have := hi.2 c hc; omega
  · split at hv
    · rename_i t hl
      have := hG.linAt hl
      simp only [decide_eq_true_eq] at hv
      have := hG.2 t hv
      omega
    · cases hv

/-- A sum, difference or product whose exact interval lies within its type doesn't overflow. -/
theorem exact_sound {o : Arith} {t : IntTy} {a b : Int} {i : Interval}
    (ho : o = .add ∨ o = .sub ∨ o = .mul)
    (hi : i.Has (match o with | .add => a + b | .sub => a - b | _ => a * b))
    (hw : i.within t.min t.max = true) :
    Op.apply (.arith o t) [.int a, .int b] ≠ .error (.panic .overflow) := by
  intro hp
  obtain ⟨a', b', ha, hb, he⟩ := arith_apply_panic hp
  cases ha; cases hb
  have hc := hi.within hw
  rcases ho with rfl | rfl | rfl <;> simp only [IntTy.arith] at he <;>
    exact (IntTy.check_panic he).2 hc

/-- An operation that `verifyOp` proves can't panic with a kind doesn't (facts.proved-divisions
and facts.proved-overflow). -/
theorem verifyOp_sound {o : Op} {d : Nat} {lins : List (Option (Term × Int))} {vs : List Value}
    {k : PanicKind} (hv : verifyOp o d lins G k = true) (hG : G.Holds ν) (hz : ν .zero = 0)
    (hlen : vs.length = lins.length)
    (hops : ∀ i (h : i < vs.length), ν (.opnd (d + i)) = vs[i].intOr) :
    o.apply vs ≠ .error (.panic k) := by
  have ia := hG.interval hz (.opnd d)
  have ib := hG.interval hz (.opnd (d + 1))
  have two : ∀ x y, vs = [x, y] → ν (.opnd d) = x.intOr ∧ ν (.opnd (d + 1)) = y.intOr :=
    fun x y h => by subst h; exact ⟨by simpa using hops 0 (by simp), hops 1 (by simp)⟩
  have divZero : ∀ o' t, (o' = .div ∨ o' = .rem) → ∀ x y, vs = [x, y] →
      nonzeroDivisor G (d + 1) (linOf lins 1) = true →
      Op.apply (.arith o' t) [x, y] ≠ .error (.panic .divideByZero) := by
    intro o' t ho x y hvs hnz hp
    obtain ⟨a, b, rfl, rfl, he⟩ := arith_apply_panic hp
    rcases IntTy.divides_panic ho he with ⟨-, rfl⟩ | ⟨h, -⟩
    · have := nonzeroDivisor_sound hnz hG hz
      rw [(two _ _ hvs).2] at this
      exact this rfl
    · cases h
  have divOver : ∀ o' t, (o' = .div ∨ o' = .rem) → ∀ x y, vs = [x, y] →
      (!t.signed || (G.interval (.opnd d)).1.any (t.min < ·) ||
        (G.interval (.opnd (d + 1))).1.any (-1 < ·) ||
          (G.interval (.opnd (d + 1))).2.any (· < -1)) = true →
      Op.apply (.arith o' t) [x, y] ≠ .error (.panic .overflow) := by
    intro o' t ho x y hvs hc hp
    obtain ⟨ha, hb⟩ := two _ _ hvs
    obtain ⟨a, b, rfl, rfl, he⟩ := arith_apply_panic hp
    simp only [Value.intOr] at ha hb
    rcases IntTy.divides_panic ho he with ⟨h, -⟩ | ⟨-, hca, hcb, hb0, hct⟩
    · cases h
    · refine hct (IntTy.contains_tdiv_of hca hcb hb0 ?_)
      simp only [Bool.or_eq_true, Bool.not_eq_true', Option.any_eq_true, decide_eq_true_eq] at hc
      rcases hc with ((h | ⟨c, hc, h1⟩) | ⟨c, hc, h1⟩) | ⟨c, hc, h1⟩
      · exact .inl h
      · exact .inr (.inl (by have := ia.1 c hc; omega))
      · exact .inr (.inr (by have := ib.1 c hc; omega))
      · exact .inr (.inr (by have := ib.2 c hc; omega))
  have exact' : ∀ o' t, (o' = .add ∨ o' = .sub ∨ o' = .mul) → ∀ x y, vs = [x, y] →
      (match o' with
        | .add => (G.interval (.opnd d)).add (G.interval (.opnd (d + 1)))
        | .sub => (G.interval (.opnd d)).sub (G.interval (.opnd (d + 1)))
        | _ => (G.interval (.opnd d)).mul (G.interval (.opnd (d + 1)))).within t.min t.max = true →
      Op.apply (.arith o' t) [x, y] ≠ .error (.panic .overflow) := by
    intro o' t ho x y hvs hw hp
    obtain ⟨ha, hb⟩ := two _ _ hvs
    obtain ⟨a, b, rfl, rfl, he⟩ := arith_apply_panic hp
    simp only [Value.intOr] at ha hb
    rw [ha] at ia; rw [hb] at ib
    rcases ho with rfl | rfl | rfl
    · exact exact_sound (.inl rfl) (Interval.Has.add ia ib) hw hp
    · exact exact_sound (.inr (.inl rfl)) (Interval.Has.sub ia ib) hw hp
    · exact exact_sound (.inr (.inr rfl)) (Interval.Has.mul ia ib) hw hp
  unfold verifyOp at hv
  split at hv
  · obtain ⟨x, y, rfl⟩ := length_two hlen; exact divZero _ _ (.inl rfl) x y rfl hv
  · obtain ⟨x, y, rfl⟩ := length_two hlen; exact divZero _ _ (.inr rfl) x y rfl hv
  · obtain ⟨x, y, rfl⟩ := length_two hlen; exact divOver _ _ (.inl rfl) x y rfl hv
  · obtain ⟨x, y, rfl⟩ := length_two hlen; exact divOver _ _ (.inr rfl) x y rfl hv
  · obtain ⟨x, y, rfl⟩ := length_two hlen; exact exact' _ _ (.inl rfl) x y rfl hv
  · obtain ⟨x, y, rfl⟩ := length_two hlen; exact exact' _ _ (.inr (.inl rfl)) x y rfl hv
  · obtain ⟨x, y, rfl⟩ := length_two hlen; exact exact' _ _ (.inr (.inr rfl)) x y rfl hv
  · obtain ⟨x, rfl⟩ := length_one hlen
    have ha : ν (.opnd d) = x.intOr := by simpa using hops 0 (by simp)
    intro hp
    obtain ⟨a, rfl, he⟩ := neg_apply_panic hp
    simp only [Value.intOr] at ha
    rw [ha] at ia
    exact (IntTy.check_panic he).2 ((Interval.Has.neg ia).within hv)
  · obtain ⟨x, y, rfl⟩ := length_two hlen
    obtain ⟨-, hb⟩ := two x y rfl
    intro hp
    obtain ⟨a, b, rfl, rfl, he⟩ := shift_apply_panic hp
    simp only [Value.intOr] at hb
    rw [hb] at ib
    simp only [IntTy.shift] at he
    split at he
    · have := ib.within hv; omega
    · cases he
  · cases hv

end Stilt
