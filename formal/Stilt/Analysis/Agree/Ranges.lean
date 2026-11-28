import Stilt.Analysis.Agree.For
import Stilt.Panics.Ranges

/-!
# `for` loops over ranges

A range `a..b` evaluated, the values a `for` runs its body on lie within its bounds: no less
than the first's linear form, and, for `a..b`, below the second's (`range_iter`), as they were
when the range was evaluated; a turn that leaves the first's term no greater and the second's no
less keeps them (`rangeQ_keeps`); and the body starts with those bounds on the loop's variable
(`Facts.Holds.forRange`), facts.for-loops' bounds of its counter, read on each value.
-/

namespace Stilt

/-- The terms of a range's bounds, at a frame, no greater than `p.1` for the first and no less
than `p.2` for the second. -/
def rangeQ (lo hi : Option (Term × Int)) (st : List Value) (p : Int × Int) (fr : Copy.Frame) :
    Prop :=
  (∀ t c, lo = some (t, c) → fr.nu st .unit t ≤ p.1) ∧
    (∀ t c, hi = some (t, c) → p.2 ≤ fr.nu st .unit t)

/-- A value within a range's bounds, `p.1 + c` the first and `p.2 + c` the second. -/
def rangeOk (lo hi : Option (Term × Int)) (p : Int × Int) (v : Value) : Prop :=
  (∀ t c, lo = some (t, c) → p.1 + c ≤ v.intOr) ∧ (∀ t c, hi = some (t, c) → v.intOr < p.2 + c)

theorem Term.steady_nu {x : Name} {W Ls : List Name} {lower : Bool} {t : Term}
    (h : t.steady x W Ls lower = true) (fr : Copy.Frame) (st st' : List Value) (v v' : Value) :
    fr.nu st v t = fr.nu st' v' t := by
  cases t <;> simp_all [Term.steady, Copy.Frame.nu]

theorem Term.steady_ne {x : Name} {W Ls : List Name} {lower : Bool} {t : Term}
    (h : t.steady x W Ls lower = true) : t.name? ≠ some x := by
  cases t <;> simp_all [Term.steady, Term.name?]

theorem lenOr_nonneg (v : Value) : 0 ≤ v.lenOr := by
  cases v <;> simp [Value.lenOr]

/-- A turn that keeps the frame keeps the bounds' terms where `steady` says. -/
theorem rangeQ_keeps {lo hi : Option (Term × Int)} {st : List Value} {p : Int × Int} {x : Name}
    {W Ls : List Name} {v u : Value} {fr rest : Copy.Frame}
    (hlo : ∀ t c, lo = some (t, c) → t.steady x W Ls true = true)
    (hhi : ∀ t c, hi = some (t, c) → t.steady x W Ls false = true)
    (k : Frame.Keeps W Ls ((x, v) :: fr) ((x, u) :: rest)) (hq : rangeQ lo hi st p fr) :
    rangeQ lo hi st p rest := by
  have kt : Frame.Keeps W Ls fr rest := k.tail
  refine ⟨fun t c ht => ?_, fun t c ht => ?_⟩
  · have hs := hlo t c ht
    have := hq.1 t c ht
    cases t with
    | zero => exact this
    | val y =>
      simp only [Term.steady, Bool.and_eq_true, decide_eq_true_eq] at hs
      simp only [Copy.Frame.nu] at this ⊢
      rw [kt.lookup hs.2]; exact this
    | len y =>
      simp only [Term.steady, Bool.and_eq_true, decide_eq_true_eq, ite_true] at hs
      simp only [Copy.Frame.nu] at this ⊢
      rw [kt.lookup hs.2]; exact this
    | _ => simp [Term.steady] at hs
  · have hs := hhi t c ht
    have := hq.2 t c ht
    cases t with
    | zero => exact this
    | val y =>
      simp only [Term.steady, Bool.and_eq_true, decide_eq_true_eq] at hs
      simp only [Copy.Frame.nu] at this ⊢
      rw [kt.lookup hs.2]; exact this
    | len y =>
      simp only [Term.steady, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true,
        ite_false] at hs
      simp only [Copy.Frame.nu] at this ⊢
      cases hl : fr.lookup y with
      | none =>
        simp only [hl, Option.getD_none, Value.lenOr] at this
        exact Int.le_trans this (lenOr_nonneg _)
      | some w =>
        rw [hl] at this
        cases w with
        | list vs =>
          obtain ⟨vs', h', hlen⟩ := kt.lookup_list hs.2 hl
          rw [h']; simpa [Value.lenOr, hlen] using this
        | _ => simp only [Option.getD_some, Value.lenOr] at this; exact Int.le_trans this (lenOr_nonneg _)
    | _ => simp [Term.steady] at hs

namespace Facts

theorem Holds.forRange {C : Facts} {x : Name} {lo hi : Option (Term × Int)} {ν : Valuation}
    (h : C.Holds ν) (hlo : ∀ t c, lo = some (t, c) → ν t + c ≤ ν (.val x))
    (hhi : ∀ t c, hi = some (t, c) → ν (.val x) < ν t + c) : (C.forRange x lo hi).Holds ν := by
  unfold Facts.forRange
  have h1 : (match lo with | some (t, c) => C.insert ⟨t, .val x, -c⟩ | none => C).Holds ν := by
    cases lo with
    | none => exact h
    | some p =>
      obtain ⟨t, c⟩ := p
      exact h.insert (by have := hlo t c rfl; simp only [Diff.Holds]; omega)
  cases hi with
  | none => exact h1
  | some p =>
    obtain ⟨t, c⟩ := p
    exact h1.insert (by have := hhi t c rfl; simp only [Diff.Holds]; omega)

end Facts

/-- The facts a `for`'s body starts with over a range: its head facts, on no term of `x`, and
`x`'s bounds, read on a value within them. -/
theorem forRange_start {J : Facts} {x : Name} {lo hi : Option (Term × Int)} {W Ls : List Name}
    {st : List Value} {p : Int × Int} {v : Value} {fr : Copy.Frame}
    (hlo : ∀ t c, lo = some (t, c) → t.steady x W Ls true = true)
    (hhi : ∀ t c, hi = some (t, c) → t.steady x W Ls false = true)
    (hv : rangeOk lo hi p v) (hq : rangeQ lo hi st p fr) (hI : (J.unbind x).Holds (fr.nu st .unit)) :
    ((J.unbind x).forRange x lo hi).Holds (Copy.Frame.nu ((x, v) :: fr) st .unit) := by
  obtain ⟨hk1, hk2⟩ := hv
  have hx : Copy.Frame.nu ((x, v) :: fr) st .unit (.val x) = v.intOr := by
    simp [Copy.Frame.nu]
  refine hI.bindUnbound.forRange (fun t c ht => ?_) (fun t c ht => ?_) <;> rw [hx] <;>
    rw [Copy.Frame.nu_bind (Term.steady_ne (by first | exact hlo t c ht | exact hhi t c ht))]
  · have := hq.1 t c ht; have := hk1 t c ht; omega
  · have := hq.2 t c ht; have := hk2 t c ht; omega

theorem range_apply' {inclusive : Bool} {vs : List Value} {v : Value}
    (h : Op.apply (.list (.range inclusive)) vs = .ok v) :
    ∃ a b, vs = [.int a, .int b] ∧ v = .list (rangeValues a b inclusive) := by
  rcases vs with _ | ⟨u, _ | ⟨u', _ | ⟨_, _⟩⟩⟩
  · simp [Op.apply, ListOp.apply] at h
  · simp [Op.apply, ListOp.apply] at h
  · obtain ⟨a, b, rfl, rfl, rfl⟩ := range_apply h
    exact ⟨a, b, rfl, rfl⟩
  · simp [Op.apply, ListOp.apply] at h

section

variable {D : Decls} {w : WriteBack}

local notation "M" => Copy.memoryWith w

/-- The bounds of a range, with the facts after its operands giving their linear forms. -/
def rangeLo (L : Bool) (d : Nat) (F : Facts) (x : Name) (body : Expr) (es : List Expr) :
    Option (Term × Int) :=
  ((anOps L d F es).post.linAt d (linOf (anOps L d F es).lins 0)).filter
    fun p => p.1.steady x body.writes body.resizes true

def rangeHi (L : Bool) (d : Nat) (F : Facts) (x : Name) (body : Expr) (inclusive : Bool)
    (es : List Expr) : Option (Term × Int) :=
  if inclusive then none else
    ((anOps L d F es).post.linAt (d + 1) (linOf (anOps L d F es).lins 1)).filter
      fun p => p.1.steady x body.writes body.resizes false

/-- What a range's value meets: there are bounds that its operands' terms meet, as they are
where it ends, and every value of it lies within them. -/
def RangeVal (lo hi : Option (Term × Int)) (st : List Value) (r : Value) (s : Copy.State) : Prop :=
  ∃ p, rangeQ lo hi st p s.1 ∧ ∀ vs, r = .list vs → ∀ v ∈ vs, rangeOk lo hi p v

/-- The step of a range, its operands met their facts: its values lie within its bounds. -/
theorem range_step {L : Bool} {d : Nat} {F : Facts} {x : Name} {body : Expr} {inclusive : Bool}
    {es : List Expr} {st vs : List Value} {s₁ : Copy.State} {B C : Copy.State → Prop}
    (hd : st.length = d) (hvs : (anOps L d F es).Done st es.length vs s₁) :
    (Eval.world M (Op.run (.list (.range inclusive)) vs) s₁).Sat
      (RangeVal (rangeLo L d F x body es) (rangeHi L d F x body inclusive es) st) B C := by
  obtain ⟨fr, wd⟩ := s₁
  rw [Eval.world_copy, Op.run_of_ne (fun _ h => by cases h)]
  cases hap : Op.apply (.list (.range inclusive)) vs with
  | error e => cases e <;> trivial
  | ok r =>
    obtain ⟨a, b, rfl, rfl⟩ := range_apply' hap
    simp only [Functor.map, Except.map]
    refine ⟨(((rangeLo L d F x body es).map fun q => fr.nu st .unit q.1).getD 0,
      ((rangeHi L d F x body inclusive es).map fun q => fr.nu st .unit q.1).getD 0),
      ⟨fun t c h => by rw [h]; exact Int.le_refl _, fun t c h => by rw [h]; exact Int.le_refl _⟩,
      fun vs' hvs' v hv => ?_⟩
    cases hvs'
    obtain ⟨k', rfl, hlo, hhi⟩ := mem_rangeValues hv
    have hpost := hvs.2
    have ha : fr.nu (st ++ [.int a, .int b]) .unit (.opnd d) = a := by
      subst hd; simp [Copy.Frame.nu, Value.intOr, List.getD_eq_getElem?_getD]
    have hb : fr.nu (st ++ [.int a, .int b]) .unit (.opnd (d + 1)) = b := by
      subst hd; simp [Copy.Frame.nu, Value.intOr, List.getD_eq_getElem?_getD]
    refine ⟨fun t c ht => ?_, fun t c ht => ?_⟩
    · rw [ht]
      show _ ≤ k'
      simp only [Option.map_some, Option.getD_some]
      unfold rangeLo at ht
      obtain ⟨hl, hs⟩ := Option.filter_eq_some_iff.1 ht
      have := hpost.linAt hl
      rw [ha, Term.steady_nu (by simpa using hs) fr _ st _ .unit] at this
      omega
    · rw [ht]
      show k' < _
      simp only [Option.map_some, Option.getD_some]
      unfold rangeHi at ht
      split at ht
      · cases ht
      · rename_i hinc
        obtain ⟨hl, hs⟩ := Option.filter_eq_some_iff.1 ht
        have := hpost.linAt hl
        rw [hb, Term.steady_nu (by simpa using hs) fr _ st _ .unit] at this
        have := hhi (by simpa using hinc)
        omega

/-- A range evaluated: every value lies within the bounds its operands' facts give, as their
terms are where it ends. -/
theorem range_iter {k : Nat} (hA : AgreeRun (evalR D M k) (eval D M k)) {L : Bool} {d : Nat}
    {F : Facts} {x : Name} {body : Expr} {inclusive : Bool} {es : List Expr} {st : List Value}
    {s : Copy.State} (hok : (anOps L d F es).ok = true) (hd : st.length = d)
    (hF : F.Holds (s.1.nu st .unit)) :
    ((Eval.list (eval D M k) es >>= fun vs => Eval.world M (Op.run (.list (.range inclusive)) vs))
      >>= Eval.asList) s |>.Sat
      (fun vs s₁ => ∃ p, rangeQ (rangeLo L d F x body es) (rangeHi L d F x body inclusive es) st p
        s₁.1 ∧ ∀ v ∈ vs, rangeOk (rangeLo L d F x body es) (rangeHi L d F x body inclusive es) p v)
      (fun _ => True) (fun _ => True) := by
  refine (((agree_list hA es L d F st s hok hd hF).bind (B' := fun _ => True)
      (C' := fun _ => True) (fun _ _ => trivial) (fun _ _ => trivial) fun vs s₁ hvs =>
        Eval.Agree.same (range_step (x := x) (body := body) hd hvs)).bind (f' := Eval.asList)
      (f := Eval.asList) (fun _ h => h) (fun _ h => h) fun r s₂ hr => Eval.Agree.same ?_).2
  obtain ⟨p, hq, hv⟩ := hr
  cases r with
  | list vs => exact ⟨p, hq, hv vs rfl⟩
  | _ => trivial

/-- A `for`'s first bound, when its iterable is a range, as the analysis reads it. -/
abbrev forLo (L : Bool) (d : Nat) (F : Facts) (x : Name) (body e : Expr) : Option (Term × Int) :=
  if e.isRange then (an L d F e).lo.filter (·.1.steady x body.writes body.resizes true) else none

/-- A `for`'s second bound, when its iterable is a range `a..b`, as the analysis reads it. -/
abbrev forHi (L : Bool) (d : Nat) (F : Facts) (x : Name) (body e : Expr) : Option (Term × Int) :=
  if e.isExclusiveRange then (an L d F e).hi.filter (·.1.steady x body.writes body.resizes false)
  else none

theorem forLo_steady {L : Bool} {d : Nat} {F : Facts} {x : Name} {body e : Expr} :
    ∀ t c, forLo L d F x body e = some (t, c) → t.steady x body.writes body.resizes true = true := by
  intro t c h
  unfold forLo at h
  split at h
  · exact (Option.filter_eq_some_iff.1 h).2
  · cases h

theorem forHi_steady {L : Bool} {d : Nat} {F : Facts} {x : Name} {body e : Expr} :
    ∀ t c, forHi L d F x body e = some (t, c) → t.steady x body.writes body.resizes false = true := by
  intro t c h
  unfold forHi at h
  split at h
  · exact (Option.filter_eq_some_iff.1 h).2
  · cases h

theorem an_range {L : Bool} {d : Nat} {F : Facts} {inclusive : Bool} {es : List Expr} :
    (an L d F (.op (.list (.range inclusive)) es)).lo =
        (anOps L d F es).post.linAt d (linOf (anOps L d F es).lins 0) ∧
      (an L d F (.op (.list (.range inclusive)) es)).hi =
        (anOps L d F es).post.linAt (d + 1) (linOf (anOps L d F es).lins 1) := by
  simp only [an]
  rw [opRes_other (fun ⟨_, _, _, _, h, _⟩ => by cases h)]
  exact ⟨rfl, rfl⟩

theorem forLo_range {L : Bool} {d : Nat} {F : Facts} {x : Name} {body : Expr} {inclusive : Bool}
    {es : List Expr} :
    forLo L d F x body (.op (.list (.range inclusive)) es) = rangeLo L d F x body es := by
  simp only [forLo, Expr.isRange, ite_true, an_range.1, rangeLo]

theorem forHi_range {L : Bool} {d : Nat} {F : Facts} {x : Name} {body : Expr} {inclusive : Bool}
    {es : List Expr} :
    forHi L d F x body (.op (.list (.range inclusive)) es) = rangeHi L d F x body inclusive es := by
  cases inclusive <;> simp [forHi, Expr.isExclusiveRange, an_range.2, rangeHi]

theorem Outcome.sat_and {α : Type} {P P' : α → Copy.State → Prop} {B C B' C' : Copy.State → Prop} :
    ∀ {o : Outcome Copy.State α}, o.Sat P B C → o.Sat P' B' C' →
      o.Sat (fun a s => P a s ∧ P' a s) (fun s => B s ∧ B' s) (fun s => C s ∧ C' s)
  | .done _ _, h, h' => ⟨h, h'⟩
  | .jumped .brk _, h, h' => ⟨h, h'⟩
  | .jumped .cont _, h, h' => ⟨h, h'⟩
  | .jumped (.ret _) _, _, _ => trivial
  | .performed _ _ _ _, h, h' => fun w x => Outcome.sat_and (h w x) (h' w x)
  | .raised _ _, _, _ | .panicked _ _, _, _ | .outOfFuel, _, _ | .stuck, _, _ => trivial

theorem Outcome.sat_trivial {α : Type} {P : α → Copy.State → Prop} {B C : Copy.State → Prop}
    (hP : ∀ a s, P a s) (hB : ∀ s, B s) (hC : ∀ s, C s) : ∀ {o : Outcome Copy.State α}, o.Sat P B C
  | .done _ _ => hP _ _
  | .jumped .brk _ => hB _
  | .jumped .cont _ => hC _
  | .jumped (.ret _) _ => trivial
  | .performed _ _ _ _ => fun _ _ => Outcome.sat_trivial hP hB hC
  | .raised _ _ | .panicked _ _ | .outOfFuel | .stuck => trivial

/-- A `for`'s iterable: its facts after it, and, over a range, the bounds its values lie
within. -/
theorem agree_forIter {n : Nat} (hall : ∀ k ≤ n, AgreeRun (evalR D M k) (eval D M k)) {L : Bool}
    {d : Nat} {F : Facts} {x : Name} {e body : Expr} {st : List Value} {s : Copy.State}
    (he : (an L d F e).ok = true) (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    Eval.Agree (fun vs s => (an L d F e).post.noRes.Holds (s.1.nu st .unit) ∧
        ∃ p, rangeQ (forLo L d F x body e) (forHi L d F x body e) st p s.1 ∧
          ∀ v ∈ vs, rangeOk (forLo L d F x body e) (forHi L d F x body e) p v)
      (fun s => (an L d F e).brk.Holds (s.1.nu st .unit))
      (fun s => (an L d F e).cont.Holds (s.1.nu st .unit))
      (evalR D M n e >>= Eval.asList) (eval D M n e >>= Eval.asList) s := by
  have base := (hall n (Nat.le_refl _) L d F e st s he hd hF).bind (f' := Eval.asList)
    (f := Eval.asList) (Q := fun vs s => (an L d F e).post.noRes.Holds (s.1.nu st .unit))
    (fun _ h => h) (fun _ h => h) fun v s₁ hv => Eval.Agree.same (by
      cases v <;> first | exact hv.1.noRes | trivial)
  have range : ((eval D M n e >>= Eval.asList) s).Sat (fun vs s => ∃ p,
      rangeQ (forLo L d F x body e) (forHi L d F x body e) st p s.1 ∧
        ∀ v ∈ vs, rangeOk (forLo L d F x body e) (forHi L d F x body e) p v)
      (fun _ => True) (fun _ => True) := by
    by_cases hr : ∃ inclusive es, e = .op (.list (.range inclusive)) es
    · obtain ⟨inclusive, es, rfl⟩ := hr
      cases n with
      | zero => trivial
      | succ k =>
        have hok : (anOps L d F es).ok = true := by
          simpa [an, opRes_ok] using he
        rw [forLo_range, forHi_range]
        exact range_iter (hall k (by omega)) hok hd hF
    · have hlo : forLo L d F x body e = none := by
        unfold forLo
        split
        · rename_i h
          unfold Expr.isRange at h; split at h
          · exact absurd ⟨_, _, rfl⟩ hr
          · cases h
        · rfl
      have hhi : forHi L d F x body e = none := by
        unfold forHi
        split
        · rename_i h
          unfold Expr.isExclusiveRange at h; split at h
          · exact absurd ⟨_, _, rfl⟩ hr
          · cases h
        · rfl
      rw [hlo, hhi]
      exact Outcome.sat_trivial (fun _ _ => ⟨(0, 0), ⟨fun _ _ h => (nomatch h), fun _ _ h => nomatch h⟩,
        fun _ _ => ⟨fun _ _ h => (nomatch h), fun _ _ h => nomatch h⟩⟩) (fun _ => trivial)
        (fun _ => trivial)
  exact ⟨base.1, (Outcome.sat_and base.2 range).mono (fun _ _ h => h) (fun _ h => h.1)
    (fun _ h => h.1)⟩

end

end Stilt
