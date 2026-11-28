import Stilt.Analysis.Agree.Operands
import Stilt.Panics.Facts

/-!
# Straight-line code

The release run agrees with the run that keeps every check, and meets the analysis, on
literals, bindings read, `!`, field reads, indexes, blocks, `if` and the jumps, each from the
agreement of its parts.
-/

namespace Stilt

/-- The release step agrees with the step that keeps every check, and meets `R`. -/
abbrev Res.Agrees (R : Res) (st : List Value) (m' m : Eval Copy.State Value) (s : Copy.State) :
    Prop :=
  Eval.Agree (R.Done st) (fun s => R.brk.Holds (s.1.nu st .unit))
    (fun s => R.cont.Holds (s.1.nu st .unit)) m' m s

theorem Res.done_of {R : Res} {st : List Value} {v : Value} {s : Copy.State}
    (hp : R.post.Holds (s.1.nu st v)) (ht : v = .bool true → R.tt.Holds (s.1.nu st v))
    (hf : v = .bool false → R.ff.Holds (s.1.nu st v)) : R.Done st v s := ⟨hp, ht, hf⟩

theorem Res.pure_done {G : Facts} {l : Option (Term × Int)} {st : List Value} {v : Value}
    {s : Copy.State} (h : G.Holds (s.1.nu st v)) : ({ Res.pure G with lin := l }).Done st v s :=
  ⟨h, fun _ => h, fun _ => h⟩

theorem Copy.Frame.nu_bool {fr : Copy.Frame} {st : List Value} (b b' : Bool) :
    fr.nu st (.bool b) = fr.nu st (.bool b') := by
  funext t; cases t <;> rfl

variable {runR run : Expr → Eval Copy.State Value}

theorem Eval.list_single {σ : Type} (r : Expr → Eval σ Value) (e : Expr) :
    Eval.list r [e] = (r e >>= fun v => Pure.pure [v]) := rfl

theorem Eval.Agree.asInt {P : Value → Copy.State → Prop} {B C : Copy.State → Prop}
    {m' m : Eval Copy.State Value} {s : Copy.State} (h : Eval.Agree P B C m' m s) :
    Eval.Agree (fun k s => P (.int k) s) B C (m' >>= Eval.asInt) (m >>= Eval.asInt) s :=
  h.bind (fun _ h => h) (fun _ h => h) fun v s' hv => Eval.Agree.same (by
    cases v <;> first | exact hv | trivial)

theorem Eval.Agree.asBool {P : Value → Copy.State → Prop} {B C : Copy.State → Prop}
    {m' m : Eval Copy.State Value} {s : Copy.State} (h : Eval.Agree P B C m' m s) :
    Eval.Agree (fun b s => P (.bool b) s) B C (m' >>= Eval.asBool) (m >>= Eval.asBool) s :=
  h.bind (fun _ h => h) (fun _ h => h) fun v s' hv => Eval.Agree.same (by
    cases v <;> first | exact hv | trivial)

/-- A step that ends with a value in the state it started from, or faults. -/
theorem Res.agrees_still {R : Res} {st : List Value} {s : Copy.State} {m : Eval Copy.State Value}
    (hm : (∃ v, m s = .done v s ∧ R.Done st v s) ∨ ∃ f, m s = Outcome.fault f s) :
    R.Agrees st m m s := by
  refine Eval.Agree.same ?_
  rcases hm with ⟨v, h, hv⟩ | ⟨f, h⟩ <;> rw [h]
  · exact hv
  · exact Outcome.sat_fault f s

/-- The read of a binding (facts.linear-forms): its value's term is the binding's, and its
length the binding's length. -/
theorem agree_var (w : WriteBack) {L : Bool} {d : Nat} {F : Facts} {x : Name} {st : List Value}
    {s : Copy.State} (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.var x)).Agrees st (Eval.inspect fun s => (Copy.memoryWith w).read s x [])
      (Eval.inspect fun s => (Copy.memoryWith w).read s x []) s := by
  refine Res.agrees_still ?_
  show (∃ v, Eval.ofExcept (Copy.read s.1 x []) s = _ ∧ _) ∨
    ∃ f, Eval.ofExcept (Copy.read s.1 x []) s = _
  cases hl : s.1.lookup x with
  | none => exact .inr ⟨.stuck, by simp [Copy.read, hl, Eval.ofExcept]⟩
  | some v =>
    refine .inl ⟨v, by simp [Copy.read, hl, Eval.ofExcept, Value.get], Res.pure_done ?_⟩
    have hv : s.1.nu st v (.val x) = s.1.nu st v .res ∧ s.1.nu st v (.len x) = s.1.nu st v .reslen := by
      simp [Copy.Frame.nu, hl]
    refine (((((hF.noRes).insert ?_).insert ?_).insert ?_).insert ?_).tidy rfl L <;>
      simp only [Diff.Holds] <;> omega

theorem agree_move (w : WriteBack) {L : Bool} {d : Nat} {F : Facts} {x : Name} {st : List Value}
    {s : Copy.State} (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.move x)).Agrees st (Eval.inspect fun s => (Copy.memoryWith w).read s x [])
      (Eval.inspect fun s => (Copy.memoryWith w).read s x []) s :=
  agree_var w (d := d) hF

/-- An integer literal: zero plus its value (facts.linear-forms). -/
theorem agree_int {L : Bool} {d : Nat} {F : Facts} {k : Int} {st : List Value} {s : Copy.State}
    (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.int k)).Agrees st (Pure.pure (.int k)) (Pure.pure (.int k)) s := by
  refine Eval.Agree.pure (Res.pure_done ?_)
  have hG : ((F.noRes.equate .zero k).insert ⟨.reslen, .zero, 0⟩).Holds (s.1.nu st (.int k)) :=
    (hF.noRes.equate (by simp [Copy.Frame.nu, Value.intOr])).insert
      (by simp [Diff.Holds, Copy.Frame.nu, Value.lenOr])
  refine Facts.Holds.tidy ?_ rfl L
  split
  · exact hG
  · exact hG.addNonzero (by simp only [Copy.Frame.nu, Value.intOr]; assumption)

theorem agree_bool {L : Bool} {d : Nat} {F : Facts} {b : Bool} {st : List Value} {s : Copy.State}
    (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.bool b)).Agrees st (Pure.pure (.bool b)) (Pure.pure (.bool b)) s := by
  refine Eval.Agree.pure ⟨hF.noRes, fun h => ?_, fun h => ?_⟩ <;>
    simp only [Value.bool.injEq] at h <;> subst h <;> exact hF.noRes

/-- Code that ends in the state it started from, with facts on nothing but the code around. -/
theorem agree_still {R : Res} {F : Facts} {st : List Value} {s : Copy.State} {m : Eval Copy.State Value}
    (hR : R.post = F.noRes ∧ R.tt = F.noRes ∧ R.ff = F.noRes) (hF : F.Holds (s.1.nu st .unit))
    (hm : (∃ v, m s = .done v s) ∨ ∃ f, m s = Outcome.fault f s) : R.Agrees st m m s := by
  refine Res.agrees_still ?_
  rcases hm with ⟨v, h⟩ | h
  · exact .inl ⟨v, h, by rw [Res.Done, hR.1, hR.2.1, hR.2.2]; exact ⟨hF.noRes, fun _ => hF.noRes,
      fun _ => hF.noRes⟩⟩
  · exact .inr h

set_option linter.unusedSimpArgs false in
/-- `!c`: where it is true, `c`'s facts where it is false, and the other way round
(facts.conditions). -/
theorem agree_not (w : WriteBack) (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts} {c : Expr}
    {st : List Value} {s : Copy.State} (hok : (an L d F (.op .not [c])).ok = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.op .not [c])).Agrees st
      (Eval.list runR [c] >>= fun vs => Eval.world (Copy.memoryWith w) (Op.not.run vs))
      (Eval.list run [c] >>= fun vs => Eval.world (Copy.memoryWith w) (Op.not.run vs)) s := by
  simp only [an] at hok ⊢
  rw [Eval.list_single, Eval.list_single]
  have hc := ih L d F c st s hok hd hF
  refine Eval.Agree.bind (P := fun vs s => ∃ v, vs = [v] ∧ (an L d F c).Done st v s)
    (B := fun s => (an L d F c).brk.Holds (s.1.nu st .unit))
    (C := fun s => (an L d F c).cont.Holds (s.1.nu st .unit)) ?_ (fun _ h => h) (fun _ h => h)
    fun vs s₁ hvs => ?_
  · refine hc.bind (fun _ h => h) (fun _ h => h) fun v s₁ hv => ?_
    exact Eval.Agree.pure (P := fun vs s => ∃ v, vs = [v] ∧ (an L d F c).Done st v s)
      ⟨v, rfl, hv⟩
  · obtain ⟨v, rfl, hv⟩ := hvs
    refine Eval.Agree.same ?_
    obtain ⟨fr, wd⟩ := s₁
    rw [Eval.world_copy, Op.run_of_ne (fun _ h => by cases h)]
    cases hap : Op.apply .not [v] with
    | error e => exact Outcome.sat_fault e _
    | ok r =>
      obtain ⟨b, rfl, rfl⟩ := Op.not_apply hap
      have hν := Copy.Frame.nu_bool (fr := fr) (st := st) b (!b)
      refine ⟨by rw [← hν]; exact hv.1, fun h => ?_, fun h => ?_⟩ <;>
        simp only [Value.bool.injEq, Bool.not_eq_true', Bool.not_eq_false'] at h <;> subst h <;>
        simp only [Functor.map, Except.map] <;> rw [← hν]
      · exact hv.2.2 rfl
      · exact hv.2.1 rfl

end Stilt
