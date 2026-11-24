import Stilt.Modes.Monotone
import Stilt.Modes.Facts

/-!
# Consumption and once, solved

The rounds of `Decls.consumed` reach the fixed point of values.consumed-parameters, and
those of `Decls.onceParams` the fixed point of modes.once-parameters: one more round
changes nothing (`Decls.consumed_fixed`, `Decls.onceParams_fixed`). So what a
parameter's modes read from its function's body is what the program solves:
its locality is its consumption (`ModeEnv.paramModes_locality`, modes.escaping), and it is `once` exactly when the program's `once` parameters hold
it (`ModeEnv.paramModes_once`).
-/

namespace Stilt

namespace Decls

/-- The function a name finds is one of the program's, with that name. -/
theorem fn?_mem {D : Decls} {g : Name} {d : FnDecl} (h : D.fn? g = some d) :
    d ∈ D.fns ∧ d.name = g := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  simpa using List.find?_some h

/-- A round holds only parameters of the program's functions. -/
theorem consumeStep_supp (D : Decls) (C : Consumed) (g : Name) (n : Nat)
    (h : D.consumeStep C g n = true) : (g, n) ∈ D.slotList := by
  unfold consumeStep at h
  split at h
  · rename_i d hd
    split at h
    · rename_i p hp
      obtain ⟨hmem, rfl⟩ := fn?_mem hd
      have hn := (List.getElem?_eq_some_iff.1 hp).1
      exact List.mem_flatMap.2 ⟨d, hmem, List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩⟩
    · cases h
  · cases h

/-- A round given more consumed parameters consumes no fewer. -/
theorem consumeStep_mono (D : Decls) (C C' : Consumed) (h : ParamSet.Le C C') :
    ParamSet.Le (D.consumeStep C) (D.consumeStep C') := by
  intro g n hc
  unfold consumeStep at hc ⊢
  split at hc
  · split at hc
    · simp only [FnDecl.consumes, Expr.consumes, Bool.and_eq_true] at hc ⊢
      exact ⟨hc.1, Expr.leaves_mono _ _ C' _ _ h (OutLe.refl _) hc.2⟩
    · cases hc
  · cases hc

/-- **Consumption is solved** (values.consumed-parameters): one more round of
`Decls.consumed` changes nothing. -/
theorem consumed_fixed (D : Decls) : D.consumeStep D.consumed = D.consumed :=
  repeat_fixed (S := D.slotList) (D.consumeStep_mono) (D.consumeStep_supp)

end Decls

namespace Decls

/-- A round of `once` parameters holds only parameters of the program's
functions. -/
theorem onceStep_supp (D : Decls) (O : OnceParams) (g : Name) (n : Nat)
    (h : D.onceStep O g n = true) : (g, n) ∈ D.slotList := by
  unfold onceStep at h
  split at h
  · rename_i d hd
    split at h
    · rename_i p hp
      obtain ⟨hmem, rfl⟩ := fn?_mem hd
      have hn := (List.getElem?_eq_some_iff.1 hp).1
      exact List.mem_flatMap.2 ⟨d, hmem, List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩⟩
    · cases h
  · cases h

/-- A round given more `once` parameters makes no fewer `once`. -/
theorem onceStep_mono (D : Decls) (O O' : OnceParams) (h : ParamSet.Le O O') :
    ParamSet.Le (D.onceStep O) (D.onceStep O') := by
  intro g n ho
  unfold onceStep at ho ⊢
  split at ho
  · split at ho
    · simp only [Bool.and_eq_true, beq_iff_eq] at ho ⊢
      exact ⟨ho.1, (Expr.use_below _ O O' _ h).2 ho.2⟩
    · cases ho
  · cases ho

/-- **`once` parameters are solved** (modes.once-parameters): one more round of
`Decls.onceParams` changes nothing. -/
theorem onceParams_fixed (D : Decls) : D.onceStep D.onceParams = D.onceParams :=
  repeat_fixed_top (S := D.slotList) (D.onceStep_mono) (D.onceStep_supp)

end Decls

/-- **A parameter's locality is its consumption, as the program solves it**
(modes.escaping; values.consumed-parameters): a parameter of a copy-on-write type of a
function of the program escapes exactly when the program's consumption holds
it. -/
theorem ModeEnv.paramModes_locality (p : Program) {g : Name} {d : FnDecl}
    (hd : p.decls.fn? g = some d) {n : Nat} {q : Param} (hq : d.params[n]? = some q)
    (hcow : p.decls.cow q.type = true) :
    (p.modeEnv.paramModes d.params d.body q).locality = .escapes ↔
      p.decls.consumed g n = true := by
  show paramLocality p.decls p.decls.consumed (inoutNames d.params) d.body q = .escapes ↔ _
  rw [paramLocality_escapes_iff _ _ d q hcow, ← consumeStep_fn hd hq,
    Decls.consumed_fixed]

/-- **A parameter is `once` as the program solves it** (modes.once-parameters): a
parameter of function type of a function of the program is `once` exactly when
the program's `once` parameters hold it. -/
theorem ModeEnv.paramModes_once (p : Program) {g : Name} {d : FnDecl}
    (hd : p.decls.fn? g = some d) {n : Nat} {q : Param} (hq : d.params[n]? = some q)
    (hfn : q.type.isFn = true) :
    (p.modeEnv.paramModes d.params d.body q).once = some .once ↔
      p.decls.onceParams g n = true := by
  rw [← Decls.onceParams_fixed]
  simp only [ModeEnv.paramModes, Program.modeEnv, hfn, Decls.onceStep, hd, hq, Bool.true_and,
    beq_iff_eq]
  split <;> simp_all

end Stilt
