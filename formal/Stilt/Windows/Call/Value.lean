import Stilt.Windows.Call.Enter

/-!
# Running a callee's body

A call binds its parameters to the arguments passed (`bindArgs`), which have the same shapes in
both models, starts the callee (`enter`), runs its body, and ends as `Outcome.leaveCall` and,
in the model of windows, `Outcome.settle` say (values.inout-arguments, views.across-calls).
From what the start of a call gives (`enter_rel`), the body's run in the callee's context gives
the call's: values read alike, each window of the one of windows a window of a value
passed.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- What a call gives against the caller's context: values read alike, the in-place one a value
the checks accept, each window of the other reading the region of a window of a value passed. -/
def ValueG (D : Decls) (ps' : List Passed) (u v : Value) (si : IState) (sw : WState) : Prop :=
  VRel si.1.store sw.1.store v u ∧ u.Viewed D ∧ ∀ win ∈ windowsOf v, ∃ a ∈ ps', ∃ w,
    a.value? = some w ∧ ∃ w' ∈ windowsOf w, w'.1 = win.1 ∧ w'.2.1 = win.2.1

/-- A step of the model of windows that frees the locations from the store's length on when it
ends, as a call does. -/
def settled (m : Eval WState Value) : Eval WState Value := fun s => (m s).settle s.1.store.length

theorem freeFrom_self (s : WState) : freeFrom s.1.store.length s = s := by
  simp [freeFrom]

theorem mem_bindArgs : ∀ {params : List Param} {args : List Passed} {bound : List (Name × Passed)},
    bindArgs params args = some bound → ∀ ya ∈ bound, ya.2 ∈ args
  | [], [], _, h, ya, hm => by simp only [bindArgs, Option.some.injEq] at h; subst h; cases hm
  | [], _ :: _, _, h, _, _ => by simp [bindArgs] at h
  | _ :: _, [], _, h, _, _ => by simp [bindArgs] at h
  | p :: ps, a :: args, bound, h, ya, hm => by
    have key : ∀ b, bindArgs ps args = some b → bound = (p.name, a) :: b → ya.2 ∈ a :: args := by
      intro b hb he
      subst he
      rcases List.mem_cons.1 hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_bindArgs hb ya hm)
    unfold bindArgs at h
    split at h
    all_goals first
      | (cases hb : bindArgs ps args with
          | none => simp [hb] at h
          | some b =>
            simp only [hb, Option.map_some, Option.some.injEq] at h
            exact key b hb h.symm)
      | simp at h

/-- Passed arguments of the same shapes bind alike. -/
theorem bindArgs_rel {c : Ctx} {si : IState} {sw : WState} :
    ∀ (params : List Param) {ps ps' : List Passed}, PassRel D c si sw ps ps' →
      (bindArgs params ps = none ∧ bindArgs params ps' = none) ∨
        ∃ b b', bindArgs params ps = some b ∧ bindArgs params ps' = some b'
  | [], _, _, .nil => .inr ⟨[], [], rfl, rfl⟩
  | [], _, _, .value .. => .inl ⟨rfl, rfl⟩
  | [], _, _, .moved .. => .inl ⟨rfl, rfl⟩
  | [], _, _, .place .. => .inl ⟨rfl, rfl⟩
  | _ :: _, _, _, .nil => .inl ⟨rfl, rfl⟩
  | p :: params, _, _, .value _ _ _ h | p :: params, _, _, .moved _ _ _ _ h
  | p :: params, _, _, .place _ _ _ _ _ h => by
    rcases bindArgs_rel params h with ⟨h₁, h₂⟩ | ⟨b, b', h₁, h₂⟩ <;>
      cases hm : p.mode <;> simp [bindArgs, hm, h₁, h₂]

theorem ParamsInst.names {ps₀ ps : List Param} (h : ParamsInst D ps₀ ps) :
    ps.map Param.name = ps₀.map Param.name := by
  induction h with
  | nil => rfl
  | cons hp _ ih => simp only [List.map_cons, hp.2.1, ih]

theorem ParamsInst.refl : ∀ ps : List Param, ParamsInst D ps ps
  | [] => .nil
  | p :: ps => .cons ⟨rfl, rfl, TyInst.refl D p.type, id⟩ (ParamsInst.refl ps)

/-- A failed start, in both models. -/
theorem fault_settle {c : Ctx} {pend : List (Window × Value)}
    {G : Value → Value → IState → WState → Prop}
    {si : IState} {sw : WState} (hp : Pre D c pend si sw) (e : Fault) :
    (Outcome.fault e si : Outcome IState Value).Rel (CorrG D c pend G sw.1.env)
      ((Outcome.fault e sw : Outcome WState Value).settle sw.1.store.length) := by
  cases e with
  | stuck => trivial
  | panic k =>
    show Outcome.Rel _ (.panicked k si) (.panicked k (freeFrom sw.1.store.length sw))
    rw [freeFrom_self]
    exact ⟨hp, rfl, rfl⟩

/-- What the call gives against the callee's context, against the caller's. -/
theorem callG_value {c' : Ctx} {bound' : List (Name × Passed)} {ps' : List Passed}
    {params : List Param} (hb' : bindArgs params ps' = some bound') (hIn : c'.In = inOf bound')
    {u v : Value} {si : IState} {sw : WState} (h : CallG D c' u v si sw) :
    ValueG D ps' u v si sw := by
  refine ⟨h.1, h.2.1, fun win hwin => ?_⟩
  obtain ⟨-, p, -, w, hw, w', hw', h₁, h₂⟩ := h.2.2 win hwin
  rw [hIn] at hw
  obtain ⟨a, ha, hav⟩ := mem_inOf.1 hw
  exact ⟨a, mem_bindArgs hb' _ ha, w, hav, w', hw', h₁, h₂⟩

end Windows

end Stilt
