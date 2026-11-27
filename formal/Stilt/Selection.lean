import Stilt.Semantics

/-!
# How a `match` selects its arm

What holds of each way an arm may run holds of the `match`: an arm without a guard runs
its body with the parts its pattern binds, and an arm with a guard runs the guard with each
way its pattern matches, then its body or what comes next (patterns.match and
patterns.guards). A `match` whose value one arm without a guard matches, each of whose ways
binds as many parts as its arm names, never runs out of arms. The proofs of the semantics
take a `match` apart with these inductions, one for a property of one run and one for a
relation between two.
-/

namespace Stilt

namespace Eval

variable {σ σ' : Type}

/-- Whether some arm without a guard matches the value: then a `match` takes an arm. -/
def Covered (arms : List Arm) (v : Value) : Prop :=
  ∃ arm ∈ arms, arm.guard = none ∧ (arm.pattern.matchOn v).isSome

/-- Whether each way an arm may take the value binds one part for each of the arm's names. -/
def Bound (arms : List Arm) (v : Value) : Prop :=
  ∀ arm ∈ arms, ∀ us, (arm.pattern.matchOn v = some us ∨ us ∈ arm.pattern.ways v) →
    arm.binders.length = us.length

theorem Covered.tail {arm : Arm} {arms : List Arm} {v : Value} (h : Covered (arm :: arms) v)
    (hn : arm.guard = none → arm.pattern.matchOn v = none) : Covered arms v := by
  obtain ⟨a, ha, hg, hm⟩ := h
  rcases List.mem_cons.1 ha with rfl | ha
  · rw [hn hg] at hm; exact nomatch hm
  · exact ⟨a, ha, hg, hm⟩

theorem Bound.tail {arm : Arm} {arms : List Arm} {v : Value} (h : Bound (arm :: arms) v) :
    Bound arms v := fun a ha => h a (List.mem_cons_of_mem _ ha)

section

variable {M : Memory σ} {run : Expr → Eval σ Value} {v : Value} (Q : Eval σ Value → Prop)

/-- An arm with a guard keeps a property: when it holds of what runs after the guard is false
with every way, it holds of the arm. -/
theorem guarded_of {bs : List Name} {g body : Expr} {next : Eval σ Value}
    {ways : List (List Value)} (hn : Q next)
    (hlen : Q (fail .stuck) ∨ ∀ us ∈ ways, bs.length = us.length)
    (hg : ∀ us ∈ ways, bs.length = us.length → ∀ m, Q m → Q (tryWay M run bs g body us m)) :
    Q (guarded M run bs g body next ways) := by
  induction ways with
  | nil => exact hn
  | cons us ways ih =>
    simp only [guarded]
    split
    · rename_i hl
      exact hg us List.mem_cons_self hl _ (ih (hlen.imp_right fun h us' hu =>
        h us' (List.mem_cons_of_mem _ hu)) fun us' hu => hg us' (List.mem_cons_of_mem _ hu))
    · rename_i hl
      rcases hlen with h | h
      · exact h
      · exact absurd (h us List.mem_cons_self) hl

/-- A property of each body run with what its pattern binds, kept by running a guard first,
holds of a `match`, when the value is covered and bound, or when the property holds of
getting stuck. -/
theorem select_of :
    ∀ {arms : List Arm}, (Q (fail .stuck) ∨ Covered arms v) → (Q (fail .stuck) ∨ Bound arms v) →
    (∀ arm ∈ arms, arm.guard = none → ∀ us, arm.pattern.matchOn v = some us →
      arm.binders.length = us.length → Q (withVars M (arm.binders.zip us) (run arm.body))) →
    (∀ arm ∈ arms, ∀ g, arm.guard = some g → ∀ us ∈ arm.pattern.ways v,
      arm.binders.length = us.length → ∀ m, Q m → Q (tryWay M run arm.binders g arm.body us m)) →
    Q (select M run arms v)
  | [], hend, _, _, _ => by
    rcases hend with h | ⟨_, h, _⟩
    · exact h
    · exact nomatch h
  | arm :: arms, hend, hbd, hb, hg => by
    have hb' := fun a ha => hb a (List.mem_cons_of_mem _ ha)
    have hg' := fun a ha => hg a (List.mem_cons_of_mem _ ha)
    have hbd' := hbd.imp_right Bound.tail
    simp only [select]
    split
    · rename_i hn
      split
      · rename_i us hm
        split
        · rename_i hl
          exact hb arm List.mem_cons_self hn us hm hl
        · rename_i hl
          rcases hbd with h | h
          · exact h
          · exact absurd (h arm List.mem_cons_self us (.inl hm)) hl
      · rename_i hm
        exact select_of (hend.imp_right fun h => h.tail fun _ => hm) hbd' hb' hg'
    · rename_i g hs
      exact guarded_of Q
        (select_of (hend.imp_right fun h => h.tail fun hn => by rw [hs] at hn; exact nomatch hn)
          hbd' hb' hg')
        (hbd.imp_right fun h us hu => h arm List.mem_cons_self us (.inr hu))
        (hg arm List.mem_cons_self g hs)

end

section

variable {M : Memory σ} {M' : Memory σ'} {run : Expr → Eval σ Value} {run' : Expr → Eval σ' Value}
  (R : Eval σ Value → Eval σ' Value → Prop)

theorem forall₂_refl {α : Type} {P : α → α → Prop} : ∀ {l : List α}, (∀ a ∈ l, P a a) → Forall₂ P l l
  | [], _ => .nil
  | a :: _, h => .cons (h a List.mem_cons_self) (forall₂_refl fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- An arm with a guard keeps a relation between two runs of it, way by way. -/
theorem guarded_rel {bs bs' : List Name} {g g' body body' : Expr} {next : Eval σ Value}
    {next' : Eval σ' Value} (hfail : R (fail .stuck) (fail .stuck)) (hbs : bs.length = bs'.length) :
    ∀ {ways ways' : List (List Value)}, Forall₂ (fun us us' => us.length = us'.length ∧
      (bs.length = us.length → ∀ m m', R m m' →
        R (tryWay M run bs g body us m) (tryWay M' run' bs' g' body' us' m'))) ways ways' →
    R next next' →
    R (guarded M run bs g body next ways) (guarded M' run' bs' g' body' next' ways')
  | [], [], .nil, hn => hn
  | us :: _, us' :: _, .cons ⟨hl, h⟩ hs, hn => by
    simp only [guarded]
    by_cases hu : bs.length = us.length
    · have hu' : bs'.length = us'.length := by omega
      simp only [hu, hu', ↓reduceIte]
      exact h hu _ _ (guarded_rel hfail hbs hs hn)
    · have hu' : ¬ bs'.length = us'.length := by omega
      simp only [hu, hu', ↓reduceIte]
      exact hfail

/-- A relation between two runs of each body, kept by running a guard first, holds between
two runs of a `match` on one value, when it holds of getting stuck. -/
theorem select_rel {v : Value} (hfail : R (fail .stuck) (fail .stuck)) :
    ∀ {arms : List Arm},
    (∀ arm ∈ arms, arm.guard = none → ∀ us, arm.pattern.matchOn v = some us →
      arm.binders.length = us.length →
      R (withVars M (arm.binders.zip us) (run arm.body))
        (withVars M' (arm.binders.zip us) (run' arm.body))) →
    (∀ arm ∈ arms, ∀ g, arm.guard = some g → ∀ us ∈ arm.pattern.ways v,
      arm.binders.length = us.length → ∀ m m', R m m' →
      R (tryWay M run arm.binders g arm.body us m) (tryWay M' run' arm.binders g arm.body us m')) →
    R (select M run arms v) (select M' run' arms v)
  | [], _, _ => hfail
  | arm :: arms, hb, hg => by
    have hb' := fun a ha => hb a (List.mem_cons_of_mem _ ha)
    have hg' := fun a ha => hg a (List.mem_cons_of_mem _ ha)
    simp only [select]
    split
    · rename_i hn
      split
      · rename_i us hm
        split
        · rename_i hl
          exact hb arm List.mem_cons_self hn us hm hl
        · exact hfail
      · exact select_rel hfail hb' hg'
    · rename_i g hs
      exact guarded_rel R hfail rfl
        (forall₂_refl fun us hu => ⟨rfl, hg arm List.mem_cons_self g hs us hu⟩)
        (select_rel hfail hb' hg')

end

end Eval

end Stilt
