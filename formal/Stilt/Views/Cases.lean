import Stilt.Views.Within

/-!
# The cases of the simulation

`Simulates D loops n` says that evaluating with fuel `n` keeps the simulation:
from states that agree, an expression that obeys the law of exclusivity with
the reads of views, and whose views don't outlive their sources, ends alike
in both models (`Post`). Each lemma here proves one case of the evaluator
with fuel `n + 1` from it, stated on the step the evaluator takes. A view that
an operand's evaluation holds keeps reading its part, since its sources are
among the reads under which the operand is evaluated (views.reads-that-last).
-/

namespace Stilt.Views

variable {D : Decls} {loops : Bool} {n : Nat}

/-- Evaluating with fuel `n` keeps the simulation. -/
def Simulates (D : Decls) (loops : Bool) (n : Nat) : Prop :=
  ∀ (e : VExpr) (Γ : Sources) (R : List Shape) (sw sc : VState),
    e.exclusive loops Γ R = true → e.contained Γ = true → StateAgrees sw sc →
    InScope Γ R sw.env →
    Agree (Post R (e.sources Γ) sw) (veval D .window n e sw) (veval D .copy n e sc)

/-- An operand's value, the same in both models, with states that agree after
a step under the reads `R`. -/
structure Operand {α : Type} (R : List Shape) (s₀ sw sc : VState) (a b : α) : Prop where
  eq : a = b
  states : StateAgrees sw sc
  steps : Steps R s₀ sw

theorem InScope.after {Γ : Sources} {R R' : List Shape} {s₀ s : VState}
    (h : InScope Γ R s₀.env) (hs : Steps R' s₀ s) : InScope Γ R s.env :=
  hs.env ▸ h

theorem Post.val {R S : List Shape} {s₀ s sc : VState} {v : Value} (hst : StateAgrees s sc)
    (hs : Steps R s₀ s) : Post R S s₀ s sc (.val v) (.val v) :=
  ⟨hst, hs, rfl, trivial⟩

/-- A post after a step, with fewer reads and more sources. -/
theorem Post.after {R R' S S' : List Shape} {s₀ s₁ s sc : VState} {rw rc : RVal}
    (h₁ : Steps R s₀ s₁) (h : Post R' S s₁ s sc rw rc) (hR : ∀ x ∈ R, x ∈ R')
    (hS : ∀ x ∈ S, x ∈ S') : Post R S' s₀ s sc rw rc :=
  ⟨h.states, h₁.trans h.steps hR, h.agrees, h₁.env ▸ h.within.mono hS⟩

theorem mem_append_right' {R : List Shape} (S : List Shape) : ∀ x ∈ R, x ∈ S ++ R :=
  fun _ h => List.mem_append_right _ h

/-- A view that a post gives keeps reading its part through a step under its
sources' reads. -/
theorem Post.held {R R' S : List Shape} {s₀ s₁ s sc₁ : VState} {rw rc : RVal}
    (h : Post R S s₀ s₁ sc₁ rw rc) (hs : Steps (S ++ R') s₁ s) : Agrees s.store rw rc :=
  h.agrees.preserved (fun ℓ π a b he => by
    subst he
    exact (h.steps.env ▸ (h.within : Covered S s₀.env ℓ π)).guarded R') hs.preserves

namespace Simulates

variable (ih : Simulates D loops n)
include ih

theorem value {e : VExpr} {Γ : Sources} {R : List Shape} {sw sc : VState}
    (hex : e.exclusive loops Γ R = true) (hco : e.contained Γ = true) (hst : StateAgrees sw sc)
    (hsc : InScope Γ R sw.env) :
    Agree (Operand R sw) ((veval D .window n e >>= Run.asVal) sw)
      ((veval D .copy n e >>= Run.asVal) sc) :=
  Agree.bind (ih e Γ R sw sc hex hco hst hsc) fun _ _ _ _ hp =>
    hp.agrees.asVal fun _ _ => ⟨rfl, hp.states, hp.steps⟩

theorem int {e : VExpr} {Γ : Sources} {R : List Shape} {sw sc : VState}
    (hex : e.exclusive loops Γ R = true) (hco : e.contained Γ = true) (hst : StateAgrees sw sc)
    (hsc : InScope Γ R sw.env) :
    Agree (Operand R sw) ((veval D .window n e >>= Run.asInt) sw)
      ((veval D .copy n e >>= Run.asInt) sc) :=
  Agree.bind (ih e Γ R sw sc hex hco hst hsc) fun _ _ _ _ hp =>
    hp.agrees.asInt fun _ => ⟨rfl, hp.states, hp.steps⟩

theorem bool {e : VExpr} {Γ : Sources} {R : List Shape} {sw sc : VState}
    (hex : e.exclusive loops Γ R = true) (hco : e.contained Γ = true) (hst : StateAgrees sw sc)
    (hsc : InScope Γ R sw.env) :
    Agree (Operand R sw) ((veval D .window n e >>= Run.asBool) sw)
      ((veval D .copy n e >>= Run.asBool) sc) :=
  Agree.bind (ih e Γ R sw sc hex hco hst hsc) fun _ _ _ _ hp =>
    hp.agrees.asBool fun _ => ⟨rfl, hp.states, hp.steps⟩

end Simulates

/-! ## Variables and values -/

/-- The sources of a variable's binding cover the window it holds. -/
theorem Pointwise.lookup_sources {env : List (Name × Binding)} :
    ∀ {Γ : Sources} {E : List (Name × Binding)},
      Pointwise (fun (g : Name × List Shape) (e : Name × Binding) =>
        g.1 = e.1 ∧ ∀ ℓ π a b, e.2 = .view (.window ℓ π a b) → Covered g.2 env ℓ π) Γ E →
      ∀ x ℓ π a b, E.lookup x = some (.view (.window ℓ π a b)) →
        Covered ((Γ.lookup x).getD []) env ℓ π
  | _, _, .nil, _, _, _, _, _, h => by cases h
  | (y, S) :: _, (y', c) :: _, .cons ⟨hy, hc⟩ hrest, x, ℓ, π, a, b, h => by
    simp only at hy hc
    subst hy
    by_cases hxy : x = y
    · subst hxy
      simp only [List.lookup_cons_self, Option.some.injEq] at h ⊢
      exact hc ℓ π a b h
    · rw [lookup_cons_ne hxy] at h ⊢
      exact Pointwise.lookup_sources hrest x ℓ π a b h

theorem ExceptAgree.mono {α β : Type} {P Q : α → β → Prop} {x : Except Fault α}
    {y : Except Fault β} (h : ExceptAgree P x y) (hPQ : ∀ a b, x = .ok a → P a b → Q a b) :
    ExceptAgree Q x y := by
  cases x <;> cases y <;> first | exact h | exact hPQ _ _ rfl h

theorem read_window {s : VState} {x : Name} {ℓ : Nat} {π : Path} {a b : Int}
    (h : s.read x = .ok (.window ℓ π a b)) : s.env.lookup x = some (.view (.window ℓ π a b)) := by
  unfold VState.read at h
  split at h
  · rename_i heq
    revert h
    cases cell s.store _ <;> simp [lift]
  · cases h
    assumption
  · cases h

theorem sim_var {x : Name} {Γ : Sources} {R : List Shape} {sw sc : VState}
    (hst : StateAgrees sw sc) (hsc : InScope Γ R sw.env) :
    Agree (Post R ((Γ.lookup x).getD []) sw) (Eval.inspect (fun s => s.read x) sw)
      (Eval.inspect (fun s => s.read x) sc) := by
  refine Agree.inspect ((hst.read x).mono fun rw rc hx hag => ⟨hst, Steps.refl R sw, hag, ?_⟩)
  cases rw with
  | window ℓ π a b => exact Pointwise.lookup_sources hsc.sources x ℓ π a b (read_window hx)
  | _ => trivial

end Stilt.Views
