import Stilt.Views.Places

/-!
# Loops

The case of the simulation for `for`. A loop over a list iterates the value
the list had when it started, in both models, as copy-on-write makes it
(modes.change-while-iterating), so a change to the list in the body changes nothing it
reads: E0404 protects a cost, and the simulation doesn't need it. A loop over
a view reads each element through the window as it reaches it, so the body
runs under the view's reads (views.for-over-view), and the window reads its part
at every element.
-/

namespace Stilt.Views

variable {D : Decls} {loops : Bool} {n : Nat}

section Loop

variable (ih : Simulates D loops n) {x : Name} {it body : VExpr} {Γ : Sources}
  {R : List Shape} {s₀ s₁ sc₁ : VState} {rw rc : RVal}
  (hb : body.exclusive loops ((x, []) :: Γ)
    (hide (it.sources Γ ++ ((if loops then iterated it else []) ++ R)) x) = true)
  (hcb : body.contained ((x, []) :: Γ) = true) (hsc : InScope Γ R s₀.env)
  (hp : Post R (it.sources Γ) s₀ s₁ sc₁ rw rc)
include ih hb hcb hsc hp

/-- What each element of a loop keeps: states that agree, a step under the
loop's reads, and the iterated view reading its part. -/
def LoopInv (R₂ : List Shape) (s₁ : VState) (rw rc : RVal) (s sc : VState) : Prop :=
  StateAgrees s sc ∧ Steps R₂ s₁ s ∧ Agrees s.store rw rc

/-- One element of a loop: the body runs with the element bound. -/
theorem loop_step {s sc : VState} (v : Value)
    (hI : LoopInv (it.sources Γ ++ ((if loops then iterated it else []) ++ R)) s₁ rw rc s sc) :
    Agree (fun s' sc' _ _ =>
        LoopInv (it.sources Γ ++ ((if loops then iterated it else []) ++ R)) s₁ rw rc s' sc')
      (Run.discard (Run.within x (.val v) (veval D .window n body)) s)
      (Run.discard (Run.within x (.val v) (veval D .copy n body)) sc) := by
  have henv : s.env = s₀.env := hI.2.1.env.trans hp.steps.env
  have hsc' : InScope Γ (it.sources Γ ++ ((if loops then iterated it else []) ++ R)) s.env :=
    henv ▸ hsc.mono fun _ h => List.mem_append_right _ (List.mem_append_right _ h)
  refine Agree.discard (Agree.within (S := []) hI.1 hsc' rfl trivial
    fun sw sc hst hsc'' => ih body _ _ sw sc hb hcb hst hsc'') fun s' sc' _ _ hcl => ?_
  refine ⟨hcl.states, hI.2.1.trans hcl.steps fun _ h => h, hI.2.2.preserved ?_ hcl.steps.preserves⟩
  intro ℓ π a c he
  subst he
  exact henv ▸ (hp.within : Covered (it.sources Γ) s₀.env ℓ π).guarded _

/-- A loop keeps the simulation, over a list or a view. -/
theorem sim_loop :
    Agree (fun s sc _ _ => StateAgrees s sc ∧ Steps R s₀ s)
      (Run.loop (veval D .window n) x rw body s₁) (Run.loop (veval D .copy n) x rc body sc₁) := by
  have hI : LoopInv (it.sources Γ ++ ((if loops then iterated it else []) ++ R)) s₁ rw rc s₁ sc₁ :=
    ⟨hp.states, Steps.refl _ _, hp.agrees⟩
  have hdone : ∀ s sc, LoopInv (it.sources Γ ++ ((if loops then iterated it else []) ++ R))
      s₁ rw rc s sc → StateAgrees s sc ∧ Steps R s₀ s := fun _ _ hI =>
    ⟨hI.1, hp.steps.trans hI.2.1 fun _ h => List.mem_append_right _ (List.mem_append_right _ h)⟩
  have hag := hp.agrees
  cases rw <;> cases rc <;> try exact False.elim hag
  · rename_i v w
    cases (show v = w from hag)
    cases v <;> try exact Agree.stuck
    exact (Agree.each (fun v _ _ hI => loop_step ih hb hcb hsc hp v hI) _ _ _ hI).mono
      fun s sc _ _ h => hdone s sc h
  · rename_i ℓ π a b part
    have hlen : b - a = (part.length : Int) := hag.len
    show Agree _ (Run.each (fun k => do
        let v ← Eval.inspect fun s => (RVal.window ℓ π a b).elem s.store k
        Run.discard (Run.within x (.val v) (veval D .window n body))) (Run.indices (b - a)) s₁)
      (Run.each (fun k => do
        let v ← Eval.inspect fun s => (RVal.copied part).elem s.store k
        Run.discard (Run.within x (.val v) (veval D .copy n body))) (Run.indices part.length) sc₁)
    rw [hlen]
    refine (Agree.each (fun k s sc hI => ?_) _ _ _ hI).mono fun s sc _ _ h => hdone s sc h
    refine Agree.bind (Q := fun s' sc' v v' => v = v' ∧ s' = s ∧
      LoopInv (it.sources Γ ++ ((if loops then iterated it else []) ++ R)) s₁
        (.window ℓ π a b) (.copied part) s' sc')
      (Agree.inspect ?_) fun s' sc' v v' ⟨hv, hs', hI'⟩ => ?_
    · show ExceptAgree _ ((RVal.window ℓ π a b).elem s.store k) ((RVal.copied part).elem sc.store k)
      rw [← hI.1.store, hI.2.2.elem k]
      exact ExceptAgree.of_eq _ fun _ => ⟨rfl, rfl, hI⟩
    · subst hv
      exact loop_step ih hb hcb hsc hp _ hI'

end Loop

theorem sim_for (ih : Simulates D loops n) {x : Name} {it body : VExpr} {Γ : Sources}
    {R S : List Shape} {sw sc : VState} (hst : StateAgrees sw sc) (hsc : InScope Γ R sw.env)
    (hi : it.exclusive loops Γ R = true)
    (hb : body.exclusive loops ((x, []) :: Γ)
      (hide (it.sources Γ ++ ((if loops then iterated it else []) ++ R)) x) = true)
    (hci : it.contained Γ = true) (hcb : body.contained ((x, []) :: Γ) = true) :
    Agree (Post R S sw)
      ((veval D .window n it >>= fun r => Run.loop (veval D .window n) x r body >>= fun _ =>
        pure (.val .unit)) sw)
      ((veval D .copy n it >>= fun r => Run.loop (veval D .copy n) x r body >>= fun _ =>
        pure (.val .unit)) sc) :=
  Agree.bind (ih it Γ R sw sc hi hci hst hsc) fun _ _ _ _ hp =>
    Agree.bind (sim_loop ih hb hcb hsc hp) fun _ _ _ _ ⟨hst₂, hs₂⟩ => Post.val hst₂ hs₂

end Stilt.Views
