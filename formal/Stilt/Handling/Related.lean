import Stilt.Handling
import Stilt.Related

/-!
# Handling keeps outcomes related

A `with` handles related outcomes of its block alike, in every simulation whose
relation lets the two runs call related clauses from related performances,
resume with what related bodies end with, and carry what a body ends with to
the states the rest of the block left (`Outcome.Rel.handleWith`).
-/

namespace Stilt

variable {σ τ : Type}

/-- `R` relates at the frames of the states `s` and `t` whatever it relates at
any states, in their worlds: what a handler's body ends with, carried to the
frames the rest of the block left. -/
def Outcome.Relation.Lifts (M : Memory σ) (M' : Memory τ) (R : Outcome.Relation σ τ Value Value)
    (s : σ) (t : τ) : Prop :=
  let ls (s' : σ) := M.setWorld s (M.world s')
  let lt (t' : τ) := M'.setWorld t (M'.world t')
  (∀ a s' b t', R.done a s' b t' → R.done a (ls s') b (lt t')) ∧
    (∀ e s' e' t', R.raised e s' e' t' → R.raised e (ls s') e' (lt t')) ∧
    (∀ j s' j' t', R.jumped j s' j' t' → R.jumped j (ls s') j' (lt t')) ∧
    (∀ k s' k' t', R.panicked k s' k' t' → R.panicked k (ls s') k' (lt t')) ∧
    (∀ op v s' op' v' t', R.performed op v s' op' v' t' → R.performed op v (ls s') op' v' (lt t'))

/-- Two clauses of related handlers: both missing, or related by `C`. -/
def ClauseRel (C : Value → Value → Prop) : Option Value → Option Value → Prop
  | some c, some c' => C c c'
  | none, none => True
  | _, _ => False

namespace Outcome

variable {R : Relation σ τ Value Value} {M : Memory σ} {M' : Memory τ}

theorem Rel.lift {s : σ} {t : τ} (hL : R.Lifts M M' s t) {o : Outcome σ Value}
    {o' : Outcome τ Value} (h : o.Rel R o') : (o.lift M s).Rel R (o'.lift M' t) := by
  obtain ⟨hd, hr, hj, hp, hP⟩ := hL
  induction o generalizing o' with
  | performed op v s₁ k ih =>
    cases o' with
    | performed op' v' t₁ k' =>
      exact ⟨hP _ _ _ _ _ _ h.1, fun w x w' x' hw => ih w x (h.2 w x w' x' hw)⟩
    | _ => exact absurd h id
  | _ =>
    cases o' <;> first | exact absurd h id | trivial | skip
    all_goals first | exact hd _ _ _ _ h | exact hr _ _ _ _ h | exact hj _ _ _ _ h |
      exact hp _ _ _ _ h

/-- The bodies of handlers that take control, related, run alike when their
`resume`s run related rests of the block. -/
theorem Rel.runBody {resume : Value → World → Outcome σ Value}
    {resume' : Value → World → Outcome τ Value}
    (hres : ∀ a s b t, R.done a s b t → R.resume .resume a (M.world s) b (M'.world t))
    (hlift : ∀ r s r' t, R.done r s r' t → R.Lifts M M' s t)
    (hr : ∀ u s u' t, R.performed .resume u s .resume u' t →
      (resume u (M.world s)).Rel R (resume' u' (M'.world t)))
    (hop : ∀ op v s op' v' t, R.performed op v s op' v' t → op' = op) {o : Outcome σ Value}
    {o' : Outcome τ Value} (h : o.Rel R o') :
    (o.runBody M resume).Rel R (o'.runBody M' resume') := by
  induction o generalizing o' with
  | performed op u s k ih =>
    cases o' with
    | performed op' u' t k' =>
      have hoo := (hop _ _ _ _ _ _ h.1).symm
      subst hoo
      unfold Outcome.runBody
      split
      · rename_i hres'
        subst hres'
        refine Rel.bind (hr _ _ _ _ h.1) ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h,
          fun _ _ _ _ h => h, fun _ _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩ ?_
        intro r s₃ r' t₃ hd
        exact Rel.lift (hlift _ _ _ _ hd) (ih r _ (h.2 r _ r' _ (hres _ _ _ _ hd)))
      · exact ⟨h.1, fun w x w' x' hw => ih w x (h.2 w x w' x' hw)⟩
    | _ => exact absurd h id
  | _ => cases o' <;> first | exact absurd h id | exact h

/-- **Handling keeps outcomes related.** A `with` of related handlers, whose
clauses called from related performances end alike, handles related outcomes of
its block alike. -/
theorem Rel.handleWith {C : Value → Value → Prop} {effect : Name} {control : Bool}
    {hv hv' : Value} {call : Value → Value → σ → Outcome σ Value}
    {call' : Value → Value → τ → Outcome τ Value}
    (hop : ∀ op v s op' v' t, R.performed op v s op' v' t → op' = op)
    (hcl : ∀ n, ClauseRel C (hv.clause? n) (hv'.clause? n))
    (hcall : ∀ c c' op v s v' t, C c c' → R.performed op v s op v' t →
      (call c v s).Rel R (call' c' v' t))
    (hres : ∀ op a s b t, R.done a s b t → R.resume op a (M.world s) b (M'.world t))
    (hresume : ∀ op u s u' t, R.performed .resume u s .resume u' t →
      R.resume op u (M.world s) u' (M'.world t))
    (hlift : ∀ r s r' t, R.done r s r' t → R.Lifts M M' s t) {o : Outcome σ Value}
    {o' : Outcome τ Value} (h : o.Rel R o') :
    (o.handleWith M effect control hv call).Rel R (o'.handleWith M' effect control hv' call') := by
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' t k' =>
      have hoo := (hop _ _ _ _ _ _ h.1).symm
      subst hoo
      unfold Outcome.handleWith
      split
      · have hc := hcl op.name
        revert hc
        cases hv.clause? op.name <;> cases hv'.clause? op.name <;> intro hc <;>
          first | exact absurd hc id | trivial | skip
        rename_i c c'
        dsimp only
        split
        · exact Rel.runBody (hres .resume) hlift
            (fun u _ u' _ hu => ih u _ (h.2 u _ u' _ (hresume _ _ _ _ _ hu))) hop
            (hcall c c' op v s v' t hc h.1)
        · refine Rel.bind (hcall c c' op v s v' t hc h.1) ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h,
            fun _ _ _ _ h => h, fun _ _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩ ?_
          intro w s₂ w' t₂ hd
          exact ih w _ (h.2 w _ w' _ (hres op _ _ _ _ hd))
      · exact ⟨h.1, fun w x w' x' hw => ih w x (h.2 w x w' x' hw)⟩
    | _ => exact absurd h id
  | _ => cases o' <;> first | exact absurd h id | exact h

end Outcome

end Stilt
