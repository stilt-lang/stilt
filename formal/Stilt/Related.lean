import Stilt.Semantics

/-!
# Related outcomes

A simulation says that two runs, from states that correspond, end alike: two
models of memory running the same program, or one model running a program and
its erasure. Each says it of outcomes by a relation, `Outcome.Rel`, which asks
the two to end the same way, each way with its own relation on what the two
carry: their values and states, their raised errors, their jumps, their panics
or their performances. Two performances are related when their rests are, once
resumed with values and worlds that `resume` relates. Each simulation chooses those
relations, and equality is one choice (`Outcome.rel_eq_iff`).

The steps that pass an outcome on, `Outcome.bind`, `Outcome.handle`,
`Outcome.turn` and `Outcome.unbind`, keep related outcomes related; this module
proves it once, for every simulation.
-/

namespace Stilt

variable {σ τ α β γ δ : Type}

/-- What two related outcomes relate, one relation for each way an evaluation
ends: on values with their states, on raised errors, on jumps, on panics and on
performances, each with its states; and `resume`, of an operation, on the
values and the worlds that may resume two performances of it. -/
structure Outcome.Relation (σ τ α β : Type) where
  done : α → σ → β → τ → Prop
  raised : Value → σ → Value → τ → Prop
  jumped : Jump → σ → Jump → τ → Prop
  panicked : PanicKind → σ → PanicKind → τ → Prop
  performed : Operation → Value → σ → Operation → Value → τ → Prop
  resume : Operation → Value → World → Value → World → Prop

/-- Two outcomes that end the same way, with what they carry related by `R`:
values, raises, jumps and panics, each with its state; performances, whose
rests are related once resumed with values that `R` relates; or both out of
fuel, or both stuck. -/
def Outcome.Rel (R : Outcome.Relation σ τ α β) : Outcome σ α → Outcome τ β → Prop
  | .done a s, .done b t => R.done a s b t
  | .raised e s, .raised e' t => R.raised e s e' t
  | .jumped j s, .jumped j' t => R.jumped j s j' t
  | .panicked k s, .panicked k' t => R.panicked k s k' t
  | .performed op v s k, .performed op' v' t k' =>
    R.performed op v s op' v' t ∧
      ∀ w x w' x', R.resume op w x w' x' → Outcome.Rel R (k w x) (k' w' x')
  | .outOfFuel, .outOfFuel => True
  | .stuck, .stuck => True
  | _, _ => False

namespace Outcome.Relation

/-- Equality of what two outcomes carry, a performance resumed alike. -/
def eq : Relation σ σ α α where
  done a s b t := a = b ∧ s = t
  raised e s e' t := e = e' ∧ s = t
  jumped j s j' t := j = j' ∧ s = t
  panicked k s k' t := k = k' ∧ s = t
  performed op v s op' v' t := op = op' ∧ v = v' ∧ s = t
  resume _ w x w' x' := w = w' ∧ x = x'

/-- `R'` relates every raise, jump, panic and performance that `R` relates,
and `R` every value that resumes a performance which `R'` relates: what a step
that runs after a value leaves as it is. -/
def Escapes (R : Relation σ τ α β) (R' : Relation σ τ γ δ) : Prop :=
  (∀ e s e' t, R.raised e s e' t → R'.raised e s e' t) ∧
    (∀ j s j' t, R.jumped j s j' t → R'.jumped j s j' t) ∧
    (∀ k s k' t, R.panicked k s k' t → R'.panicked k s k' t) ∧
    (∀ op v s op' v' t, R.performed op v s op' v' t → R'.performed op v s op' v' t) ∧
    (∀ op w x w' x', R'.resume op w x w' x' → R.resume op w x w' x')

/-- `R'` relates everything that `R` relates. -/
def Sub (R R' : Relation σ τ α β) : Prop :=
  (∀ a s b t, R.done a s b t → R'.done a s b t) ∧ R.Escapes R'

theorem Sub.escapes {R R' : Relation σ τ α β} (h : R.Sub R') : R.Escapes R' := h.2

/-- A relation that relates performances and resumptions as another does. -/
def Performs (R : Relation σ τ α β) (R' : Relation σ τ γ δ) : Prop :=
  (∀ op v s op' v' t, R.performed op v s op' v' t → R'.performed op v s op' v' t) ∧
    (∀ op w x w' x', R'.resume op w x w' x' → R.resume op w x w' x')

theorem Escapes.performs {R : Relation σ τ α β} {R' : Relation σ τ γ δ} (h : R.Escapes R') :
    R.Performs R' :=
  h.2.2.2

end Outcome.Relation

open Outcome.Relation

namespace Outcome

/-- Two outcomes related by equality are equal, and the other way round:
equal outcomes are the instance of `Rel` at equality. -/
theorem rel_eq_iff {o o' : Outcome σ α} : o.Rel Relation.eq o' ↔ o = o' := by
  constructor
  · intro h
    induction o generalizing o' with
    | performed op v s k ih =>
      cases o' with
      | performed op' v' t k' =>
        obtain ⟨⟨rfl, rfl, rfl⟩, hk⟩ := h
        have : k = k' := funext fun w => funext fun x => ih w x (hk w x w x ⟨rfl, rfl⟩)
        rw [this]
      | _ => exact absurd h id
    | _ =>
      cases o' <;> simp only [Rel, Relation.eq] at h <;>
        first | (obtain ⟨rfl, rfl⟩ := h; rfl) | (cases h) | rfl
  · rintro rfl
    induction o with
    | performed op v s k ih =>
      exact ⟨⟨rfl, rfl, rfl⟩, fun w x w' x' ⟨hw, hx⟩ => hw ▸ hx ▸ ih w x⟩
    | _ => simp [Rel, Relation.eq]

/-- Two related performances, by what their rests do once resumed. -/
theorem Rel.performed {R : Relation σ τ α β} {op op' : Operation} {v v' : Value} {s : σ} {t : τ}
    {k : Value → World → Outcome σ α} {k' : Value → World → Outcome τ β} :
    (Outcome.performed op v s k).Rel R (.performed op' v' t k') ↔
      R.performed op v s op' v' t ∧
        ∀ w x w' x', R.resume op w x w' x' → (k w x).Rel R (k' w' x') :=
  Iff.rfl

theorem Rel.mono {R R' : Relation σ τ α β} {o : Outcome σ α} {o' : Outcome τ β} (h : o.Rel R o')
    (hR : R.Sub R') : o.Rel R' o' := by
  obtain ⟨hd, hr, hj, hp, hP, hres⟩ := hR
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' t k' =>
      exact ⟨hP _ _ _ _ _ _ h.1, fun w x w' x' hw => ih w x (h.2 w x w' x' (hres _ _ _ _ _ hw))⟩
    | _ => exact absurd h id
  | _ =>
    cases o' <;> first | exact absurd h id | trivial | skip
    all_goals first | exact hd _ _ _ _ h | exact hr _ _ _ _ h | exact hj _ _ _ _ h |
      exact hp _ _ _ _ h

/-- A fault at related states, whose panics `R` relates. -/
theorem Rel.fault {R : Relation σ τ α β} {s : σ} {t : τ} (h : ∀ k, R.panicked k s k t)
    (f : Fault) : (Outcome.fault f s : Outcome σ α).Rel R (Outcome.fault f t) := by
  cases f
  · exact h _
  · trivial

/-- The steps after related values, related wherever `R` relates the values,
keep outcomes related, a performance's rest included. -/
theorem Rel.bind {R : Relation σ τ α β} {R' : Relation σ τ γ δ} {o : Outcome σ α}
    {o' : Outcome τ β} {f : α → σ → Outcome σ γ} {f' : β → τ → Outcome τ δ} (h : o.Rel R o')
    (hR : R.Escapes R') (hf : ∀ a s b t, R.done a s b t → (f a s).Rel R' (f' b t)) :
    (o.bind f).Rel R' (o'.bind f') := by
  obtain ⟨hr, hj, hp, hP, hres⟩ := hR
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' t k' =>
      exact ⟨hP _ _ _ _ _ _ h.1, fun w x w' x' hw => ih w x (h.2 w x w' x' (hres _ _ _ _ _ hw))⟩
    | _ => exact absurd h id
  | _ =>
    cases o' <;> first | exact absurd h id | trivial | skip
    all_goals first | exact hf _ _ _ _ h | exact hr _ _ _ _ h | exact hj _ _ _ _ h |
      exact hp _ _ _ _ h

/-- Handlers related wherever `R` relates the raises keep outcomes related. -/
theorem Rel.handle {R R' : Relation σ τ α β} {o : Outcome σ α} {o' : Outcome τ β}
    {g : Value → σ → Outcome σ α} {g' : Value → τ → Outcome τ β} (h : o.Rel R o')
    (hd : ∀ a s b t, R.done a s b t → R'.done a s b t)
    (hj : ∀ j s j' t, R.jumped j s j' t → R'.jumped j s j' t)
    (hp : ∀ k s k' t, R.panicked k s k' t → R'.panicked k s k' t) (hP : R.Performs R')
    (hg : ∀ e s e' t, R.raised e s e' t → (g e s).Rel R' (g' e' t)) :
    (o.handle g).Rel R' (o'.handle g') := by
  obtain ⟨hP, hres⟩ := hP
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' t k' =>
      exact ⟨hP _ _ _ _ _ _ h.1, fun w x w' x' hw => ih w x (h.2 w x w' x' (hres _ _ _ _ _ hw))⟩
    | _ => exact absurd h id
  | _ =>
    cases o' <;> first | exact absurd h id | trivial | skip
    all_goals first | exact hd _ _ _ _ h | exact hg _ _ _ _ h | exact hj _ _ _ _ h |
      exact hp _ _ _ _ h

/-- A loop body's related outcomes give related turns, when `R'` relates
the turns that its related values and jumps end. -/
theorem Rel.turn {R : Relation σ τ Value Value} {R' : Relation σ τ Bool Bool}
    {o : Outcome σ Value} {o' : Outcome τ Value} (h : o.Rel R o')
    (hd : ∀ a s b t, R.done a s b t → R'.done true s true t)
    (hr : ∀ e s e' t, R.raised e s e' t → R'.raised e s e' t)
    (hj : ∀ j s j' t, R.jumped j s j' t →
      (Outcome.jumped j s : Outcome σ Value).turn.Rel R'
        (Outcome.jumped j' t : Outcome τ Value).turn)
    (hp : ∀ k s k' t, R.panicked k s k' t → R'.panicked k s k' t) (hP : R.Performs R') :
    o.turn.Rel R' o'.turn := by
  obtain ⟨hP, hres⟩ := hP
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' t k' =>
      exact ⟨hP _ _ _ _ _ _ h.1, fun w x w' x' hw => ih w x (h.2 w x w' x' (hres _ _ _ _ _ hw))⟩
    | _ => exact absurd h id
  | jumped j s => cases o' <;> first | exact absurd h id | exact hj _ _ _ _ h
  | _ =>
    cases o' <;> first | exact absurd h id | trivial | skip
    all_goals first | exact hd _ _ _ _ h | exact hr _ _ _ _ h | exact hp _ _ _ _ h

/-- Ending a scope's binding on both sides keeps outcomes related, when `R'`
relates what `R` does once the binding is gone. -/
theorem Rel.unbind {R : Relation σ τ α β} {R' : Relation σ τ α β} (M : Memory σ) (M' : Memory τ)
    {o : Outcome σ α} {o' : Outcome τ β} (h : o.Rel R o')
    (hd : ∀ a s b t, R.done a s b t → R'.done a (M.unbind s) b (M'.unbind t))
    (hr : ∀ e s e' t, R.raised e s e' t → R'.raised e (M.unbind s) e' (M'.unbind t))
    (hj : ∀ j s j' t, R.jumped j s j' t → R'.jumped j (M.unbind s) j' (M'.unbind t))
    (hp : ∀ k s k' t, R.panicked k s k' t → R'.panicked k (M.unbind s) k' (M'.unbind t))
    (hP : ∀ op v s op' v' t, R.performed op v s op' v' t →
      R'.performed op v (M.unbind s) op' v' (M'.unbind t))
    (hres : ∀ op w x w' x', R'.resume op w x w' x' → R.resume op w x w' x') :
    (o.unbind M).Rel R' (o'.unbind M') := by
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' t k' =>
      exact ⟨hP _ _ _ _ _ _ h.1, fun w x w' x' hw => ih w x (h.2 w x w' x' (hres _ _ _ _ _ hw))⟩
    | _ => exact absurd h id
  | _ =>
    cases o' <;> first | exact absurd h id | trivial | skip
    all_goals first | exact hd _ _ _ _ h | exact hr _ _ _ _ h | exact hj _ _ _ _ h |
      exact hp _ _ _ _ h

end Outcome

end Stilt
