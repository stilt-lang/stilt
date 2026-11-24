import Stilt.Views.Forms

/-!
# Places

The cases of the simulation that evaluate a place: an assignment, which
writes it where no read overlaps it (modes.change-while-iterating; views.change-while-viewed), and
`View.of`, whose window reads the place it was made from or a temporary
(views.making-view). A place's indexes are evaluated in both models alike, and its
shape is the one the static analysis compares.
-/

namespace Stilt.Views

variable {D : Decls} {loops : Bool} {n : Nat}

theorem ExceptAgree.of_eq {α : Type} {P : α → α → Prop} (x : Except Fault α) (h : ∀ a, P a a) :
    ExceptAgree P x x := by
  cases x
  · exact rfl
  · exact h _

/-- A place, evaluated in both models: the same root and path, whose fields
are its shape's. -/
theorem Simulates.place (ih : Simulates D loops n) {Γ : Sources} {R : List Shape} :
    ∀ (t : VExpr) {sw sc : VState}, t.placeExclusive loops Γ R = true → t.contained Γ = true →
      StateAgrees sw sc → InScope Γ R sw.env →
      Agree (fun s sc' (p q : Name × Path) =>
          p = q ∧ t.shape? = some ⟨p.1, fieldsOf p.2⟩ ∧ StateAgrees s sc' ∧ Steps R sw s)
        (Run.place (veval D .window n) t sw) (Run.place (veval D .copy n) t sc)
  | .var _, _, _, _, _, hst, _ => ⟨rfl, rfl, hst, Steps.refl R _⟩
  | .field e f, _, _, hex, hco, hst, hsc => by
    simp only [VExpr.placeExclusive, VExpr.contained] at hex hco
    refine Agree.bind (Simulates.place ih e hex hco hst hsc)
      fun s₁ sc₁ p q ⟨hpq, hsh, hst₁, hs₁⟩ => ?_
    subst hpq
    exact ⟨rfl, by simp [VExpr.shape?, hsh, fieldsOf_append, fieldsOf], hst₁, hs₁⟩
  | .index e i, _, _, hex, hco, hst, hsc => by
    simp only [VExpr.placeExclusive, VExpr.contained, Bool.and_eq_true] at hex hco
    refine Agree.bind (Simulates.place ih e hex.1 hco.1 hst hsc)
      fun s₁ sc₁ p q ⟨hpq, hsh, hst₁, hs₁⟩ => ?_
    subst hpq
    refine Agree.bind (ih.int hex.2 hco.2 hst₁ (hsc.after hs₁)) fun s₂ sc₂ k k' ho => ?_
    cases ho.eq
    exact ⟨rfl, by simp [VExpr.shape?, hsh, fieldsOf_append, fieldsOf], ho.states,
      hs₁.trans ho.steps fun _ h => h⟩
  | .int _, _, _, _, _, _, _ | .bool _, _, _, _, _, _, _ | .unit, _, _, _, _, _, _
  | .record _ _, _, _, _, _, _, _ | .list _ _, _, _, _, _, _, _
  | .letIn _ _ _ _, _, _, _, _, _, _ | .varIn _ _ _ _, _, _, _, _, _, _
  | .assign _ _, _, _, _, _, _, _ | .seq _ _, _, _, _, _, _, _ | .if _ _ _ _, _, _, _, _, _, _
  | .for _ _ _ _, _, _, _, _, _, _ | .viewOf _ _ _, _, _, _, _, _, _
  | .sub _ _ _, _, _, _, _, _, _ | .len _, _, _, _, _, _, _ | .copy _, _, _, _, _, _, _ =>
    Agree.stuck

/-- `View.of` in both models: a window and the part it reads. -/
theorem make_agrees (store : Store) (ℓ : Nat) (π : Path) (a b : Int) :
    ExceptAgree (fun rw rc => Agrees store rw rc ∧ rw = .window ℓ π a b)
      (Model.window.make store ℓ π a b) (Model.copy.make store ℓ π a b) := by
  unfold Model.make
  cases h : source store ℓ π with
  | error f => exact rfl
  | ok v =>
    cases v <;> try exact rfl
    dsimp only
    split
    · rename_i hb
      exact ⟨by simp [Agrees, RVal.part, h, hb], rfl⟩
    · exact rfl

section Places

variable (ih : Simulates D loops n) {Γ : Sources} {R S : List Shape} {sw sc : VState}
  (hst : StateAgrees sw sc) (hsc : InScope Γ R sw.env)
include ih hst hsc

/-- An assignment writes a place that no read overlaps (modes.change-while-iterating;
views.change-while-viewed). -/
theorem sim_assign {target value : VExpr} (ht : target.placeExclusive loops Γ R = true)
    (hv : value.exclusive loops Γ R = true) (hu : target.shape?.all (unread R) = true)
    (hct : target.contained Γ = true) (hcv : value.contained Γ = true) :
    Agree (Post R S sw) (Run.assign (veval D .window n) target value sw)
      (Run.assign (veval D .copy n) target value sc) := by
  refine Agree.bind (ih.place target ht hct hst hsc) fun s₁ sc₁ p q ⟨hpq, hsh, hst₁, hs₁⟩ => ?_
  subst hpq
  refine Agree.bind (ih.value hv hcv hst₁ (hsc.after hs₁)) fun s₂ sc₂ w w' ho => ?_
  cases ho.eq
  have hu' : unread R ⟨p.1, fieldsOf p.2⟩ = true := by
    rw [hsh] at hu
    exact hu
  have hs₂ := hs₁.trans ho.steps fun _ h => h
  refine Agree.bind (Agree.update (Q := fun s sc' _ _ => StateAgrees s sc' ∧ Steps R s₂ s)
    (ho.states.write (hsc.after hs₂) hu')) fun s₃ sc₃ _ _ ⟨hst₃, hs₃⟩ => ?_
  exact Post.val hst₃ (hs₂.trans hs₃ fun _ h => h)

/-- `View.of(x.p, a, b)`: a window into the place, whose shape is its source. -/
theorem sim_make_place {src a b : VExpr} {sh : Shape} (hs : src.shape? = some sh)
    (hp : src.placeExclusive loops Γ R = true) (ha : a.exclusive loops Γ R = true)
    (hb : b.exclusive loops Γ R = true) (hcp : src.contained Γ = true)
    (hca : a.contained Γ = true) (hcb : b.contained Γ = true) :
    Agree (Post R [sh] sw) (Run.make .window (veval D .window n) src a b sw)
      (Run.make .copy (veval D .copy n) src a b sc) := by
  unfold Run.make
  rw [hs]
  refine Agree.bind (ih.place src hp hcp hst hsc) fun s₁ sc₁ p q ⟨hpq, hsh, hst₁, hs₁⟩ => ?_
  subst hpq
  refine Agree.bind (ih.int ha hca hst₁ (hsc.after hs₁)) fun s₂ sc₂ x x' ho₂ => ?_
  have hs₂ := hs₁.trans ho₂.steps fun _ h => h
  refine Agree.bind (ih.int hb hcb ho₂.states (hsc.after hs₂)) fun s₃ sc₃ y y' ho₃ => ?_
  cases ho₂.eq
  cases ho₃.eq
  have hs₃ := hs₂.trans ho₃.steps fun _ h => h
  refine Agree.inspect ?_
  rw [← ho₃.states.loc p.1, ← ho₃.states.store]
  cases hl : s₃.loc? p.1 with
  | error f => exact rfl
  | ok ℓ =>
    refine (make_agrees s₃.store ℓ p.2 x y).mono fun rw rc _ ⟨hag, hw⟩ =>
      ⟨ho₃.states, hs₃, hag, ?_⟩
    subst hw
    rw [hs, Option.some.injEq] at hsh
    subst hsh
    intro z hz
    have hmem : (p.1, Binding.loc ℓ) ∈ sw.env := hs₃.env ▸ mem_of_lookup (loc?_lookup hl)
    rw [hsc.distinct z p.1 ℓ hz hmem]
    exact List.mem_singleton_self _

/-- `View.of(e, a, b)` for an `e` that is no place: a window into a temporary,
which no variable names (views.making-view). -/
theorem sim_make_temp {src a b : VExpr} (hs : src.shape? = none)
    (hv : src.exclusive loops Γ R = true) (ha : a.exclusive loops Γ R = true)
    (hb : b.exclusive loops Γ R = true) (hcv : src.contained Γ = true)
    (hca : a.contained Γ = true) (hcb : b.contained Γ = true) :
    Agree (Post R [] sw) (Run.make .window (veval D .window n) src a b sw)
      (Run.make .copy (veval D .copy n) src a b sc) := by
  unfold Run.make
  rw [hs]
  refine Agree.bind (ih.value hv hcv hst hsc) fun s₁ sc₁ v v' ho₁ => ?_
  cases ho₁.eq
  have ht := ho₁.states.temp v R
  refine Agree.bind (Q := fun s sc' (l l' : Nat) => l = l' ∧ l = s₁.store.length ∧
    StateAgrees s sc' ∧ Steps R sw s) ⟨by simp [ho₁.states.store], rfl, ht.1,
      ho₁.steps.trans ht.2 fun _ h => h⟩ fun s₂ sc₂ l l' ⟨hl, hl₁, hst₂, hs₂⟩ => ?_
  cases hl
  refine Agree.bind (ih.int ha hca hst₂ (hsc.after hs₂)) fun s₃ sc₃ x x' ho₃ => ?_
  have hs₃ := hs₂.trans ho₃.steps fun _ h => h
  refine Agree.bind (ih.int hb hcb ho₃.states (hsc.after hs₃)) fun s₄ sc₄ y y' ho₄ => ?_
  cases ho₃.eq
  cases ho₄.eq
  refine Agree.inspect ?_
  rw [← ho₄.states.store]
  refine (make_agrees s₄.store l [] x y).mono fun rw rc _ ⟨hag, hw⟩ =>
    ⟨ho₄.states, hs₃.trans ho₄.steps fun _ h => h, hag, ?_⟩
  subst hw
  intro z hz
  have hlt := ho₁.states.locs z l (ho₁.steps.env ▸ hz)
  omega

end Places

end Stilt.Views
