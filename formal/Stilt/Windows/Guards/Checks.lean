import Stilt.Windows.Guards.Writes
import Stilt.ViewReads

/-!
# What E0423 accepts, operand by operand

`Expr.viewsRead` checks the operands of a form in turn, each under the places read around
it and the sources of the views among the operands before it. The guard of the views clause
needs only that each operand is checked under reads that hold those around the form: these
lemmas give that, for lists of operands, the fields of a record literal, the indexes of a
place, a call's arguments and the arms of a `match`.
-/

namespace Stilt

/-- Fewer reads leave unread whatever more reads leave unread. -/
theorem unread_sub {R R' : List Shape} {s : Shape} (h : unread R' s = true)
    (hR : ∀ t ∈ R, t ∈ R') : unread R s = true := by
  rw [unread_iff] at h ⊢
  exact fun t ht => h t (hR t ht)

theorem sub_append (S R : List Shape) : ∀ t ∈ R, t ∈ S ++ R :=
  fun _ ht => List.mem_append_right _ ht

/-- A scope whose reads add some and hide those rooted at its name. -/
theorem hide_sub_hide (S R : List Shape) (x : Name) : ∀ t ∈ hide R x, t ∈ hide (S ++ R) x := by
  intro t ht
  simp only [hide, List.mem_filter] at ht ⊢
  exact ⟨List.mem_append_right _ ht.1, ht.2⟩

variable {D : Decls}

/-- Each operand of a list is checked under reads that hold those around it. -/
theorem exprsViewsRead_mem : ∀ {Γ : ViewScope} {R : List Shape} {es : List Expr},
    exprsViewsRead D Γ R es = true →
      ∀ e ∈ es, ∃ R', (∀ t ∈ R, t ∈ R') ∧ e.viewsRead D Γ R' = true
  | _, _, [], _, _, he => by cases he
  | Γ, R, e :: es, h, e', he' => by
    simp only [exprsViewsRead, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨R, fun _ h => h, h.1⟩
    · obtain ⟨R', hR', h'⟩ := exprsViewsRead_mem h.2 e' he'
      exact ⟨R', fun t ht => hR' t (List.mem_append_right _ ht), h'⟩

theorem fieldsViewsRead_mem : ∀ {Γ : ViewScope} {R : List Shape} {fs : List (Name × Expr)},
    fieldsViewsRead D Γ R fs = true →
      ∀ fe ∈ fs, ∃ R', (∀ t ∈ R, t ∈ R') ∧ fe.2.viewsRead D Γ R' = true
  | _, _, [], _, _, he => by cases he
  | _, _, (_, e) :: fs, h, fe, hfe => by
    simp only [fieldsViewsRead, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hfe with rfl | hfe
    · exact ⟨_, fun _ h => h, h.1⟩
    · obtain ⟨R', hR', h'⟩ := fieldsViewsRead_mem h.2 fe hfe
      exact ⟨R', fun t ht => hR' t (List.mem_append_right _ ht), h'⟩

theorem pathViewsRead_mem : ∀ {Γ : ViewScope} {R : List Shape} {ps : List Projection},
    pathViewsRead D Γ R ps = true → ∀ i, Projection.index i ∈ ps → i.viewsRead D Γ R = true
  | _, _, [], _, _, hi => by cases hi
  | _, _, .field _ :: ps, h, i, hi => by
    simp only [pathViewsRead] at h
    rcases List.mem_cons.1 hi with hi | hi
    · cases hi
    · exact pathViewsRead_mem h i hi
  | _, _, .index j :: ps, h, i, hi => by
    simp only [pathViewsRead, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hi with hi | hi
    · cases hi
      exact h.1
    · exact pathViewsRead_mem h.2 i hi

/-- Each arm's body is checked under the reads around the `match`, its binders' hidden. -/
theorem armsViewsRead_mem : ∀ {Γ : ViewScope} {R S : List Shape} {arms : List Arm},
    armsViewsRead D Γ R S arms = true →
      ∀ arm ∈ arms, ∃ Γ', arm.body.viewsRead D Γ' (arm.binders.foldl hide R) = true
  | _, _, _, [], _, _, h => by cases h
  | Γ, _, S, ⟨_, binders, body⟩ :: arms, h, arm, harm => by
    simp only [armsViewsRead, Bool.and_eq_true] at h
    rcases List.mem_cons.1 harm with rfl | harm
    · exact ⟨_, h.1⟩
    · exact armsViewsRead_mem h.2 arm harm

/-- The arguments of a call keep the regions when every expression checked under reads that
hold those around the call does. -/
theorem argsViewsRead_keep {G : List Path} {run : Expr → Eval (InPlace.State × World) Value}
    (ih : ∀ e Γ R, e.viewsRead D Γ R = true → Eval.Guards G R (fun _ => True) (run e)) :
    ∀ {Γ : ViewScope} {R : List Shape} {as : List Arg}, argsViewsRead D Γ R as = true →
      Eval.Guards.ArgsKeep G R run as
  | _, _, [], _ => trivial
  | Γ, R, .value e :: as, h => by
    simp only [argsViewsRead, Bool.and_eq_true] at h
    refine ⟨ih e Γ R h.1, ?_⟩
    have := argsViewsRead_keep ih h.2
    exact keep_sub this (sub_append _ R)
  | Γ, R, .inout ⟨_, ps⟩ :: as, h => by
    simp only [argsViewsRead, Bool.and_eq_true] at h
    exact ⟨fun i hi => ih i Γ R (pathViewsRead_mem h.1 i hi), argsViewsRead_keep ih h.2⟩
where
  keep_sub {R R' : List Shape} : ∀ {as : List Arg}, Eval.Guards.ArgsKeep G R' run as →
      (∀ t ∈ R, t ∈ R') → Eval.Guards.ArgsKeep G R run as
    | [], _, _ => trivial
    | .value _ :: _, ⟨he, has⟩, hR => ⟨he.sub hR, keep_sub has hR⟩
    | .inout ⟨_, _⟩ :: _, ⟨hps, has⟩, hR => ⟨fun i hi => (hps i hi).sub hR, keep_sub has hR⟩

end Stilt
