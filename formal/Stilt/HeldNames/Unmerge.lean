import Stilt.HeldNames

/-!
# Coarser names, more overlaps

`Expr.exclusive_unmerge`: code that obeys the law of exclusivity with some names written as
coarser ones obeys it with them written as finer ones, when it binds none of them. Writing
names as one only makes more places overlap: two shapes that overlap under the finer names
overlap under the coarser, and a binding hides the same shapes under both
(shared.names-that-may-be-one-place).
-/

namespace Stilt

section

variable {P : Name → Bool} {f m : Name → Name}

mutual

/-- The law with names written by `m` gives it with them written by `f`. -/
theorem Expr.exclusive_unmerge (h : Merges P f m) :
    ∀ (e : Expr) (r : List Shape), e.bindsNone P = true →
    (e.rename m).exclusive (r.map (Shape.rename m)) = true →
    (e.rename f).exclusive (r.map (Shape.rename f)) = true
  | .var _, _, _, _ | .move _, _, _, _ | .int _, _, _, _ | .bool _, _, _, _ | .unit, _, _, _
  | .break, _, _, _ | .continue, _, _, _ | .fnRef .., _, _, _ | .method .., _, _, _ => rfl
  | .record _ _ fs, r, hb, he => fieldsExclusive_unmerge h fs r hb he
  | .variant _ _ _ es, r, hb, he | .list _ es, r, hb, he | .op _ es, r, hb, he
  | .view es, r, hb, he => exprsExclusive_unmerge h es r hb he
  | .field e _, r, hb, he | .raise e, r, hb, he | .try e, r, hb, he | .form _ e, r, hb, he | .return e, r, hb, he
  | .loop e, r, hb, he | .perform _ e, r, hb, he => Expr.exclusive_unmerge h e r hb he
  | .closure _ _ _ e, _, hb, he => Expr.exclusive_unmerge h e [] hb he
  | .index a b, r, hb, he | .seq a b, r, hb, he | .while a b, r, hb, he
  | .withH _ _ a b, r, hb, he => by
    simp only [Expr.bindsNone, Bool.and_eq_true] at hb
    simp only [Expr.rename, Expr.exclusive, Bool.and_eq_true] at he ⊢
    exact ⟨Expr.exclusive_unmerge h a r hb.1 he.1, Expr.exclusive_unmerge h b r hb.2 he.2⟩
  | .letIn x _ a b, r, hb, he | .varIn x _ a b, r, hb, he | .tryCatch a _ x b _, r, hb, he => by
    simp only [Expr.bindsNone, Bool.and_eq_true, Bool.not_eq_true'] at hb
    simp only [Expr.rename, Expr.exclusive, Bool.and_eq_true] at he ⊢
    rw [h.m_off x hb.1.1, hide_rename h.m_off h.m_in hb.1.1] at he
    rw [h.f_off x hb.1.1, hide_rename h.f_off h.f_in hb.1.1]
    exact ⟨Expr.exclusive_unmerge h a r hb.1.2 he.1, Expr.exclusive_unmerge h b _ hb.2 he.2⟩
  | .for x _ a b, r, hb, he => by
    simp only [Expr.bindsNone, Bool.and_eq_true, Bool.not_eq_true'] at hb
    simp only [Expr.rename, Expr.exclusive, Bool.and_eq_true] at he ⊢
    rw [h.m_off x hb.1.1, iterated_rename, ← List.map_append,
      hide_rename h.m_off h.m_in hb.1.1] at he
    rw [h.f_off x hb.1.1, iterated_rename, ← List.map_append, hide_rename h.f_off h.f_in hb.1.1]
    exact ⟨Expr.exclusive_unmerge h a r hb.1.2 he.1, Expr.exclusive_unmerge h b _ hb.2 he.2⟩
  | .call callee args _, r, hb, he => by
    simp only [Expr.bindsNone, Bool.and_eq_true] at hb
    simp only [Expr.rename, Expr.exclusive, Bool.and_eq_true, inoutShapes_rename] at he ⊢
    exact ⟨⟨⟨Expr.exclusive_unmerge h callee r hb.1 he.1.1.1,
      argsExclusive_unmerge h args r hb.2 he.1.1.2⟩, h.all_unread_of he.1.2⟩, h.disjoint_of he.2⟩
  | .assign ⟨x, path⟩ v, r, hb, he => by
    simp only [Expr.bindsNone, Bool.and_eq_true] at hb
    simp only [Expr.rename, Expr.exclusive, Bool.and_eq_true, shape_rename] at he ⊢
    exact ⟨⟨pathExclusive_unmerge h path r hb.1 he.1.1, Expr.exclusive_unmerge h v r hb.2 he.1.2⟩,
      h.unread_of he.2⟩
  | .if c _ a b, r, hb, he => by
    simp only [Expr.bindsNone, Bool.and_eq_true] at hb
    simp only [Expr.rename, Expr.exclusive, Bool.and_eq_true] at he ⊢
    exact ⟨⟨Expr.exclusive_unmerge h c r hb.1.1 he.1.1, Expr.exclusive_unmerge h a r hb.1.2 he.1.2⟩,
      Expr.exclusive_unmerge h b r hb.2 he.2⟩
  | .match e _ arms, r, hb, he => by
    simp only [Expr.bindsNone, Bool.and_eq_true] at hb
    simp only [Expr.rename, Expr.exclusive, Bool.and_eq_true] at he ⊢
    exact ⟨Expr.exclusive_unmerge h e r hb.1 he.1, armsExclusive_unmerge h arms r hb.2 he.2⟩
  | .held ns hs b, r, hb, he => by
    simp only [Expr.bindsNone, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hb
    simp only [Expr.rename, Expr.exclusive, Bool.and_eq_true, List.map_map] at he ⊢
    have hns : ∀ x ∈ ns.map Prod.fst, P x = false := fun x hx => by
      obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hx
      exact hb.1.1 n hn
    have hm : (Prod.fst ∘ fun p : Name × Ty => (m p.1, p.2)) = m ∘ Prod.fst := rfl
    have hf : (Prod.fst ∘ fun p : Name × Ty => (f p.1, p.2)) = f ∘ Prod.fst := rfl
    rw [hm, ← List.map_map, foldl_hide_rename h.m_off h.m_in _ _ hns] at he
    rw [hf, ← List.map_map, foldl_hide_rename h.f_off h.f_in _ _ hns]
    exact ⟨exprsExclusive_unmerge h hs r hb.1.2 he.1, Expr.exclusive_unmerge h b _ hb.2 he.2⟩

theorem exprsExclusive_unmerge (h : Merges P f m) :
    ∀ (es : List Expr) (r : List Shape), exprsBindsNone P es = true →
    exprsExclusive (r.map (Shape.rename m)) (renameExprs m es) = true →
    exprsExclusive (r.map (Shape.rename f)) (renameExprs f es) = true
  | [], _, _, _ => rfl
  | e :: es, r, hb, he => by
    simp only [exprsBindsNone, renameExprs, exprsExclusive, Bool.and_eq_true] at hb he ⊢
    exact ⟨Expr.exclusive_unmerge h e r hb.1 he.1, exprsExclusive_unmerge h es r hb.2 he.2⟩

theorem fieldsExclusive_unmerge (h : Merges P f m) :
    ∀ (fs : List (Name × Expr)) (r : List Shape),
    fieldsBindsNone P fs = true →
    fieldsExclusive (r.map (Shape.rename m)) (renameFields m fs) = true →
    fieldsExclusive (r.map (Shape.rename f)) (renameFields f fs) = true
  | [], _, _, _ => rfl
  | (_, e) :: fs, r, hb, he => by
    simp only [fieldsBindsNone, renameFields, fieldsExclusive, Bool.and_eq_true] at hb he ⊢
    exact ⟨Expr.exclusive_unmerge h e r hb.1 he.1, fieldsExclusive_unmerge h fs r hb.2 he.2⟩

theorem argsExclusive_unmerge (h : Merges P f m) :
    ∀ (args : List Arg) (r : List Shape), argsBindsNone P args = true →
    argsExclusive (r.map (Shape.rename m)) (renameArgs m args) = true →
    argsExclusive (r.map (Shape.rename f)) (renameArgs f args) = true
  | [], _, _, _ => rfl
  | .value e :: args, r, hb, he => by
    simp only [argsBindsNone, renameArgs, argsExclusive, Bool.and_eq_true] at hb he ⊢
    exact ⟨Expr.exclusive_unmerge h e r hb.1 he.1, argsExclusive_unmerge h args r hb.2 he.2⟩
  | .inout ⟨_, path⟩ :: args, r, hb, he => by
    simp only [argsBindsNone, renameArgs, argsExclusive, Bool.and_eq_true] at hb he ⊢
    exact ⟨pathExclusive_unmerge h path r hb.1 he.1, argsExclusive_unmerge h args r hb.2 he.2⟩

theorem pathExclusive_unmerge (h : Merges P f m) :
    ∀ (path : List Projection) (r : List Shape),
    pathBindsNone P path = true →
    pathExclusive (r.map (Shape.rename m)) (renamePath m path) = true →
    pathExclusive (r.map (Shape.rename f)) (renamePath f path) = true
  | [], _, _, _ => rfl
  | .field _ :: path, r, hb, he => by
    simp only [pathBindsNone, renamePath, pathExclusive] at hb he ⊢
    exact pathExclusive_unmerge h path r hb he
  | .index i :: path, r, hb, he => by
    simp only [pathBindsNone, renamePath, pathExclusive, Bool.and_eq_true] at hb he ⊢
    exact ⟨Expr.exclusive_unmerge h i r hb.1 he.1, pathExclusive_unmerge h path r hb.2 he.2⟩

theorem armsExclusive_unmerge (h : Merges P f m) :
    ∀ (arms : List Arm) (r : List Shape), armsBindsNone P arms = true →
    armsExclusive (r.map (Shape.rename m)) (renameArms m arms) = true →
    armsExclusive (r.map (Shape.rename f)) (renameArms f arms) = true
  | [], _, _, _ => rfl
  | ⟨_, binders, g, b⟩ :: arms, r, hb, he => by
    simp only [armsBindsNone, renameArms, armsExclusive, Bool.and_eq_true, List.all_eq_true,
      Bool.not_eq_true'] at hb he ⊢
    rw [foldl_hide_rename h.m_off h.m_in _ _ hb.1.1.1] at he
    rw [foldl_hide_rename h.f_off h.f_in _ _ hb.1.1.1]
    exact ⟨⟨guardExclusive_unmerge h g _ hb.1.1.2 he.1.1, Expr.exclusive_unmerge h b _ hb.1.2 he.1.2⟩,
      armsExclusive_unmerge h arms r hb.2 he.2⟩

theorem guardExclusive_unmerge (h : Merges P f m) :
    ∀ (g : Option Expr) (r : List Shape), guardBindsNone P g = true →
    guardExclusive (r.map (Shape.rename m)) (renameGuard m g) = true →
    guardExclusive (r.map (Shape.rename f)) (renameGuard f g) = true
  | none, _, _, _ => rfl
  | some g, r, hb, he => Expr.exclusive_unmerge h g r hb he

end

end

/-- `f` writes each name of a `when` as itself or as one of its names of the same type, and
every other name as itself: the block the export writes for handles some of which are equal
(shared.names-that-may-be-one-place). -/
def Held.Aliasing (ns : List (Name × Ty)) (f : Name → Name) : Prop :=
  ∀ x, f x = x ∨ (Held.tyOf ns x).isSome = true ∧ Held.tyOf ns (f x) = Held.tyOf ns x

/-- A name of a `when` has a first name of its type. -/
theorem Held.find_of_tyOf {ns : List (Name × Ty)} {x : Name} {τ : Ty}
    (h : Held.tyOf ns x = some τ) : (ns.find? fun n => n.2.beq τ).isSome = true := by
  simp only [Held.tyOf, Option.map_eq_some_iff] at h
  obtain ⟨⟨y, τ'⟩, hy, rfl⟩ := h
  exact List.find?_isSome.2 ⟨_, List.mem_of_find?_eq_some hy, Ty.beq_refl _⟩

/-- Each name of a `when` is its own type's. -/
theorem Held.tyOf_isSome {ns : List (Name × Ty)} {y : Name} {τ : Ty} (h : (y, τ) ∈ ns) :
    (Held.tyOf ns y).isSome = true := by
  simp only [Held.tyOf, Option.isSome_map]
  exact List.find?_isSome.2 ⟨_, h, by simp⟩

/-- Writing names as the first of their type is coarser than any aliasing. -/
theorem Held.Aliasing.merges {ns : List (Name × Ty)} {f : Name → Name} (hf : Held.Aliasing ns f) :
    Merges (fun x => (Held.tyOf ns x).isSome) f (Held.one ns) where
  f_off x hx := (hf x).resolve_right fun h => by rw [h.1] at hx; cases hx
  m_off x hx := by
    unfold Held.one
    cases h : Held.tyOf ns x with
    | none => rfl
    | some _ => rw [h] at hx; cases hx
  f_in x hx := by
    rcases hf x with h | h
    · rw [h]; exact hx
    · show (Held.tyOf ns (f x)).isSome = true
      rw [h.2]; exact hx
  m_in x hx := by
    show (Held.tyOf ns (Held.one ns x)).isSome = true
    unfold Held.one
    cases h : Held.tyOf ns x with
    | none => rw [h] at hx; cases hx
    | some τ =>
      dsimp only
      cases hy : ns.find? fun n => n.2.beq τ with
      | none => rw [h]; rfl
      | some y => exact Held.tyOf_isSome (List.mem_of_find?_eq_some hy)
  comp x := by
    rcases hf x with h | h
    · rw [h]
    · unfold Held.one
      rw [h.2]
      cases ht : Held.tyOf ns x with
      | none => rw [ht] at h; cases h.1
      | some τ =>
        dsimp only
        cases hy : ns.find? fun n => n.2.beq τ with
        | none =>
          have := Held.find_of_tyOf ht
          rw [hy] at this; cases this
        | some _ => rfl

/-- **Names that may be one place** (shared.names-that-may-be-one-place): in a program that
passes the rule, the block of each `when`, with any of its names written as another of the
same type, as the export writes it for handles that are equal, obeys the law of exclusivity,
when it binds none of the `when`'s names. -/
theorem Program.HeldNames.aliased {p : Program} (hp : p.HeldNames) {w : When} (hw : w ∈ p.whens)
    {f : Name → Name} (hf : Held.Aliasing w.1 f)
    (hb : w.2.bindsNone (fun x => (Held.tyOf w.1 x).isSome) = true) :
    (w.2.rename f).exclusive [] = true :=
  Expr.exclusive_unmerge hf.merges w.2 [] hb (hp w hw)

end Stilt
