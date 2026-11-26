import Stilt.Exclusivity

/-!
# Names that may be one place

shared.names-that-may-be-one-place, lifted from `Stilt.Interactions.Held` to the core calculus.
Two names of one `when` whose values have the same type may reach one value, and the block
then means what it means with the second written as the first: the export writes a `when`
as a test of its handles' equality, with that block in the branch where they are equal. The
law checks each block the export writes, and `Program.HeldNames` checks the one with every
name written as the first of its type (`Held.one`).

`Expr.exclusive_unmerge` proves that the rule is enough for all of them: renaming names to
coarser ones only makes more places overlap, so a block that obeys the law with all the
names of one type written as one obeys it with any of them written as another of its type
(`Program.HeldNames.aliased`), when it binds none of the `when`'s names, as the export's
blocks don't. Places that the rule accepts are then different places of the store whichever
names reach one value, as `accepted_disjoint` says of its model, and the in-place agreement
of `soundness` covers the block that runs.
-/

namespace Stilt

/-- A shape whose root `g` renames. -/
def Shape.rename (g : Name → Name) (s : Shape) : Shape := ⟨g s.root, s.fields⟩

mutual

/-- Whether `e` binds no name of which `P` holds, so that renaming those names hides
nothing. -/
def Expr.bindsNone (P : Name → Bool) : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => true
  | .record _ _ fields => fieldsBindsNone P fields
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => exprsBindsNone P es
  | .field e _ | .raise e | .try e | .return e | .loop e | .perform _ e
  | .closure _ _ _ e => e.bindsNone P
  | .index a b | .seq a b | .while a b | .withH _ _ a b => a.bindsNone P && b.bindsNone P
  | .letIn x _ a b | .varIn x _ a b | .for x _ a b | .tryCatch a _ x b _ =>
    !P x && a.bindsNone P && b.bindsNone P
  | .call callee args _ => callee.bindsNone P && argsBindsNone P args
  | .assign ⟨_, path⟩ value => pathBindsNone P path && value.bindsNone P
  | .if c _ a b => c.bindsNone P && a.bindsNone P && b.bindsNone P
  | .match e _ arms => e.bindsNone P && armsBindsNone P arms
  | .held ns hs body => ns.all (fun n => !P n.1) && exprsBindsNone P hs && body.bindsNone P

def exprsBindsNone (P : Name → Bool) : List Expr → Bool
  | [] => true
  | e :: es => e.bindsNone P && exprsBindsNone P es

def fieldsBindsNone (P : Name → Bool) : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.bindsNone P && fieldsBindsNone P fields

def argsBindsNone (P : Name → Bool) : List Arg → Bool
  | [] => true
  | .value e :: args => e.bindsNone P && argsBindsNone P args
  | .inout ⟨_, path⟩ :: args => pathBindsNone P path && argsBindsNone P args

def pathBindsNone (P : Name → Bool) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathBindsNone P path
  | .index i :: path => i.bindsNone P && pathBindsNone P path

def armsBindsNone (P : Name → Bool) : List Arm → Bool
  | [] => true
  | ⟨_, binders, body⟩ :: arms => binders.all (fun x => !P x) && body.bindsNone P &&
    armsBindsNone P arms

end

/-- `m` writes the names of which `P` holds as coarser ones than `f` does: both leave every
other name, send those names to such names, and `m` gives each what it gives its image by
`f`. -/
structure Merges (P : Name → Bool) (f m : Name → Name) : Prop where
  f_off : ∀ x, P x = false → f x = x
  m_off : ∀ x, P x = false → m x = x
  f_in : ∀ x, P x = true → P (f x) = true
  m_in : ∀ x, P x = true → P (m x) = true
  comp : ∀ x, m (f x) = m x

/-! ## Shapes under renaming -/

theorem fieldNames_renamePath (g : Name → Name) : ∀ path : List Projection,
    (renamePath g path).filterMap Projection.fieldName? = path.filterMap Projection.fieldName?
  | [] => rfl
  | .field _ :: path => by
    simp [renamePath, Projection.fieldName?, fieldNames_renamePath g path]
  | .index _ :: path => by
    simp only [renamePath, List.filterMap_cons, Projection.fieldName?]
    exact fieldNames_renamePath g path

theorem shape_rename (g : Name → Name) (x : Name) (path : List Projection) :
    (Place.mk (g x) (renamePath g path)).shape = (Place.mk x path).shape.rename g := by
  simp [Place.shape, Shape.rename, fieldNames_renamePath]

theorem inoutShapes_rename (g : Name → Name) : ∀ args : List Arg,
    inoutShapes (renameArgs g args) = (inoutShapes args).map (Shape.rename g)
  | [] => rfl
  | .value _ :: args => by simp [renameArgs, inoutShapes, inoutShapes_rename g args]
  | .inout ⟨x, path⟩ :: args => by
    simp only [renameArgs, inoutShapes, List.map_cons, inoutShapes_rename g args, shape_rename]

theorem placeShape_rename (g : Name → Name) : ∀ e : Expr,
    (e.rename g).place?.map Place.shape = (e.place?.map Place.shape).map (Shape.rename g)
  | .var _ | .move _ => rfl
  | .field e f => by
    have ih := placeShape_rename g e
    simp only [Expr.rename, Expr.place?, Option.map_map] at ih ⊢
    cases h₁ : (e.rename g).place? <;> cases h₂ : e.place? <;> simp_all [Place.shape, Shape.rename,
      Projection.fieldName?]
  | .index e i => by
    have ih := placeShape_rename g e
    simp only [Expr.rename, Expr.place?, Option.map_map] at ih ⊢
    cases h₁ : (e.rename g).place? <;> cases h₂ : e.place? <;> simp_all [Place.shape, Shape.rename,
      Projection.fieldName?, List.filterMap_cons, List.filterMap_nil]
  | .assign ⟨_, _⟩ _ => rfl
  | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. | .record ..
  | .variant .. | .list .. | .op .. | .view .. | .closure .. | .call .. | .letIn .. | .varIn ..
  | .seq .. | .if .. | .match .. | .for .. | .raise .. | .try .. | .tryCatch ..
  | .while .. | .loop .. | .return .. | .perform .. | .withH .. | .held .. => rfl

theorem iterated_rename (g : Name → Name) (e : Expr) :
    iterated (e.rename g) = (iterated e).map (Shape.rename g) := by
  have h := placeShape_rename g e
  simp only [iterated] at h ⊢
  cases h₁ : (e.rename g).place? <;> cases h₂ : e.place? <;> simp_all

section

variable {P : Name → Bool} {g : Name → Name}

theorem hide_rename (hoff : ∀ x, P x = false → g x = x) (hin : ∀ x, P x = true → P (g x) = true)
    {x : Name} (hx : P x = false) (r : List Shape) :
    hide (r.map (Shape.rename g)) x = (hide r x).map (Shape.rename g) := by
  unfold hide
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro t _
  show (g t.root != x) = (t.root != x)
  cases hp : P t.root
  · rw [hoff _ hp]
  · have h1 := hin _ hp
    have h2 : g t.root ≠ x := fun he => by rw [he, hx] at h1; cases h1
    have h3 : t.root ≠ x := fun he => by rw [he, hx] at hp; cases hp
    rw [bne_iff_ne.2 h2, bne_iff_ne.2 h3]

theorem foldl_hide_rename (hoff : ∀ x, P x = false → g x = x)
    (hin : ∀ x, P x = true → P (g x) = true) :
    ∀ (xs : List Name) (r : List Shape), (∀ x ∈ xs, P x = false) →
      (xs.map g).foldl hide (r.map (Shape.rename g)) = (xs.foldl hide r).map (Shape.rename g)
  | [], _, _ => rfl
  | x :: xs, r, h => by
    simp only [List.map_cons, List.foldl_cons]
    rw [hoff x (h x List.mem_cons_self), hide_rename hoff hin (h x List.mem_cons_self)]
    exact foldl_hide_rename hoff hin xs _ fun y hy => h y (List.mem_cons_of_mem _ hy)

end

section

variable {P : Name → Bool} {f m : Name → Name} (h : Merges P f m)
include h

theorem Merges.overlaps_of {s t : Shape} (ho : (s.rename f).overlaps (t.rename f) = true) :
    (s.rename m).overlaps (t.rename m) = true := by
  simp only [Shape.overlaps, Shape.rename, Bool.and_eq_true, beq_iff_eq] at ho ⊢
  exact ⟨by rw [← h.comp s.root, ho.1, h.comp], ho.2⟩

theorem Merges.unread_of {r : List Shape} {s : Shape}
    (hu : unread (r.map (Shape.rename m)) (s.rename m) = true) :
    unread (r.map (Shape.rename f)) (s.rename f) = true := by
  simp only [unread, List.any_map, Bool.not_eq_true', List.any_eq_false, Function.comp_apply,
    Bool.not_eq_true] at hu ⊢
  intro t ht
  cases ho : (s.rename f).overlaps (t.rename f)
  · rfl
  · have := hu t ht
    rw [h.overlaps_of ho] at this
    cases this

theorem Merges.disjoint_of : ∀ {ss : List Shape},
    pairwiseDisjoint (ss.map (Shape.rename m)) = true →
      pairwiseDisjoint (ss.map (Shape.rename f)) = true
  | [], _ => rfl
  | s :: ss, hp => by
    simp only [List.map_cons, pairwiseDisjoint, Bool.and_eq_true, List.all_map, List.all_eq_true,
      Function.comp_apply, Bool.not_eq_true'] at hp ⊢
    refine ⟨fun t ht => ?_, Merges.disjoint_of hp.2⟩
    cases ho : (s.rename f).overlaps (t.rename f)
    · rfl
    · have := hp.1 t ht
      rw [h.overlaps_of ho] at this
      cases this

theorem Merges.all_unread_of {r ss : List Shape}
    (hu : (ss.map (Shape.rename m)).all (unread (r.map (Shape.rename m))) = true) :
    (ss.map (Shape.rename f)).all (unread (r.map (Shape.rename f))) = true := by
  simp only [List.all_map, List.all_eq_true, Function.comp_apply] at hu ⊢
  exact fun s hs => h.unread_of (hu s hs)

end

end Stilt
