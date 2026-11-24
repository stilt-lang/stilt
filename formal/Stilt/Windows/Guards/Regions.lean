import Stilt.Windows.Guards.Evolves
import Stilt.Exclusivity

/-!
# Regions that reads guard

A part of the in-place store, named by its path from the store read as a list, is
`Guarded` by the places `R` being read when every variable in scope reaches it, or a part
that holds it, or a part within it, only along a path whose shape overlaps one of `R`
(modes.overlap). A modification that `R` allows, of a place whose shape overlaps none of
`R`, then misses the part: so the reads that E0423 counts (views.change-while-viewed) keep
the parts that live views read as they were.

`Regions G R s` says that each path of `G` is such a part of `s`'s store, at one of its
locations. It survives evolution, which keeps the variables and the locations, and a new
binding, which has a new location, when the reads in its scope hide only the shapes
rooted at the new name. `guarded_of_source` gives a part guarded from the shape of a
variable's place: the parts that a window reads.
-/

namespace Stilt

/-- The fields of a path, its indexes removed: what modes.overlap compares of a place
whose indexes have been evaluated. -/
def Path.fieldNames : Path → List Name
  | [] => []
  | .field f :: p => f :: Path.fieldNames p
  | .index _ :: p => Path.fieldNames p

namespace Path

theorem fieldNames_append : ∀ (p q : Path), (p ++ q).fieldNames = p.fieldNames ++ q.fieldNames
  | [], _ => rfl
  | .field f :: p, q => by simp [fieldNames, fieldNames_append p q]
  | .index _ :: p, q => by simp [fieldNames, fieldNames_append p q]

/-- A path that resolves a place has the place's fields. -/
theorem fieldNames_of_resolves :
    ∀ {p : Path} {ps : List Projection}, p.Resolves ps →
      p.fieldNames = ps.filterMap Projection.fieldName?
  | [], [], _ => rfl
  | .field f :: p, .field g :: ps, ⟨hfg, h⟩ => by
    subst hfg
    simp [fieldNames, Projection.fieldName?, fieldNames_of_resolves h]
  | .index _ :: p, .index _ :: ps, h => by
    simp only [fieldNames, List.filterMap_cons, Projection.fieldName?]
    exact fieldNames_of_resolves (p := p) h
  | [], _ :: _, h | _ :: _, [], h => by simp [Path.Resolves] at h
  | .field _ :: _, .index _ :: _, h | .index _ :: _, .field _ :: _, h => by
    simp [Path.Resolves] at h

/-- Paths that aren't disjoint extend one another. -/
theorem prefix_of_not_disjoint : ∀ {p q : Path}, ¬p.Disjoint q → p <+: q ∨ q <+: p
  | [], _, _ => .inl (List.nil_prefix)
  | _ :: _, [], _ => .inr (List.nil_prefix)
  | s :: p, t :: q, h => by
    simp only [Path.Disjoint, not_or, Decidable.not_not] at h
    obtain ⟨rfl, h⟩ := h
    rcases prefix_of_not_disjoint h with h | h
    · exact .inl (List.cons_prefix_cons.2 ⟨rfl, h⟩)
    · exact .inr (List.cons_prefix_cons.2 ⟨rfl, h⟩)

theorem fieldNames_prefix {p q : Path} (h : p <+: q) : p.fieldNames <+: q.fieldNames := by
  obtain ⟨r, rfl⟩ := h
  rw [fieldNames_append]
  exact List.prefix_append _ _

end Path

namespace Shape

/-- A place whose fields extend those of another overlaps whatever the extension does. -/
theorem overlaps_of_append {x : Name} {f f' : List Name} {t : Shape}
    (h : (Shape.mk x (f ++ f')).overlaps t = true) : (Shape.mk x f).overlaps t = true := by
  simp only [overlaps, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    List.isPrefixOf_iff_prefix] at h ⊢
  obtain ⟨hx, h | h⟩ := h
  · exact ⟨hx, .inl ((List.prefix_append f f').trans h)⟩
  · exact ⟨hx, List.prefix_or_prefix_of_prefix h (List.prefix_append f f') |>.symm⟩

end Shape

namespace InPlace

/-- The part of the store at `g` is guarded by the places `R` being read: every variable in
scope that reaches a part not disjoint from it reaches that part by a place whose shape
overlaps one of `R`. -/
def Guarded (R : List Shape) (env : List (Name × Ref)) (g : Path) : Prop :=
  ∀ y r, env.lookup y = some r → ∀ p : Path, ¬(r.toPath ++ p).Disjoint g →
    unread R ⟨y, p.fieldNames⟩ = false

/-- Each path of `G` is a part of `s`'s store, at one of its locations, guarded by `R`. -/
def Regions (G : List Path) (R : List Shape) (s : State) : Prop :=
  ∀ g ∈ G, (∃ (ℓ : Nat) (π : Path), g = .index ℓ :: π ∧ ℓ < s.store.length) ∧
    Guarded R s.env g

/-- A path disjoint from each path of `G`. -/
def Avoids (G : List Path) (P : Path) : Prop := ∀ g ∈ G, P.Disjoint g

theorem avoids_nil (P : Path) : Avoids [] P := fun _ hg => by cases hg

theorem regions_nil (R : List Shape) (s : State) : Regions [] R s := fun _ hg => by cases hg

theorem unread_eq_false {R : List Shape} {s : Shape} :
    unread R s = false ↔ ∃ t ∈ R, s.overlaps t = true := by
  simp [unread, List.any_eq_true]

theorem Guarded.mono {R R' : List Shape} {env : List (Name × Ref)} {g : Path}
    (h : Guarded R env g) (hR : ∀ t ∈ R, t ∈ R') : Guarded R' env g := by
  intro y r hl p hp
  obtain ⟨t, ht, ho⟩ := unread_eq_false.1 (h y r hl p hp)
  exact unread_eq_false.2 ⟨t, hR t ht, ho⟩

namespace Regions

variable {G : List Path} {R R' : List Shape} {s s' : State}

theorem mono (h : Regions G R s) (hR : ∀ t ∈ R, t ∈ R') : Regions G R' s :=
  fun g hg => ⟨(h g hg).1, (h g hg).2.mono hR⟩

/-- Evolving keeps the variables and the locations, so the regions. -/
theorem evolve {ok : Path → Prop} (h : Regions G R s) (he : EvolvesBy ok s s') : Regions G R s' := by
  intro g hg
  obtain ⟨⟨ℓ, π, hgl, hl⟩, hgd⟩ := h g hg
  refine ⟨⟨ℓ, π, hgl, Nat.lt_of_lt_of_le hl he.length_le⟩, ?_⟩
  rw [he.env_eq]
  exact hgd

/-- A new binding has a new location, disjoint from every region; the reads in its scope
may hide the shapes rooted at its name, which no other variable reaches by. -/
theorem bind {x : Name} {v : Value} (h : Regions G R s) (hR : ∀ t ∈ R, t.root ≠ x → t ∈ R') :
    Regions G R' (InPlace.bind s x v) := by
  intro g hg
  obtain ⟨⟨ℓ, π, rfl, hl⟩, hgd⟩ := h g hg
  refine ⟨⟨ℓ, π, rfl, by simp [InPlace.bind]; omega⟩, fun y r hly p hp => ?_⟩
  simp only [InPlace.bind] at hly
  by_cases hy : y = x
  · subst hy
    simp only [List.lookup_cons_self, Option.some.injEq] at hly
    subst hly
    exact absurd (.inl (by simp; omega)) hp
  · rw [lookup_cons_ne hy] at hly
    obtain ⟨t, ht, ho⟩ := unread_eq_false.1 (hgd y r hly p hp)
    have hroot : t.root = y := by
      simp only [Shape.overlaps, Bool.and_eq_true, beq_iff_eq] at ho
      exact ho.1.symm
    exact unread_eq_false.2 ⟨t, hR t ht (hroot ▸ hy), ho⟩

/-- A binding whose scope's reads hide the shapes rooted at its name. -/
theorem bind_hide {x : Name} {v : Value} (h : Regions G R s) (hR : ∀ t ∈ hide R x, t ∈ R') :
    Regions G R' (InPlace.bind s x v) :=
  h.bind fun t ht hx => hR t (List.mem_filter.2 ⟨ht, by simpa using hx⟩)

end Regions

/-- A modification of a place whose shape overlaps none of the places being read, and
anything below it, misses every guarded region. -/
theorem avoids_of_unread {G : List Path} {R : List Shape} {s : State} (h : Regions G R s)
    {x : Name} {r : Ref} (hl : s.env.lookup x = some r) {p : Path} {ps : List Projection}
    (hp : p.Resolves ps) (hu : unread R (Place.mk x ps).shape = true) (q : Path) :
    Avoids G (r.toPath ++ (p ++ q)) := by
  intro g hg
  refine Classical.byContradiction fun hd => ?_
  obtain ⟨t, ht, ho⟩ := unread_eq_false.1 ((h g hg).2 x r hl (p ++ q) hd)
  rw [Path.fieldNames_append] at ho
  have ho' := Shape.overlaps_of_append ho
  rw [Path.fieldNames_of_resolves hp] at ho'
  rw [unread_iff] at hu
  exact absurd (hu t ht) (by simp [Place.shape, ho'])

/-- The part of a variable's place is guarded by reads that hold a shape of the variable
that the place extends, when the references in scope reach disjoint parts. -/
theorem guarded_of_source {R : List Shape} {env : List (Name × Ref)}
    (hd : env.Pairwise fun a b => a.2.Disjoint b.2) {y : Name} {r : Ref}
    (hl : env.lookup y = some r) {π : Path} {t : Shape} (ht : t ∈ R) (hroot : t.root = y)
    (hpre : t.fields <+: π.fieldNames) : Guarded R env (r.toPath ++ π) := by
  intro z rz hlz q hq
  by_cases hz : z = y
  · subst hz
    rw [hl] at hlz
    cases hlz
    have hq' : ¬q.Disjoint π := fun h => hq (Path.Disjoint.prefix _ h)
    refine unread_eq_false.2 ⟨t, ht, ?_⟩
    simp only [Shape.overlaps, hroot, beq_self_eq_true, Bool.true_and, Bool.or_eq_true,
      List.isPrefixOf_iff_prefix]
    rcases Path.prefix_of_not_disjoint hq' with h | h
    · exact List.prefix_or_prefix_of_prefix (Path.fieldNames_prefix h) hpre
    · exact .inr (hpre.trans (Path.fieldNames_prefix h))
  · exact absurd (Path.Disjoint.append (lookup_disjoint hd hlz hl hz) q π) hq

end InPlace

end Stilt
