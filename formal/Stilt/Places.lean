import Stilt.Values

/-!
# Places and overlap

Places, and when two of them overlap (modes.places and modes.overlap). Overlap is a
syntactic relation: it removes every index before comparing. The last theorem
shows that this is safe: places that don't overlap reach disjoint parts of a
value, whatever their indexes evaluate to.
-/

namespace Stilt

/-- The field a projection takes, if it takes one. -/
def Projection.fieldName? : Projection → Option Name
  | .field f => some f
  | .index _ => none

/-- A place holds no index: each of its projections takes a field (modes.places). -/
def Place.indexFree (p : Place) : Bool := p.path.all fun q => q.fieldName?.isSome

/-- What modes.overlap compares of a place: its root and its fields, with
every index removed. -/
structure Shape where
  root : Name
  fields : List Name
  deriving DecidableEq, Repr

/-- A place with its indexes removed. -/
def Place.shape (p : Place) : Shape := ⟨p.root, p.path.filterMap Projection.fieldName?⟩

/-- Two places overlap when, after every index is removed from both, one is a
prefix of the other (modes.overlap). So `xs[i]` overlaps every access to `xs`,
and `a.b` overlaps `a` and `a.b.c` but not `a.c`. -/
def Shape.overlaps (a b : Shape) : Bool :=
  a.root == b.root && (a.fields.isPrefixOf b.fields || b.fields.isPrefixOf a.fields)

/-- The place an expression is, if it is one: a variable followed by fields
and indexes (expressions.places). -/
def Expr.place? : Expr → Option Place
  | .var x | .move x => some ⟨x, []⟩
  | .field e f => e.place?.map fun p => ⟨p.root, p.path ++ [.field f]⟩
  | .index e i => e.place?.map fun p => ⟨p.root, p.path ++ [.index i]⟩
  | _ => none

/-- A path that evaluating the indexes of a place's projections can give: the
same fields, and an integer for each index (values.index-reads). -/
def Path.Resolves : Path → List Projection → Prop
  | [], [] => True
  | .field f :: r, .field g :: ps => f = g ∧ Path.Resolves r ps
  | .index _ :: r, .index _ :: ps => Path.Resolves r ps
  | _, _ => False

/-! ## Lemmas -/

namespace Shape

theorem overlaps_comm (a b : Shape) : a.overlaps b = b.overlaps a := by
  rw [overlaps, overlaps, Bool.beq_comm, Bool.or_comm]

theorem overlaps_self (a : Shape) : a.overlaps a = true := by
  simp [overlaps, List.isPrefixOf_iff_prefix]

/-- A place overlaps every place that extends it. -/
theorem overlaps_of_prefix {a b : Shape} (hroot : a.root = b.root)
    (h : a.fields <+: b.fields) : a.overlaps b = true := by
  simp [overlaps, hroot, List.isPrefixOf_iff_prefix, h]

end Shape

/-- An index adds nothing to a place's shape: `a[i]` counts as all of `a`
(modes.overlap). -/
theorem Place.shape_index (x : Name) (path : List Projection) (i : Expr) :
    (⟨x, path ++ [.index i]⟩ : Place).shape = (⟨x, path⟩ : Place).shape := by
  simp [Place.shape, Projection.fieldName?]

/-- A place overlaps each of its prefixes. -/
theorem Place.overlaps_append (x : Name) (path more : List Projection) :
    (⟨x, path⟩ : Place).shape.overlaps (⟨x, path ++ more⟩ : Place).shape = true :=
  Shape.overlaps_of_prefix rfl (by simp [Place.shape, List.filterMap_append])

theorem Path.disjoint_of_not_prefix :
    ∀ (ps qs : List Projection) (r r' : Path),
      (ps.filterMap Projection.fieldName?).isPrefixOf
        (qs.filterMap Projection.fieldName?) = false →
      (qs.filterMap Projection.fieldName?).isPrefixOf
        (ps.filterMap Projection.fieldName?) = false →
      r.Resolves ps → r'.Resolves qs → Path.Disjoint r r'
  | [], _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, _, h, _, _ => by simp at h
  | p :: ps, q :: qs, r, r', h₁, h₂, hr, hr' => by
    rcases r with _ | ⟨s, r⟩
    · cases p <;> simp [Path.Resolves] at hr
    rcases r' with _ | ⟨t, r'⟩
    · cases q <;> simp [Path.Resolves] at hr'
    by_cases hst : s = t
    · subst hst
      refine .inr (Path.disjoint_of_not_prefix ps qs r r' ?_ ?_ ?_ ?_)
      · cases p <;> cases q <;> cases s <;>
          simp_all [Path.Resolves, Projection.fieldName?, List.isPrefixOf,
            List.filterMap_cons]
      · cases p <;> cases q <;> cases s <;>
          simp_all [Path.Resolves, Projection.fieldName?, List.isPrefixOf,
            List.filterMap_cons]
      · cases p <;> cases s <;> simp_all [Path.Resolves]
      · cases q <;> cases s <;> simp_all [Path.Resolves]
    · exact .inl hst

/-- Places with a common root whose shapes don't overlap reach disjoint parts
of the root's value, whatever their indexes evaluate to. So modes.overlap,
which never looks at the value of an index, misses no overlap. -/
theorem Path.disjoint_of_not_overlaps {p q : Place} {r r' : Path}
    (hroot : p.root = q.root) (h : p.shape.overlaps q.shape = false)
    (hr : r.Resolves p.path) (hr' : r'.Resolves q.path) : Path.Disjoint r r' := by
  simp only [Shape.overlaps, Place.shape, hroot, beq_self_eq_true, Bool.true_and,
    Bool.or_eq_false_iff] at h
  exact Path.disjoint_of_not_prefix p.path q.path r r' h.1 h.2 hr hr'

/-! ## The table of modes.overlap -/

private def placeOf (x : Name) (path : List Projection) : Shape := (Place.mk x path).shape

example : (placeOf "a" [.field "b"]).overlaps (placeOf "a" []) = true := by decide
example : (placeOf "a" [.field "b"]).overlaps (placeOf "a" [.field "b", .field "c"]) = true := by
  decide
example : (placeOf "a" [.field "b"]).overlaps (placeOf "a" [.field "c"]) = false := by decide
example :
    (placeOf "xs" [.index (.var "i")]).overlaps (placeOf "xs" [.index (.var "j")]) = true := by
  decide
example : (placeOf "xs" [.index (.var "i")]).overlaps (placeOf "xs" []) = true := by decide

end Stilt
