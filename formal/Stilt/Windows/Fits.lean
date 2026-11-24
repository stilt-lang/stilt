import Stilt.Windows.Agree

/-!
# Where windows lie, and what guards them

Lemmas on `Tracked`, `Unreached` and `Fits`, and how they give a window guarded by the reads
around: one that no variable reaches is guarded by any reads, and one that a value's sources
track, when the reads hold those sources and distinct variables reach disjoint parts of the
store (`guarded_of_tracked`). A new binding, at a new location, keeps a window guarded when the
reads in its scope hide only the shapes of its name (`Guarded.bind_hide`).
-/

namespace Stilt

open InPlace (Ref)

/-! ## Values the checks accept, and their parts -/

namespace Value.Viewed

variable {D : Decls}

theorem passesToParts (D : Decls) : Value.PassesToParts (Value.Viewed D) where
  record _ _ h := by cases h; assumption
  variant _ _ _ h := by cases h; assumption
  list _ := ⟨fun h => by cases h; assumption, .list⟩

theorem get {v w : Value} {p : Path} (hv : v.Viewed D) (h : v.get p = .ok w) : w.Viewed D := by
  induction p generalizing v with
  | nil => cases h; exact hv
  | cons s p ih =>
    cases s with
    | field f =>
      cases v with
      | record R fields =>
        simp only [Value.get] at h
        split at h
        · rename_i x hx
          cases hv with
          | record hfs => exact ih (hfs (f, x) (mem_of_lookup hx)) h
        · cases h
      | _ => cases h
    | index i =>
      cases v with
      | list vs =>
        simp only [Value.get] at h
        split at h
        · rename_i x hx
          cases hv with
          | list hvs => exact ih (hvs x (mem_of_elemAt? hx)) h
        · cases h
      | _ => cases h

theorem set {v w v' : Value} {p : Path} (hv : v.Viewed D) (hw : w.Viewed D)
    (h : v.set p w = .ok v') : v'.Viewed D := by
  induction p generalizing v v' with
  | nil => cases h; exact hw
  | cons s p ih =>
    cases s with
    | field f =>
      cases v with
      | record R fields =>
        simp only [Value.set] at h
        split at h
        · rename_i x hx
          cases hx' : x.set p w with
          | error e => simp [hx', Functor.map, Except.map] at h
          | ok x' =>
            simp only [hx', Functor.map, Except.map, Except.ok.injEq] at h
            subst h
            cases hv with
            | record hfs =>
              refine .record fun fv hfv => ?_
              rcases mem_assocSet hfv with hfv | hfv
              · exact hfs fv hfv
              · exact hfv ▸ ih (hfs (f, x) (mem_of_lookup hx)) hx'
        · cases h
      | _ => cases h
    | index i =>
      cases v with
      | list vs =>
        simp only [Value.set] at h
        split at h
        · rename_i x hx
          cases hx' : x.set p w with
          | error e => simp [hx', Functor.map, Except.map] at h
          | ok x' =>
            simp only [hx', Functor.map, Except.map, Except.ok.injEq] at h
            subst h
            cases hv with
            | list hvs =>
              refine .list fun u hu => ?_
              rcases List.mem_or_eq_of_mem_set hu with hu | rfl
              · exact hvs u hu
              · exact ih (hvs x (mem_of_elemAt? hx)) hx'
        · cases h
      | _ => cases h

end Value.Viewed

namespace Windows

/-! ## Where windows lie -/

theorem Window.loc_of_toPath {w : Window} {r : Ref} {q : Path}
    (h : w.ref.toPath = r.toPath ++ q) : w.1 = r.loc := by
  simp only [Window.ref, InPlace.Ref.toPath, List.cons_append, List.cons.injEq,
    Step.index.injEq] at h
  exact_mod_cast h.1

theorem Covered.loc {env : List (Name × Ref)} {s : Shape} {w : Window} (h : Covered env s w) :
    ∃ r, (s.root, r) ∈ env ∧ w.1 = r.loc := by
  obtain ⟨r, hr, q, hq, -⟩ := h
  exact ⟨r, hr, Window.loc_of_toPath hq⟩

theorem Tracked.env_mono {env env' : List (Name × Ref)} {In : List (Name × Value)} {S : List Shape}
    {w : Window} (h : Tracked env In S w) (he : ∀ xr ∈ env, xr ∈ env') : Tracked env' In S w := by
  obtain ⟨s, hs, ⟨r, hr, hc⟩ | hb⟩ := h
  · exact ⟨s, hs, .inl ⟨r, he _ hr, hc⟩⟩
  · exact ⟨s, hs, .inr hb⟩

theorem Tracked.sub {env : List (Name × Ref)} {In : List (Name × Value)} {S S' : List Shape}
    {w : Window} (h : Tracked env In S w) (hS : ∀ s ∈ S, s ∈ S') : Tracked env In S' w := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hS s hs, h⟩

/-- A window tracked through the variables with a new one at a location it isn't on is tracked
without it. -/
theorem Tracked.pop {x : Name} {r : Ref} {env : List (Name × Ref)} {In : List (Name × Value)}
    {S : List Shape} {w : Window} (h : Tracked ((x, r) :: env) In S w) (hw : w.1 ≠ r.loc) :
    Tracked env In S w := by
  obtain ⟨s, hs, ⟨r', hr', hc⟩ | hb⟩ := h
  · rcases List.mem_cons.1 hr' with he | hr'
    · cases he
      obtain ⟨q, hq, -⟩ := hc
      exact absurd (Window.loc_of_toPath hq) hw
    · exact ⟨s, hs, .inl ⟨r', hr', hc⟩⟩
  · exact ⟨s, hs, .inr hb⟩

theorem Unreached.cons {env : List (Name × Ref)} {w : Window} (h : Unreached env w) {x : Name}
    {r : Ref} (hr : r.toPath.Disjoint w.ref.toPath) : Unreached ((x, r) :: env) w := by
  intro yr hyr
  rcases List.mem_cons.1 hyr with rfl | hyr
  · exact hr
  · exact h yr hyr

theorem Unreached.tail {env : List (Name × Ref)} {w : Window} {xr : Name × Ref}
    (h : Unreached (xr :: env) w) : Unreached env w :=
  fun yr hyr => h yr (List.mem_cons_of_mem _ hyr)

theorem disjoint_fresh {w : Window} {n : Nat} (h : w.1 < n) :
    (⟨n, []⟩ : Ref).toPath.Disjoint w.ref.toPath :=
  .inl (by simp [Window.ref]; omega)

theorem Unreached.bind {env : List (Name × Ref)} {w : Window} (h : Unreached env w) (x : Name)
    {n : Nat} (hn : w.1 < n) : Unreached ((x, ⟨n, []⟩) :: env) w :=
  h.cons (disjoint_fresh hn)

/-! ## Guards -/

theorem disjoint_append_left : ∀ {a b : Path}, a.Disjoint b → ∀ p : Path, (a ++ p).Disjoint b
  | _ :: _, _ :: _, h, _ => by
    simp only [Path.Disjoint, List.cons_append] at h ⊢
    rcases h with h | h
    · exact .inl h
    · exact .inr (disjoint_append_left h _)
  | [], _, h, _ | _ :: _, [], h, _ => by simp [Path.Disjoint] at h

/-- A region no variable reaches is guarded by any reads. -/
theorem guarded_of_unreached {env : List (Name × Ref)} {w : Window} (h : Unreached env w)
    (R : List Shape) : InPlace.Guarded R env w.ref.toPath := by
  intro y r hl p hp
  exact absurd (disjoint_append_left (h (y, r) (mem_of_lookup hl)) p) hp

theorem disjoint_self : ∀ p : Path, ¬p.Disjoint p
  | [] => by simp [Path.Disjoint]
  | s :: p => by simp only [Path.Disjoint, ne_eq, not_true_eq_false, false_or]; exact disjoint_self p

/-- Two variables whose parts of the store aren't disjoint are the same one. -/
theorem eq_of_not_disjoint {env : List (Name × Ref)}
    (hd : env.Pairwise fun a b => a.2.Disjoint b.2) {a b : Name × Ref} (ha : a ∈ env)
    (hb : b ∈ env) (h : ¬a.2.Disjoint b.2) : a = b := by
  induction env with
  | nil => cases ha
  | cons c env ih =>
    rw [List.pairwise_cons] at hd
    rcases List.mem_cons.1 ha with ha' | ha' <;> rcases List.mem_cons.1 hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd (hd.1 b hb') h
    · subst hb'; exact absurd (hd.1 a ha').symm h
    · exact ih hd.2 ha' hb'

theorem not_disjoint_of_prefix : ∀ {a b : Path}, a <+: b → ¬a.Disjoint b
  | [], _, _ => by simp [Path.Disjoint]
  | _ :: _, [], h => by simp at h
  | s :: a, t :: b, h => by
    obtain ⟨hst, hab⟩ := List.cons_prefix_cons.1 h
    subst hst
    simp only [Path.Disjoint, ne_eq, not_true_eq_false, false_or]
    exact not_disjoint_of_prefix hab

/-- Parts that extensions of two paths reach in common start at comparable paths. -/
theorem not_disjoint_base {a b p q : Path} (h : ¬(a ++ p).Disjoint (b ++ q)) : ¬a.Disjoint b := by
  rcases Path.prefix_of_not_disjoint h with h | h
  · rcases List.prefix_or_prefix_of_prefix ((List.prefix_append a p).trans h)
      (List.prefix_append b q) with h' | h'
    · exact not_disjoint_of_prefix h'
    · exact fun hd => not_disjoint_of_prefix h' hd.symm
  · rcases List.prefix_or_prefix_of_prefix ((List.prefix_append b q).trans h)
      (List.prefix_append a p) with h' | h'
    · exact fun hd => not_disjoint_of_prefix h' hd.symm
    · exact not_disjoint_of_prefix h'

/-- A window that a value's sources track is guarded by reads that hold each source whose
root's visible variable reaches it, when distinct variables reach disjoint parts and no
variable reaches what the parameters brought in. -/
theorem guarded_of_tracked {env : List (Name × Ref)} {In : List (Name × Value)} {S R : List Shape}
    {w : Window} (hd : env.Pairwise fun a b => a.2.Disjoint b.2)
    (hin : ∀ xv ∈ In, ∀ w' ∈ windowsOf xv.2, Unreached env w')
    (hS : ∀ s ∈ S, s ∈ R ∨ ∀ r, env.lookup s.root = some r → r.toPath.Disjoint w.ref.toPath)
    (h : Tracked env In S w) : InPlace.Guarded R env w.ref.toPath := by
  obtain ⟨s, hs, ⟨r, hr, q, hq, hpre⟩ | ⟨v, hv, w', hw', h1, h2⟩⟩ := h
  · intro y ry hl p hp
    have hsame : (y, ry) = (s.root, r) := by
      refine eq_of_not_disjoint hd (mem_of_lookup hl) hr fun hdj => ?_
      rw [hq] at hp
      exact not_disjoint_base hp hdj
    cases hsame
    rcases hS s hs with hR | hR
    · have hg := InPlace.guarded_of_source (π := q) hd hl hR rfl hpre
      rw [hq] at hp
      exact hg _ _ hl p hp
    · exact absurd (disjoint_append_left (hR r hl) p) hp
  · have hu : Unreached env w := by
      intro xr hxr
      have := hin (s.root, v) hv w' hw' xr hxr
      simpa [Window.ref, h1, h2] using this
    exact guarded_of_unreached hu R

/-- A new variable, at a location past a region, keeps the region guarded when the reads in
its scope keep every shape of the others. -/
theorem Guarded.bind_hide {R R' : List Shape} {env : List (Name × Ref)} {w : Window}
    (h : InPlace.Guarded R env w.ref.toPath) (x : Name) {n : Nat} (hn : w.1 < n)
    (hR : ∀ t ∈ R, t.root ≠ x → t ∈ R') :
    InPlace.Guarded R' ((x, ⟨n, []⟩) :: env) w.ref.toPath := by
  intro y r hly p hp
  by_cases hy : y = x
  · subst hy
    simp only [List.lookup_cons_self, Option.some.injEq] at hly
    subst hly
    exact absurd (disjoint_append_left (disjoint_fresh hn) p) hp
  · rw [lookup_cons_ne hy] at hly
    obtain ⟨t, ht, ho⟩ := InPlace.unread_eq_false.1 (h y r hly p hp)
    have hroot : t.root = y := by
      simp only [Shape.overlaps, Bool.and_eq_true, beq_iff_eq] at ho
      exact ho.1.symm
    exact InPlace.unread_eq_false.2 ⟨t, hR t ht (hroot ▸ hy), ho⟩

end Windows

end Stilt
