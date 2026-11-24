import Stilt.Values

/-!
# Paths

The laws of reading and writing along paths: reading along two paths in turn
is reading along both, writing back the value a path holds changes nothing, a
write leaves every disjoint path as it was, and writes to disjoint paths
commute.
-/

namespace Stilt

namespace Value

/-- Reading along a path, then along another, is reading along both. In the
in-place model, a variable bound to an `inout` parameter is a path into the
caller's variable, and this is what makes reading through it work. -/
theorem get_append (v : Value) (p q : Path) :
    v.get (p ++ q) = (v.get p).bind (·.get q) := by
  induction p generalizing v with
  | nil => rfl
  | cons s p ih =>
    cases s with
    | field f =>
      cases v with
      | record R fields =>
        simp only [List.cons_append, get]
        split <;> simp [ih, Except.bind]
      | _ => rfl
    | index i =>
      cases v with
      | list vs =>
        simp only [List.cons_append, get]
        split <;> simp [ih, Except.bind]
      | _ => rfl

/-- Writing back the value a path holds changes nothing. So an `inout`
argument that the callee leaves alone comes back unchanged (values.inout-arguments). -/
theorem set_of_get {v w : Value} {p : Path} (h : v.get p = .ok w) :
    v.set p w = .ok v := by
  induction p generalizing v with
  | nil =>
    cases h
    rfl
  | cons s p ih =>
    cases s with
    | field f =>
      cases v with
      | record R fields =>
        simp only [get] at h
        split at h
        · rename_i x hx
          simp [set, hx, ih h, assocSet_of_lookup _ _ _ hx, Functor.map, Except.map]
        · cases h
      | _ => cases h
    | index i =>
      cases v with
      | list vs =>
        simp only [get] at h
        split at h
        · rename_i x hx
          simp [set, hx, ih h, set_of_elemAt? hx, Functor.map, Except.map]
        · cases h
      | _ => cases h

/-- After a write, the path holds what was written. -/
theorem get_of_set {v w v' : Value} {p : Path} (h : v.set p w = .ok v') :
    v'.get p = .ok w := by
  induction p generalizing v v' with
  | nil =>
    cases h
    rfl
  | cons s p ih =>
    cases s with
    | field f =>
      cases v with
      | record R fields =>
        simp only [set] at h
        split at h
        · rename_i x hx
          cases hset : x.set p w with
          | error e => simp [hset, Functor.map, Except.map] at h
          | ok x' =>
            simp only [hset, Functor.map, Except.map, Except.ok.injEq] at h
            subst h
            have hsome : (fields.lookup f).isSome = true := by simp [hx]
            simp [get, lookup_assocSet_self _ _ _ hsome, ih hset]
        · cases h
      | _ => cases h
    | index i =>
      cases v with
      | list vs =>
        simp only [set] at h
        split at h
        · rename_i x hx
          cases hset : x.set p w with
          | error e => simp [hset, Functor.map, Except.map] at h
          | ok x' =>
            simp only [hset, Functor.map, Except.map, Except.ok.injEq] at h
            subst h
            simp [get, elemAt?_set_self hx, ih hset]
        · cases h
      | _ => cases h

/-- A write leaves every disjoint path as it was. -/
theorem get_of_set_disjoint {v w v' : Value} {p q : Path} (hd : p.Disjoint q)
    (h : v.set p w = .ok v') : v'.get q = v.get q := by
  induction p generalizing v v' q with
  | nil => cases q <;> simp [Path.Disjoint] at hd
  | cons s p ih =>
    cases q with
    | nil => simp [Path.Disjoint] at hd
    | cons t q =>
      cases s with
      | field f =>
        cases v with
        | record R fields =>
          simp only [set] at h
          split at h
          · rename_i x hx
            cases hset : x.set p w with
            | error e => simp [hset, Functor.map, Except.map] at h
            | ok x' =>
              simp only [hset, Functor.map, Except.map, Except.ok.injEq] at h
              subst h
              cases t with
              | index j => rfl
              | field g =>
                by_cases hfg : f = g
                · subst hfg
                  have hsome : (fields.lookup f).isSome = true := by simp [hx]
                  have hpq : Path.Disjoint p q := by simpa [Path.Disjoint] using hd
                  simp [get, lookup_assocSet_self _ _ _ hsome, hx, ih hpq hset]
                · simp [get, lookup_assocSet_ne _ _ (Ne.symm hfg)]
          · cases h
        | _ => cases h
      | index i =>
        cases v with
        | list vs =>
          simp only [set] at h
          split at h
          · rename_i x hx
            cases hset : x.set p w with
            | error e => simp [hset, Functor.map, Except.map] at h
            | ok x' =>
              simp only [hset, Functor.map, Except.map, Except.ok.injEq] at h
              subst h
              cases t with
              | field g => rfl
              | index j =>
                by_cases hij : i = j
                · subst hij
                  have hpq : Path.Disjoint p q := by simpa [Path.Disjoint] using hd
                  simp [get, elemAt?_set_self hx, hx, ih hpq hset]
                · simp [get, elemAt?_set_ne _ (nonneg_of_elemAt? hx) hij]
          · cases h
        | _ => cases h

/-- The step of `set_set_disjoint` for a path that starts with a field:
writes along it and along a disjoint path commute if writes along the rest of
it do. -/
private theorem set_set_disjoint_field {f : Name} {p : Path} {a b : Value}
    (ih : ∀ {v v₁ v₂ : Value} {q : Path}, p.Disjoint q → v.set p a = .ok v₁ →
      v₁.set q b = .ok v₂ → ∃ v₁', v.set q b = .ok v₁' ∧ v₁'.set p a = .ok v₂)
    {v v₁ v₂ : Value} {q : Path} (hd : Path.Disjoint (.field f :: p) q)
    (h₁ : v.set (.field f :: p) a = .ok v₁) (h₂ : v₁.set q b = .ok v₂) :
    ∃ v₁', v.set q b = .ok v₁' ∧ v₁'.set (.field f :: p) a = .ok v₂ := by
  cases q with
  | nil => simp [Path.Disjoint] at hd
  | cons t q =>
    cases v with
    | record R fields =>
      simp only [set] at h₁
      split at h₁
      · rename_i x hx
        cases hx' : x.set p a with
        | error e => simp [hx', Functor.map, Except.map] at h₁
        | ok x' =>
          simp only [hx', Functor.map, Except.map, Except.ok.injEq] at h₁
          subst h₁
          cases t with
          | index j => simp [set] at h₂
          | field g =>
            have hsome : (fields.lookup f).isSome = true := by simp [hx]
            by_cases hfg : f = g
            · subst hfg
              have hpq : Path.Disjoint p q := by simpa [Path.Disjoint] using hd
              simp only [set, lookup_assocSet_self _ _ _ hsome] at h₂
              cases hy : x'.set q b with
              | error e => simp [hy, Functor.map, Except.map] at h₂
              | ok y =>
                simp only [hy, Functor.map, Except.map, Except.ok.injEq] at h₂
                subst h₂
                obtain ⟨x₁, hq, hp⟩ := ih hpq hx' hy
                refine ⟨.record R (assocSet fields f x₁), ?_, ?_⟩
                · simp [set, hx, hq, Functor.map, Except.map]
                · simp [set, lookup_assocSet_self _ _ _ hsome, hp, Functor.map,
                    Except.map, assocSet_assocSet_self]
            · simp only [set, lookup_assocSet_ne _ _ (Ne.symm hfg)] at h₂
              split at h₂
              · rename_i y hy
                cases hy' : y.set q b with
                | error e => simp [hy', Functor.map, Except.map] at h₂
                | ok y' =>
                  simp only [hy', Functor.map, Except.map, Except.ok.injEq] at h₂
                  subst h₂
                  refine ⟨.record R (assocSet fields g y'), ?_, ?_⟩
                  · simp [set, hy, hy', Functor.map, Except.map]
                  · simp [set, lookup_assocSet_ne _ _ hfg, hx, hx', Functor.map,
                      Except.map, assocSet_comm _ _ _ hfg]
              · cases h₂
      · cases h₁
    | _ => cases h₁

/-- The step of `set_set_disjoint` for a path that starts with an index:
writes along it and along a disjoint path commute if writes along the rest of
it do. -/
private theorem set_set_disjoint_index {i : Int} {p : Path} {a b : Value}
    (ih : ∀ {v v₁ v₂ : Value} {q : Path}, p.Disjoint q → v.set p a = .ok v₁ →
      v₁.set q b = .ok v₂ → ∃ v₁', v.set q b = .ok v₁' ∧ v₁'.set p a = .ok v₂)
    {v v₁ v₂ : Value} {q : Path} (hd : Path.Disjoint (.index i :: p) q)
    (h₁ : v.set (.index i :: p) a = .ok v₁) (h₂ : v₁.set q b = .ok v₂) :
    ∃ v₁', v.set q b = .ok v₁' ∧ v₁'.set (.index i :: p) a = .ok v₂ := by
  cases q with
  | nil => simp [Path.Disjoint] at hd
  | cons t q =>
    cases v with
    | list vs =>
      simp only [set] at h₁
      split at h₁
      · rename_i x hx
        cases hx' : x.set p a with
        | error e => simp [hx', Functor.map, Except.map] at h₁
        | ok x' =>
          simp only [hx', Functor.map, Except.map, Except.ok.injEq] at h₁
          subst h₁
          cases t with
          | field g => simp [set] at h₂
          | index j =>
            have hi := nonneg_of_elemAt? hx
            by_cases hij : i = j
            · subst hij
              have hpq : Path.Disjoint p q := by simpa [Path.Disjoint] using hd
              simp only [set, elemAt?_set_self hx] at h₂
              cases hy : x'.set q b with
              | error e => simp [hy, Functor.map, Except.map] at h₂
              | ok y =>
                simp only [hy, Functor.map, Except.map, Except.ok.injEq] at h₂
                subst h₂
                obtain ⟨x₁, hq, hp⟩ := ih hpq hx' hy
                refine ⟨.list (vs.set i.toNat x₁), ?_, ?_⟩
                · simp [set, hx, hq, Functor.map, Except.map]
                · simp [set, elemAt?_set_self hx, hp, Functor.map, Except.map,
                    List.set_set]
            · simp only [set, elemAt?_set_ne _ hi hij] at h₂
              split at h₂
              · rename_i y hy
                cases hy' : y.set q b with
                | error e => simp [hy', Functor.map, Except.map] at h₂
                | ok y' =>
                  simp only [hy', Functor.map, Except.map, Except.ok.injEq] at h₂
                  subst h₂
                  have hj := nonneg_of_elemAt? hy
                  have hne : i.toNat ≠ j.toNat := by omega
                  refine ⟨.list (vs.set j.toNat y'), ?_, ?_⟩
                  · simp [set, hy, hy', Functor.map, Except.map]
                  · simp [set, elemAt?_set_ne _ hj (Ne.symm hij), hx, hx', Functor.map,
                      Except.map, List.set_comm _ _ hne]
              · cases h₂
      · cases h₁
    | _ => cases h₁

/-- Writes to disjoint paths commute. So when the `inout` arguments of a call
don't overlap, the order in which they are written back doesn't matter
(values.inout-argument-order; modes.overlapping-inout). -/
theorem set_set_disjoint {v a b v₁ v₂ : Value} {p q : Path} (hd : p.Disjoint q)
    (h₁ : v.set p a = .ok v₁) (h₂ : v₁.set q b = .ok v₂) :
    ∃ v₁', v.set q b = .ok v₁' ∧ v₁'.set p a = .ok v₂ := by
  induction p generalizing v v₁ v₂ q with
  | nil => cases q <;> simp [Path.Disjoint] at hd
  | cons s p ih =>
    cases s with
    | field f => exact set_set_disjoint_field ih hd h₁ h₂
    | index i => exact set_set_disjoint_index ih hd h₁ h₂

end Value

end Stilt
