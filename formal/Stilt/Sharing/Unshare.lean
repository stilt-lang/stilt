import Stilt.Sharing.Store

/-!
# Stopping sharing, and writing

What `unshare`, `modify` and `assignWhole` of `Stilt.Sharing.Memory` do to a frame: a binding
that stops sharing gets a copy of its own when it referred to another's storage, and otherwise
every other binding that referred into its home does; a write the inference calls `unique`
writes where its binding refers, and a shared one stops sharing first (modes.shared-writes).
-/

namespace Stilt

namespace Sharing

open InPlace (Ref)

/-- The position that `findIdx?` finds holds the entry that `lookup` finds. -/
theorem lookup_of_findIdx? {x : Name} :
    ∀ {env : List (Name × Entry)} {i : Nat} {e : Entry}, env.findIdx? (·.1 == x) = some i →
      env.lookup x = some e → env[i]? = some (x, e)
  | [], _, _, h, _ => by simp at h
  | (y, f) :: env, i, e, h₁, h₂ => by
    by_cases hy : y = x
    · subst hy
      simp only [List.findIdx?_cons, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h₁
      subst h₁
      simp only [List.lookup_cons_self, Option.some.injEq] at h₂
      subst h₂
      rfl
    · have hb : (y == x) = false := by simpa using hy
      rw [List.findIdx?_cons, hb] at h₁
      simp only [Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h₁
      obtain ⟨j, hj, rfl⟩ := h₁
      rw [lookup_cons_ne (Ne.symm hy)] at h₂
      simpa using lookup_of_findIdx? hj h₂

/-- What `unshare s x` does: `x` is bound at the position `i` that `lookup` reads, the store
grows and the names stay; when `x` referred to another's storage, it alone gets a copy of its
own, and otherwise every other binding that referred into its home does. -/
theorem unshare_spec {s s' : State} {x : Name} (h : unshare s x = .ok s') :
    ∃ i e, s.env.findIdx? (·.1 == x) = some i ∧ s.env.lookup x = some e ∧
      (((∃ r, e.alias = some r) ∧ ∃ s₁ e', Settled s e s₁ e' ∧
          s' = { s₁ with env := s.env.set i (x, e') }) ∨
        (e.alias = none ∧ Grows s.store s'.store ∧ Evacuated e.home i s s' 0 s.env s'.env)) := by
  unfold unshare at h
  split at h
  · rename_i i e hi he
    refine ⟨i, e, hi, he, ?_⟩
    split at h
    · rename_i r hr
      obtain ⟨⟨s₁, e₁⟩, hs, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hst := settle_spec hs
      exact .inl ⟨⟨r, hr⟩, s₁, e₁, hst, by rw [hst.env]⟩
    · rename_i hr
      obtain ⟨⟨s₁, env₁⟩, hs, h⟩ := bind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨hg, -, hev⟩ := evacuate_spec hs
      exact .inr ⟨hr, hg, Evacuated.congr (s₁ := s₁) (s₂ := ⟨env₁, s₁.store⟩) rfl hev⟩
  · cases h

/-- What `modify s x path w` does: a `unique` binding is written where it refers, and a shared
one stops sharing first, and is then written where it refers. -/
theorem modify_spec {s s' : State} {x : Name} {path : Path} {w : Value}
    (h : modify s x path w = .ok s') :
    ∃ e, s.env.lookup x = some e ∧
      (e.unique = true → setAt s e.ref path w = .ok s') ∧
      (e.unique = false → ∃ s₁, unshare s x = .ok s₁ ∧ write s₁ x path w = .ok s') := by
  unfold modify at h
  split at h
  · rename_i e he
    refine ⟨e, he, fun hu => by simpa [hu] using h, fun hu => ?_⟩
    simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨s₁, hs, h⟩ := bind_ok h
    exact ⟨s₁, hs, h⟩
  · cases h

/-- What `assignWhole s x w alias?` does: a local of a copy-on-write type assigned a place comes
to refer to it; any other assignment gives every other binding that referred into the home a
copy of its own, then writes the value in the home, which the binding refers to from then on. -/
theorem assignWhole_spec {s s' : State} {x : Name} {w : Value} {alias? : Option Ref}
    (h : assignWhole s x w alias? = .ok s') :
    ∃ i e, s.env.findIdx? (·.1 == x) = some i ∧ s.env.lookup x = some e ∧
      ((∃ r, alias? = some r ∧ e.cow = true ∧ e.inout = false ∧
          s' = { s with env := s.env.set i (x, { e with alias := some r }) }) ∨
        ∃ s₁ env₁, evacuate e.home i 0 s s.env = .ok (s₁, env₁) ∧
          setAt { s₁ with env := env₁.set i (x, { e with alias := none }) } e.home [] w = .ok s') := by
  unfold assignWhole assignWhole.replace at h
  split at h
  · rename_i i e hi he
    refine ⟨i, e, hi, he, ?_⟩
    split at h
    · rename_i r
      split at h
      · rename_i hc
        simp only [Except.ok.injEq] at h
        subst h
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
        exact .inl ⟨r, rfl, hc.1, hc.2, rfl⟩
      · obtain ⟨⟨s₁, env₁⟩, hs, h⟩ := bind_ok h
        exact .inr ⟨s₁, env₁, hs, h⟩
    · obtain ⟨⟨s₁, env₁⟩, hs, h⟩ := bind_ok h
      exact .inr ⟨s₁, env₁, hs, h⟩
  · cases h

end Sharing

end Stilt
