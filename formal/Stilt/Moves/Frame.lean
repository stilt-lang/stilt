import Stilt.Moves.Relation

/-!
# What a step leaves alone

A state that evolves by writes below some references keeps every part of the
store that is disjoint from them. In a state whose references reach disjoint
parts of the store, every variable but `x` reaches a part disjoint from the
reference of `x`. Together they say that a step that writes no live binding of
`x` leaves the value of `x` as it was, which is what a call needs of a last use
passed as an argument before it (values.passing-values and values.inout-argument-order).
-/

namespace Stilt

open InPlace

namespace Value

theorem get_setSeq_disjoint {q : Path} :
    ∀ {W : List (Path × Value)} {v v' : Value}, (∀ pw ∈ W, pw.1.Disjoint q) →
      v.setSeq W = .ok v' → v'.get q = v.get q
  | [], _, _, _, h => by cases h; rfl
  | (p, w) :: W, v, v', hd, h => by
    simp only [Value.setSeq] at h
    cases h₁ : v.set p w with
    | error e => simp [h₁, Except.bind] at h
    | ok v₁ =>
      simp only [h₁, Except.bind] at h
      rw [get_setSeq_disjoint (fun pw hpw => hd pw (List.mem_cons_of_mem _ hpw)) h,
        get_of_set_disjoint (hd (p, w) List.mem_cons_self) h₁]

end Value

namespace InPlace

/-- Writes below references disjoint from `r` leave what `r` reaches. -/
theorem Evolves.deref_disjoint {E : List (Name × Ref)} {st st' : List Value} {r : Ref}
    (h : Evolves ⟨E, st⟩ ⟨E, st'⟩) (hr : r.loc < st.length) (hd : ∀ e ∈ E, e.2.Disjoint r) :
    deref ⟨[], st'⟩ r [] = deref ⟨[], st⟩ r [] := by
  obtain ⟨-, W, st₁, extra, hs, hW, hseq⟩ := h
  obtain ⟨A, B, hR, hlen, hB, -, -⟩ := setSeq_append_store (B := [])
    (fun pw hpw => atLoc_of_under (hW pw hpw)) (by rw [List.append_nil]; exact hseq)
  have hB' : B = [] := List.eq_nil_of_length_eq_zero hB
  subst hB'
  simp only [List.append_nil, Value.list.injEq] at hR
  subst hR
  have hlt : r.loc < st₁.length := hlen ▸ hr
  simp only at hs
  rw [hs, deref_store_append hlt, deref_eq_get hlt [], deref_eq_get hr []]
  refine Value.get_setSeq_disjoint (fun pw hpw => ?_) hseq
  obtain ⟨P, hP, q, hq⟩ := hW pw hpw
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hP
  rw [hq]
  simpa using Path.Disjoint.append (hd e he) q []

/-- In a state whose references reach disjoint parts of the store, a variable
other than `x` reaches a part disjoint from the reference of `x`. -/
theorem disjoint_of_lookup {x : Name} {r : Ref} :
    ∀ {env : List (Name × Ref)}, env.Pairwise (fun a b => a.2.Disjoint b.2) →
      env.lookup x = some r → ∀ e ∈ env, e.1 ≠ x → e.2.Disjoint r
  | [], _, h => by simp at h
  | (z, rz) :: env, hp, hl => by
    rw [List.pairwise_cons] at hp
    intro e he hne
    by_cases hz : z = x
    · subst hz
      simp only [List.lookup_cons_self, Option.some.injEq] at hl
      subst hl
      rcases List.mem_cons.1 he with rfl | he
      · exact absurd rfl hne
      · exact (hp.1 e he).symm
    · rw [lookup_cons_ne (Ne.symm hz)] at hl
      rcases List.mem_cons.1 he with rfl | he
      · exact hp.1 _ (mem_of_lookup hl)
      · exact disjoint_of_lookup hp.2 hl e he hne

end InPlace

end Stilt
