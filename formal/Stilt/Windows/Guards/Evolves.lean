import Stilt.InPlace.Evolves

/-!
# Evolving by allowed writes

`EvolvesBy ok s s'` is `Evolves s s'` with each write at a path that `ok` allows: the
variables are the same, and the store comes from `s`'s by writes below the references of
`s`'s variables, each at an allowed path, and by new locations past its end. The guard of
the views clause takes for `ok` the paths disjoint from the parts that live views read
(`Stilt.Windows.Guards.Regions`), and every in-place evaluation evolves its state this way
with `ok` allowing every path (`Stilt.Windows.Guards.Writes`).

Evolutions by allowed writes compose, ending a binding forgets the writes to its location,
and writing a place evolves the state by one write below the place's variable.
-/

namespace Stilt.InPlace

/-- `s'` comes from `s` by writes below the references of the variables of `s`, each at a
path that `ok` allows, and by new locations past the end of its store. -/
def EvolvesBy (ok : Path → Prop) (s s' : State) : Prop :=
  s'.env = s.env ∧ ∃ (W : List (Path × Value)) (st extra : List Value),
    s'.store = st ++ extra ∧ (∀ pw ∈ W, pw.1.Under s.paths ∧ ok pw.1) ∧
      (Value.list s.store).setSeq W = .ok (.list st)

namespace EvolvesBy

variable {ok ok' : Path → Prop} {s s₁ s₂ : State}

theorem refl (ok : Path → Prop) (s : State) : EvolvesBy ok s s :=
  ⟨rfl, [], s.store, [], by simp, by simp, rfl⟩

theorem evolves (h : EvolvesBy ok s s₁) : Evolves s s₁ := by
  obtain ⟨he, W, st, extra, hs, hW, hseq⟩ := h
  exact ⟨he, W, st, extra, hs, fun pw hpw => (hW pw hpw).1, hseq⟩

theorem mono (h : EvolvesBy ok s s₁) (hok : ∀ P, ok P → ok' P) : EvolvesBy ok' s s₁ := by
  obtain ⟨he, W, st, extra, hs, hW, hseq⟩ := h
  exact ⟨he, W, st, extra, hs, fun pw hpw => ⟨(hW pw hpw).1, hok _ (hW pw hpw).2⟩, hseq⟩

/-- An evolution keeps the variables. -/
theorem env_eq (h : EvolvesBy ok s s₁) : s₁.env = s.env := h.1

/-- An evolution keeps the store's locations and may add more. -/
theorem length_le (h : EvolvesBy ok s s₁) : s.store.length ≤ s₁.store.length := by
  obtain ⟨-, W, st, extra, hs, hW, hseq⟩ := h
  obtain ⟨A, B, hR, hlen, hB, -, -⟩ := setSeq_append_store (B := [])
    (fun pw hpw => atLoc_of_under (hW pw hpw).1) (by rw [List.append_nil]; exact hseq)
  have hB' : B = [] := List.eq_nil_of_length_eq_zero hB
  subst hB'
  simp only [List.append_nil, Value.list.injEq] at hR
  subst hR
  rw [hs, List.length_append, hlen]
  omega

/-- An evolution keeps every reference valid. -/
theorem valid (hv : Valid s) (h : EvolvesBy ok s s₁) : Valid s₁ := fun xr hxr => by
  rw [h.env_eq] at hxr
  exact Nat.lt_of_lt_of_le (hv xr hxr) h.length_le

theorem trans (hv : Valid s) (h₁ : EvolvesBy ok s s₁) (h₂ : EvolvesBy ok s₁ s₂) :
    EvolvesBy ok s s₂ := by
  obtain ⟨he₁, W₁, st₁, e₁, hs₁, hW₁, hseq₁⟩ := h₁
  obtain ⟨he₂, W₂, st₂, e₂, hs₂, hW₂, hseq₂⟩ := h₂
  have hpaths : s₁.paths = s.paths := by simp [State.paths, he₁]
  rw [hpaths] at hW₂
  obtain ⟨A, B, hR, hlen, hB, -, -⟩ := setSeq_append_store (B := [])
    (fun pw hpw => atLoc_of_under (hW₁ pw hpw).1) (by rw [List.append_nil]; exact hseq₁)
  have hB' : B = [] := List.eq_nil_of_length_eq_zero hB
  subst hB'
  simp only [List.append_nil, Value.list.injEq] at hR
  subst hR
  rw [hs₁] at hseq₂
  have hall : ∀ pw ∈ W₂, below st₁.length pw = true := fun pw hpw => by
    rw [hlen]
    exact below_of_under hv (hW₂ pw hpw).1 pw.2
  obtain ⟨A₂, B₂, hR₂, -, -, hseqA, hkeep⟩ := setSeq_append_store
    (fun pw hpw => atLoc_of_under (hW₂ pw hpw).1) hseq₂
  rw [List.filter_eq_self.2 hall] at hseqA
  rw [hkeep hall] at hR₂
  simp only [Value.list.injEq] at hR₂
  refine ⟨he₂.trans he₁, W₁ ++ W₂, A₂, e₁ ++ e₂, by rw [hs₂, hR₂, List.append_assoc], ?_, ?_⟩
  · intro pw hpw
    rcases List.mem_append.1 hpw with hpw | hpw
    · exact hW₁ pw hpw
    · exact hW₂ pw hpw
  · rw [Value.setSeq_append, hseq₁]
    exact hseqA

/-- Ending a binding keeps the writes below the other variables, and forgets the ones to
the binding's own location. -/
theorem unbind {x : Name} {v : Value} (h : EvolvesBy ok (InPlace.bind s x v) s₁) :
    EvolvesBy ok s ⟨s.env, s₁.store⟩ := by
  obtain ⟨-, W, st, extra, hs, hW, hseq⟩ := h
  obtain ⟨A, B, hR, -, -, hseqA, -⟩ := setSeq_append_store
    (fun pw hpw => atLoc_of_under (hW pw hpw).1) hseq
  simp only [Value.list.injEq] at hR
  subst hR
  refine ⟨rfl, _, A, B ++ extra, by rw [hs, List.append_assoc], fun pw hpw => ?_, hseqA⟩
  obtain ⟨hpw, hb⟩ := List.mem_filter.1 hpw
  obtain ⟨⟨P, hP, q, hq⟩, hok⟩ := hW pw hpw
  simp only [State.paths, InPlace.bind, List.map_cons, List.mem_cons] at hP
  rcases hP with rfl | hP
  · simp [below, hq, Ref.toPath] at hb
  · exact ⟨⟨P, hP, q, hq⟩, hok⟩

end EvolvesBy

/-- Writing a place evolves the state by one write, at the place's path below its
variable's reference. -/
theorem write_evolvesBy {s s' : State} {x : Name} {p : Path} {w : Value}
    (h : InPlace.write s x p w = .ok s') :
    ∃ r, s.env.lookup x = some r ∧
      EvolvesBy (fun P => P = r.toPath ++ p) s s' := by
  unfold InPlace.write at h
  cases hl : s.env.lookup x with
  | none => rw [hl] at h; cases h
  | some r =>
    rw [hl] at h
    cases hu : s.store[r.loc]? with
    | none => simp only [hu] at h; cases h
    | some u =>
      simp only [hu] at h
      cases hset : u.set (r.path ++ p) w with
      | error e => rw [hset] at h; cases h
      | ok u' =>
        rw [hset] at h
        cases h
        refine ⟨r, rfl, rfl, [(r.toPath ++ p, w)], s.store.set r.loc u', [], by simp, ?_, ?_⟩
        · intro pw hpw
          rw [List.mem_singleton.1 hpw]
          exact ⟨⟨r.toPath, List.mem_map.2 ⟨(x, r), mem_of_lookup hl, rfl⟩, p, rfl⟩, rfl⟩
        · simp [Value.setSeq, set_whole hu, hset, Functor.map, Except.map, Except.bind]

end Stilt.InPlace
