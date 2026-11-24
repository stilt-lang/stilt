import Stilt.InPlace.Store

/-!
# How a state evolves

`Evolves s s'`: the state `s'` comes from `s` by a sequence of writes, each
below the reference of one of the variables of `s`, and by new locations past
the end of the store; the variables are the same. Every evaluation in the
in-place model evolves its state this way, so a callee's writes reach only the
caller's places that its `inout` parameters refer to.

This file proves that evaluations compose: writes and new locations compose,
and ending a binding forgets the writes to its location. It also proves that
both models write a place alike.
-/

namespace Stilt.InPlace

/-! ## Writes into the store -/

/-- A path into the store, read as a list, that starts at a location. -/
def AtLoc (p : Path) : Prop := ∃ (i : Nat) (q : Path), p = .index i :: q

/-- A write into the store below location `n`. -/
def below (n : Nat) (pw : Path × Value) : Bool :=
  match pw.1 with
  | .index i :: _ => decide (i < n)
  | _ => false

theorem get_whole {st : List Value} {r : Ref} {u : Value} (hu : st[r.loc]? = some u) (p : Path) :
    (Value.list st).get (r.toPath ++ p) = u.get (r.path ++ p) := by
  simp [Ref.toPath, Value.get, elemAt?, hu]

theorem set_whole {st : List Value} {r : Ref} {u : Value} (hu : st[r.loc]? = some u) (p : Path)
    (w : Value) : (Value.list st).set (r.toPath ++ p) w =
      (fun u' => Value.list (st.set r.loc u')) <$> u.set (r.path ++ p) w := by
  simp [Ref.toPath, Value.set, elemAt?, hu]

theorem set_append_low {A B : List Value} {i : Nat} {q : Path} {w R : Value}
    (hi : i < A.length) (h : (Value.list (A ++ B)).set (.index i :: q) w = .ok R) :
    ∃ A', R = .list (A' ++ B) ∧ A'.length = A.length ∧
      (Value.list A).set (.index i :: q) w = .ok (.list A') := by
  have hA : elemAt? (A ++ B) i = elemAt? A i := by
    simp [elemAt?, List.getElem?_append_left hi]
  simp only [Value.set, hA] at h
  split at h
  · rename_i u hu
    cases hu' : u.set q w with
    | error e => simp [hu', Functor.map, Except.map] at h
    | ok u' =>
      simp only [hu', Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      refine ⟨A.set i u', ?_, by simp, by simp [Value.set, hu, hu', Functor.map, Except.map]⟩
      simp [List.set_append_left _ _ hi]
  · cases h

theorem set_append_high {A B : List Value} {i : Nat} {q : Path} {w R : Value}
    (hi : A.length ≤ i) (h : (Value.list (A ++ B)).set (.index i :: q) w = .ok R) :
    ∃ B', R = .list (A ++ B') ∧ B'.length = B.length := by
  simp only [Value.set] at h
  split at h
  · rename_i u hu
    cases hu' : u.set q w with
    | error e => simp [hu', Functor.map, Except.map] at h
    | ok u' =>
      simp only [hu', Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      exact ⟨B.set (i - A.length) u', by simp [List.set_append_right _ _ hi], by simp⟩
  · cases h

/-- A sequence of writes into a store that ends in `B` changes `A` by its
writes below `A`'s length, and keeps the length of each part. -/
theorem setSeq_append_store :
    ∀ {W : List (Path × Value)} {A B : List Value} {R : Value}, (∀ pw ∈ W, AtLoc pw.1) →
      (Value.list (A ++ B)).setSeq W = .ok R →
      ∃ A' B', R = .list (A' ++ B') ∧ A'.length = A.length ∧ B'.length = B.length ∧
        (Value.list A).setSeq (W.filter (below A.length)) = .ok (.list A') ∧
        ((∀ pw ∈ W, below A.length pw = true) → B' = B)
  | [], A, B, R, _, h => by
    cases h
    exact ⟨A, B, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | (p, w) :: W, A, B, R, hW, h => by
    obtain ⟨i, q, rfl⟩ := hW (p, w) List.mem_cons_self
    have hW' := fun pw hpw => hW pw (List.mem_cons_of_mem _ hpw)
    simp only [Value.setSeq] at h
    cases h₁ : (Value.list (A ++ B)).set (.index i :: q) w with
    | error e => simp [h₁, Except.bind] at h
    | ok R₁ =>
      simp only [h₁, Except.bind] at h
      by_cases hi : i < A.length
      · obtain ⟨A₁, rfl, hlen, hA⟩ := set_append_low hi h₁
        obtain ⟨A', B', rfl, hlen', hB', hseq, hall⟩ := setSeq_append_store hW' h
        refine ⟨A', B', rfl, hlen'.trans hlen, hB', ?_, fun hb => hall fun pw hpw => ?_⟩
        · have hb : below A.length (.index i :: q, w) = true := by simp [below, hi]
          simp only [List.filter_cons, hb, ↓reduceIte, Value.setSeq, hA, Except.bind]
          rw [hlen] at hseq
          exact hseq
        · rw [hlen]
          exact hb pw (List.mem_cons_of_mem _ hpw)
      · obtain ⟨B₁, rfl, hlenB⟩ := set_append_high (by omega) h₁
        obtain ⟨A', B', rfl, hlen', hB', hseq, hall⟩ := setSeq_append_store hW' h
        refine ⟨A', B', rfl, hlen', hB'.trans hlenB, ?_, fun hb => ?_⟩
        · have hb : below A.length (.index i :: q, w) = false := by simp [below, hi]
          simp only [List.filter_cons, hb, Bool.false_eq_true, ↓reduceIte]
          exact hseq
        · exact absurd (hb _ List.mem_cons_self) (by simp [below, hi])

/-! ## Evolution -/

/-- The paths of the references of a state's variables. -/
def State.paths (s : State) : List Path := s.env.map fun xr => xr.2.toPath

/-- `s'` comes from `s` by writes below the references of the variables of
`s`, in some order, and by new locations past the end of its store. -/
def Evolves (s s' : State) : Prop :=
  s'.env = s.env ∧ ∃ (W : List (Path × Value)) (st extra : List Value),
    s'.store = st ++ extra ∧ (∀ pw ∈ W, pw.1.Under s.paths) ∧
      (Value.list s.store).setSeq W = .ok (.list st)

theorem atLoc_of_under {s : State} {p : Path} (h : p.Under s.paths) : AtLoc p := by
  obtain ⟨P, hP, q, rfl⟩ := h
  obtain ⟨xr, _, rfl⟩ := List.mem_map.1 hP
  exact ⟨xr.2.loc, xr.2.path ++ q, rfl⟩

theorem below_of_under {s : State} (hv : Valid s) {p : Path} (h : p.Under s.paths) (w : Value) :
    below s.store.length (p, w) = true := by
  obtain ⟨P, hP, q, rfl⟩ := h
  obtain ⟨xr, hxr, rfl⟩ := List.mem_map.1 hP
  simpa [below, Ref.toPath] using hv xr hxr

theorem Evolves.refl (s : State) : Evolves s s :=
  ⟨rfl, [], s.store, [], by simp, by simp, rfl⟩

theorem Evolves.trans {s s₁ s₂ : State} (hv : Valid s) (h₁ : Evolves s s₁) (h₂ : Evolves s₁ s₂) :
    Evolves s s₂ := by
  obtain ⟨he₁, W₁, st₁, e₁, hs₁, hW₁, hseq₁⟩ := h₁
  obtain ⟨he₂, W₂, st₂, e₂, hs₂, hW₂, hseq₂⟩ := h₂
  have hpaths : s₁.paths = s.paths := by simp [State.paths, he₁]
  rw [hpaths] at hW₂
  obtain ⟨A, B, hR, hlen, hB, -, -⟩ := setSeq_append_store (B := [])
    (fun pw hpw => atLoc_of_under (hW₁ pw hpw)) (by rw [List.append_nil]; exact hseq₁)
  have hB' : B = [] := List.eq_nil_of_length_eq_zero hB
  subst hB'
  simp only [List.append_nil, Value.list.injEq] at hR
  subst hR
  rw [hs₁] at hseq₂
  have hall : ∀ pw ∈ W₂, below st₁.length pw = true := fun pw hpw => by
    rw [hlen]
    exact below_of_under hv (hW₂ pw hpw) pw.2
  obtain ⟨A₂, B₂, hR₂, -, -, hseqA, hkeep⟩ := setSeq_append_store
    (fun pw hpw => atLoc_of_under (hW₂ pw hpw)) hseq₂
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

/-- Ending a binding keeps the writes below the other variables, and forgets
the ones to the binding's own location. -/
theorem Evolves.unbind {s s₁ : State} {x : Name} {v : Value}
    (h : Evolves (InPlace.bind s x v) s₁) : Evolves s ⟨s.env, s₁.store⟩ := by
  obtain ⟨-, W, st, extra, hs, hW, hseq⟩ := h
  obtain ⟨A, B, hR, -, -, hseqA, -⟩ := setSeq_append_store
    (fun pw hpw => atLoc_of_under (hW pw hpw)) hseq
  simp only [Value.list.injEq] at hR
  subst hR
  refine ⟨rfl, _, A, B ++ extra, by rw [hs, List.append_assoc], fun pw hpw => ?_, hseqA⟩
  obtain ⟨hpw, hb⟩ := List.mem_filter.1 hpw
  obtain ⟨P, hP, q, hq⟩ := hW pw hpw
  simp only [State.paths, InPlace.bind, List.map_cons, List.mem_cons] at hP
  rcases hP with rfl | hP
  · simp [below, hq, Ref.toPath] at hb
  · exact ⟨P, hP, q, hq⟩

/-! ## Writing a place -/

/-- Both models write a place alike: they fail alike, or they write it, the
frame and the state still agree, and the state evolves by the write. -/
theorem Agrees.write {fr : Copy.Frame} {s : State} (h : Agrees fr s) {w : Value} (hw : w.Safe)
    (x : Name) (p : Path) :
    (∃ f, Copy.write fr x p w = .error f ∧ InPlace.write s x p w = .error f) ∨
      ∃ fr' s', Copy.write fr x p w = .ok fr' ∧ InPlace.write s x p w = .ok s' ∧
        Agrees fr' s' ∧ Evolves s s' := by
  rcases h.holds.lookup x with ⟨h₁, h₂⟩ | ⟨v, r, h₁, h₂, hd⟩
  · exact .inl ⟨.stuck, by simp [Copy.write, h₁], by simp [InPlace.write, h₂]⟩
  have hlt := lt_of_deref hd
  obtain ⟨u, hu⟩ : ∃ u, s.store[r.loc]? = some u := ⟨_, List.getElem?_eq_getElem hlt⟩
  have hget : u.get r.path = .ok v := by simpa [deref, hu] using hd
  have hset : u.set (r.path ++ p) w = (v.set p w).bind fun v' => u.set r.path v' := by
    rw [Value.set_append, hget]
    rfl
  cases hv' : v.set p w with
  | error f =>
    refine .inl ⟨f, ?_, ?_⟩
    · simp [Copy.write, h₁, hv', Functor.map, Except.map]
    · simp [InPlace.write, h₂, hu, hset, hv', Except.bind, Functor.map, Except.map]
  | ok v' =>
    obtain ⟨u', hu'⟩ := Value.set_ok_of_get hget v'
    have hsetw : u.set (r.path ++ p) w = .ok u' := by rw [hset, hv']; exact hu'
    refine .inr ⟨assocSet fr x v', ⟨s.env, s.store.set r.loc u'⟩, ?_, ?_, ?_, ?_⟩
    · simp [Copy.write, h₁, hv', Functor.map, Except.map]
    · simp [InPlace.write, h₂, hu, hsetw, Functor.map, Except.map]
    · refine ⟨h.holds.write ?_ ?_ h.disjoint h₂, h.disjoint, fun xv hxv => ?_⟩
      · simp [deref, List.getElem?_set_self hlt, Value.get_of_set hu']
      · intro r' hr'
        by_cases hloc : r'.loc = r.loc
        · have hpath : r'.path.Disjoint r.path := by
            simpa [Ref.Disjoint, Ref.toPath, Path.Disjoint, hloc] using hr'
          simp [deref, hloc, List.getElem?_set_self hlt, hu,
            Value.get_of_set_disjoint hpath.symm hu']
        · simp [deref, List.getElem?_set_ne (Ne.symm hloc)]
      · rcases mem_assocSet hxv with hxv | hxv
        · exact h.safe xv hxv
        · exact hxv ▸ Value.Safe.set (h.safe (x, v) (mem_of_lookup h₁)) hw hv'
    · refine ⟨rfl, [(r.toPath ++ p, w)], s.store.set r.loc u', [], by simp, ?_, ?_⟩
      · intro pw hpw
        rw [List.mem_singleton.1 hpw]
        exact ⟨r.toPath, List.mem_map.2 ⟨(x, r), mem_of_lookup h₂, rfl⟩, p, rfl⟩
      · simp [Value.setSeq, set_whole hu, hsetw, Functor.map, Except.map, Except.bind]

end Stilt.InPlace
