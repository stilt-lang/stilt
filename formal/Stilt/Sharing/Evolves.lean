import Stilt.Sharing.Unshare
import Stilt.InPlace.Evolves

/-!
# How a state of sharing evolves

`Evolves s s'`: the store of `s'` comes from the store of `s` by a sequence of writes, each below
the home of one of the bindings of `s` or below the part one refers to, and by locations past the
end of the store, which may hold anything. Unlike the in-place model's, the frame may change: a
binding may come to refer to another part, or to a new home.

This file proves that a write below those paths and a store that grows are evolutions, that
evolutions compose when the later one writes the earlier store only below its paths, and that a
part of the store disjoint from every one of those paths reads alike after an evolution.
-/

namespace Stilt.Sharing
open InPlace (Ref)

/-- The paths of the homes, and of the parts referred to, of a state's bindings. -/
def State.paths (s : State) : List Path :=
  s.env.flatMap fun ye => [ye.2.home.toPath, ye.2.ref.toPath]

/-- `s'` comes from `s` by writes below the paths of `s`'s bindings, in some order, at the
locations `s` has, and by locations past the end of its store, which may hold anything. -/
def Evolves (s s' : State) : Prop :=
  ∃ (W : List (Path × Value)) (st extra : List Value),
    s'.store.toList = st ++ extra ∧ (∀ pw ∈ W, pw.1.Under s.paths) ∧
      (Value.list s.store.toList).setSeq W = .ok (.list st)

/-! ## Paths into the store -/

/-- Each path of a state starts at a location. -/
theorem atLoc_of_mem {s : State} {P : Path} (h : P ∈ s.paths) :
    ∃ (i : Nat) (q : Path), P = .index i :: q := by
  simp only [State.paths, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at h
  obtain ⟨ye, -, rfl | rfl⟩ := h
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

theorem atLoc_of_under {s : State} {p : Path} (h : p.Under s.paths) : InPlace.AtLoc p := by
  obtain ⟨P, hP, q, rfl⟩ := h
  obtain ⟨i, q', rfl⟩ := atLoc_of_mem hP
  exact ⟨i, q' ++ q, rfl⟩

/-- Writes below the paths of a state keep the length of its store. -/
theorem length_of_setSeq {s : State} {W : List (Path × Value)} {st : List Value}
    (hW : ∀ pw ∈ W, pw.1.Under s.paths)
    (h : (Value.list s.store.toList).setSeq W = .ok (.list st)) : st.length = s.store.size := by
  obtain ⟨A, B, hR, hlen, hB, -, -⟩ := InPlace.setSeq_append_store (B := [])
    (fun pw hpw => atLoc_of_under (hW pw hpw)) (by rw [List.append_nil]; exact h)
  have hB' : B = [] := List.eq_nil_of_length_eq_zero hB
  subst hB'
  simp only [List.append_nil, Value.list.injEq] at hR
  rw [hR, hlen, Array.length_toList]

/-- Reading a part of the store is reading the store, as a list, along the part's path. -/
theorem deref_toList (s : State) {r : Ref} (hr : s.Has r) (p : Path) :
    deref s r p = (Value.list s.store.toList).get (r.toPath ++ p) := by
  have hr' : r.loc < s.store.size := hr
  have hs : s.store[r.loc]? = some s.store[r.loc] := Array.getElem?_eq_getElem hr'
  have hu : s.store.toList[r.loc]? = some s.store[r.loc] := by rw [Array.getElem?_toList, hs]
  rw [InPlace.get_whole hu]
  simp only [deref, hs]

/-- A sequence of writes leaves every path disjoint from each of them as it was. -/
theorem get_setSeq_disjoint :
    ∀ {W : List (Path × Value)} {v v' : Value} {p : Path}, (∀ pw ∈ W, pw.1.Disjoint p) →
      v.setSeq W = .ok v' → v'.get p = v.get p
  | [], _, _, _, _, h => by cases h; rfl
  | (q, a) :: W, v, v', p, hW, h => by
    simp only [Value.setSeq] at h
    cases h₁ : v.set q a with
    | error e => simp [h₁, Except.bind] at h
    | ok v₁ =>
      simp only [h₁, Except.bind] at h
      rw [get_setSeq_disjoint (fun pw hpw => hW pw (List.mem_cons_of_mem _ hpw)) h]
      exact Value.get_of_set_disjoint (hW _ List.mem_cons_self) h₁

/-! ## Evolution -/

theorem Evolves.refl (s : State) : Evolves s s :=
  ⟨[], s.store.toList, [], by simp, by simp, rfl⟩

theorem Evolves.grows {s s' : State} (h : Grows s.store s'.store) : Evolves s s' := by
  refine ⟨[], s.store.toList, s'.store.toList.drop s.store.size, ?_, by simp, rfl⟩
  suffices ht : s'.store.toList.take s.store.size = s.store.toList by
    rw [← ht, List.take_append_drop]
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, Array.getElem?_toList, Array.getElem?_toList]
  split
  · rename_i hi
    exact h.same i hi
  · rename_i hi
    exact (Array.getElem?_eq_none (by omega)).symm

theorem Evolves.setAt {s s' : State} {r : Ref} {p : Path} {w : Value} (h : setAt s r p w = .ok s')
    (hu : (r.at p).toPath.Under s.paths) : Evolves s s' := by
  obtain ⟨v, v', hv, hs, rfl⟩ := setAt_ok h
  refine ⟨[((r.at p).toPath, w)], s.store.toList.set r.loc v', [], by simp [Array.set!], ?_, ?_⟩
  · intro pw hpw
    rw [List.mem_singleton.1 hpw]
    exact hu
  · have hv' : s.store.toList[r.loc]? = some v := by simpa using hv
    show ((Value.list s.store.toList).set (r.toPath ++ p) w).bind (fun v' => v'.setSeq []) = _
    rw [InPlace.set_whole hv' p w, hs]
    rfl

/-- A write below a path of the later state, at a location the earlier store has, is below a
path of the earlier state when every such path of the later state is. -/
theorem under_of_below {s s₁ : State}
    (hp : ∀ P ∈ s₁.paths, ∀ i q, P = .index i :: q → i < s.store.size → P.Under s.paths)
    {pw : Path × Value} (hu : pw.1.Under s₁.paths) (hb : InPlace.below s.store.size pw = true) :
    pw.1.Under s.paths := by
  obtain ⟨p, w⟩ := pw
  obtain ⟨P, hP, q, hq⟩ := hu
  dsimp only at hq
  subst hq
  obtain ⟨i, q', rfl⟩ := atLoc_of_mem hP
  simp only [InPlace.below, List.cons_append, decide_eq_true_eq] at hb
  obtain ⟨P₀, hP₀, q₀, hq₀⟩ := hp _ hP i q' rfl hb
  exact ⟨P₀, hP₀, q₀ ++ q, by rw [hq₀, List.append_assoc]⟩

theorem Evolves.trans {s s₁ s₂ : State} (h₁ : Evolves s s₁) (h₂ : Evolves s₁ s₂)
    (hp : ∀ P ∈ s₁.paths, ∀ i q, P = .index i :: q → i < s.store.size → P.Under s.paths) :
    Evolves s s₂ := by
  obtain ⟨W₁, st₁, e₁, hs₁, hW₁, hseq₁⟩ := h₁
  obtain ⟨W₂, st₂, e₂, hs₂, hW₂, hseq₂⟩ := h₂
  have hlen := length_of_setSeq hW₁ hseq₁
  rw [hs₁] at hseq₂
  obtain ⟨A₂, B₂, hR₂, -, -, hseqA, -⟩ := InPlace.setSeq_append_store
    (fun pw hpw => atLoc_of_under (hW₂ pw hpw)) hseq₂
  simp only [Value.list.injEq] at hR₂
  refine ⟨W₁ ++ W₂.filter (InPlace.below st₁.length), A₂, B₂ ++ e₂,
    by rw [hs₂, hR₂, List.append_assoc], fun pw hpw => ?_, ?_⟩
  · rcases List.mem_append.1 hpw with hpw | hpw
    · exact hW₁ pw hpw
    · obtain ⟨hpw, hb⟩ := List.mem_filter.1 hpw
      rw [hlen] at hb
      exact under_of_below hp (hW₂ pw hpw) hb
  · rw [Value.setSeq_append, hseq₁]
    exact hseqA

theorem Evolves.deref {s s' : State} (h : Evolves s s') {q : Ref} (hq : s.Has q)
    (hd : ∀ P ∈ s.paths, P.Disjoint q.toPath) (p : Path) : deref s' q p = deref s q p := by
  obtain ⟨W, st, extra, hs, hW, hseq⟩ := h
  have hlen := length_of_setSeq hW hseq
  have hlt : q.loc < st.length := by rw [hlen]; exact hq
  have hq' : s'.Has q := by
    show q.loc < s'.store.size
    rw [← Array.length_toList, hs, List.length_append]
    omega
  rw [deref_toList s hq, deref_toList s' hq', hs]
  have hext : (Value.list (st ++ extra)).get (q.toPath ++ p) =
      (Value.list st).get (q.toPath ++ p) := by
    simp [InPlace.Ref.toPath, Value.get, elemAt?, List.getElem?_append_left hlt]
  rw [hext]
  refine get_setSeq_disjoint (fun pw hpw => ?_) hseq
  obtain ⟨P, hP, r, hr⟩ := hW pw hpw
  rw [hr]
  exact (hd P hP).append r p

end Stilt.Sharing
