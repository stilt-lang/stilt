import Stilt.Sharing.Unshared

/-!
# Modifying a binding when every binding is shared

A modification of a binding that the inference calls `shared` first `unshare`s it, after which
no other binding's part overlaps its home, so the write changes its value alone, as the copy
model's write does (modes.shared-writes).
-/

namespace Stilt.Sharing

open InPlace (Ref)

/-- A write along `p` below a part that reads `v` leaves the part reading `v` written along
`p`. -/
theorem deref_setAt_whole {s s' : State} {r : Ref} {p : Path} {w v v' : Value}
    (hd : deref s r [] = .ok v) (hv : v.set p w = .ok v') (h : setAt s r p w = .ok s') :
    deref s' r [] = .ok v' := by
  obtain ⟨V, V', hV, hs, rfl⟩ := setAt_ok h
  have hg : V.get r.path = .ok v := by simpa [deref, hV] using hd
  rw [Value.set_append, hg] at hs
  simp only [Except.bind, hv] at hs
  have hlt : r.loc < s.store.size := by
    rcases Nat.lt_or_ge r.loc s.store.size with hl | hl
    · exact hl
    · simp [Array.getElem?_eq_none hl] at hV
  simp only [deref, Array.set!, Array.getElem?_setIfInBounds_self_of_lt hlt, List.append_nil]
  exact Value.get_of_set hs

/-- A write below a part that reads a value succeeds when the write into that value does. -/
theorem setAt_ok_of_deref {s : State} {r : Ref} {p : Path} {w v v' : Value}
    (hd : deref s r [] = .ok v) (hv : v.set p w = .ok v') : ∃ s', setAt s r p w = .ok s' := by
  unfold deref at hd
  cases hV : s.store[r.loc]? with
  | none => simp [hV] at hd
  | some V =>
    simp only [hV, List.append_nil] at hd
    obtain ⟨V', hV'⟩ := Value.set_ok_of_get hd v'
    refine ⟨{ s with store := s.store.set! r.loc V' }, ?_⟩
    simp only [setAt, hV, Value.set_append, hd, Except.bind, hv, hV']
    rfl

/-- A write that fails below a part fails alike in the part's value. -/
theorem setAt_error_of_deref {s : State} {r : Ref} {p : Path} {w v : Value} {f : Fault}
    (hd : deref s r [] = .ok v) (hv : v.set p w = .error f) : setAt s r p w = .error f := by
  unfold deref at hd
  cases hV : s.store[r.loc]? with
  | none => simp [hV] at hd
  | some V =>
    simp only [hV, List.append_nil] at hd
    simp only [setAt, hV, Value.set_append, hd, Except.bind, hv]
    rfl

/-- A frame reads alike in a store where each of its bindings reads what it read. -/
theorem ReadsAlike.same {st st' : Array Value} :
    ∀ {env : List (Name × Entry)},
      (∀ ye ∈ env, deref ⟨[], st'⟩ ye.2.ref [] = deref ⟨[], st⟩ ye.2.ref []) →
      ReadsAlike st st' env env
  | [], _ => trivial
  | _ :: _, h => ⟨⟨rfl, h _ List.mem_cons_self⟩,
      ReadsAlike.same fun ye hye => h ye (List.mem_cons_of_mem _ hye)⟩

/-- A binding whose home is apart from every other's is the only one with its entry. -/
theorem ne_of_apart {a b : Name × Entry} (h : overlaps a.2.home b.2.home = false) : a.2 ≠ b.2 :=
  fun he => by rw [he, overlaps_self] at h; cases h

/-- After a write of the newest binding of `x`, which then reads `v'`, every other binding
reading what it read, the frame with `x` written holds what the state reads. -/
theorem Holds.write {st st' : Array Value} {x : Name} {e₁ : Entry} {v' : Value}
    (h₁ : deref ⟨[], st'⟩ e₁.ref [] = .ok v') :
    ∀ {fr : Copy.Frame} {env : List (Name × Entry)}, Holds st fr env → env.lookup x = some e₁ →
      env.Pairwise (fun a b => overlaps a.2.home b.2.home = false) →
      (∀ ye ∈ env, ye.2 ≠ e₁ → deref ⟨[], st'⟩ ye.2.ref [] = deref ⟨[], st⟩ ye.2.ref []) →
      Holds st' (assocSet fr x v') env
  | [], [], _, hl, _, _ => by simp at hl
  | (z, v) :: fr, (_, e) :: env, ⟨rfl, hd, h⟩, hl, hp, ho => by
    rw [List.pairwise_cons] at hp
    have hrest : ∀ ye ∈ env, ye.2 ≠ e₁ → deref ⟨[], st'⟩ ye.2.ref [] = deref ⟨[], st⟩ ye.2.ref [] :=
      fun ye hye => ho ye (List.mem_cons_of_mem _ hye)
    by_cases hx : x = z
    · subst hx
      rw [List.lookup_cons_self, Option.some.injEq] at hl
      subst hl
      simp only [assocSet, ↓reduceIte]
      exact ⟨rfl, h₁, Holds.alike h (ReadsAlike.same fun ye hye =>
        hrest ye hye (fun he => ne_of_apart (hp.1 ye hye) he.symm))⟩
    · rw [lookup_cons_ne hx] at hl
      simp only [assocSet, hx, ↓reduceIte]
      have hne : e ≠ e₁ := ne_of_apart (b := (x, e₁)) (hp.1 _ (mem_of_lookup hl))
      exact ⟨rfl, (ho _ List.mem_cons_self hne).trans hd, Holds.write h₁ h hl hp.2 hrest⟩
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

theorem map_fst_assocSet {β : Type} (k : Name) (b : β) :
    ∀ l : List (Name × β), (assocSet l k b).map Prod.fst = l.map Prod.fst
  | [] => rfl
  | (k', b') :: l => by
    by_cases h : k = k'
    · simp [assocSet, h]
    · simp [assocSet, h, map_fst_assocSet k b l]

theorem mem_assocSet {β : Type} {k : Name} {b : β} :
    ∀ {l : List (Name × β)} {a : Name × β}, a ∈ assocSet l k b → a ∈ l ∨ a.2 = b
  | [], _, h => by simp [assocSet] at h
  | (k', b') :: l, a, h => by
    by_cases hk : k = k'
    · simp only [assocSet, hk, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inr rfl
      · exact .inl (List.mem_cons_of_mem _ h)
    · simp only [assocSet, hk, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | h
      · exact .inl List.mem_cons_self
      · exact (mem_assocSet h).imp (List.mem_cons_of_mem _) id

/-- A write of the binding that `unshare` left alone at its home keeps every binding agreeing,
shared and following. -/
theorem AgreesAll.write_home {fr : Copy.Frame} {s₁ s' : State} (h : AgreesAll fr s₁)
    (hsh : AllShared s₁) {x : Name} {e₁ : Entry} {p : Path} {w v v' : Value} (hw : w.Safe)
    (h₁ : fr.lookup x = some v) (hl : s₁.env.lookup x = some e₁) (hd : deref s₁ e₁.ref [] = .ok v)
    (hv : v.set p w = .ok v') (hov : ∀ ye ∈ s₁.env, ye.2 ≠ e₁ → overlaps e₁.home ye.2.ref = false)
    (ha : e₁.alias = none) (hs : setAt s₁ e₁.ref p w = .ok s') :
    AgreesAll (assocSet fr x v') s' ∧ AllShared s' ∧ Follows s₁ s' := by
  have henv := setAt_env hs
  have hsize := setAt_size hs
  have hr : e₁.ref = e₁.home := by simp [Entry.ref, ha]
  have hothers : ∀ ye ∈ s₁.env, ye.2 ≠ e₁ →
      deref ⟨[], s'.store⟩ ye.2.ref [] = deref ⟨[], s₁.store⟩ ye.2.ref [] := fun ye hye hne =>
    deref_setAt_other hs (by rw [hr]; exact overlaps_at (hov ye hye hne) p) []
  have hholds : Holds s'.store (assocSet fr x v') s'.env := by
    have hwhole := deref_setAt_whole hd hv hs
    have hself : deref ⟨[], s'.store⟩ e₁.ref [] = .ok v' := hwhole
    rw [henv]
    exact Holds.write hself h.holds_all hl h.homes hothers
  have hlen : (assocSet fr x v').length = s'.env.length := by
    rw [← List.length_map (f := Prod.fst), map_fst_assocSet, h.align, henv, List.length_map]
  refine ⟨⟨by simp, by rw [map_fst_assocSet, h.align, henv], ?_, fun ye hye => ?_, henv ▸ h.homes,
      fun xv hxv => ?_⟩, ⟨fun ye hye => hsh.shared ye (henv ▸ hye),
      fun ye hye => hsh.homes ye (henv ▸ hye), fun ye hye => hsh.inout ye (henv ▸ hye)⟩, ?_⟩
  · rw [Moving.keep_all (by simp) (by simp), Moving.keep_all (by simp) (by simp [hlen])]
    exact hholds
  · rw [henv] at hye
    exact ⟨by simpa [State.Has, hsize] using (h.has ye hye).1,
      by simpa [State.Has, hsize] using (h.has ye hye).2⟩
  · rcases mem_assocSet hxv with hxv | hxv
    · exact h.safe xv hxv
    · rw [hxv]
      exact Value.Safe.set (h.safe (x, v) (mem_of_lookup h₁)) hw hv
  · refine ⟨Evolves.setAt hs ?_, fun P hP _ _ _ _ => ⟨P, by rwa [State.paths, henv] at hP, [],
      by rw [List.append_nil]⟩, Kept.same henv⟩
    refine ⟨e₁.ref.toPath, List.mem_flatMap.2 ⟨(x, e₁), mem_of_lookup hl, by simp⟩, p, ?_⟩
    simp [InPlace.Ref.at, InPlace.Ref.toPath]

/-- A modification of a binding when every binding is shared: both models fail alike, or write
it, the frame and the state still agreeing on every binding, every binding still shared, and
the state following from the first (modes.shared-writes). -/
theorem AgreesAll.modify {fr : Copy.Frame} {s : State} (h : AgreesAll fr s) (hsh : AllShared s)
    {w : Value} (hw : w.Safe) (x : Name) (p : Path) :
    (∃ f, Copy.write fr x p w = .error f ∧ Sharing.modify s x p w = .error f) ∨
      ∃ fr' s', Copy.write fr x p w = .ok fr' ∧ Sharing.modify s x p w = .ok s' ∧ AgreesAll fr' s' ∧
        AllShared s' ∧ Follows s s' := by
  rcases h.holds_all.lookup x with ⟨h₁, h₂⟩ | ⟨v, e, h₁, h₂, -⟩
  · exact .inl ⟨.stuck, by simp [Copy.write, h₁], by simp [Sharing.modify, h₂]⟩
  have hu : e.unique = false := hsh.shared (x, e) (mem_of_lookup h₂)
  obtain ⟨s₁, e₁, hun, hA₁, hsh₁, hF₁, hl₁, ha₁, hov⟩ := unshare_agrees h hsh h₂
  have hd₁ : deref s₁ e₁.ref [] = .ok v := by
    rcases hA₁.holds_all.lookup x with ⟨h₁', -⟩ | ⟨v₁, e₁', h₁', h₂', hd'⟩
    · rw [h₁] at h₁'
      cases h₁'
    · rw [h₁, Option.some.injEq] at h₁'
      rw [hl₁, Option.some.injEq] at h₂'
      subst h₁' h₂'
      exact hd'
  have hmod : Sharing.modify s x p w = setAt s₁ e₁.ref p w := by
    simp only [Sharing.modify, h₂, hu, Bool.false_eq_true, ↓reduceIte, hun]
    show write s₁ x p w = _
    simp only [write, hl₁]
  cases hv : v.set p w with
  | error f =>
    exact .inl ⟨f, by simp [Copy.write, h₁, hv]; rfl, by rw [hmod]; exact setAt_error_of_deref hd₁ hv⟩
  | ok v' =>
    obtain ⟨s', hs'⟩ := setAt_ok_of_deref hd₁ hv
    obtain ⟨hA', hsh', hF'⟩ := hA₁.write_home hsh₁ hw h₁ hl₁ hd₁ hv hov ha₁ hs'
    exact .inr ⟨assocSet fr x v', s', by simp [Copy.write, h₁, hv]; rfl, by rw [hmod, hs'], hA',
      hsh', hF₁.trans hF'⟩

end Stilt.Sharing
