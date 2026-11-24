import Stilt.Sharing.Steps

/-!
# Binding with sharing

What a new binding and the end of one do to a frame of copies and a state of sharing that
agree: a binding with a new home holds its value there, and one of a place refers to the place,
which holds the same value (modes.copies); ending the newest binding ends it in both
(expressions.scope). A new home is a new location, so it overlaps no other home, and the state
follows from the one before.
-/

namespace Stilt.Sharing

open InPlace (Ref)
open Moving (keep LiveAt)

/-- A store that grows keeps what the parts it had hold. -/
theorem Holds.grows {st st' : Array Value} (hg : Grows st st') :
    ∀ {fr : Copy.Frame} {env : List (Name × Entry)}, Holds st fr env →
      (∀ ye ∈ env, ye.2.ref.loc < st.size) → Holds st' fr env
  | [], [], _, _ => trivial
  | (_, _) :: _, (_, _) :: _, ⟨h₁, h₂, h₃⟩, hh =>
    ⟨h₁, (deref_grows (s := ⟨[], st⟩) (s' := ⟨[], st'⟩) hg (hh _ List.mem_cons_self) []).trans h₂,
      Holds.grows hg h₃ fun ye hye => hh ye (List.mem_cons_of_mem _ hye)⟩
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

/-- A new binding, whose home is a new location of a store that grew and which reads `v` where
it refers, agrees with a frame given `v`. -/
theorem Agrees.cons {m : List Bool} {fr : Copy.Frame} {s s' : State} (h : Agrees m fr s)
    (x : Name) {v : Value} (hv : v.Safe) {e : Entry} (henv : s'.env = (x, e) :: s.env)
    (hg : Grows s.store s'.store) (hhome : s.store.size ≤ e.home.loc) (hhas : s'.Has e.home)
    (href : s'.Has e.ref) (hd : deref s' e.ref [] = .ok v) :
    Agrees (true :: m) ((x, v) :: fr) s' := by
  have hold : ∀ ye ∈ keep m s.env, ye.2.ref.loc < s.store.size := fun ye hye =>
    (h.has ye ((Moving.sublist_keep m s.env).subset hye)).2
  refine ⟨by simp [h.len], by simp [henv, h.align], ?_, ?_, ?_, ?_⟩
  · rw [henv, Moving.keep_cons_true, Moving.keep_cons_true]
    exact ⟨rfl, (deref_env s' [] e.ref []).symm.trans hd |>.trans rfl, h.holds.grows hg hold⟩
  · intro ye hye
    rw [henv] at hye
    rcases List.mem_cons.1 hye with rfl | hye
    · exact ⟨hhas, href⟩
    · exact ⟨(h.has ye hye).1.grows hg, (h.has ye hye).2.grows hg⟩
  · rw [henv]
    refine List.Pairwise.cons (fun ye hye => ?_) h.homes
    have hlt : ye.2.home.loc < s.store.size := (h.has ye hye).1
    simp only [overlaps, Bool.and_eq_false_iff]
    left
    simp only [beq_eq_false_iff_ne]
    omega
  · intro xv hxv
    rcases List.mem_cons.1 hxv with rfl | hxv
    · exact hv
    · exact h.safe xv hxv

theorem Agrees.bindWith {m : List Bool} {fr : Copy.Frame} {s : State} (h : Agrees m fr s)
    (x : Name) {v : Value} (hv : v.Safe) (u c : Bool) :
    Agrees (true :: m) ((x, v) :: fr) (bindWith s x v u c) :=
  h.cons x hv rfl (Grows.push _ _) (Nat.le_refl _) (by simp [State.Has, Sharing.bindWith])
    (by simp [State.Has, Sharing.bindWith, Entry.ref])
    (by simp [Sharing.bindWith, Entry.ref, deref, Value.get])

theorem Agrees.bindAlias {m : List Bool} {fr : Copy.Frame} {s : State} (h : Agrees m fr s)
    (x : Name) {v : Value} (hv : v.Safe) {r : Ref} (hd : deref s r [] = .ok v) (u : Bool) :
    Agrees (true :: m) ((x, v) :: fr) (bindAlias s x v r u) := by
  have hr : s.Has r := by
    unfold deref at hd
    split at hd
    · rename_i w hw
      exact (Array.getElem?_eq_some_iff.1 hw).1
    · cases hd
  refine h.cons x hv rfl (Grows.push _ _) (Nat.le_refl _) (by simp [State.Has, Sharing.bindAlias])
    (by simpa [State.Has, Sharing.bindAlias, Entry.ref] using Nat.lt_succ_of_lt hr) ?_
  show deref ⟨_, s.store.push v⟩ r [] = .ok v
  rw [deref_push hr]
  exact hd

/-- Ending the newest binding ends it in both models. -/
theorem Agrees.unbind {b : Bool} {m : List Bool} {x : Name} {v : Value} {fr : Copy.Frame}
    {s : State} (h : Agrees (b :: m) ((x, v) :: fr) s) : Agrees m fr ⟨s.env.tail, s.store⟩ := by
  obtain ⟨len, align, holds, has, homes, safe⟩ := h
  match s, align, holds, has, homes with
  | ⟨(y, e) :: env, st⟩, align, holds, has, homes =>
    refine ⟨by simpa using len, by simp only [List.map_cons, List.cons.injEq] at align; exact align.2, ?_, fun ye hye => has ye
      (List.mem_cons_of_mem _ hye), homes.of_cons, fun xv hxv => safe xv (List.mem_cons_of_mem _ hxv)⟩
    cases b
    · exact holds
    · exact holds.2.2

/-! ## Following -/

/-- A state with one more binding, whose home is new and whose part is new or below a binding's
of the state, follows from it. -/
theorem Grown.cons {s s' : State} {x : Name} {e : Entry} (henv : s'.env = (x, e) :: s.env)
    (hg : Grows s.store s'.store) (hhome : s.store.size ≤ e.home.loc)
    (href : s.store.size ≤ e.ref.loc ∨ e.ref.toPath.Under s.paths) : Grown s s' := by
  refine ⟨Evolves.grows hg, fun P hP i q hq hi => ?_⟩
  simp only [State.paths, henv, List.flatMap_cons, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with (rfl | rfl) | hP
  · simp only [InPlace.Ref.toPath, List.cons.injEq, Step.index.injEq] at hq
    omega
  · rcases href with hr | hr
    · simp only [InPlace.Ref.toPath, List.cons.injEq, Step.index.injEq] at hq
      omega
    · exact hr
  · exact ⟨P, by simpa [State.paths] using hP, [], by rw [List.append_nil]⟩

theorem Grown.bindWith (s : State) (x : Name) (v : Value) (u c : Bool) :
    Grown s (bindWith s x v u c) :=
  Grown.cons rfl (Grows.push _ _) (Nat.le_refl _) (.inl (Nat.le_refl _))

theorem Grown.bindAlias (s : State) (x : Name) (v : Value) {r : Ref}
    (hr : r.toPath.Under s.paths) (u : Bool) : Grown s (bindAlias s x v r u) :=
  Grown.cons rfl (Grows.push _ _) (Nat.le_refl _) (.inr hr)

/-- Ending the newest binding of a state that followed from one with exactly one binding more
than `s`. -/
theorem Follows.unbind {s s₀ s₁ : State} {a : Name × Entry} (h₀ : Grown s s₀)
    (henv : s₀.env = a :: s.env) (h₁ : Follows s₀ s₁) :
    Follows s ⟨s₁.env.tail, s₁.store⟩ := by
  have h := h₀.trans h₁.grown
  refine ⟨h.1, fun P hP i q hq hi => h.2 P ?_ i q hq hi, Kept.unbind henv h₁.2.2⟩
  obtain ⟨ye, hye, hP⟩ := List.mem_flatMap.1 hP
  exact List.mem_flatMap.2 ⟨ye, List.mem_of_mem_tail hye, hP⟩

/-! ## Every binding shared -/

theorem AllShared.cons {s s' : State} {x : Name} {e : Entry} (h : AllShared s)
    (henv : s'.env = (x, e) :: s.env) (hu : e.unique = false) (hh : e.home.path = [])
    (hio : e.inout = false) : AllShared s' :=
  ⟨fun ye hye => by
    rw [henv] at hye
    rcases List.mem_cons.1 hye with rfl | hye
    · exact hu
    · exact h.shared ye hye,
  fun ye hye => by
    rw [henv] at hye
    rcases List.mem_cons.1 hye with rfl | hye
    · exact .inl hh
    · exact h.homes ye hye,
  fun ye hye => by
    rw [henv] at hye
    rcases List.mem_cons.1 hye with rfl | hye
    · simp [hio]
    · exact h.inout ye hye⟩

theorem AllShared.tail {s : State} (h : AllShared s) (st : Array Value) :
    AllShared ⟨s.env.tail, st⟩ :=
  ⟨fun ye hye => h.shared ye (List.mem_of_mem_tail hye),
    fun ye hye => h.homes ye (List.mem_of_mem_tail hye),
    fun ye hye => h.inout ye (List.mem_of_mem_tail hye)⟩

end Stilt.Sharing
