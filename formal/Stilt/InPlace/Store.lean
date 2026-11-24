import Stilt.Memory
import Stilt.InPlace.Writes
import Stilt.InPlace.Safe

/-!
# The store

The in-place store read as one list value, so that a reference is a path into
it and the laws of `Stilt.Paths` and `Stilt.InPlace.Writes` apply to it.

On it rest the two relations of the simulation:

* `Agrees fr s`: each variable of the copy frame `fr` holds the value its
  reference in `s` reaches, and the references of `s` reach pairwise disjoint
  parts of the store;
* `Evolves s s'`: `s'` comes from `s` by writes below the references of `s`
  and by new locations, with the same variables. A body can change nothing
  else, and the end of a call reads off from it what the callee did to the
  caller's places.
-/

namespace Stilt.InPlace

/-- The path from the store, read as a list, to the part a reference
reaches. -/
def Ref.toPath (r : Ref) : Path := .index r.loc :: r.path

/-- Two references reach disjoint parts of the store. -/
def Ref.Disjoint (r r' : Ref) : Prop := r.toPath.Disjoint r'.toPath

theorem Ref.Disjoint.symm {r r' : Ref} (h : r.Disjoint r') : r'.Disjoint r := Path.Disjoint.symm h

theorem deref_store (s : State) (r : Ref) (p : Path) : deref s r p = deref ⟨[], s.store⟩ r p :=
  rfl

/-- Reading a valid reference is reading its path in the store. -/
theorem deref_eq_get {st : List Value} {r : Ref} (h : r.loc < st.length) (e : List (Name × Ref))
    (p : Path) : deref ⟨e, st⟩ r p = (Value.list st).get (r.toPath ++ p) := by
  obtain ⟨u, hu⟩ : ∃ u, st[r.loc]? = some u := ⟨st[r.loc], by simp [h]⟩
  simp [deref, hu, Ref.toPath, Value.get, elemAt?]

theorem lt_of_deref {st : List Value} {e : List (Name × Ref)} {r : Ref} {p : Path} {v : Value}
    (h : deref ⟨e, st⟩ r p = .ok v) : r.loc < st.length := by
  unfold deref at h
  split at h
  · rename_i u hu
    exact (List.getElem?_eq_some_iff.1 hu).1
  · cases h

theorem deref_append {s : State} {r : Ref} (p q : Path) :
    deref s r (p ++ q) = (deref s r p).bind (·.get q) := by
  unfold deref
  split
  · rw [← List.append_assoc, Value.get_append]
  · rfl

/-- Whatever the store holds past a valid reference changes nothing it
reads. -/
theorem deref_store_append {st : List Value} {r : Ref} (h : r.loc < st.length)
    (extra : List Value) (p : Path) : deref ⟨[], st ++ extra⟩ r p = deref ⟨[], st⟩ r p := by
  simp [deref, List.getElem?_append_left h]

/-! ## Agreement -/

/-- Each variable of a frame holds the value its reference reaches in the
store `st`. The frame and the variables agree name by name, hidden ones
included, as a closure's capture reads them all. -/
def Holds (st : List Value) : Copy.Frame → List (Name × Ref) → Prop
  | [], [] => True
  | (x, v) :: fr, (y, r) :: env => x = y ∧ deref ⟨[], st⟩ r [] = .ok v ∧ Holds st fr env
  | _, _ => False

/-- A copy frame and an in-place state agree: each variable holds the same
value in both, the references reach disjoint parts of the store, and the
values are safe. -/
structure Agrees (fr : Copy.Frame) (s : State) : Prop where
  holds : Holds s.store fr s.env
  disjoint : s.env.Pairwise fun a b => a.2.Disjoint b.2
  safe : ∀ xv ∈ fr, xv.2.Safe

/-- Every reference of a state reaches a location of its store. -/
def Valid (s : State) : Prop := ∀ xr ∈ s.env, xr.2.loc < s.store.length

namespace Holds

theorem valid {st : List Value} :
    ∀ {fr : Copy.Frame} {env : List (Name × Ref)}, Holds st fr env →
      ∀ xr ∈ env, xr.2.loc < st.length
  | [], [], _, _, hxr => by simp at hxr
  | (_, _) :: _, (_, _) :: _, ⟨_, hd, h⟩, xr, hxr => by
    rcases List.mem_cons.1 hxr with rfl | hxr
    · exact lt_of_deref hd
    · exact valid h xr hxr
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

theorem store_append {st : List Value} (extra : List Value) :
    ∀ {fr : Copy.Frame} {env : List (Name × Ref)}, Holds st fr env → Holds (st ++ extra) fr env
  | [], [], _ => trivial
  | (_, _) :: _, (_, _) :: _, ⟨hx, hd, h⟩ =>
    ⟨hx, by rw [deref_store_append (lt_of_deref hd)]; exact hd, store_append extra h⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- A variable is in the frame exactly when it is in the state, and holds the
value its reference reaches. -/
theorem lookup {st : List Value} (x : Name) :
    ∀ {fr : Copy.Frame} {env : List (Name × Ref)}, Holds st fr env →
      (fr.lookup x = none ∧ env.lookup x = none) ∨
        ∃ v r, fr.lookup x = some v ∧ env.lookup x = some r ∧ deref ⟨[], st⟩ r [] = .ok v
  | [], [], _ => .inl ⟨rfl, rfl⟩
  | (z, v) :: fr, (_, r) :: env, ⟨rfl, hd, h⟩ => by
    by_cases hx : x = z
    · subst hx
      exact .inr ⟨v, r, List.lookup_cons_self, List.lookup_cons_self, hd⟩
    · rw [lookup_cons_ne hx, lookup_cons_ne hx]
      exact lookup x h
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- A change to the store that keeps what every disjoint reference reads,
and gives the reference of `x` the value `v'`, is the write of `v'` to `x`. -/
theorem write {st st' : List Value} {x : Name} {r : Ref} {v' : Value}
    (hr : deref ⟨[], st'⟩ r [] = .ok v')
    (hkeep : ∀ r', r'.Disjoint r → deref ⟨[], st'⟩ r' [] = deref ⟨[], st⟩ r' []) :
    ∀ {fr : Copy.Frame} {env : List (Name × Ref)}, Holds st fr env →
      env.Pairwise (fun a b => a.2.Disjoint b.2) → env.lookup x = some r →
      Holds st' (assocSet fr x v') env
  | [], [], _, _, hl => by simp at hl
  | (z, v) :: fr, (_, rz) :: env, ⟨rfl, hd, h⟩, hp, hl => by
    rw [List.pairwise_cons] at hp
    by_cases hx : x = z
    · subst hx
      simp only [List.lookup_cons_self, Option.some.injEq] at hl
      subst hl
      rw [show assocSet ((x, v) :: fr) x v' = (x, v') :: fr by simp [assocSet]]
      exact ⟨rfl, hr, mono h fun xr hxr => hkeep xr.2 (hp.1 xr hxr).symm⟩
    · rw [lookup_cons_ne hx] at hl
      rw [show assocSet ((z, v) :: fr) x v' = (z, v) :: assocSet fr x v' by simp [assocSet, hx]]
      refine ⟨rfl, ?_, write hr hkeep h hp.2 hl⟩
      rw [hkeep rz (hp.1 _ (mem_of_lookup hl))]
      exact hd
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
where
  /-- A change that keeps what each reference reads keeps the frame. -/
  mono {st st' : List Value} :
      ∀ {fr : Copy.Frame} {env : List (Name × Ref)}, Holds st fr env →
        (∀ xr ∈ env, deref ⟨[], st'⟩ xr.2 [] = deref ⟨[], st⟩ xr.2 []) → Holds st' fr env
    | [], [], _, _ => trivial
    | (_, _) :: _, (_, r) :: _, ⟨hx, hd, h⟩, hkeep =>
      ⟨hx, by rw [hkeep _ List.mem_cons_self]; exact hd,
        mono h fun xr hxr => hkeep xr (List.mem_cons_of_mem _ hxr)⟩
    | [], _ :: _, h, _ => h.elim
    | _ :: _, [], h, _ => h.elim

end Holds

theorem Agrees.valid {fr : Copy.Frame} {s : State} (h : Agrees fr s) : Valid s :=
  h.holds.valid

theorem Agrees.store_append {fr : Copy.Frame} {s : State} (h : Agrees fr s)
    (extra : List Value) : Agrees fr ⟨s.env, s.store ++ extra⟩ :=
  ⟨h.holds.store_append extra, h.disjoint, h.safe⟩

/-- Distinct variables refer to disjoint parts of the store. -/
theorem lookup_disjoint {env : List (Name × Ref)} (hp : env.Pairwise fun a b => a.2.Disjoint b.2)
    {x x' : Name} {r r' : Ref} (hl : env.lookup x = some r) (hl' : env.lookup x' = some r')
    (hne : x ≠ x') : r.Disjoint r' := by
  induction env with
  | nil => simp at hl
  | cons zr env ih =>
    obtain ⟨z, rz⟩ := zr
    rw [List.pairwise_cons] at hp
    by_cases hx : x = z
    · subst hx
      simp only [List.lookup_cons_self, Option.some.injEq] at hl
      subst hl
      rw [lookup_cons_ne (Ne.symm hne)] at hl'
      exact hp.1 _ (mem_of_lookup hl')
    · rw [lookup_cons_ne hx] at hl
      by_cases hx' : x' = z
      · subst hx'
        simp only [List.lookup_cons_self, Option.some.injEq] at hl'
        subst hl'
        exact (hp.1 _ (mem_of_lookup hl)).symm
      · rw [lookup_cons_ne hx'] at hl'
        exact ih hp.2 hl hl'

/-! ## Reading, capturing and binding -/

/-- Both models read a place alike. -/
theorem Agrees.read {fr : Copy.Frame} {s : State} (h : Agrees fr s) (x : Name) (p : Path) :
    Copy.read fr x p = InPlace.read s x p := by
  unfold Copy.read InPlace.read
  rcases h.holds.lookup x with ⟨h₁, h₂⟩ | ⟨v, r, h₁, h₂, hd⟩
  · rw [h₁, h₂]
  · simp only [h₁, h₂]
    have := deref_append (s := ⟨[], s.store⟩) (r := r) [] p
    rw [List.nil_append] at this
    rw [deref_store, this, hd]
    rfl

theorem Agrees.read_safe {fr : Copy.Frame} {s : State} (h : Agrees fr s) {x : Name} {p : Path}
    {v : Value} (hv : Copy.read fr x p = .ok v) : v.Safe := by
  unfold Copy.read at hv
  split at hv
  · rename_i w hw
    exact Value.Safe.get (h.safe (x, w) (mem_of_lookup hw)) hv
  · cases hv

/-- A closure captures the same values in both models. -/
theorem Holds.capture {st : List Value} (e : List (Name × Ref)) :
    ∀ {fr : Copy.Frame} {env : List (Name × Ref)}, Holds st fr env →
      env.mapM (fun xr => (xr.1, ·) <$> deref ⟨e, st⟩ xr.2 []) = .ok fr
  | [], [], _ => rfl
  | (_, _) :: _, (_, r) :: _, ⟨rfl, hd, h⟩ => by
    have hd' : deref ⟨e, st⟩ r [] = _ := hd
    simp only [List.mapM_cons, hd', capture e h]
    rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem Agrees.capture {fr : Copy.Frame} {s : State} (h : Agrees fr s) :
    InPlace.frames.capture s = .ok fr :=
  h.holds.capture s.env

/-- A new variable gets a new location, disjoint from every other. -/
theorem Agrees.bind {fr : Copy.Frame} {s : State} (h : Agrees fr s) (x : Name) {v : Value}
    (hv : v.Safe) : Agrees ((x, v) :: fr) (InPlace.bind s x v) := by
  refine ⟨⟨rfl, ?_, h.holds.store_append [v]⟩, ?_, ?_⟩
  · simp [deref, InPlace.bind, Value.get]
  · refine List.Pairwise.cons (fun xr hxr => ?_) h.disjoint
    have := h.valid xr hxr
    exact .inl (by simp; omega)
  · intro xv hxv
    rcases List.mem_cons.1 hxv with rfl | hxv
    · exact hv
    · exact h.safe xv hxv

/-- Ending the newest binding ends it in both models. -/
theorem Agrees.unbind {fr : Copy.Frame} {s : State} (h : Agrees fr s) :
    Agrees fr.tail ⟨s.env.tail, s.store⟩ := by
  obtain ⟨holds, hd, hs⟩ := h
  match fr, s, holds, hd with
  | [], ⟨[], _⟩, _, _ => exact ⟨trivial, .nil, by simp⟩
  | (_, _) :: _, ⟨(_, _) :: _, _⟩, ⟨_, _, holds⟩, hd =>
    exact ⟨holds, hd.of_cons, fun xv hxv => hs xv (List.mem_cons_of_mem _ hxv)⟩

end Stilt.InPlace
