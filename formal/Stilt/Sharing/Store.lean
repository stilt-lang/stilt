import Stilt.Sharing.Memory
import Stilt.Paths
import Stilt.InPlace.Writes

/-!
# The store of sharing

What reading and writing the store of `Stilt.Sharing.Memory` do: a write leaves every part
that doesn't overlap the part written as it was, a new location leaves the others as they were,
and a binding given a copy of its own (`settle`), or every binding that refers into a part
(`evacuate`), reads what it read before, from a new location.
-/

namespace Stilt

namespace Path

/-- Two paths neither of which is a prefix of the other are disjoint. -/
theorem disjoint_of_not_isPrefixOf : ∀ {a b : Path}, a.isPrefixOf b = false →
    b.isPrefixOf a = false → a.Disjoint b
  | [], _, h, _ => by simp at h
  | _ :: _, [], _, h => by simp at h
  | s :: a, t :: b, h₁, h₂ => by
    by_cases hst : s = t
    · subst hst
      simp only [List.isPrefixOf, beq_self_eq_true, Bool.true_and] at h₁ h₂
      exact .inr (disjoint_of_not_isPrefixOf h₁ h₂)
    · exact .inl hst

end Path

namespace Sharing

open InPlace (Ref)

/-- The part at `p` below the part `r`. -/
def _root_.Stilt.InPlace.Ref.at (r : Ref) (p : Path) : Ref := ⟨r.loc, r.path ++ p⟩

/-- A part of the store whose location the store has. -/
def State.Has (s : State) (r : Ref) : Prop := r.loc < s.store.size

theorem deref_congr {s s' : State} {r : Ref} (h : s'.store[r.loc]? = s.store[r.loc]?) (p : Path) :
    deref s' r p = deref s r p := by
  unfold deref
  rw [h]

theorem deref_env (s : State) (env : List (Name × Entry)) (r : Ref) (p : Path) :
    deref { s with env } r p = deref s r p := rfl

/-- Reading along a path, then along another, is reading along both. -/
theorem deref_append (s : State) (r : Ref) (p q : Path) :
    deref s r (p ++ q) = (deref s r p).bind (·.get q) := by
  unfold deref
  split
  · rw [← List.append_assoc, Value.get_append]
  · rfl

theorem deref_at (s : State) (r : Ref) (p q : Path) : deref s (r.at p) q = deref s r (p ++ q) := by
  simp only [deref, InPlace.Ref.at, List.append_assoc]

/-- A new location leaves the parts of the others as they were. -/
theorem deref_push {s : State} {r : Ref} (hr : s.Has r) (env : List (Name × Entry)) (v : Value)
    (p : Path) : deref ⟨env, s.store.push v⟩ r p = deref s r p := by
  apply deref_congr
  simp [Array.getElem?_push, Nat.ne_of_lt hr]

/-- A new location holds what it was given. -/
theorem deref_push_new (s : State) (env : List (Name × Entry)) (v : Value) (p : Path) :
    deref ⟨env, s.store.push v⟩ ⟨s.store.size, []⟩ p = v.get p := by
  simp [deref]

theorem setAt_ok {s s' : State} {r : Ref} {p : Path} {w : Value} (h : setAt s r p w = .ok s') :
    ∃ v v', s.store[r.loc]? = some v ∧ v.set (r.path ++ p) w = .ok v' ∧
      s' = { s with store := s.store.set! r.loc v' } := by
  unfold setAt at h
  split at h
  · rename_i v hv
    cases hs : v.set (r.path ++ p) w with
    | ok v' =>
      rw [hs] at h
      cases h
      exact ⟨v, v', hv, hs, rfl⟩
    | error e => rw [hs] at h; cases h
  · cases h

theorem setAt_env {s s' : State} {r : Ref} {p : Path} {w : Value} (h : setAt s r p w = .ok s') :
    s'.env = s.env := by
  obtain ⟨_, _, _, _, rfl⟩ := setAt_ok h
  rfl

theorem setAt_size {s s' : State} {r : Ref} {p : Path} {w : Value} (h : setAt s r p w = .ok s') :
    s'.store.size = s.store.size := by
  obtain ⟨_, _, _, _, rfl⟩ := setAt_ok h
  simp [Array.set!]

/-- After a write, the part written holds what was written. -/
theorem deref_setAt_self {s s' : State} {r : Ref} {p : Path} {w : Value}
    (h : setAt s r p w = .ok s') : deref s' (r.at p) [] = .ok w := by
  obtain ⟨v, v', hv, hs, rfl⟩ := setAt_ok h
  have hlt : r.loc < s.store.size := by
    rcases Nat.lt_or_ge r.loc s.store.size with hl | hl
    · exact hl
    · simp [Array.getElem?_eq_none hl] at hv
  simp only [deref, InPlace.Ref.at, Array.set!, Array.getElem?_setIfInBounds_self_of_lt hlt,
    List.append_nil]
  exact Value.get_of_set hs

/-- A write leaves every part that doesn't overlap the part written as it was. -/
theorem deref_setAt_other {s s' : State} {r q : Ref} {p : Path} {w : Value}
    (h : setAt s r p w = .ok s') (hd : overlaps (r.at p) q = false) (p' : Path) :
    deref s' q p' = deref s q p' := by
  obtain ⟨v, v', hv, hs, rfl⟩ := setAt_ok h
  by_cases hl : r.loc = q.loc
  · simp only [overlaps, InPlace.Ref.at, hl, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff] at hd
    have hdis := (Path.disjoint_of_not_isPrefixOf hd.1 hd.2).append [] p'
    rw [List.append_nil] at hdis
    unfold deref
    rw [← hl]
    simp only [Array.set!, hv]
    have hlt : r.loc < s.store.size := by
      rcases Nat.lt_or_ge r.loc s.store.size with h' | h'
      · exact h'
      · simp [Array.getElem?_eq_none h'] at hv
    simp only [Array.getElem?_setIfInBounds_self_of_lt hlt]
    exact Value.get_of_set_disjoint hdis hs
  · apply deref_congr
    simp [Array.set!, hl]

/-! ## Stores that grow -/

/-- The store `b` holds every location of `a` as `a` holds it, and maybe more. -/
structure Grows (a b : Array Value) : Prop where
  size : a.size ≤ b.size
  same : ∀ i, i < a.size → b[i]? = a[i]?

theorem Grows.refl (a : Array Value) : Grows a a := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Grows.trans {a b c : Array Value} (h₁ : Grows a b) (h₂ : Grows b c) : Grows a c :=
  ⟨Nat.le_trans h₁.size h₂.size, fun i hi => (h₂.same i (Nat.lt_of_lt_of_le hi h₁.size)).trans
    (h₁.same i hi)⟩

theorem Grows.push (a : Array Value) (v : Value) : Grows a (a.push v) :=
  ⟨by simp, fun i hi => by simp [Array.getElem?_push, Nat.ne_of_lt hi]⟩

/-- A part that the smaller store has reads alike in the larger. -/
theorem deref_grows {s s' : State} (h : Grows s.store s'.store) {r : Ref} (hr : s.Has r) (p : Path) :
    deref s' r p = deref s r p :=
  deref_congr (h.same _ hr) p

theorem State.Has.grows {s s' : State} (h : Grows s.store s'.store) {r : Ref} (hr : s.Has r) :
    s'.Has r :=
  Nat.lt_of_lt_of_le hr h.size

/-! ## A binding given a copy of its own -/

/-- What `settle` does: the store grows, the frame stays, the binding refers to no other's
storage from then on and reads what it read, and its home is new when it referred to another's
storage. -/
structure Settled (s : State) (e : Entry) (s' : State) (e' : Entry) : Prop where
  grows : Grows s.store s'.store
  env : s'.env = s.env
  alias : e'.alias = none
  unique : e'.unique = e.unique
  cow : e'.cow = e.cow
  inout : e'.inout = e.inout
  reads : s.Has e.ref → ∀ p, deref s' e'.ref p = deref s e.ref p
  has : s.Has e.ref → s'.Has e'.ref
  home : e.alias = none → s' = s ∧ e' = e
  fresh : e.alias ≠ none → e'.home = ⟨s.store.size, []⟩ ∧ s'.store.size = s.store.size + 1

theorem settle_spec {s s' : State} {e e' : Entry} (h : settle s e = .ok (s', e')) :
    Settled s e s' e' := by
  unfold settle at h
  split at h
  · rename_i ha
    cases h
    exact ⟨Grows.refl _, rfl, ha, rfl, rfl, rfl, fun _ _ => rfl, id, fun _ => ⟨rfl, rfl⟩,
      fun h => absurd ha h⟩
  · rename_i r ha
    cases hd : deref s r [] with
    | error f => rw [hd] at h; cases h
    | ok v =>
      rw [hd] at h
      cases h
      refine ⟨Grows.push _ _, rfl, rfl, rfl, rfl, rfl, fun _ p => ?_,
        fun _ => by simp [State.Has, Entry.ref], fun h => by simp [ha] at h, fun _ => ⟨rfl, by simp⟩⟩
      have hr : e.ref = r := by simp [Entry.ref, ha]
      rw [hr, ← List.nil_append p, deref_append s r [] p, hd]
      exact deref_push_new s s.env v p

/-! ## Every binding that refers into a part given a copy of its own -/

/-- What `evacuate region skip i` does to each binding of a frame, from position `i`: its name,
its verdict and its kind stay, it reads what it read, and it refers to no other's storage, from
a new home, when it isn't at `skip` and referred into `region`; every other binding stays. -/
def Evacuated (region : Ref) (skip : Nat) (s s' : State) :
    Nat → List (Name × Entry) → List (Name × Entry) → Prop
  | _, [], [] => True
  | i, (y, e) :: rest, (y', e') :: rest' =>
    y' = y ∧ e'.unique = e.unique ∧ e'.cow = e.cow ∧ e'.inout = e.inout ∧
      (s.Has e.ref → ∀ p, deref s' e'.ref p = deref s e.ref p) ∧
      (if i != skip && e.alias.any (overlaps region) then
        e'.alias = none ∧ s.store.size ≤ e'.home.loc ∧ e'.home.path = []
      else e' = e) ∧
      Evacuated region skip s s' (i + 1) rest rest'
  | _, _, _ => False

theorem Evacuated.grow {region : Ref} {skip : Nat} {s s₁ s' : State} (hg : Grows s.store s₁.store)
    (hg' : Grows s₁.store s'.store) :
    ∀ {i : Nat} {env env' : List (Name × Entry)},
      Evacuated region skip s₁ s' i env env' → Evacuated region skip s s' i env env'
  | _, [], [], _ => trivial
  | i, (y, e) :: rest, (y', e') :: rest', ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ => by
    refine ⟨h₁, h₂, h₃, h₄, fun hr p => (h₅ (hr.grows hg) p).trans (deref_grows hg hr p), ?_,
      Evacuated.grow hg hg' h₇⟩
    split
    · rename_i hc
      simp only [hc, ↓reduceIte] at h₆
      exact ⟨h₆.1, Nat.le_trans hg.size h₆.2.1, h₆.2.2⟩
    · rename_i hc
      simpa [hc] using h₆

/-- `Evacuated` reads only the store of the state it ends in. -/
theorem Evacuated.congr {region : Ref} {skip : Nat} {s s₁ s₂ : State} (hst : s₂.store = s₁.store) :
    ∀ {i : Nat} {env env' : List (Name × Entry)},
      Evacuated region skip s s₁ i env env' → Evacuated region skip s s₂ i env env'
  | _, [], [], _ => trivial
  | _, (_, _) :: _, (_, _) :: _, ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ =>
    ⟨h₁, h₂, h₃, h₄, fun hr p => (deref_congr (by rw [hst]) p).trans (h₅ hr p), h₆,
      Evacuated.congr hst h₇⟩

theorem bind_ok {α β : Type} {x : Except Fault α} {f : α → Except Fault β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The step of `evacuate` at one binding. -/
theorem evacuate_head {region : Ref} {skip i : Nat} {s s₁ : State} {e e₁ : Entry}
    (h : (if i != skip && e.alias.any (overlaps region) then settle s e else pure (s, e)) =
      .ok (s₁, e₁)) :
    Grows s.store s₁.store ∧ s₁.env = s.env ∧ e₁.unique = e.unique ∧ e₁.cow = e.cow ∧
      e₁.inout = e.inout ∧ (s.Has e.ref → ∀ p, deref s₁ e₁.ref p = deref s e.ref p) ∧
      (s.Has e.ref → s₁.Has e₁.ref) ∧ (if i != skip && e.alias.any (overlaps region) then
        e₁.alias = none ∧ s.store.size ≤ e₁.home.loc ∧ e₁.home.path = []
      else e₁ = e) := by
  split at h
  · rename_i hc
    have hs := settle_spec h
    refine ⟨hs.grows, hs.env, hs.unique, hs.cow, hs.inout, hs.reads, hs.has, ?_⟩
    simp only [hc, ↓reduceIte]
    have ha : e.alias ≠ none := by
      intro hn
      simp [hn] at hc
    exact ⟨hs.alias, by rw [(hs.fresh ha).1]; exact Nat.le_refl _, by rw [(hs.fresh ha).1]⟩
  · rename_i hc
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Grows.refl _, rfl, rfl, rfl, rfl, fun _ _ => rfl, id, by simp [hc]⟩

theorem evacuate_cons {region : Ref} {skip i : Nat} {s s' : State} {y : Name} {e : Entry}
    {rest env' : List (Name × Entry)}
    (h : evacuate region skip i s ((y, e) :: rest) = .ok (s', env')) :
    ∃ s₁ e₁ rest₂, (if i != skip && e.alias.any (overlaps region) then settle s e
        else pure (s, e)) = .ok (s₁, e₁) ∧
      evacuate region skip (i + 1) s₁ rest = .ok (s', rest₂) ∧ env' = (y, e₁) :: rest₂ := by
  unfold evacuate at h
  dsimp only at h
  split at h
  all_goals
    obtain ⟨⟨s₁, e₁⟩, hse, h⟩ := bind_ok h
    obtain ⟨⟨s₂, rest₂⟩, hsr, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨s₁, e₁, rest₂, ?_, hsr, rfl⟩
    simp [*]

theorem evacuate_spec {region : Ref} {skip : Nat} :
    ∀ {i : Nat} {s s' : State} {env env' : List (Name × Entry)},
      evacuate region skip i s env = .ok (s', env') →
      Grows s.store s'.store ∧ s'.env = s.env ∧ Evacuated region skip s s' i env env'
  | _, s, s', [], env', h => by
    simp only [evacuate, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Grows.refl _, rfl, trivial⟩
  | i, s, s', (y, e) :: rest, env', h => by
    obtain ⟨s₁, e₁, rest₂, hse, hsr, rfl⟩ := evacuate_cons h
    obtain ⟨hg₂, he₂, hev⟩ := evacuate_spec hsr
    obtain ⟨hg₁, he₁, hu, hc, hi, hr, hh₁, hif⟩ := evacuate_head hse
    refine ⟨hg₁.trans hg₂, he₂.trans he₁, rfl, hu, hc, hi,
      fun hh p => (deref_grows hg₂ (hh₁ hh) p).trans (hr hh p), ?_, Evacuated.grow hg₁ hg₂ hev⟩
    · split
      · rename_i hc'
        simp only [hc', ↓reduceIte] at hif
        exact ⟨hif.1, hif.2.1, hif.2.2⟩
      · rename_i hc'
        simpa [hc'] using hif

end Sharing

end Stilt
