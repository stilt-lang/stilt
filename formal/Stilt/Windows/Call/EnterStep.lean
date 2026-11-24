import Stilt.Windows.Call.EnterArgs
import Stilt.Windows.AssignStore

/-!
# Binding a callee's variables, step by step

Both models start a call alike (`enter`): the captured values and the `let` arguments at new
locations, each `inout` parameter a reference to its argument's place, whose location the model
of windows first reads through its windows. While they bind the parameters one by one, the
states keep what the callee's simulation will need (`Entered`): the same variables and stores of
the same length; each cell of windows, read against the caller's in-place store, is the in-place
cell, and every window the caller's stores read alike reads its region as before; a location of
the caller's is as it was or holds the in-place value, which holds no window; a new location is
a variable's; and a variable on a location of the caller's is an `inout` parameter, whose cell
holds no window. The variables fit the callee's scope as parameters (`EntryOk`) and captured
variables (`BaseOk`).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- One step of the model of windows' `enter`: binding one parameter. -/
def enterStepW (caller s : State) : Name × Passed → Except Fault State
  | (y, .value v) | (y, .moved _ v) => pure (bind s y v)
  | (y, .place x path) =>
    match caller.env.lookup x with
    | some r => do
      let _ ← deref { caller with store := s.store } r path
      let c ← resolve s.store (← cell s.store r.loc)
      pure ⟨(y, ⟨r.loc, r.path ++ path⟩) :: s.env, s.store.set r.loc (some c)⟩
    | none => .error .stuck

theorem enterW_eq (caller : State) (captured : List (Name × Value))
    (bound : List (Name × Passed)) :
    enter caller captured bound = bound.foldlM (enterStepW caller)
      (captured.foldr (fun xv s => bind s xv.1 xv.2) ⟨[], caller.store⟩) := by
  unfold enter
  dsimp only
  congr 1
  all_goals first
    | rfl
    | (funext s ya
       obtain ⟨y, a⟩ := ya
       cases a <;> rfl)

/-- What a parameter of the callee holds: an `inout` one, on a location of the caller's, a cell
with no window; a `let` one, a new location of its own, whose value is its `In`, holding windows
only if its binding reads its own place. -/
def EntryOk (st : List (Option Value)) (In : List (Name × Value)) (L : Nat)
    (xb : Name × ViewBinding) (xr : Name × Ref) (_ : List (Name × Ref)) : Prop :=
  xb.2.param = true ∧ ((xr.2.loc < L ∧ ∃ u, st[xr.2.loc]? = some (some u) ∧ Free u) ∨
    (L ≤ xr.2.loc ∧ xr.2.path = [] ∧ ∃ w, st[xr.2.loc]? = some (some w) ∧ (xr.1, w) ∈ In ∧
      (¬Free w → (⟨xr.1, []⟩ : Shape) ∈ xb.2.sources)))

/-- What a captured variable holds: a new location of its own, with no window. -/
def BaseOk (st : List (Option Value)) (L : Nat) (xr : Name × Ref) : Prop :=
  L ≤ xr.2.loc ∧ xr.2.path = [] ∧ ∃ v, st[xr.2.loc]? = some (some v) ∧ Free v

/-- A change of the store that keeps every new location's cell and keeps a cell of the caller's
with no window one with no window. -/
def Keeps (L : Nat) (st st' : List (Option Value)) : Prop :=
  (∀ ℓ y, L ≤ ℓ → st[ℓ]? = some (some y) → st'[ℓ]? = some (some y)) ∧
    ∀ ℓ u, ℓ < L → st[ℓ]? = some (some u) → Free u → ∃ u', st'[ℓ]? = some (some u') ∧ Free u'

theorem keeps_append (L : Nat) (st : List (Option Value)) (c : Option Value) :
    Keeps L st (st ++ [c]) := by
  refine ⟨fun ℓ y _ hy => ?_, fun ℓ u _ hu hf => ⟨u, ?_, hf⟩⟩
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hy).1]; exact hy
  · rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hu).1]; exact hu

theorem EntryOk.keeps {st st' : List (Option Value)} {In : List (Name × Value)} {L : Nat}
    (hk : Keeps L st st') {xb : Name × ViewBinding} {xr : Name × Ref} {older : List (Name × Ref)}
    (h : EntryOk st In L xb xr older) : EntryOk st' In L xb xr older := by
  obtain ⟨hp, ⟨hl, u, hu, hf⟩ | ⟨hl, hpath, w, hw, hin, hs⟩⟩ := h
  · exact ⟨hp, .inl ⟨hl, hk.2 _ u hl hu hf⟩⟩
  · exact ⟨hp, .inr ⟨hl, hpath, w, hk.1 _ w hl hw, hin, hs⟩⟩

theorem BaseOk.keeps {st st' : List (Option Value)} {L : Nat} (hk : Keeps L st st')
    {xr : Name × Ref} (h : BaseOk st L xr) : BaseOk st' L xr := by
  obtain ⟨hl, hpath, v, hv, hf⟩ := h
  exact ⟨hl, hpath, v, hk.1 _ v hl hv, hf⟩

theorem Fits.keeps {st st' : List (Option Value)} {In : List (Name × Value)} {L : Nat}
    (hk : Keeps L st st') {Γ : ViewScope} {env : List (Name × Ref)}
    (h : Fits (EntryOk st In L) (BaseOk st L) Γ env) : Fits (EntryOk st' In L) (BaseOk st' L) Γ env :=
  Fits.mono (fun _ _ _ => EntryOk.keeps hk) (fun _ => BaseOk.keeps hk) h

/-- What the states keep while both models bind a callee's variables, the parameters `pre`
bound so far, from the caller's states `si₁` and `sw₁`. -/
structure Entered (D : Decls) (si₁ : InPlace.State) (sw₁ : State) (pre : List (Name × Passed))
    (s : InPlace.State) (t : State) : Prop where
  env : t.env = s.env
  length : t.store.length = s.store.length
  cells : ∀ (ℓ : Nat) y, t.store[ℓ]? = some (some y) →
    ∃ u, s.store[ℓ]? = some u ∧ VRel si₁.store sw₁.store y u
  viewed : ∀ u ∈ s.store, u.Viewed D
  regions : ∀ win, Holds sw₁.store si₁.store win → regionW t.store win = regionW sw₁.store win
  caller : ∀ ℓ < sw₁.store.length, t.store[ℓ]? = sw₁.store[ℓ]? ∨
    ∃ u, t.store[ℓ]? = some (some u) ∧ Free u ∧ ∃ o, sw₁.store[ℓ]? = some (some o)
  owned : ∀ (ℓ : Nat) y, sw₁.store.length ≤ ℓ → t.store[ℓ]? = some (some y) →
    ∃ xr ∈ t.env, xr.2 = ⟨ℓ, []⟩
  inout : ∀ xr ∈ t.env, xr.2.loc < sw₁.store.length →
    (∃ u, t.store[xr.2.loc]? = some (some u) ∧ Free u) ∧ ∃ x q, (xr.1, Passed.place x q) ∈ pre

variable {si₁ : InPlace.State} {sw₁ : State}

/-- The caller's states, before any binding. -/
theorem Entered.start {si : IState} {sw : WState} (hag : Agree D si sw) :
    Entered D si.1 sw.1 [] ⟨[], si.1.store⟩ ⟨[], sw.1.store⟩ where
  env := rfl
  length := hag.length
  cells ℓ y hy := hag.live ℓ y hy
  viewed := hag.viewed
  regions _ _ := rfl
  caller _ _ := .inl rfl
  owned ℓ y hl hy := absurd (List.getElem?_eq_some_iff.1 hy).1 (by simp; omega)
  inout _ h := nomatch h

theorem getElem?_append_eq {β : Type} (l : List β) (b : β) :
    (l ++ [b])[l.length]? = some b := by
  simp

/-- Binding a variable to a new location, in both models, values read alike. -/
theorem Entered.bind {pre pre' : List (Name × Passed)} {s : InPlace.State} {t : State}
    (h : Entered D si₁ sw₁ pre s t) (hlen : sw₁.store.length ≤ t.store.length)
    (hpre : ∀ z ∈ pre, z ∈ pre') (y : Name) {v w : Value}
    (hvw : VRel si₁.store sw₁.store w v) (hv : v.Viewed D) :
    Entered D si₁ sw₁ pre' (InPlace.bind s y v) (bind t y w) where
  env := by simp [InPlace.bind, Windows.bind, h.env, h.length]
  length := by simp [InPlace.bind, Windows.bind, h.length]
  cells ℓ z hz := by
    simp only [Windows.bind, getElem?_append_one] at hz
    simp only [InPlace.bind, getElem?_append_one, ← h.length]
    split at hz
    · rename_i hl
      simp only [hl, ↓reduceIte]
      exact h.cells ℓ z hz
    · rename_i hl
      split at hz
      · rename_i he
        simp only [he, ↓reduceIte, Option.some.injEq] at hz ⊢
        subst hz
        exact ⟨v, by simp, hvw⟩
      · cases hz
  viewed u hu := by
    simp only [InPlace.bind, List.mem_append, List.mem_singleton] at hu
    rcases hu with hu | rfl
    · exact h.viewed u hu
    · exact hv
  regions win hh := by
    simp only [Windows.bind]
    rw [regionW_append _ (by have := hh.lt; omega)]
    exact h.regions win hh
  caller ℓ hl := by
    simp only [Windows.bind, List.getElem?_append_left (show ℓ < t.store.length by omega)]
    exact h.caller ℓ hl
  owned ℓ z hl hz := by
    simp only [Windows.bind, getElem?_append_one] at hz
    split at hz
    · obtain ⟨xr, hxr, he⟩ := h.owned ℓ z hl hz
      exact ⟨xr, List.mem_cons_of_mem _ hxr, he⟩
    · split at hz
      · rename_i he
        exact ⟨_, List.mem_cons_self, by simp [he]⟩
      · cases hz
  inout xr hxr hl := by
    simp only [Windows.bind, List.mem_cons] at hxr
    rcases hxr with rfl | hxr
    · simp at hl; omega
    · obtain ⟨⟨u, hu, hf⟩, hn⟩ := h.inout xr hxr hl
      obtain ⟨x, q, hq⟩ := hn
      refine ⟨⟨u, ?_, hf⟩, x, q, hpre _ hq⟩
      simp only [Windows.bind]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hu).1]
      exact hu

/-- An `inout` parameter bound to a place of the caller's location `r.loc`, which the model of
windows sets to the in-place value there, holding no window. -/
theorem Entered.place {pre : List (Name × Passed)} {s : InPlace.State} {t : State}
    (h : Entered D si₁ sw₁ pre s t) {r : Ref} (hr : r.loc < sw₁.store.length) {u : Value}
    (hu : si₁.store[r.loc]? = some u) (hs : s.store[r.loc]? = some u) (hf : Free u)
    (hlive : ∃ o, sw₁.store[r.loc]? = some (some o)) (y x : Name) (q : Path) :
    Entered D si₁ sw₁ (pre ++ [(y, .place x q)]) { s with env := (y, InPlace.placeRef r q) :: s.env }
      ⟨(y, ⟨r.loc, r.path ++ q⟩) :: t.env, t.store.set r.loc (some u)⟩ where
  env := by simp [InPlace.placeRef, h.env]
  length := by simp [h.length]
  cells ℓ z hz := by
    by_cases hl : ℓ = r.loc
    · subst hl
      rw [List.getElem?_set_self (by rw [h.length]; exact (List.getElem?_eq_some_iff.1 hs).1),
        Option.some.injEq, Option.some.injEq] at hz
      subst hz
      exact ⟨u, hs, VRel.free hf⟩
    · rw [List.getElem?_set_ne (Ne.symm hl)] at hz
      exact h.cells ℓ z hz
  viewed := h.viewed
  regions win hh := by
    by_cases hl : win.1 = r.loc
    · obtain ⟨d, hW, hI, -⟩ := hh
      have hlt : r.loc < t.store.length := by rw [h.length]; exact (List.getElem?_eq_some_iff.1 hs).1
      rw [hW]
      simp only [regionI, cellIn, hl, hu] at hI
      simp only [regionW, cell, hl, List.getElem?_set_self hlt]
      exact hI
    · rw [regionW_set_ne _ (Ne.symm hl)]
      exact h.regions win hh
  caller ℓ hl := by
    by_cases he : ℓ = r.loc
    · subst he
      exact .inr ⟨u, List.getElem?_set_self (by rw [h.length]; exact
        (List.getElem?_eq_some_iff.1 hs).1), hf, hlive⟩
    · rw [List.getElem?_set_ne (Ne.symm he)]
      exact h.caller ℓ hl
  owned ℓ z hl hz := by
    rw [List.getElem?_set_ne (by omega)] at hz
    obtain ⟨xr, hxr, he⟩ := h.owned ℓ z hl hz
    exact ⟨xr, List.mem_cons_of_mem _ hxr, he⟩
  inout xr hxr hl := by
    have hlt : r.loc < t.store.length := by rw [h.length]; exact (List.getElem?_eq_some_iff.1 hs).1
    rcases List.mem_cons.1 hxr with rfl | hxr
    · exact ⟨⟨u, List.getElem?_set_self hlt, hf⟩, x, q, by simp⟩
    · obtain ⟨⟨u', hu', hf'⟩, x', q', hq⟩ := h.inout xr hxr hl
      refine ⟨?_, x', q', List.mem_append_left _ hq⟩
      by_cases he : xr.2.loc = r.loc
      · rw [he]; exact ⟨u, List.getElem?_set_self hlt, hf⟩
      · rw [List.getElem?_set_ne (Ne.symm he)]; exact ⟨u', hu', hf'⟩

theorem keeps_set {L : Nat} {st : List (Option Value)} {ℓ : Nat} (hl : ℓ < L) {u : Value}
    (hf : Free u) : Keeps L st (st.set ℓ (some u)) := by
  refine ⟨fun k z hk hz => ?_, fun k u' hk hu' hf' => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hz
  · by_cases he : k = ℓ
    · subst he
      exact ⟨u, List.getElem?_set_self (List.getElem?_eq_some_iff.1 hu').1, hf⟩
    · rw [List.getElem?_set_ne (Ne.symm he)]; exact ⟨u', hu', hf'⟩

end Windows

end Stilt
