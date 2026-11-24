import Stilt.Sharing.Assignment

/-!
# The roots of a call's `inout` arguments

When a call starts, each root of an `inout` argument that is shared stops sharing
(modes.kinds-of-access): it refers to its home, which no other binding's part overlaps, so the
callee's parameters, which refer below that home, are the only way to its storage. `unshare` of
one root leaves every other root as it was, so after `unshareArgs` every root is alone.
-/

namespace Stilt.Sharing

open InPlace (Ref)

/-- Every binding of `s'` is one of `s`'s, or refers to a new home of its own past `s`'s
store. -/
def Settles (s s' : State) : Prop :=
  ∀ yb ∈ s'.env, (∃ ya ∈ s.env, ya.2 = yb.2) ∨ (yb.2.alias = none ∧ s.store.size ≤ yb.2.home.loc)

/-- `x`'s binding refers to its home, which no other binding's part overlaps. -/
def Alone (s : State) (x : Name) : Prop :=
  ∃ e, s.env.lookup x = some e ∧ e.alias = none ∧
    ∀ ye ∈ s.env, ye.2 ≠ e → overlaps e.home ye.2.ref = false

/-- `unshare` settles: each binding after it is one from before, or one given a new home. -/
theorem unshare_settles {s s₁ : State} {y : Name} (h : unshare s y = .ok s₁) : Settles s s₁ := by
  unfold unshare at h
  split at h
  · rename_i i e hi hy
    split at h
    · rename_i r ha
      cases hse : settle s e with
      | error f =>
        rw [hse] at h
        change (Except.error f : Except Fault State) = Except.ok s₁ at h
        cases h
      | ok p =>
        obtain ⟨s', e'⟩ := p
        rw [hse] at h
        change Except.ok ({ env := s'.env.set i (y, e'), store := s'.store } : State) =
          Except.ok s₁ at h
        cases h
        have hS := settle_spec hse
        obtain ⟨hhome, -⟩ := hS.fresh (by simp [ha])
        intro yb hyb
        rw [show ({ env := s'.env.set i (y, e'), store := s'.store } : State).env =
          s'.env.set i (y, e') from rfl, hS.env] at hyb
        rcases List.mem_or_eq_of_mem_set hyb with hyb | rfl
        · exact .inl ⟨yb, hyb, rfl⟩
        · exact .inr ⟨hS.alias, by rw [show (y, e').2.home = e'.home from rfl, hhome]; exact Nat.le_refl _⟩
    · cases hev : evacuate e.home i 0 s s.env with
      | error f =>
        rw [hev] at h
        change (Except.error f : Except Fault State) = Except.ok s₁ at h
        cases h
      | ok p =>
        obtain ⟨s', env'⟩ := p
        rw [hev] at h
        change Except.ok ({ env := env', store := s'.store } : State) = Except.ok s₁ at h
        cases h
        obtain ⟨-, -, hE⟩ := evacuate_spec hev
        have hE₁ : Evacuated e.home i s { s' with env := env' } 0 s.env env' :=
          Evacuated.congr (s₁ := s') (s₂ := { s' with env := env' }) rfl hE
        exact fun yb hyb => (hE₁.mem_settled yb hyb).imp id fun ⟨_, _, _, ha', hl, _⟩ => ⟨ha', hl⟩
  · cases h

/-- Replacing the binding at a position named `y` keeps the lookup of every other name. -/
theorem lookup_set_other {x y : Name} {b : Entry} :
    ∀ {l : List (Name × Entry)} {i : Nat} {a : Entry}, l[i]? = some (y, a) → x ≠ y →
      (l.set i (y, b)).lookup x = l.lookup x
  | [], _, _, h, _ => by simp at h
  | (z, c) :: l, 0, a, h, hxy => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.set_cons_zero]
    rw [lookup_cons_ne hxy, lookup_cons_ne hxy]
  | (z, c) :: l, i + 1, a, h, hxy => by
    simp only [List.getElem?_cons_succ] at h
    simp only [List.set_cons_succ]
    by_cases hz : x = z
    · subst hz
      rw [List.lookup_cons_self, List.lookup_cons_self]
    · rw [lookup_cons_ne hz, lookup_cons_ne hz]
      exact lookup_set_other h hxy

/-- `evacuate` keeps the binding that a name finds when it refers to its own home. -/
theorem Evacuated.lookup_plain {region : Ref} {skip : Nat} {s s' : State} {x : Name}
    {e : Entry} :
    ∀ {k : Nat} {env env' : List (Name × Entry)}, Evacuated region skip s s' k env env' →
      env.lookup x = some e → e.alias = none → env'.lookup x = some e
  | _, [], [], _, h, _ => by simp at h
  | _, (y, f) :: _, (y', f') :: _, ⟨h₁, _, _, _, _, h₆, h₇⟩, hl, ha => by
    subst y'
    by_cases hy : x = y
    · subst hy
      rw [List.lookup_cons_self, Option.some.injEq] at hl
      subst hl
      simp only [ha, Option.any_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h₆
      rw [h₆, List.lookup_cons_self]
    · rw [lookup_cons_ne hy] at hl ⊢
      exact Evacuated.lookup_plain h₇ hl ha
  | _, [], _ :: _, h, _, _ => h.elim
  | _, _ :: _, [], h, _, _ => h.elim

/-- `unshare` of `y` keeps the binding that another name finds when it refers to its own
home. -/
theorem unshare_lookup_other {s s₁ : State} {x y : Name} {e : Entry} (h : unshare s y = .ok s₁)
    (hxy : x ≠ y) (hx : s.env.lookup x = some e) (ha : e.alias = none) :
    s₁.env.lookup x = some e := by
  unfold unshare at h
  split at h
  · rename_i i f hi hy
    split at h
    · cases hse : settle s f with
      | error g =>
        rw [hse] at h
        change (Except.error g : Except Fault State) = Except.ok s₁ at h
        cases h
      | ok p =>
        obtain ⟨s', f'⟩ := p
        rw [hse] at h
        change Except.ok ({ env := s'.env.set i (y, f'), store := s'.store } : State) =
          Except.ok s₁ at h
        cases h
        show (s'.env.set i (y, f')).lookup x = some e
        rw [(settle_spec hse).env, lookup_set_other (lookup_of_findIdx? hi hy) hxy, hx]
    · cases hev : evacuate f.home i 0 s s.env with
      | error g =>
        rw [hev] at h
        change (Except.error g : Except Fault State) = Except.ok s₁ at h
        cases h
      | ok p =>
        obtain ⟨s', env'⟩ := p
        rw [hev] at h
        change Except.ok ({ env := env', store := s'.store } : State) = Except.ok s₁ at h
        cases h
        obtain ⟨-, -, hE⟩ := evacuate_spec hev
        exact hE.lookup_plain hx ha
  · cases h

/-- `unshare` of another root leaves a root alone. -/
theorem Alone.unshare {s s₁ : State} {x y : Name} (hx : Alone s x)
    (hlt : ∀ ye ∈ s.env, ye.2.home.loc < s.store.size) (hxy : x ≠ y)
    (h : unshare s y = .ok s₁) : Alone s₁ x := by
  obtain ⟨e, hl, ha, hap⟩ := hx
  refine ⟨e, unshare_lookup_other h hxy hl ha, ha, fun yb hyb hne => ?_⟩
  rcases unshare_settles h yb hyb with ⟨ya, hya, he⟩ | ⟨ha', hle⟩
  · rw [← he]
    exact hap ya hya (he ▸ hne)
  · have hr : yb.2.ref = yb.2.home := by simp [Entry.ref, ha']
    rw [hr, overlaps_comm]
    exact overlaps_fresh (Nat.lt_of_lt_of_le (hlt _ (mem_of_lookup hl)) hle)

/-- Frames with the same names find the same names. -/
theorem lookup_isSome_of_names {x : Name} :
    ∀ {l l' : List (Name × Entry)}, l'.map Prod.fst = l.map Prod.fst →
      (l'.lookup x).isSome = (l.lookup x).isSome
  | [], [], _ => rfl
  | (y, _) :: l, (y', _) :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    by_cases hx : x = y'
    · subst hx
      simp [List.lookup_cons_self]
    · rw [lookup_cons_ne hx, lookup_cons_ne hx]
      exact lookup_isSome_of_names h
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- `unshareArgs` when every binding is shared: it ends, the frame and the state still agree, the
state follows from the first, every root that was alone still is, and every root of an `inout`
argument that names a binding is alone (modes.kinds-of-access). -/
theorem unshareArgs_agrees : ∀ (passed : List Passed) {fr : Copy.State} {s : State × World},
    AgreesIn fr s →
    ∃ s₁, unshareArgs passed s = .done () s₁ ∧ AgreesIn fr s₁ ∧ Follows s.1 s₁.1 ∧
      (∀ z, Alone s.1 z → Alone s₁.1 z) ∧
      ∀ x p, Passed.place x p ∈ passed → (s₁.1.env.lookup x).isSome → Alone s₁.1 x
  | [], _, s, hs => ⟨s, rfl, hs, Follows.refl _, fun _ h => h, by simp⟩
  | .value _ :: rest, _, _, hs => by
    obtain ⟨s₁, h₁, hA, hF, hz, hr⟩ := unshareArgs_agrees rest hs
    exact ⟨s₁, h₁, hA, hF, hz, fun y q hy => hr y q (by simpa using hy)⟩
  | .moved _ _ :: rest, _, _, hs => by
    obtain ⟨s₁, h₁, hA, hF, hz, hr⟩ := unshareArgs_agrees rest hs
    exact ⟨s₁, h₁, hA, hF, hz, fun y q hy => hr y q (by simpa using hy)⟩
  | .place x p :: rest, _, s, hs => by
    cases hl : s.1.env.lookup x with
    | none =>
      have hstep : unshareArgs (.place x p :: rest) s = unshareArgs rest s := by
        show (Eval.update _ >>= fun _ => unshareArgs rest) s = _
        exact update_ok (st' := s) (by simp [hl])
      obtain ⟨s₁, h₁, hA, hF, hz, hr⟩ := unshareArgs_agrees rest hs
      refine ⟨s₁, hstep.trans h₁, hA, hF, hz, fun y q hy hsome => ?_⟩
      rcases List.mem_cons.1 hy with heq | hy
      · cases heq
        rw [lookup_isSome_of_names (KeptEntries.names hF.2.2), hl] at hsome
        cases hsome
      · exact hr y q hy hsome
    | some e =>
      have hu : e.unique = false := hs.2.1.shared (x, e) (mem_of_lookup hl)
      obtain ⟨s', e₁, hun, hA', hS', hF', hl', ha', hap'⟩ := unshare_agrees hs.1 hs.2.1 hl
      have hstep : unshareArgs (.place x p :: rest) s = unshareArgs rest (s', s.2) := by
        show (Eval.update _ >>= fun _ => unshareArgs rest) s = _
        exact update_ok (st' := (s', s.2)) (by simp [hl, hu, hun]; rfl)
      obtain ⟨s₁, h₁, hA, hF, hz, hr⟩ :=
        unshareArgs_agrees rest (s := (s', s.2)) ⟨hA', hS', hs.2.2⟩
      have hx' : Alone s' x := ⟨e₁, hl', ha', hap'⟩
      refine ⟨s₁, hstep.trans h₁, hA, hF'.trans hF, fun z hzA => hz z ?_, fun y q hy hsome => ?_⟩
      · by_cases hzx : z = x
        · subst hzx
          exact hx'
        · exact Alone.unshare hzA (fun ye hye => (hs.1.has ye hye).1) hzx hun
      · rcases List.mem_cons.1 hy with heq | hy
        · cases heq
          exact hz x hx'
        · exact hr y q hy hsome

end Stilt.Sharing
