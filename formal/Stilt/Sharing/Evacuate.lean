import Stilt.Sharing.Frame

/-!
# Settling every binding that refers into a part

When every binding of a frame reads a value, `evacuate` succeeds, each binding reads what it
read, and the bindings it settles get new locations of their own, so the frame's homes still
don't overlap (modes.shared-writes).
-/

namespace Stilt.Sharing

open InPlace (Ref)

theorem has_of_deref {s : State} {r : Ref} {p : Path} {v : Value} (h : deref s r p = .ok v) :
    s.Has r := by
  unfold deref at h
  split at h
  · rename_i w hw
    exact (Array.getElem?_eq_some_iff.1 hw).1
  · cases h

theorem settle_ok {s : State} {e : Entry} {v : Value} (h : deref s e.ref [] = .ok v) :
    ∃ s' e', settle s e = .ok (s', e') := by
  unfold settle
  split
  · exact ⟨_, _, rfl⟩
  · rename_i r hr
    have : e.ref = r := by simp [Entry.ref, hr]
    rw [this] at h
    simp only [h]
    exact ⟨_, _, rfl⟩

/-- `evacuate` succeeds on bindings that each read a value. -/
theorem evacuate_ok (region : Ref) (skip : Nat) :
    ∀ (i : Nat) (s : State) (env : List (Name × Entry)),
      (∀ ye ∈ env, ∃ v, deref s ye.2.ref [] = .ok v) →
        ∃ s' env', evacuate region skip i s env = .ok (s', env')
  | _, _, [], _ => ⟨_, _, rfl⟩
  | i, s, (y, e) :: rest, h => by
    obtain ⟨v, hv⟩ := h (y, e) List.mem_cons_self
    obtain ⟨s₁, e₁, h₁⟩ : ∃ s₁ e₁, (if i != skip && e.alias.any (overlaps region) then settle s e
        else pure (s, e)) = .ok (s₁, e₁) := by
      split
      · exact settle_ok hv
      · exact ⟨s, e, rfl⟩
    have hg := (evacuate_head h₁).1
    obtain ⟨s', rest', h₂⟩ := evacuate_ok region skip (i + 1) s₁ rest fun ye hye => by
      obtain ⟨w, hw⟩ := h ye (List.mem_cons_of_mem _ hye)
      exact ⟨w, (deref_grows hg (has_of_deref hw) []).trans hw⟩
    refine ⟨s', (y, e₁) :: rest', ?_⟩
    unfold evacuate
    dsimp only
    split
    · rename_i hc
      simp only [hc, ↓reduceIte] at h₁
      rw [h₁]
      show (evacuate region skip (i + 1) s₁ rest >>= fun x => Except.ok (x.1, (y, e₁) :: x.2)) = _
      rw [h₂]
      rfl
    · rename_i hc
      simp only [hc, Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h₁
      obtain ⟨rfl, rfl⟩ := h₁
      show (evacuate region skip (i + 1) s rest >>= fun x => Except.ok (x.1, (y, e) :: x.2)) = _
      rw [h₂]
      rfl

/-- The bindings `evacuate` settles read what they read, as do the others. -/
theorem Evacuated.alike {region : Ref} {skip : Nat} {s s' : State} :
    ∀ {i : Nat} {env env' : List (Name × Entry)}, Evacuated region skip s s' i env env' →
      (∀ ye ∈ env, s.Has ye.2.ref) → ReadsAlike s.store s'.store env env'
  | _, [], [], _, _ => trivial
  | _, (_, _) :: _, (_, _) :: _, ⟨h₁, _, _, _, h₅, _, h₇⟩, hh =>
    ⟨⟨h₁.symm, (deref_env _ _ _ _).trans ((h₅ (hh _ List.mem_cons_self) []).trans
      (deref_env _ _ _ _).symm)⟩, Evacuated.alike h₇ fun ye hye => hh ye (List.mem_cons_of_mem _ hye)⟩

/-- Each binding after `evacuate` is one from before, or has a new home. -/
theorem Evacuated.mem {region : Ref} {skip : Nat} {s s' : State} :
    ∀ {i : Nat} {env env' : List (Name × Entry)}, Evacuated region skip s s' i env env' →
      ∀ yb ∈ env', (∃ ya ∈ env, ya.2 = yb.2) ∨ s.store.size ≤ yb.2.home.loc
  | _, [], [], _, _, hyb => by simp at hyb
  | _, (y, e) :: _, (y', e') :: _, ⟨_, _, _, _, _, h₆, h₇⟩, yb, hyb => by
    rcases List.mem_cons.1 hyb with rfl | hyb
    · split at h₆
      · exact .inr h₆.2.1
      · exact .inl ⟨(y, e), List.mem_cons_self, h₆.symm⟩
    · rcases Evacuated.mem h₇ yb hyb with ⟨ya, hya, h⟩ | h
      · exact .inl ⟨ya, List.mem_cons_of_mem _ hya, h⟩
      · exact .inr h

/-- Homes that don't overlap, each a location the store has. -/
def HomesApart (s : State) (env : List (Name × Entry)) : Prop :=
  env.Pairwise (fun a b => overlaps a.2.home b.2.home = false) ∧
    ∀ ye ∈ env, ye.2.home.loc < s.store.size

/-- `evacuate` keeps the homes apart: each binding it settles gets a new location. -/
theorem evacuate_apart {region : Ref} {skip : Nat} :
    ∀ {i : Nat} {s s' : State} {env env' : List (Name × Entry)},
      evacuate region skip i s env = .ok (s', env') → HomesApart s env → HomesApart s' env'
  | _, s, s', [], env', h, _ => by
    simp only [evacuate, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.nil, by simp⟩
  | i, s, s', (y, e) :: rest, env', h, ⟨hp, hl⟩ => by
    obtain ⟨s₁, e₁, rest₂, hse, hsr, rfl⟩ := evacuate_cons h
    obtain ⟨hg₁, -, -, -, -, -, -, hif⟩ := evacuate_head hse
    obtain ⟨hg₂, -, hev⟩ := evacuate_spec hsr
    have hhead : e₁ = e ∨ e₁.home = ⟨s.store.size, []⟩ ∧ s₁.store.size = s.store.size + 1 := by
      split at hif
      · rename_i hc
        right
        simp only [hc, ↓reduceIte] at hse
        have hs := settle_spec hse
        have ha : e.alias ≠ none := by intro hn; simp [hn] at hc
        exact hs.fresh ha
      · exact .inl hif
    obtain ⟨hp', hl'⟩ := evacuate_apart hsr ⟨hp.of_cons, fun ye hye =>
      Nat.lt_of_lt_of_le (hl ye (List.mem_cons_of_mem _ hye)) hg₁.size⟩
    -- each binding of the rest is one of `rest`, or has a new home past `s₁`'s store
    have hrest : ∀ yb ∈ rest₂, (∃ ya ∈ rest, ya.2 = yb.2) ∨ s₁.store.size ≤ yb.2.home.loc :=
      fun yb hyb => Evacuated.mem hev yb hyb
    refine ⟨List.Pairwise.cons (fun yb hyb => ?_) hp', fun ye hye => ?_⟩
    · rcases hrest yb hyb with ⟨ya, hya, hab⟩ | hfresh
      · rw [← hab]
        rcases hhead with rfl | ⟨hh, hsz⟩
        · exact List.rel_of_pairwise_cons hp hya
        · rw [hh]
          exact overlaps_fresh (by simpa using hl ya (List.mem_cons_of_mem _ hya))
      · have hlt : e₁.home.loc < s₁.store.size := by
          rcases hhead with rfl | ⟨hh, hsz⟩
          · exact Nat.lt_of_lt_of_le (hl _ List.mem_cons_self) hg₁.size
          · rw [hh, hsz]; exact Nat.lt_succ_self _
        exact (overlaps_comm _ _).trans (overlaps_fresh (show e₁.home.loc < yb.2.home.loc by omega))
    · rcases List.mem_cons.1 hye with rfl | hye
      · rcases hhead with rfl | ⟨hh, hsz⟩
        · exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (hl _ List.mem_cons_self) hg₁.size) hg₂.size
        · show e₁.home.loc < s'.store.size
          have := hg₂.size
          rw [hh]
          simp only
          omega
      · exact hl' ye hye

end Stilt.Sharing
