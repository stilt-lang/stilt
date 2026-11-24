import Stilt.Writes.State

/-!
# Writing and viewing in states that agree

A write to a variable that nothing freezes writes the same location in both
models, which no window reads and no writable binding writes (views.change-while-viewed;
projections.what-view-writes). A write through a writable binding writes its source's
storage in the window model and its copy in the copy model, and the copy
written back still gives the window's storage (projections.places-through-views). `View.of`
and `view.into` of a variable that no writable binding locks make a window
and the part it reads.
-/

namespace Stilt.Writes

open Stilt.Views (Store bounded slice cell source Pointwise ExceptAgree)

/-- Bindings agree in stores that are the same wherever they look. -/
theorem BAgrees.congr {sw sc sw' sc' : Store} {b c : WBinding} (h : BAgrees sw sc b c)
    (hs : ∀ ℓ, Refers b ℓ → sw'[ℓ]? = sw[ℓ]? ∧ sc'[ℓ]? = sc[ℓ]?) : BAgrees sw' sc' b c := by
  cases b with
  | loc _ => cases c <;> exact h
  | view r =>
    obtain ⟨r', rfl, hag⟩ := h.view_inv
    show Agrees sw' r r'
    cases r <;> cases r' <;> simp only [Agrees] at hag ⊢ <;>
      first | exact hag | (rename_i ℓ _ _ _ _; rw [part_congr _ _ _ (hs ℓ rfl).1]; exact hag) |
        (rename_i ℓ _ _ _ _ _ _ _ _; rw [part_congr _ _ _ (hs ℓ rfl).1]; exact hag)
  | writes r =>
    obtain ⟨ℓ, π, a, b, part, rfl, rfl, c, c', hc, hc', hr⟩ := h.writes_inv
    obtain ⟨h₁, h₂⟩ := hs ℓ rfl
    exact ⟨rfl, rfl, rfl, rfl, c, c', by rw [cell_congr h₂, hc], by rw [cell_congr h₁, hc'], hr⟩

/-- A variable that nothing freezes holds no location that a guard keeps. -/
theorem Guarded.ne {F : List Name} {env : List (Name × WBinding)} {ℓ ℓ' : Nat} {x : Name}
    {b : WBinding} (hg : Guarded F env ℓ') (hx : env.lookup x = some b) (hb : Changes b ℓ)
    (hF : x ∉ F) : ℓ' ≠ ℓ := fun he => hF (hg x b hx (he ▸ hb))

theorem getElem?_set_eq {st st' : Store} {ℓ : Nat} (c : Option Value)
    (h : st.length = st'.length) : (st.set ℓ c)[ℓ]? = (st'.set ℓ c)[ℓ]? := by
  simp [List.getElem?_set, h]

/-! ## Writing a variable -/

/-- A write to a variable that nothing freezes (E0423 and E0429). -/
theorem StateAgrees.setLoc {Γ : Sources} {R W : List Name} {sw sc : WState} {x : Name}
    {ℓ : Nat} {π : Path} {w : Value} (h : StateAgrees sw sc) (hs : InScope Γ R W sw.env)
    (hx : sw.env.lookup x = some (.loc ℓ)) (hF : x ∉ R ++ W) :
    ExceptAgree (fun st st' => StateAgrees ⟨sw.env, st⟩ ⟨sc.env, st'⟩ ∧
        Steps (R ++ W) sw ⟨sw.env, st⟩) (setCell sw.store ℓ π w) (setCell sc.store ℓ π w) := by
  have hun := hs.untargeted hx fun hw => hF (List.mem_append_right _ hw)
  unfold setCell
  rw [← cell_congr (h.off ℓ hun)]
  cases hc : cell sw.store ℓ with
  | error f => exact rfl
  | ok v =>
    dsimp only
    cases v.set π w with
    | error f => exact rfl
    | ok v' =>
      have hne : ∀ ℓ', Guarded (R ++ W) sw.env ℓ' → ℓ' ≠ ℓ := fun ℓ' hg => hg.ne hx rfl hF
      have hrefers : ∀ y b ℓ', (y, b) ∈ sw.env → Refers b ℓ' → ℓ' ≠ ℓ := by
        intro y b ℓ' hy hr
        cases b with
        | loc _ => exact hr.elim
        | view r =>
          cases r <;> simp only [Refers] at hr
          subst hr
          exact hne _ (hs.guarded y _ _ _ _ hy)
        | writes r =>
          cases r <;> simp only [Refers] at hr
          subst hr
          exact fun he => hun y _ hy (he ▸ rfl)
      refine ⟨⟨by simp [h.length], ?_, fun ℓ' hu => ?_, fun y ℓ' hy => ?_⟩,
        ⟨rfl, by simp, fun ℓ' hg _ => List.getElem?_set_ne (hne ℓ' hg).symm⟩⟩
      · refine Pointwise.imp_left (fun e c he hp => ⟨hp.1, hp.2.congr fun ℓ' hr => ?_⟩) h.env
        have := (hrefers e.1 e.2 ℓ' he hr).symm
        exact ⟨List.getElem?_set_ne this, List.getElem?_set_ne this⟩
      · by_cases he : ℓ' = ℓ
        · subst he
          exact getElem?_set_eq _ h.length
        · simp only [List.getElem?_set_ne (Ne.symm he)]
          exact h.off ℓ' hu
      · simpa using h.locs y ℓ' hy

/-! ## Writing through a writable binding -/

/-- Replacing the newest binding of `x` in the copy state, which writes the
location `ℓ`, keeps the environments agreeing with the window's, when the
bindings that don't write `ℓ` still agree. -/
theorem EnvAgrees.through {sw sc sw' sc' : Store} {x : Name} {ℓ : Nat} {bw bc' : WBinding} :
    ∀ {Ew Ec : List (Name × WBinding)}, EnvAgrees sw sc Ew Ec →
      Ew.Pairwise (fun e e' => ∀ ℓ, Targets e.2 ℓ → ¬Targets e'.2 ℓ) →
      Ew.lookup x = some bw → Targets bw ℓ → BAgrees sw' sc' bw bc' →
      (∀ y b c, (y, b) ∈ Ew → ¬Targets b ℓ → BAgrees sw sc b c → BAgrees sw' sc' b c) →
      EnvAgrees sw' sc' Ew (assocSet Ec x bc')
  | _, _, .nil, _, h, _, _, _ => by cases h
  | (y, b) :: _, (y', c) :: _, .cons ⟨hy, hbc⟩ hrest, hap, hl, ht, hnew, hold => by
    simp only at hy hbc
    subst hy
    rw [List.pairwise_cons] at hap
    by_cases hxy : x = y
    · subst hxy
      simp only [List.lookup_cons_self, Option.some.injEq] at hl
      subst hl
      simp only [assocSet, ↓reduceIte]
      exact .cons ⟨rfl, hnew⟩ (Pointwise.imp_left (fun e c he hp =>
        ⟨hp.1, hold e.1 e.2 c.2 (List.mem_cons_of_mem _ he) (hap.1 e he ℓ ht) hp.2⟩) hrest)
    · rw [lookup_cons_ne hxy] at hl
      simp only [assocSet, hxy, ↓reduceIte]
      have hb : ¬Targets b ℓ := fun hb => hap.1 (x, bw) (Views.mem_of_lookup hl) ℓ hb ht
      exact .cons ⟨rfl, hold y b c List.mem_cons_self hb hbc⟩ (EnvAgrees.through hrest hap.2 hl
        ht hnew fun z b' c' hz => hold z b' c' (List.mem_cons_of_mem _ hz))

theorem elemAt?_isSome {vs : List Value} {k : Int} (h₁ : 0 ≤ k) (h₂ : k < vs.length) :
    ∃ v, elemAt? vs k = some v :=
  ⟨vs[k.toNat]'(by omega), by simp [elemAt?, h₁]⟩

theorem elemAt?_none {vs : List Value} {k : Int} (h : ¬(0 ≤ k ∧ k < vs.length)) :
    elemAt? vs k = none := by
  unfold elemAt?
  split
  · exact List.getElem?_eq_none (by omega)
  · rfl

/-- `x[k] = w` through a writable binding that nothing freezes (E0423): the
window writes its source's storage, the copy its part (projections.places-through-views). -/
theorem StateAgrees.through {Γ : Sources} {R W : List Name} {sw sc : WState} {x : Name}
    {ℓ : Nat} {π : Path} {a b k : Int} {part : List Value} {w : Value} (h : StateAgrees sw sc)
    (hs : InScope Γ R W sw.env) (hx : sw.env.lookup x = some (.writes (.window ℓ π a b)))
    (hr : Restored sw.store sc.store ℓ π a b part) (hF : x ∉ R ++ W) :
    ExceptAgree (fun sw' sc' => StateAgrees sw' sc' ∧ Steps (R ++ W) sw sw')
      (sw.through x (.window ℓ π a b) k w) (sc.through x (.pending part ℓ π a b) k w) := by
  obtain ⟨c, c', hc, hc', hres⟩ := hr
  obtain ⟨vs, hvs, hb, hp, -⟩ := restore_ok hres
  have hab := (bounded_iff.1 hb).2.1
  unfold WState.through
  by_cases hk : 0 ≤ k ∧ k < b - a
  · obtain ⟨_, hel⟩ := elemAt?_isSome (vs := part) hk.1 (by omega)
    obtain ⟨c'', hc''⟩ : ∃ c'', restore c π a b (part.set k.toNat w) = .ok c'' := by
      simpa [restore, hvs, hb, hp] using Value.set_ok_of_get hvs _
    simp only [hk, and_self, ↓reduceIte, setCell, hc', restore_put w hres hk.1 hk.2, hc'',
      WVal.put, hel]
    have hne : ∀ ℓ', Guarded (R ++ W) sw.env ℓ' → ℓ' ≠ ℓ := fun ℓ' hg => hg.ne hx rfl hF
    have hxm := Views.mem_of_lookup hx
    refine ⟨⟨by simp [h.length], ?_, fun ℓ' hu => ?_, fun y ℓ' hy => ?_⟩,
      ⟨rfl, by simp, fun ℓ' hg _ => List.getElem?_set_ne (hne ℓ' hg).symm⟩⟩
    · refine h.env.through (hs.apart) hx rfl ⟨rfl, rfl, rfl, rfl, c, c'', hc, ?_, hc''⟩
        fun y b' c₀ hy ht hbc => hbc.congr fun ℓ' hr' => ⟨?_, rfl⟩
      · simp [cell, List.getElem?_set_self (Views.cell_lt hc')]
      · refine List.getElem?_set_ne fun he => ?_
        subst he
        cases b' with
        | loc _ => exact hr'.elim
        | writes r => exact ht (by cases r <;> simp_all [Refers, Targets])
        | view r =>
          cases r <;> simp only [Refers] at hr'
          exact hne _ (hs.guarded y _ _ _ _ hy) hr'
    · have hne' : ℓ' ≠ ℓ := fun he => hu x _ hxm (by simp [Targets, he])
      simp only [List.getElem?_set_ne hne'.symm]
      exact h.off ℓ' fun y b' hy => hu y b' hy
    · simpa using h.locs y ℓ' hy
  · have hel : elemAt? part k = none := elemAt?_none (by rw [hp]; omega)
    simp only [hk, ↓reduceIte, WVal.put, hel]
    exact rfl

/-! ## Views of a variable -/

/-- The sources of a view of a variable that no writable binding locks cover
its window (views.making-view). -/
theorem InScope.cover_root {Γ : Sources} {R W : List Name} {env : List (Name × WBinding)}
    (hs : InScope Γ R W env) {x : Name} {ℓ : Nat} (hx : env.lookup x = some (.loc ℓ))
    (hW : x ∉ W) : Cover [x] env ℓ := by
  intro y b hy hb
  cases b with
  | loc ℓ' =>
    cases (show ℓ' = ℓ from hb)
    exact List.mem_singleton.2 (hs.distinct y x ℓ hy (Views.mem_of_lookup hx))
  | view _ => exact hb.elim
  | writes r => exact (hs.untargeted hx hW y _ hy (by cases r <;> exact hb)).elim

/-- No binding views a variable that nothing freezes (projections.writable-views). -/
theorem InScope.alone_root {Γ : Sources} {R W : List Name} {env : List (Name × WBinding)}
    (hs : InScope Γ R W env) {x : Name} {ℓ : Nat} (hx : env.lookup x = some (.loc ℓ))
    (hF : x ∉ R ++ W) : Alone env ℓ := by
  intro y b hy hb
  cases b with
  | loc _ => exact hb
  | view r =>
    cases r <;> simp only [Refers] at hb
    exact (hs.guarded y _ _ _ _ hy).ne hx rfl hF hb
  | writes r =>
    exact hs.untargeted hx (fun hw => hF (List.mem_append_right _ hw)) y _ hy
      (by cases r <;> exact hb)

/-- `View.of` and `view.into` of a variable that no writable binding locks: a
window, and the part it reads, with the place it writes back to for
`view.into` (views.making-view; projections.writable-views). -/
theorem StateAgrees.make {Γ : Sources} {R W : List Name} {sw sc : WState}
    (h : StateAgrees sw sc) (hs : InScope Γ R W sw.env) {x : Name} {ℓ : Nat}
    (hx : sw.env.lookup x = some (.loc ℓ)) (hW : x ∉ W) (wr : Bool) (π : Path) (a b : Int) :
    ExceptAgree (fun rw rc => Agrees sw.store rw rc ∧ rw = .window ℓ π a b ∧
        (wr = true → ∃ part, rc = .pending part ℓ π a b))
      (makeView .window wr sw.store ℓ π a b) (makeView .copy wr sc.store ℓ π a b) := by
  have hsrc : source sc.store ℓ π = source sw.store ℓ π := by
    simp only [source, cell_congr (h.off ℓ (hs.untargeted hx hW)).symm]
  unfold makeView
  rw [hsrc]
  cases hv : source sw.store ℓ π with
  | error f => exact rfl
  | ok v =>
    cases v <;> try exact rfl
    rename_i vs
    dsimp only
    split
    · rename_i hb
      have hag : (WVal.window ℓ π a b).part sw.store = .ok (slice vs a b) := by
        simp [WVal.part, hv, hb]
      cases wr
      · exact ⟨hag, rfl, fun h => nomatch h⟩
      · exact ⟨⟨rfl, rfl, rfl, rfl, hag⟩, rfl, fun _ => ⟨_, rfl⟩⟩
    · exact rfl

end Stilt.Writes
