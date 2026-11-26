import Stilt.Moves.Control

/-!
# Holding shared values, moving

Copy-in, copy-out and `Moving` run a `when` alike. The analysis keeps its names live to the
end of its block, so both models read the same values of them there and put them back in one
world; and a `with` lets the same cells go in both (shared.when).
-/

namespace Stilt

namespace Moving

open InPlace

variable {α : Type} {G : α → Prop} {L X : Live}

/-- Putting back the values of live names from states that agree: the same fault, or one new
world for both, its cells holding values that a run may hold. -/
theorem putBack_agrees (held : Bool) : ∀ (cells : List (Name × Ty × Nat)) {m : List Bool}
    {fr : Copy.State} {s : State × World}, MAgreesIn m fr s →
    (∀ c ∈ cells, LiveAt c.1 m (names fr.1)) →
    (∃ e, Copy.memory.putBack held cells fr = .error e ∧
        Moving.memory.putBack held cells s = .error e) ∨
      ∃ w, Copy.memory.putBack held cells fr = .ok (fr.1, w) ∧
        Moving.memory.putBack held cells s = .ok (s.1, w) ∧ w.All VOk
  | [], _, (_, _), (_, _), ⟨_, hw, hx⟩, _ => by
    simp only at hw
    subst hw
    exact .inr ⟨_, rfl, rfl, hx⟩
  | (x, c) :: rest, _, (f, w), (t, y), ⟨hm, hw, hx⟩, hl => by
    cases hw
    have hlx := hl (x, c) List.mem_cons_self
    have hr : Copy.memory.read (f, w) x [] = Moving.memory.read (t, w) x [] := hm.read hlx []
    simp only [Memory.putBack]
    rw [← hr]
    cases hv : Copy.memory.read (f, w) x [] with
    | error e => exact .inl ⟨e, rfl, rfl⟩
    | ok v =>
      have hvok : VOk v := hm.read_ok hlx (by exact hv)
      exact putBack_agrees held rest (fr := (f, w.put c v held)) (s := (t, w.put c v held))
        ⟨hm, rfl, hx.put c hvok held⟩ fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')

theorem MCorr.after {held : Bool} {cells : List (Name × Ty × Nat)} {mk : List Bool} {s₀ : State}
    {fr : Copy.State} {s : State × World} (hp : Post L X mk s₀ fr s)
    (hL : ∀ c ∈ cells, L.mem c.1 = true) (hlive : ∀ c ∈ cells, LiveAt c.1 mk (keys s₀))
    {o : Copy.State → Outcome Copy.State α} {o' : State × World → Outcome (State × World) α}
    (ho : ∀ fr' s', Post L X mk s₀ fr' s' → MCorr G L X mk s₀ (o fr') (o' s')) :
    MCorr G L X mk s₀ (Outcome.after (Copy.memory.putBack held cells) fr o)
      (Outcome.after (Moving.memory.putBack held cells) s o') := by
  obtain ⟨m, hag, hk, henv, hev⟩ := hp
  have hn : names fr.1 = keys s₀ := hag.1.keys_eq.trans (by simp only [keys, henv])
  unfold Outcome.after
  rcases putBack_agrees held cells hag fun c hc =>
      hn ▸ (hlive c hc).of_kills (.inl (hL c hc)) hk with
    ⟨e, h₁, h₂⟩ | ⟨w, h₁, h₂, hw⟩
  · rw [h₁, h₂]
    cases e
    · exact ⟨rfl, m, hag, hk, henv, hev⟩
    · trivial
  · rw [h₁, h₂]
    exact ho _ _ ⟨m, ⟨hag.1, rfl, hw⟩, hk, henv, hev⟩

/-- A `when`'s block in both models, its names, live to its end, put back however it ends. -/
theorem MCorr.release (cells : List (Name × Ty × Nat)) {mk : List Bool} {s₀ : State}
    (hL : ∀ c ∈ cells, L.mem c.1 = true) (hlive : ∀ c ∈ cells, LiveAt c.1 mk (keys s₀)) :
    ∀ {o : Outcome Copy.State α} {o' : Outcome (State × World) α}, MCorr G L X mk s₀ o o' →
      MCorr G L X mk s₀ (o.release Copy.memory cells) (o'.release Moving.memory cells)
  | .done _ _, .done _ _, ⟨rfl, hG, hp⟩ => MCorr.after hp hL hlive fun _ _ hp' => ⟨rfl, hG, hp'⟩
  | .raised _ _, .raised _ _, ⟨rfl, he, hp⟩ => MCorr.after hp hL hlive fun _ _ hp' => ⟨rfl, he, hp'⟩
  | .jumped _ _, .jumped _ _, ⟨rfl, hj, hp⟩ => MCorr.after hp hL hlive fun _ _ hp' => ⟨rfl, hj, hp'⟩
  | .panicked _ _, .panicked _ _, ⟨rfl, hp⟩ => MCorr.after hp hL hlive fun _ _ hp' => ⟨rfl, hp'⟩
  | .performed _ _ _ _, .performed _ _ _ _, ⟨⟨rfl, rfl, hv, hp⟩, hk⟩ =>
    MCorr.after hp hL hlive fun _ _ hp' =>
      ⟨⟨rfl, rfl, hv, hp'⟩, fun w x w' x' hw => MCorr.release cells hL hlive (hk w x w' x' hw)⟩
  | .outOfFuel, .outOfFuel, _ | .stuck, .stuck, _ => trivial

theorem Post.letGo {mk : List Bool} {s₀ : State} {fr : Copy.State} {s : State × World}
    (hp : Post L X mk s₀ fr s) (before : World) :
    Post L X mk s₀ (fr.1, before.letGo fr.2) (s.1, before.letGo s.2) := by
  obtain ⟨m, ⟨hag, hw, hx⟩, hk, henv, hev⟩ := hp
  exact ⟨m, ⟨hag, by rw [hw], hx.letGo before⟩, hk, henv, hev⟩

/-- A `with` in both models, letting go of the same cells. -/
theorem MCorr.letGo (before : World) {mk : List Bool} {s₀ : State} :
    ∀ {o : Outcome Copy.State α} {o' : Outcome (State × World) α}, MCorr G L X mk s₀ o o' →
      MCorr G L X mk s₀ (o.letGo Copy.memory before) (o'.letGo Moving.memory before)
  | .done _ (_, _), .done _ (_, _), ⟨rfl, hG, hp⟩ => ⟨rfl, hG, hp.letGo before⟩
  | .raised _ (_, _), .raised _ (_, _), ⟨rfl, he, hp⟩ => ⟨rfl, he, hp.letGo before⟩
  | .jumped _ (_, _), .jumped _ (_, _), ⟨rfl, hj, hp⟩ => ⟨rfl, hj, hp.letGo before⟩
  | .panicked _ (_, _), .panicked _ (_, _), ⟨rfl, hp⟩ => ⟨rfl, hp.letGo before⟩
  | .performed _ _ _ _, .performed _ _ _ _, ⟨h, hk⟩ =>
    ⟨h, fun w x w' x' hw => MCorr.letGo before (hk w x w' x' hw)⟩
  | .outOfFuel, .outOfFuel, _ | .stuck, .stuck, _ => trivial

namespace MSim

variable {Lb : Live}

theorem letGo {m : Eval Copy.State α} {m' : Eval (State × World) α} (hm : MSim G Lb L X m m') :
    MSim G Lb L X (Eval.letGo Copy.memory m) (Eval.letGo Moving.memory m') := by
  intro fr s mk hag hinv
  show MCorr G L X mk s.1 ((m fr).letGo Copy.memory fr.2) ((m' s).letGo Moving.memory s.2)
  rw [hag.2.1]
  exact MCorr.letGo s.2 (hm fr s mk hag hinv)

/-- A `when` in both models: its block's names live at its start and to its end
(shared.when). -/
theorem held {Lbody Xb : Live} {m : Eval Copy.State Value} {m' : Eval (State × World) Value}
    (names : List Name) (vs : List Value) (hm : MSim VOk Lbody (L.union (Live.ofList names)) Xb m m')
    (hX : (Xb.eraseAll names).Sub X) (hLb : Lbody.Sub (Lb.union (Live.ofList names))) (hLL : L.Sub Lb)
    (hnames : (Live.ofList names).Sub Lbody) :
    MSim VOk Lb L X (Eval.held Copy.memory m names vs) (Eval.held Moving.memory m' names vs) := by
  unfold Eval.held
  refine bind (G := fun _ => True) (L₁ := Lb) (ofExcept _ fun _ _ => trivial) (fun cells _ => ?_)
    (Live.Sub.refl _) hLL
  refine bind (L₁ := Lb) (bind (L₁ := Lb) (world _ fun x v x' hx h => ?_) (fun _ hv => asList hv)
    (Live.Sub.refl _) (Live.Sub.refl _)) (fun us hus => ?_) (Live.Sub.refl _) hLL
  · cases ht : World.take cells x with
    | error e => rw [ht] at h; cases h
    | ok p =>
      rw [ht] at h
      cases h
      obtain ⟨hp, hx'⟩ := hx.take ht
      exact ⟨⟨.list fun v h => (hp v h).1, .list fun v h => (hp v h).2⟩, hx'⟩
  · split
    · rename_i hlen
      have hmem : ∀ c ∈ names.zip cells, c.1 ∈ names := fun c hc => (List.of_mem_zip hc).1
      have hrel : MSim VOk Lbody (L.union (Live.ofList names)) Xb
          (Eval.release Copy.memory (names.zip cells) m) (Eval.release Moving.memory (names.zip cells) m') :=
        fun fr s mk hag hinv => MCorr.release _
          (fun c hc => by simp [hmem c hc])
          (fun c hc => hinv.live c.1 (hnames _ (by simp [hmem c hc]))) (hm fr s mk hag hinv)
      have hfst : (names.zip us).map Prod.fst = names := List.map_fst_zip (by omega)
      refine withVars hrel _ Lb L X (fun xv hxv => hus _ (List.of_mem_zip hxv).2) (by rw [hfst]; exact hLb)
        (by rw [hfst]; exact (Live.eraseAll_sub L names).trans (Live.sub_union_left _ _))
        (by rw [hfst]; exact hX)
    · exact fail _

end MSim

end Moving

end Stilt
