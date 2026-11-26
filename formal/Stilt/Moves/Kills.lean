import Stilt.Moves.Mask

/-!
# Which bindings an expression ends

* `Kills L X mk m ns`: `m` comes from `mk` by ending bindings whose names `X`
  holds and `L` doesn't, and revives none. An expression ends only variables
  it mentions, at their last uses, so never one that what follows it
  mentions.
* `Inv L m ns`: every variable of `L` has a live newest binding. A closure
  literal reads only the newest binding of each variable it captures, which it
  mentions (expressions.capture), so its capture reads live bindings only.
* `sel m X env`: the live bindings whose names `X` holds. An expression writes
  only below their references (values.let-and-var and values.assignment-order).
-/

namespace Stilt.Moving

/-- `m` comes from `mk` by ending bindings whose names `X` holds and `L`
doesn't. -/
def Kills (L X : Live) : List Bool → List Bool → List Name → Prop
  | b :: mk, c :: m, x :: ns =>
    (c = true → b = true) ∧ (b = true → c = false → L.mem x = false ∧ X.mem x = true) ∧
      Kills L X mk m ns
  | [], [], [] => True
  | _, _, _ => False

/-- Every variable of `L` has a live newest binding. -/
structure Inv (L : Live) (m : List Bool) (ns : List Name) : Prop where
  live : ∀ x, L.mem x = true → LiveAt x m ns

/-- The live bindings whose names `X` holds. -/
def sel {β : Type} (m : List Bool) (X : Live) (env : List (Name × β)) : List (Name × β) :=
  (keep m env).filter fun e => X.mem e.1

variable {L L' L₁ X X' : Live}

theorem Kills.refl (L X : Live) :
    ∀ (m : List Bool) (ns : List Name), m.length = ns.length → Kills L X m m ns
  | [], [], _ => trivial
  | _ :: m, _ :: ns, h =>
    ⟨id, fun hb hc => by simp [hb] at hc, Kills.refl L X m ns (by simpa using h)⟩
  | [], _ :: _, h | _ :: _, [], h => by simp at h

theorem Kills.length : ∀ {mk m : List Bool} {ns : List Name}, Kills L X mk m ns →
    m.length = mk.length ∧ mk.length = ns.length
  | [], [], [], _ => ⟨rfl, rfl⟩
  | _ :: _, _ :: _, _ :: _, h => by
    have := Kills.length h.2.2
    simp [this.1, this.2]
  | [], [], _ :: _, h | [], _ :: _, _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => h.elim

theorem Kills.trans : ∀ {mk m₁ m₂ : List Bool} {ns : List Name}, Kills L₁ X mk m₁ ns →
    Kills L X m₁ m₂ ns → L.Sub L₁ → Kills L X mk m₂ ns
  | [], [], [], [], _, _, _ => trivial
  | b :: mk, c :: m₁, d :: m₂, x :: ns, ⟨r₁, h₁, k₁⟩, ⟨r₂, h₂, k₂⟩, hL => by
    refine ⟨fun hd => r₁ (r₂ hd), fun hb hd => ?_, Kills.trans k₁ k₂ hL⟩
    cases c
    · obtain ⟨hm, hX⟩ := h₁ hb rfl
      refine ⟨?_, hX⟩
      cases hx : L.mem x
      · rfl
      · exact absurd (hL x hx) (by simp [hm])
    · exact h₂ rfl hd
  | [], [], _ :: _, _, _, h, _ | [], _ :: _, _, _, h, _, _ | _ :: _, [], _, _, h, _, _
  | _ :: _, _ :: _, [], _, _, h, _ | _ :: _, _ :: _, _ :: _, [], h, _, _
  | [], [], [], _ :: _, h, _, _ => h.elim

theorem Kills.mono : ∀ {mk m : List Bool} {ns : List Name}, Kills L X mk m ns → L'.Sub L →
    X.Sub X' → Kills L' X' mk m ns
  | [], [], [], _, _, _ => trivial
  | _ :: _, _ :: _, x :: _, ⟨r, h, k⟩, hL, hX => by
    refine ⟨r, fun hb hc => ?_, Kills.mono k hL hX⟩
    obtain ⟨hm, hx⟩ := h hb hc
    refine ⟨?_, hX x hx⟩
    cases h' : L'.mem x
    · rfl
    · exact absurd (hL x h') (by simp [hm])
  | [], [], _ :: _, h, _, _ | [], _ :: _, _, h, _, _ | _ :: _, [], _, h, _, _
  | _ :: _, _ :: _, [], h, _, _ => h.elim

/-- A variable that `X` doesn't hold, or that `L` holds, keeps its live
binding. -/
theorem LiveAt.of_kills {x : Name} : ∀ {mk m : List Bool} {ns : List Name}, LiveAt x mk ns →
    (L.mem x = true ∨ X.mem x = false) → Kills L X mk m ns → LiveAt x m ns
  | [], [], [], _, _, _ => trivial
  | b :: mk, c :: m, y :: ns, h, hx, ⟨_, hk, k⟩ => by
    by_cases hy : y = x
    · subst hy
      simp only [LiveAt, ↓reduceIte] at h ⊢
      cases c
      · obtain ⟨h₁, h₂⟩ := hk h rfl
        rcases hx with hx | hx <;> simp_all
      · rfl
    · simp only [LiveAt, hy, ↓reduceIte] at h ⊢
      exact LiveAt.of_kills h hx k
  | [], [], _ :: _, _, _, k | [], _ :: _, _, _, _, k | _ :: _, [], _, _, _, k
  | _ :: _, _ :: _, [], _, _, k => k.elim

/-- The bindings live after an expression were live before it. -/
theorem Kills.keep_sub {β : Type} : ∀ {mk m : List Bool} {l : List (Name × β)},
    Kills L X mk m (l.map Prod.fst) → ∀ e ∈ keep m l, e ∈ keep mk l
  | [], [], [], _ => by simp [keep]
  | b :: mk, c :: m, a :: l, ⟨r, _, k⟩ => by
    intro e he
    cases c
    · simp only [keep, Bool.false_eq_true, ↓reduceIte] at he
      have := Kills.keep_sub k e he
      cases b <;> simp [keep, this]
    · rw [r rfl]
      simp only [keep, ↓reduceIte, List.mem_cons] at he ⊢
      exact he.imp id (Kills.keep_sub k e)
  | [], [], _ :: _, k | [], _ :: _, _, k | _ :: _, [], _, k | _ :: _, _ :: _, [], k => k.elim

theorem mem_sel {β : Type} {m : List Bool} {env : List (Name × β)} {e : Name × β} :
    e ∈ sel m X env ↔ e ∈ keep m env ∧ X.mem e.1 = true := by
  simp [sel]

theorem sel_sub {β : Type} {mk m : List Bool} {env : List (Name × β)}
    (hk : Kills L X mk m (env.map Prod.fst)) (hX : X'.Sub X) :
    ∀ e ∈ sel m X' env, e ∈ sel mk X env := by
  intro e he
  rw [mem_sel] at he ⊢
  exact ⟨hk.keep_sub e he.1, hX _ he.2⟩

theorem Inv.of_kills {Lb : Live} {mk m : List Bool} {ns : List Name} (hi : Inv Lb mk ns)
    (hL : L.Sub Lb) (hk : Kills L X mk m ns) : Inv L m ns :=
  ⟨fun x hx => (hi.live x (hL x hx)).of_kills (.inl hx) hk⟩

theorem Inv.mono {m : List Bool} {ns : List Name} (hi : Inv L m ns) (h : L'.Sub L) : Inv L' m ns :=
  ⟨fun x hx => hi.live x (h x hx)⟩

theorem Inv.cons {Lb Lb' : Live} {mk : List Bool} {ns : List Name} {x : Name} (hinv : Inv Lb mk ns)
    (hLb : ∀ z, Lb'.mem z = true → z ≠ x → Lb.mem z = true) :
    Inv Lb' (true :: mk) (x :: ns) := by
  refine ⟨fun z hz => ?_⟩
  by_cases hzx : z = x
  · subst hzx
    exact LiveAt.cons_self z mk ns
  · exact (hinv.live z (hLb z hz hzx)).cons hzx

/-- Ending the newest binding of `x`, which `X` holds and `L` doesn't. -/
theorem Kills.kill {x : Name} (hx : L.mem x = false) (hX : X.mem x = true) :
    ∀ (mk : List Bool) (ns : List Name), mk.length = ns.length → Kills L X mk (kill x mk ns) ns
  | [], [], _ => trivial
  | b :: mk, y :: ns, hl => by
    by_cases hy : y = x
    · subst hy
      simp only [Moving.kill, ↓reduceIte]
      exact ⟨by simp, fun _ _ => ⟨hx, hX⟩, Kills.refl L X mk ns (by simpa using hl)⟩
    · simp only [Moving.kill, hy, ↓reduceIte]
      exact ⟨id, fun hb hc => by simp [hb] at hc, Kills.kill hx hX mk ns (by simpa using hl)⟩
  | [], _ :: _, hl | _ :: _, [], hl => by simp at hl

end Stilt.Moving
