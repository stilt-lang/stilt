import Stilt.Moves.Mask

/-!
# Which bindings an expression ends

* `Kills L X mk m ns`: `m` comes from `mk` by ending bindings whose names `X`
  holds and `L` doesn't, each the newest binding of its name, and revives none.
  An expression ends only variables it mentions, at their last uses, so never
  one that what follows it mentions; and it reads and writes only the newest
  binding of each name, so never one that a newer binding of its name hides.
* `Inv L m ns`: every variable of `L` has a live newest binding. A closure
  literal reads only the newest binding of each variable it captures, which it
  mentions (expressions.capture), so its capture reads live bindings only.
* `sel m X env`: the live bindings whose names `X` holds, each the newest
  binding of its name. An expression writes only below their references
  (values.let-and-var and values.assignment-order).

That only the newest binding of a name may end lets a body in the scope of a
binder `let x` end its `x` while an `x` that the binder hides is used after
the body: what follows the body mentions the hidden `x`, which no step of the
body ends or writes.
-/

namespace Stilt.Moving

/-- `m` comes from `mk` by ending bindings whose names `X` holds and `L`
doesn't, each the newest binding of its name: past a binding of `x`, `X` no
longer holds `x`. -/
def Kills (L X : Live) : List Bool → List Bool → List Name → Prop
  | b :: mk, c :: m, x :: ns =>
    (c = true → b = true) ∧ (b = true → c = false → L.mem x = false ∧ X.mem x = true) ∧
      Kills L (X.erase x) mk m ns
  | [], [], [] => True
  | _, _, _ => False

/-- Every variable of `L` has a live newest binding. -/
structure Inv (L : Live) (m : List Bool) (ns : List Name) : Prop where
  live : ∀ x, L.mem x = true → LiveAt x m ns

/-- The live bindings whose names `X` holds, each the newest binding of its
name. -/
def sel {β : Type} : List Bool → Live → List (Name × β) → List (Name × β)
  | b :: m, X, e :: env =>
    if b && X.mem e.1 then e :: sel m (X.erase e.1) env else sel m (X.erase e.1) env
  | _, _, _ => []

variable {L L' L₁ X X' : Live}

theorem _root_.Stilt.Live.Sub.erase {a b : Live} (h : a.Sub b) (y : Name) :
    (a.erase y).Sub (b.erase y) := fun z hz => by
  simp only [Live.mem_erase_eq, Bool.and_eq_true] at hz ⊢
  exact ⟨h z hz.1, hz.2⟩

theorem Kills.refl (L : Live) :
    ∀ (X : Live) (m : List Bool) (ns : List Name), m.length = ns.length → Kills L X m m ns
  | _, [], [], _ => trivial
  | X, _ :: m, x :: ns, h =>
    ⟨id, fun hb hc => by simp [hb] at hc, Kills.refl L (X.erase x) m ns (by simpa using h)⟩
  | _, [], _ :: _, h | _, _ :: _, [], h => by simp at h

theorem Kills.length : ∀ {X : Live} {mk m : List Bool} {ns : List Name}, Kills L X mk m ns →
    m.length = mk.length ∧ mk.length = ns.length
  | _, [], [], [], _ => ⟨rfl, rfl⟩
  | _, _ :: _, _ :: _, _ :: _, h => by
    have := Kills.length h.2.2
    simp [this.1, this.2]
  | _, [], [], _ :: _, h | _, [], _ :: _, _, h | _, _ :: _, [], _, h | _, _ :: _, _ :: _, [], h =>
    h.elim

theorem Kills.trans : ∀ {X : Live} {mk m₁ m₂ : List Bool} {ns : List Name}, Kills L₁ X mk m₁ ns →
    Kills L X m₁ m₂ ns → L.Sub L₁ → Kills L X mk m₂ ns
  | _, [], [], [], [], _, _, _ => trivial
  | _, b :: mk, c :: m₁, d :: m₂, x :: ns, ⟨r₁, h₁, k₁⟩, ⟨r₂, h₂, k₂⟩, hL => by
    refine ⟨fun hd => r₁ (r₂ hd), fun hb hd => ?_, Kills.trans k₁ k₂ hL⟩
    cases c
    · obtain ⟨hm, hX⟩ := h₁ hb rfl
      refine ⟨?_, hX⟩
      cases hx : L.mem x
      · rfl
      · exact absurd (hL x hx) (by simp [hm])
    · exact h₂ rfl hd
  | _, [], [], _ :: _, _, _, h, _ | _, [], _ :: _, _, _, h, _, _ | _, _ :: _, [], _, _, h, _, _
  | _, _ :: _, _ :: _, [], _, _, h, _ | _, _ :: _, _ :: _, _ :: _, [], h, _, _
  | _, [], [], [], _ :: _, h, _, _ => h.elim

/-- Weakens what the bindings that end avoid and what holds their names: a
binding whose name `X` holds that `L'` keeps is one that `L` keeps. -/
theorem Kills.weaken : ∀ {X X' : Live} {mk m : List Bool} {ns : List Name}, Kills L X mk m ns →
    (∀ z, X.mem z = true → L'.mem z = true → L.mem z = true) → X.Sub X' → Kills L' X' mk m ns
  | _, _, [], [], [], _, _, _ => trivial
  | _, _, _ :: _, _ :: _, x :: _, ⟨r, h, k⟩, hL, hX => by
    refine ⟨r, fun hb hc => ?_, Kills.weaken k (fun z hz => hL z (Live.mem_erase hz)) (hX.erase x)⟩
    obtain ⟨hm, hx⟩ := h hb hc
    refine ⟨?_, hX x hx⟩
    cases h' : L'.mem x
    · rfl
    · exact absurd (hL x hx h') (by simp [hm])
  | _, _, [], [], _ :: _, h, _, _ | _, _, [], _ :: _, _, h, _, _ | _, _, _ :: _, [], _, h, _, _
  | _, _, _ :: _, _ :: _, [], h, _, _ => h.elim

theorem Kills.mono {mk m : List Bool} {ns : List Name} (h : Kills L X mk m ns) (hL : L'.Sub L)
    (hX : X.Sub X') : Kills L' X' mk m ns :=
  h.weaken (fun z _ hz => hL z hz) hX

/-- A variable that `X` doesn't hold, or that `L` holds, keeps its live
binding. -/
theorem LiveAt.of_kills {x : Name} : ∀ {X : Live} {mk m : List Bool} {ns : List Name},
    LiveAt x mk ns → (L.mem x = true ∨ X.mem x = false) → Kills L X mk m ns → LiveAt x m ns
  | _, [], [], [], _, _, _ => trivial
  | X, b :: mk, c :: m, y :: ns, h, hx, ⟨_, hk, k⟩ => by
    by_cases hy : y = x
    · subst hy
      simp only [LiveAt, ↓reduceIte] at h ⊢
      cases c
      · obtain ⟨h₁, h₂⟩ := hk h rfl
        rcases hx with hx | hx <;> simp_all
      · rfl
    · simp only [LiveAt, hy, ↓reduceIte] at h ⊢
      refine LiveAt.of_kills h (hx.imp id fun hx => ?_) k
      simp [hx]
  | _, [], [], _ :: _, _, _, k | _, [], _ :: _, _, _, _, k | _, _ :: _, [], _, _, _, k
  | _, _ :: _, _ :: _, [], _, _, k => k.elim

/-- The bindings live after an expression were live before it. -/
theorem Kills.keep_sub {β : Type} : ∀ {X : Live} {mk m : List Bool} {l : List (Name × β)},
    Kills L X mk m (l.map Prod.fst) → ∀ e ∈ keep m l, e ∈ keep mk l
  | _, [], [], [], _ => by simp [keep]
  | _, b :: mk, c :: m, a :: l, ⟨r, _, k⟩ => by
    intro e he
    cases c
    · simp only [keep, Bool.false_eq_true, ↓reduceIte] at he
      have := Kills.keep_sub k e he
      cases b <;> simp [keep, this]
    · rw [r rfl]
      simp only [keep, ↓reduceIte, List.mem_cons] at he ⊢
      exact he.imp id (Kills.keep_sub k e)
  | _, [], [], _ :: _, k | _, [], _ :: _, _, k | _, _ :: _, [], _, k | _, _ :: _, _ :: _, [], k =>
    k.elim

/-- A binding that `sel` keeps is live, and `X` holds its name. -/
theorem sel_mem {β : Type} : ∀ {m : List Bool} {X : Live} {env : List (Name × β)} {e : Name × β},
    e ∈ sel m X env → e ∈ keep m env ∧ X.mem e.1 = true
  | [], _, _, _, h | _ :: _, _, [], _, h => by simp [sel] at h
  | b :: m, X, a :: env, e, h => by
    have ih : e ∈ sel m (X.erase a.1) env → e ∈ keep m env ∧ X.mem e.1 = true := fun h =>
      (sel_mem h).imp id Live.mem_erase
    simp only [sel] at h
    split at h
    · rename_i hb
      simp only [Bool.and_eq_true] at hb
      rw [hb.1]
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨by simp [keep], hb.2⟩
      · exact (ih h).imp (fun h => by simp [keep, h]) id
    · exact (ih h).imp (fun h => by cases b <;> simp [keep, h]) id

theorem sel_mono {β : Type} : ∀ {m : List Bool} {X X' : Live} {env : List (Name × β)},
    X.Sub X' → ∀ e ∈ sel m X env, e ∈ sel m X' env
  | [], _, _, _, _, _, h | _ :: _, _, _, [], _, _, h => by simp [sel] at h
  | b :: m, X, X', a :: env, hX, e, h => by
    have ih := sel_mono (m := m) (env := env) (hX.erase a.1) e
    simp only [sel] at h ⊢
    split at h
    · rename_i hb
      simp only [Bool.and_eq_true] at hb
      simp only [hb.1, hX _ hb.2, Bool.and_self, ↓reduceIte, List.mem_cons] at h ⊢
      exact h.imp id ih
    · split
      · exact List.mem_cons_of_mem _ (ih h)
      · exact ih h

/-- The newest binding of a live variable that `X` holds is one that `sel`
keeps. -/
theorem mem_sel_of_lookup {β : Type} {x : Name} {r : β} : ∀ {m : List Bool} {X : Live}
    {env : List (Name × β)}, m.length = env.length → LiveAt x m (env.map Prod.fst) →
    env.lookup x = some r → X.mem x = true → (x, r) ∈ sel m X env
  | [], _, [], _, _, h, _ => by simp at h
  | b :: m, X, (y, v) :: env, hl, hlive, h, hX => by
    simp only [List.map_cons, LiveAt] at hlive
    simp only [sel]
    by_cases hy : y = x
    · subst hy
      simp only [↓reduceIte] at hlive
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      subst h
      simp [hlive, hX]
    · simp only [hy, ↓reduceIte] at hlive
      rw [lookup_cons_ne (Ne.symm hy)] at h
      have ih := mem_sel_of_lookup (X := X.erase y) (by simpa using hl) hlive h
        (by simp [hX, Ne.symm hy])
      split
      · exact List.mem_cons_of_mem _ ih
      · exact ih
  | [], _, _ :: _, hl, _, _, _ | _ :: _, _, [], hl, _, _, _ => by simp at hl

theorem sel_sub {β : Type} : ∀ {X X' : Live} {mk m : List Bool} {env : List (Name × β)},
    Kills L X mk m (env.map Prod.fst) → X'.Sub X → ∀ e ∈ sel m X' env, e ∈ sel mk X env
  | _, _, [], [], [], _, _, _, h => by simp [sel] at h
  | X, X', b :: mk, c :: m, a :: env, ⟨r, _, k⟩, hX, e, h => by
    have ih := sel_sub (env := env) k (hX.erase a.1) e
    simp only [sel] at h ⊢
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      simp only [r hc.1, hX _ hc.2, Bool.and_self, ↓reduceIte, List.mem_cons] at h ⊢
      exact h.imp id ih
    · split
      · exact List.mem_cons_of_mem _ (ih h)
      · exact ih h
  | _, _, [], [], _ :: _, k, _, _, _ | _, _, [], _ :: _, _, k, _, _, _
  | _, _, _ :: _, [], _, k, _, _, _ | _, _, _ :: _, _ :: _, [], k, _, _, _ => k.elim

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
theorem Kills.kill {x : Name} (hx : L.mem x = false) :
    ∀ {X : Live}, X.mem x = true → ∀ (mk : List Bool) (ns : List Name), mk.length = ns.length →
      Kills L X mk (kill x mk ns) ns
  | _, _, [], [], _ => trivial
  | X, hX, b :: mk, y :: ns, hl => by
    by_cases hy : y = x
    · subst hy
      simp only [Moving.kill, ↓reduceIte]
      exact ⟨by simp, fun _ _ => ⟨hx, hX⟩, Kills.refl L _ mk ns (by simpa using hl)⟩
    · simp only [Moving.kill, hy, ↓reduceIte]
      exact ⟨id, fun hb hc => by simp [hb] at hc,
        Kills.kill hx (by simp [hX, Ne.symm hy]) mk ns (by simpa using hl)⟩
  | _, _, [], _ :: _, hl | _, _, _ :: _, [], hl => by simp at hl

/-- What a body that ran in the scope of a binding of `x` ends, past that
binding: a binding that `L` keeps, but `x`, the body's `L'` keeps, and one of
another name than `x` that `X'` holds `X` holds. -/
theorem Kills.pop {b c : Bool} {mk m : List Bool} {x : Name} {ns : List Name}
    (hk : Kills L' X' (b :: mk) (c :: m) (x :: ns))
    (hL : ∀ z, L.mem z = true → z ≠ x → L'.mem z = true) (hX : (X'.erase x).Sub X) :
    Kills L X mk m ns :=
  hk.2.2.weaken (fun z hz h => hL z h fun e => by subst e; simp at hz) hX

end Stilt.Moving
