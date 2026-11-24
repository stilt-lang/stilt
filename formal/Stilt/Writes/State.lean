import Stilt.Writes.Relation

/-!
# Reading and writing states that agree

The operations of a view on values that agree, and reading, writing and
viewing a variable in states that agree. A variable that no writable binding
locks holds the same value in both models (projections.what-view-writes, E0429). A write to
it, or through a writable binding, reaches no location that a read-only window
reads, since its root is free (views.change-while-viewed, E0423), and none that another
writable binding writes.
-/

namespace Stilt.Writes

open Stilt.Views (Store bounded slice cell source Pointwise ExceptAgree Agree)

/-! ## Values -/

namespace Agrees

theorem asVal {Q : WState → WState → Value → Value → Prop} {sw sc : WState} {rw rc : WVal}
    (h : Agrees sw.store rw rc) (hQ : ∀ v, Q sw sc v v) :
    Agree Q (Run.asVal rw sw) (Run.asVal rc sc) := by
  cases rw <;> cases rc <;> simp only [Agrees] at h <;> first | exact Agree.stuck | skip
  subst h
  exact hQ _

theorem asInt {Q : WState → WState → Int → Int → Prop} {sw sc : WState} {rw rc : WVal}
    (h : Agrees sw.store rw rc) (hQ : ∀ k, Q sw sc k k) :
    Agree Q (Run.asInt rw sw) (Run.asInt rc sc) := by
  cases rw <;> cases rc <;> simp only [Agrees] at h <;> first | exact Agree.stuck | skip
  subst h
  rename_i v
  cases v <;> first | exact hQ _ | exact Agree.stuck

theorem window {store : Store} {ℓ : Nat} {π : Path} {a b : Int} {part : List Value}
    (h : (WVal.window ℓ π a b).part store = .ok part) :
    ∃ vs, source store ℓ π = .ok (.list vs) ∧ bounded vs.length a b = true ∧
      part = slice vs a b := by
  simp only [WVal.part] at h
  split at h
  · rename_i vs _
    split at h
    · cases h
      exact ⟨vs, by assumption, by assumption, rfl⟩
    · cases h
  · cases h

/-- Values that agree read the same part. -/
theorem part {store : Store} {rw rc : WVal} (h : Agrees store rw rc) :
    rw.part store = rc.part store := by
  cases rw <;> cases rc <;> simp only [Agrees] at h <;> first | exact h.elim | skip
  · rfl
  · exact h
  · exact h.2.2.2.2

theorem window_lt {store : Store} {ℓ : Nat} {π : Path} {a b : Int} {rc : WVal}
    (h : Agrees store (.window ℓ π a b) rc) : ℓ < store.length := by
  cases rc <;> simp only [Agrees] at h
  · exact part_lt h
  · exact part_lt h.2.2.2.2

theorem len {store : Store} {rw rc : WVal} (h : Agrees store rw rc) :
    ExceptAgree (· = ·) rw.len rc.len := by
  cases rw <;> cases rc <;> simp only [Agrees] at h <;> first | exact h.elim | skip
  · exact rfl
  all_goals
    first
    | obtain ⟨vs, -, hb, rfl⟩ := window h
    | obtain ⟨vs, -, hb, rfl⟩ := window h.2.2.2.2
    show (_ : Int) - _ = ((slice vs _ _).length : Int)
    rw [Views.slice_length hb]
    simp only [bounded, decide_eq_true_eq] at hb
    omega

theorem elem {store : Store} {rw rc : WVal} (h : Agrees store rw rc) (k : Int) :
    rw.elem store k = rc.elem store k := by
  simp only [WVal.elem, h.part]

/-- Indexing values or views that agree gives the same element. A copy reads
no store. -/
theorem index {store : Store} {rw rc : WVal} (h : Agrees store rw rc) (st : Store) (k : Int) :
    ∃ x, rw.index store k = lift x ∧ rc.index st k = lift x := by
  have he := elem h k
  cases rw <;> cases rc <;> simp only [Agrees] at h <;> first | exact h.elim | skip
  · subst h
    exact ⟨_, rfl, rfl⟩
  all_goals exact ⟨_, rfl, (congrArg lift he).symm⟩

theorem readOnly {store : Store} {rw rc : WVal} (h : Agrees store rw rc) :
    Agrees store rw rc.readOnly := by
  cases rw <;> cases rc <;> simp only [Agrees] at h <;> first | exact h.elim | skip
  · exact h
  · exact h
  · exact h.2.2.2.2

/-- The parts of views that agree, which a window gives by moving its offsets
in the same location (views.making-view and views.functions-of-views). -/
theorem sub {store : Store} {rw rc : WVal} (h : Agrees store rw rc) (s t : Int) :
    ExceptAgree (fun a b => Agrees store a b ∧ ∀ ℓ π c d, a = .window ℓ π c d →
      ∃ c' d', rw = .window ℓ π c' d') (rw.sub s t) (rc.sub s t) := by
  cases rw with
  | val v => cases rc <;> simp only [Agrees] at h; exact rfl
  | copied _ | pending _ _ _ _ _ => cases rc <;> simp only [Agrees] at h
  | window ℓ π a b =>
    obtain ⟨part, hpart, hrc⟩ : ∃ part, (WVal.window ℓ π a b).part store = .ok part ∧
        rc.sub s t = (WVal.copied part).sub s t := by
      cases rc <;> simp only [Agrees] at h
      · exact ⟨_, h, rfl⟩
      · exact ⟨_, h.2.2.2.2, rfl⟩
    rw [hrc]
    obtain ⟨vs, hsrc, hb, rfl⟩ := window hpart
    simp only [WVal.sub, Views.slice_length hb]
    split
    · rename_i hst
      refine ⟨?_, fun _ _ _ _ he => by cases he; exact ⟨a, b, rfl⟩⟩
      have hb' : bounded vs.length (a + s) (a + t) = true := by
        simp only [bounded, decide_eq_true_eq] at hb hst ⊢
        omega
      simp only [Agrees, WVal.part, hsrc, hb', ite_true, Views.slice_slice hb hst]
    · exact rfl

end Agrees

/-! ## Environments -/

theorem Pointwise.imp_left {α β : Type} {P Q : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, (∀ a b, a ∈ as → P a b → Q a b) →
      Pointwise P as bs → Pointwise Q as bs
  | _, _, _, .nil => .nil
  | _, _, h, .cons hab hrest =>
    .cons (h _ _ List.mem_cons_self hab)
      (Pointwise.imp_left (fun a b ha => h a b (List.mem_cons_of_mem _ ha)) hrest)

theorem Pointwise.imp_right {α β : Type} {P Q : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, (∀ a b, b ∈ bs → P a b → Q a b) →
      Pointwise P as bs → Pointwise Q as bs
  | _, _, _, .nil => .nil
  | _, _, h, .cons hab hrest =>
    .cons (h _ _ List.mem_cons_self hab)
      (Pointwise.imp_right (fun a b hb => h a b (List.mem_cons_of_mem _ hb)) hrest)

/-- Environments that agree find agreeing bindings, or none. -/
theorem EnvAgrees.lookup {sw sc : Store} :
    ∀ {Ew Ec : List (Name × WBinding)}, EnvAgrees sw sc Ew Ec → ∀ x,
      (Ew.lookup x = none ∧ Ec.lookup x = none) ∨
        ∃ b c, Ew.lookup x = some b ∧ Ec.lookup x = some c ∧ BAgrees sw sc b c
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | (y, b) :: _, (y', c) :: _, .cons ⟨hy, hb⟩ hrest, x => by
    simp only at hy hb
    subst hy
    by_cases hxy : x = y
    · subst hxy
      exact .inr ⟨b, c, by simp, by simp, hb⟩
    · rw [lookup_cons_ne hxy, lookup_cons_ne hxy]
      exact EnvAgrees.lookup hrest x

/-- A binding of the window state agrees with one of the copy state. -/
theorem EnvAgrees.mem {sw sc : Store} :
    ∀ {Ew Ec : List (Name × WBinding)}, EnvAgrees sw sc Ew Ec → ∀ {x b}, (x, b) ∈ Ew →
      ∃ c, BAgrees sw sc b c
  | _, _, .nil, _, _, h => by cases h
  | _ :: _, _ :: _, .cons ⟨_, hb⟩ hrest, _, _, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, hb⟩
    · exact EnvAgrees.mem hrest h

theorem BAgrees.view_inv {sw sc : Store} {r : WVal} {c : WBinding}
    (h : BAgrees sw sc (.view r) c) : ∃ r', c = .view r' ∧ Agrees sw r r' := by
  cases c <;> simp only [BAgrees] at h
  exact ⟨_, rfl, h⟩

theorem BAgrees.writes_inv {sw sc : Store} {r : WVal} {c : WBinding}
    (h : BAgrees sw sc (.writes r) c) : ∃ ℓ π a b part, r = .window ℓ π a b ∧
      c = .writes (.pending part ℓ π a b) ∧ Restored sw sc ℓ π a b part := by
  cases c with
  | writes r' =>
    cases r <;> cases r' <;> simp only [BAgrees] at h
    obtain ⟨rfl, rfl, rfl, rfl, hr⟩ := h
    exact ⟨_, _, _, _, _, rfl, rfl, hr⟩
  | _ => cases r <;> simp only [BAgrees] at h

/-- Every location a binding of the window state holds or views is
allocated. -/
theorem StateAgrees.lt {sw sc : WState} (h : StateAgrees sw sc) {x : Name} {b : WBinding}
    {ℓ : Nat} (hx : (x, b) ∈ sw.env) (hb : Changes b ℓ ∨ Refers b ℓ) : ℓ < sw.store.length := by
  obtain ⟨c, hbc⟩ := h.env.mem hx
  cases b with
  | loc ℓ' =>
    have : ℓ' = ℓ := by simpa [Changes, Refers] using hb
    exact this ▸ h.locs x ℓ' hx
  | view r =>
    obtain ⟨r', -, hag⟩ := hbc.view_inv
    cases r <;> simp only [Changes, Refers, false_or, or_self] at hb
    subst hb
    exact hag.window_lt
  | writes r =>
    obtain ⟨_, _, _, _, _, rfl, -, _, _, -, hc', -⟩ := hbc.writes_inv
    simp only [Changes, Refers, or_self] at hb
    exact hb ▸ Views.cell_lt hc'

/-- A variable that E0429 lets the body reach names a location that no
writable binding writes. -/
theorem InScope.untargeted {Γ : Sources} {R W : List Name} {env : List (Name × WBinding)}
    (hs : InScope Γ R W env) {x : Name} {ℓ : Nat} (hx : env.lookup x = some (.loc ℓ))
    (hW : x ∉ W) : ∀ y b, (y, b) ∈ env → ¬Targets b ℓ :=
  fun y b hy ht => hW (hs.locked y b ℓ hy ht x hx)

/-- The sources of a variable's binding cover its window. -/
theorem sources_lookup {env : List (Name × WBinding)} :
    ∀ {Γ : Sources} {E : List (Name × WBinding)},
      Pointwise (fun (g : Name × List Name) (e : Name × WBinding) =>
        g.1 = e.1 ∧ ∀ ℓ, Refers e.2 ℓ → Cover g.2 env ℓ) Γ E →
      ∀ x b ℓ, E.lookup x = some b → Refers b ℓ → Cover ((Γ.lookup x).getD []) env ℓ
  | _, _, .nil, _, _, _, h, _ => by cases h
  | (y, S) :: _, (y', c) :: _, .cons ⟨hy, hc⟩ hrest, x, b, ℓ, h, hr => by
    simp only at hy hc
    subst hy
    by_cases hxy : x = y
    · subst hxy
      simp only [List.lookup_cons_self, Option.some.injEq] at h ⊢
      subst h
      exact hc ℓ hr
    · rw [lookup_cons_ne hxy] at h ⊢
      exact sources_lookup hrest x b ℓ h hr

/-! ## Reading -/

/-- Reading a variable that no writable binding locks: the same value, or
views that agree, whose window its binding's sources cover. -/
theorem StateAgrees.read {Γ : Sources} {R W : List Name} {sw sc : WState}
    (h : StateAgrees sw sc) (hs : InScope Γ R W sw.env) {x : Name} (hW : x ∉ W) :
    ExceptAgree (fun rw rc => Agrees sw.store rw rc ∧
        ∀ ℓ π a b, rw = .window ℓ π a b → Cover ((Γ.lookup x).getD []) sw.env ℓ)
      (sw.read x) (sc.read x) := by
  unfold WState.read
  rcases h.env.lookup x with ⟨h₁, h₂⟩ | ⟨b, c, h₁, h₂, hbc⟩
  · rw [h₁, h₂]
    exact rfl
  rw [h₁, h₂]
  cases b with
  | loc ℓ =>
    cases c <;> simp only [BAgrees] at hbc
    subst hbc
    dsimp only
    rw [cell_congr (h.off _ (hs.untargeted h₁ hW)).symm]
    cases cell sw.store ℓ
    · exact rfl
    · exact ⟨rfl, fun _ _ _ _ he => nomatch he⟩
  | view r =>
    obtain ⟨r', rfl, hag⟩ := hbc.view_inv
    refine ⟨hag, fun ℓ π a b he => ?_⟩
    subst he
    exact sources_lookup hs.sources x _ _ h₁ rfl
  | writes r =>
    obtain ⟨_, _, _, _, _, rfl, rfl, _, _, -, hc', hr⟩ := hbc.writes_inv
    refine ⟨restore_part hr hc', fun ℓ π a b he => ?_⟩
    cases he
    exact sources_lookup hs.sources x _ _ h₁ rfl

end Stilt.Writes
