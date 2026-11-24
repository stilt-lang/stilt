import Stilt.Views.Steps

/-!
# Reading and writing states that agree

Both models read and write a variable alike, since their stores are equal and
their environments give each variable the same location. A write keeps every
window guarded by the reads that allow it reading what it read: that is where
the law of exclusivity, with the reads of views, does its work (modes.law and modes.change-while-iterating; views.change-while-viewed).
-/

namespace Stilt.Views

theorem Pointwise.imp_mem {α β : Type} {P Q : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, (∀ a b, b ∈ bs → P a b → Q a b) →
      Pointwise P as bs → Pointwise Q as bs
  | _, _, _, .nil => .nil
  | _, _, h, .cons hab hrest =>
    .cons (h _ _ List.mem_cons_self hab)
      (Pointwise.imp_mem (fun a b hb => h a b (List.mem_cons_of_mem _ hb)) hrest)

/-! ## Environments -/

/-- Environments that agree find agreeing bindings, or none. -/
theorem EnvAgrees.lookup {store : Store} :
    ∀ {Ew Ec : List (Name × Binding)}, EnvAgrees store Ew Ec → ∀ x,
      (Ew.lookup x = none ∧ Ec.lookup x = none) ∨
        ∃ b c, Ew.lookup x = some b ∧ Ec.lookup x = some c ∧ BAgrees store b c
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | (y, b) :: _, (y', c) :: _, .cons ⟨hy, hb⟩ hrest, x => by
    simp only at hy hb
    subst hy
    by_cases hxy : x = y
    · subst hxy
      exact .inr ⟨b, c, by simp, by simp, hb⟩
    · rw [lookup_cons_ne hxy, lookup_cons_ne hxy]
      exact EnvAgrees.lookup hrest x

/-- A window in an environment that agrees reads an allocated location. -/
theorem EnvAgrees.window_lt {store : Store} :
    ∀ {Ew Ec : List (Name × Binding)}, EnvAgrees store Ew Ec →
      ∀ {x ℓ π a b}, (x, Binding.view (.window ℓ π a b)) ∈ Ew → ℓ < store.length
  | _, _, .nil, _, _, _, _, _, h => by cases h
  | _ :: _, c :: _, .cons ⟨_, hb⟩ hrest, _, _, _, _, _, h => by
    rcases List.mem_cons.1 h with rfl | h
    · obtain ⟨y, c⟩ := c
      cases c with
      | loc _ => exact False.elim hb
      | view rc =>
        cases rc <;> try exact False.elim hb
        exact part_lt hb
    · exact EnvAgrees.window_lt hrest h

/-- A value or view that agrees in one store agrees in another where its
window's source is the same. -/
theorem Agrees.congr {store store' : Store} {rw rc : RVal} (h : Agrees store rw rc)
    (hs : ∀ ℓ π a b, rw = .window ℓ π a b → source store' ℓ π = source store ℓ π) :
    Agrees store' rw rc := by
  cases rw <;> cases rc <;> try exact False.elim h
  · exact h
  · rename_i ℓ π a b _
    show (RVal.window ℓ π a b).part store' = _
    rw [part_congr a b (hs ℓ π a b rfl)]
    exact h

theorem EnvAgrees.congr {store store' : Store} :
    ∀ {Ew Ec : List (Name × Binding)}, EnvAgrees store Ew Ec →
      (∀ x ℓ π a b, (x, Binding.view (.window ℓ π a b)) ∈ Ew →
        source store' ℓ π = source store ℓ π) → EnvAgrees store' Ew Ec
  | _, _, .nil, _ => .nil
  | (y, b) :: _, (_, c) :: _, .cons ⟨hy, hb⟩ hrest, hs => by
    refine .cons ⟨hy, ?_⟩ (EnvAgrees.congr hrest fun x ℓ π a b hx =>
      hs x ℓ π a b (List.mem_cons_of_mem _ hx))
    cases b <;> cases c <;> try exact False.elim hb
    · exact hb
    · exact Agrees.congr hb fun ℓ π a b' he => by
        subst he
        exact hs y ℓ π a b' List.mem_cons_self

/-! ## Reading -/

theorem StateAgrees.loc {sw sc : VState} (h : StateAgrees sw sc) (x : Name) :
    sw.loc? x = sc.loc? x := by
  unfold VState.loc?
  rcases h.env.lookup x with ⟨h₁, h₂⟩ | ⟨b, c, h₁, h₂, hbc⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂]
    cases b <;> cases c <;> try exact False.elim hbc
    · rw [show _ = _ from hbc]
    · rfl

theorem StateAgrees.read {sw sc : VState} (h : StateAgrees sw sc) (x : Name) :
    ExceptAgree (Agrees sw.store) (sw.read x) (sc.read x) := by
  unfold VState.read
  rcases h.env.lookup x with ⟨h₁, h₂⟩ | ⟨b, c, h₁, h₂, hbc⟩
  · rw [h₁, h₂]
    exact rfl
  · rw [h₁, h₂]
    cases b <;> cases c <;> try exact False.elim hbc
    · rw [show _ = _ from hbc, ← h.store]
      exact ExceptAgree.lift _ fun _ => rfl
    · exact hbc

theorem loc?_lookup {s : VState} {x : Name} {ℓ : Nat} (h : s.loc? x = .ok ℓ) :
    s.env.lookup x = some (.loc ℓ) := by
  unfold VState.loc? at h
  split at h
  · cases h
    assumption
  · cases h

/-! ## Writing -/

/-- A write to a place that no read overlaps leaves every guarded part as it
was (modes.change-while-iterating; views.change-while-viewed). -/
theorem write_source {R : List Shape} {env : List (Name × Binding)} {store : Store}
    {x : Name} {ℓ : Nat} {π : Path} {w v v' : Value} (hl : env.lookup x = some (.loc ℓ))
    (hc : cell store ℓ = .ok v) (hv : v.set π w = .ok v')
    (hu : unread R ⟨x, fieldsOf π⟩ = true) {ℓ' : Nat} {π' : Path} (hg : Guarded R env ℓ' π') :
    source (store.set ℓ (some v')) ℓ' π' = source store ℓ' π' := by
  by_cases hℓ : ℓ = ℓ'
  · subst hℓ
    have hlt := cell_lt hc
    have hr := (unread_iff R _).1 hu _ (hg x hl)
    have hset : cell (store.set ℓ (some v')) ℓ = .ok v' := by
      simp [cell, List.getElem?_set_self hlt]
    simp only [source, hc, hset]
    exact get_of_set_apart hr hv
  · exact source_set_ne _ _ hℓ

theorem StateAgrees.write {Γ : Sources} {R : List Shape} {sw sc : VState} {x : Name}
    {π : Path} {w : Value} (h : StateAgrees sw sc) (hs : InScope Γ R sw.env)
    (hu : unread R ⟨x, fieldsOf π⟩ = true) :
    ExceptAgree (fun sw' sc' => StateAgrees sw' sc' ∧ Steps R sw sw')
      (sw.write x π w) (sc.write x π w) := by
  unfold VState.write
  rw [← h.loc x, ← h.store]
  cases hl : sw.loc? x with
  | error f => exact rfl
  | ok ℓ =>
    dsimp only
    cases hc : cell sw.store ℓ with
    | error f => exact rfl
    | ok v =>
      dsimp only
      cases hv : v.set π w with
      | error f => exact rfl
      | ok v' =>
        have hsrc := fun {ℓ' π'} (hg : Guarded R sw.env ℓ' π') =>
          write_source (loc?_lookup hl) hc hv hu hg
        refine ⟨⟨rfl, h.env.congr fun y ℓ' π' a b hy => hsrc (hs.guarded y ℓ' π' a b hy), ?_⟩,
          ⟨rfl, by simp, fun ℓ' π' hg _ => hsrc hg⟩⟩
        intro y ℓ' hy
        simpa using h.locs y ℓ' hy

/-! ## Temporaries -/

/-- Storing a temporary in both models keeps them agreeing, and changes no
part in scope. -/
theorem StateAgrees.temp {sw sc : VState} (h : StateAgrees sw sc) (v : Value) (R : List Shape) :
    StateAgrees { sw with store := sw.store ++ [some v] }
        { sc with store := sc.store ++ [some v] } ∧
      Steps R sw { sw with store := sw.store ++ [some v] } := by
  refine ⟨⟨by simp [h.store], h.env.congr fun _ ℓ π _ _ hx => ?_, fun y ℓ hy => ?_⟩,
    ⟨rfl, by simp, fun ℓ π _ hℓ => source_append _ π hℓ⟩⟩
  · exact source_append _ π (h.env.window_lt hx)
  · have := h.locs y ℓ hy
    simp only [List.length_append, List.length_singleton]
    omega

end Stilt.Views
