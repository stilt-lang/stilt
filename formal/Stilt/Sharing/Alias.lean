import Stilt.Sharing.Scope

/-!
# Bindings of places

A `let` or a `var` whose initializer is a place, at a copy-on-write type, refers to the place
(modes.copies): evaluating such a place reads it and changes nothing (`eval_alias`), so the
place holds the initializer's value when the binding is made, and the binding agrees with the
copy that copy-in, copy-out binds.
-/

namespace Stilt.Sharing

open InPlace (Ref)

theorem pathOf_append_field (s : State) (f : Name) :
    ∀ ps : List Projection, pathOf s (ps ++ [.field f]) = (· ++ [.field f]) <$> pathOf s ps
  | [] => rfl
  | .field g :: ps => by
    simp only [List.cons_append, pathOf, pathOf_append_field s f ps]
    cases pathOf s ps <;> rfl
  | .index i :: ps => by
    simp only [List.cons_append, pathOf, pathOf_append_field s f ps]
    cases pureIndex s i <;> cases pathOf s ps <;> rfl

theorem pathOf_append_index (s : State) (i : Expr) :
    ∀ ps : List Projection, pathOf s (ps ++ [.index i]) =
      (pathOf s ps).bind fun p => (fun k => p ++ [.index k]) <$> pureIndex s i
  | [] => by
    simp only [List.nil_append, pathOf]
    cases pureIndex s i <;> rfl
  | .field g :: ps => by
    simp only [List.cons_append, pathOf, pathOf_append_index s i ps]
    cases pathOf s ps <;> cases pureIndex s i <;> rfl
  | .index j :: ps => by
    simp only [List.cons_append, pathOf, pathOf_append_index s i ps]
    cases pureIndex s j <;> cases pathOf s ps <;> cases pureIndex s i <;> rfl

theorem read_append (s : State) (x : Name) (p q : Path) :
    read s x (p ++ q) = (read s x p).bind (·.get q) := by
  unfold read
  split
  · exact deref_append s _ p q
  · rfl

theorem ofExcept_done {σ α : Type} {x : Except Fault α} {s s₁ : σ} {a : α}
    (h : Eval.ofExcept x s = .done a s₁) : x = .ok a ∧ s₁ = s := by
  cases x with
  | ok b => cases h; exact ⟨rfl, rfl⟩
  | error f => cases f <;> cases h

/-- Reading a variable as the evaluator does. -/
theorem eval_var {D : Decls} {shared : Name → Bool} {n : Nat} {z : Name} {s s₁ : State × World}
    {u : Value} (h : Sharing.eval D shared (n + 1) (.var z) s = .done u s₁) :
    read s.1 z [] = .ok u ∧ s₁ = s :=
  ofExcept_done (x := (memory shared).read s z []) h

theorem eval_move {D : Decls} {shared : Name → Bool} {n : Nat} {z : Name} {s s₁ : State × World}
    {u : Value} (h : Sharing.eval D shared (n + 1) (.move z) s = .done u s₁) :
    read s.1 z [] = .ok u ∧ s₁ = s :=
  ofExcept_done (x := (memory shared).read s z []) h

/-- An index that is an integer or a variable evaluates to its integer and changes nothing. -/
theorem eval_pureIndex {D : Decls} {shared : Name → Bool} {n : Nat} {i : Expr}
    {s s₁ : State × World} {k : Int} (hk : pureIndex s₁.1 i = some k) {u : Value}
    (h : Sharing.eval D shared n i s = .done u s₁) : s₁ = s ∧ u = .int k := by
  cases n with
  | zero => cases h
  | succ n =>
    match i, hk, h with
    | .int j, hk, h =>
      simp only [pureIndex, Option.some.injEq] at hk
      subst hk
      cases h
      exact ⟨rfl, rfl⟩
    | .var z, hk, h =>
      obtain ⟨hr, rfl⟩ := eval_var h
      refine ⟨rfl, ?_⟩
      simp only [pureIndex, hr] at hk
      split at hk <;> simp_all

/-- A place whose indexes are integers or variables evaluates to what reading it gives, and
changes nothing. -/
theorem eval_place (D : Decls) (shared : Name → Bool) :
    ∀ (n : Nat) (e : Expr) (s : State × World) (v : Value) (s₁ : State × World),
      Sharing.eval D shared n e s = .done v s₁ → ∀ y ps path, e.place? = some ⟨y, ps⟩ →
        pathOf s₁.1 ps = some path → s₁ = s ∧ read s.1 y path = .ok v
  | 0, _, _, _, _, h, _, _, _, _, _ => by cases h
  | n + 1, e, s, v, s₁, h, y, ps, path, hp, hpath => by
    match e, hp, h with
    | .var z, hp, h =>
      simp only [Expr.place?, Option.some.injEq, Place.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      simp only [pathOf, Option.some.injEq] at hpath
      subst hpath
      obtain ⟨hr, rfl⟩ := eval_var h
      exact ⟨rfl, hr⟩
    | .move z, hp, h =>
      simp only [Expr.place?, Option.some.injEq, Place.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      simp only [pathOf, Option.some.injEq] at hpath
      subst hpath
      obtain ⟨hr, rfl⟩ := eval_move h
      exact ⟨rfl, hr⟩
    | .field e f, hp, h =>
      simp only [Expr.place?, Option.map_eq_some_iff] at hp
      obtain ⟨⟨y', ps'⟩, hp', hq⟩ := hp
      simp only [Place.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rw [pathOf_append_field] at hpath
      obtain ⟨p₀, hp₀, rfl⟩ := Option.map_eq_some_iff.1 hpath
      have h' : ((Sharing.eval D shared n e s).bind fun v' s' =>
          Eval.ofExcept (v'.get [.field f]) s') = .done v s₁ := h
      obtain ⟨v', s', he, hg⟩ := Outcome.bind_eq_done h'
      obtain ⟨hget, rfl⟩ := ofExcept_done hg
      obtain ⟨rfl, hr⟩ := eval_place D shared n e s v' _ he _ _ _ hp' hp₀
      exact ⟨rfl, by rw [read_append, hr]; exact hget⟩
    | .index e i, hp, h =>
      simp only [Expr.place?, Option.map_eq_some_iff] at hp
      obtain ⟨⟨y', ps'⟩, hp', hq⟩ := hp
      simp only [Place.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      rw [pathOf_append_index] at hpath
      obtain ⟨p₀, hp₀, hk⟩ := Option.bind_eq_some_iff.1 hpath
      obtain ⟨k, hik, rfl⟩ : ∃ k, pureIndex s₁.1 i = some k ∧ p₀ ++ [.index k] = path := by
        cases hq : pureIndex s₁.1 i with
        | none => simp [hq] at hk
        | some k => simp only [hq, Option.map_eq_map, Option.map_some, Option.some.injEq] at hk; exact ⟨k, rfl, hk⟩
      have h' : ((Sharing.eval D shared n e s).bind fun v' s' =>
          ((Sharing.eval D shared n i s').bind fun u s'' => Eval.asInt u s'').bind fun k s'' =>
            Eval.ofExcept (v'.get [.index k]) s'') = .done v s₁ := h
      obtain ⟨v', s', he, h₂⟩ := Outcome.bind_eq_done h'
      obtain ⟨k', s'', hi, hg⟩ := Outcome.bind_eq_done h₂
      obtain ⟨hget, rfl⟩ := ofExcept_done hg
      obtain ⟨u, s₃, hiu, hint⟩ := Outcome.bind_eq_done hi
      cases u <;> try (simp [Eval.asInt, Eval.fail, Outcome.fault] at hint; done)
      cases hint
      obtain ⟨rfl, hj⟩ := eval_pureIndex hik hiu
      cases hj
      obtain ⟨rfl, hr⟩ := eval_place D shared n e s v' _ he _ _ _ hp' hp₀
      exact ⟨rfl, by rw [read_append, hr]; exact hget⟩
    | .int _, hp, _ | .bool _, hp, _ | .unit, hp, _ => simp [Expr.place?] at hp

/-- An index that is an integer or a variable. -/
def _root_.Stilt.Expr.isPureIndex : Expr → Bool
  | .int _ | .var _ => true
  | _ => false

/-- A place whose indexes are integers or variables, the initializers `aliasRef?` may find a part
for. -/
def _root_.Stilt.Expr.pureIndexes : Expr → Bool
  | .var _ | .move _ => true
  | .field e _ => e.pureIndexes
  | .index e i => e.pureIndexes && i.isPureIndex
  | _ => false

theorem pureIndex_some {s : State} {i : Expr} {k : Int} (h : pureIndex s i = some k) :
    i.isPureIndex = true := by
  cases i <;> first | rfl | (unfold pureIndex at h; cases h)

theorem pureIndexes_of_pathOf {s : State} :
    ∀ {e : Expr} {y : Name} {ps : List Projection} {path : Path}, e.place? = some ⟨y, ps⟩ →
      pathOf s ps = some path → e.pureIndexes = true
  | .var _, _, _, _, _, _ | .move _, _, _, _, _, _ => rfl
  | .field e f, y, ps, path, hp, hpath => by
    simp only [Expr.place?, Option.map_eq_some_iff] at hp
    obtain ⟨⟨y', ps'⟩, hp', hq⟩ := hp
    simp only [Place.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    rw [pathOf_append_field] at hpath
    obtain ⟨p₀, hp₀, -⟩ := Option.map_eq_some_iff.1 hpath
    show e.pureIndexes = true
    exact pureIndexes_of_pathOf hp' hp₀
  | .index e i, y, ps, path, hp, hpath => by
    simp only [Expr.place?, Option.map_eq_some_iff] at hp
    obtain ⟨⟨y', ps'⟩, hp', hq⟩ := hp
    simp only [Place.mk.injEq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    rw [pathOf_append_index] at hpath
    obtain ⟨p₀, hp₀, hk⟩ := Option.bind_eq_some_iff.1 hpath
    cases hq : pureIndex s i with
    | none => simp [hq] at hk
    | some k =>
      simp only [Expr.pureIndexes, Bool.and_eq_true]
      exact ⟨pureIndexes_of_pathOf hp' hp₀, pureIndex_some hq⟩

/-- A part `aliasRef?` finds is one of an initializer whose indexes are integers or variables. -/
theorem pureIndexes_of_aliasRef {s : State} {e : Expr} {r : Ref} (h : aliasRef? s e = some r) :
    e.pureIndexes = true := by
  unfold aliasRef? at h
  cases hp : e.place? with
  | none => simp [hp] at h
  | some pl =>
    obtain ⟨y, ps⟩ := pl
    cases hpath : pathOf s ps with
    | none => simp [hp, hpath] at h
    | some path => exact pureIndexes_of_pathOf hp hpath

/-- An outcome that only a value, a fault, or the lack of fuel ends. -/
def _root_.Stilt.Outcome.Simple {σ α : Type} : Outcome σ α → Prop
  | .raised .. | .jumped .. | .performed .. => False
  | _ => True

theorem Outcome.Simple.bind {σ α β : Type} {o : Outcome σ α} {f : α → σ → Outcome σ β}
    (h : o.Simple) (hf : ∀ a s, (f a s).Simple) : (o.bind f).Simple := by
  cases o <;> first | exact h.elim | trivial | exact hf _ _

theorem ofExcept_simple {σ α : Type} (x : Except Fault α) (s : σ) : (Eval.ofExcept x s).Simple := by
  cases x with
  | ok _ => trivial
  | error f => cases f <;> trivial

theorem eval_index_simple {D : Decls} {shared : Name → Bool} {n : Nat} {i : Expr}
    (h : i.isPureIndex = true) (s : State × World) : (Sharing.eval D shared n i s).Simple := by
  cases n with
  | zero => trivial
  | succ n =>
    match i, h with
    | .int _, _ => trivial
    | .var z, _ => exact ofExcept_simple ((memory shared).read s z []) s

/-- A place whose indexes are integers or variables neither raises, nor jumps, nor performs. -/
theorem eval_simple (D : Decls) (shared : Name → Bool) :
    ∀ (n : Nat) (e : Expr) (s : State × World), e.pureIndexes = true →
      (Sharing.eval D shared n e s).Simple
  | 0, _, _, _ => trivial
  | n + 1, e, s, h => by
    match e, h with
    | .var z, _ | .move z, _ => exact ofExcept_simple ((memory shared).read s z []) s
    | .field e f, h =>
      exact Outcome.Simple.bind (eval_simple D shared n e s h) fun v s' => ofExcept_simple _ s'
    | .index e i, h =>
      simp only [Expr.pureIndexes, Bool.and_eq_true] at h
      exact Outcome.Simple.bind (eval_simple D shared n e s h.1) fun v s' =>
        Outcome.Simple.bind (Outcome.Simple.bind (eval_index_simple h.2 s') fun u s'' => by
          cases u <;> first | trivial | exact ofExcept_simple (.error .stuck) s'')
          fun k s'' => ofExcept_simple _ s''

/-- The place an initializer names, when `aliasRef?` finds one, holds the initializer's value
in the state its evaluation ends in, and is below a binding of that state. -/
theorem eval_alias (D : Decls) (shared : Name → Bool) :
    ∀ (n : Nat) (e : Expr) (s : State × World) (v : Value) (s₁ : State × World),
      Sharing.eval D shared n e s = .done v s₁ → ∀ r, aliasRef? s₁.1 e = some r →
        deref s₁.1 r [] = .ok v ∧ r.toPath.Under s₁.1.paths := by
  intro n e s v s₁ h r hr
  unfold aliasRef? at hr
  cases hp : e.place? with
  | none => simp [hp] at hr
  | some pl =>
    obtain ⟨y, ps⟩ := pl
    cases hl : s₁.1.env.lookup y with
    | none => simp [hp, hl] at hr
    | some entry =>
      cases hpath : pathOf s₁.1 ps with
      | none => simp [hp, hl, hpath] at hr
      | some path =>
        simp only [hp, hl, hpath, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at hr
        subst hr
        obtain ⟨rfl, hread⟩ := eval_place D shared n e s v s₁ h y ps path hp hpath
        refine ⟨?_, ⟨entry.ref.toPath, List.mem_flatMap.2 ⟨(y, entry), mem_of_lookup hl,
          by simp⟩, path, by simp [InPlace.Ref.toPath]⟩⟩
        have hd := deref_at s₁.1 entry.ref path []
        simp only [InPlace.Ref.at, List.append_nil] at hd
        rw [hd]
        simpa [read, hl] using hread

end Stilt.Sharing
