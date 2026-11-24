import Stilt.Writes.Writing

/-!
# Scopes

A binding and its scope, in both models. A value takes a new location, a view
that reads is held by its variable, and a writable binding holds its view:
the window, or the copy with the place it writes back to (projections.writable-bindings).
The binding hides the reads and writes of its name, a view that reads holds
its sources as reads, and a writable binding holds what its view writes as
writes, for its scope (views.reads-that-last and projections.what-view-writes).

When the scope ends, a location is freed, and the copy model writes a
writable binding's copy back, which gives the window model's storage. The
value of the rest of the block reads none of what the end frees, which views.escaping
of the Reference checks (E0422).
-/

namespace Stilt.Writes

open Stilt.Views (Store bounded slice cell source Pointwise ExceptAgree Agree)

/-- What a new binding is, from the window state `s`, with the sources `S` of
its initializer and the names `F` frozen around it: a new location, a view
that `S` covers, or a writable binding's window, which `S` covers, into a
location that no binding views and that a variable nothing freezes holds. -/
def Fresh (F S : List Name) (w : Bool) (s : WState) : WBinding → Prop
  | .loc ℓ => w = false ∧ s.store.length ≤ ℓ
  | .view r => w = false ∧ ∀ ℓ π a b, r = .window ℓ π a b → Cover S s.env ℓ
  | .writes r => w = true ∧ ∃ ℓ π a b, r = .window ℓ π a b ∧ Cover S s.env ℓ ∧ Alone s.env ℓ ∧
      ∃ y, s.env.lookup y = some (.loc ℓ) ∧ y ∉ F

/-- The facts of `Post.pend`. -/
def Pending (F : List Name) (env : List (Name × WBinding)) (rw rc : WVal) : Prop :=
  ∃ part ℓ π a b, rw = .window ℓ π a b ∧ rc = .pending part ℓ π a b ∧ Alone env ℓ ∧
    ∃ y, env.lookup y = some (.loc ℓ) ∧ y ∉ F

theorem getElem?_append_eq {st st' : Store} (c : Store) (h : st.length = st'.length) {ℓ : Nat}
    (hl : st.length ≤ ℓ) : (st ++ c)[ℓ]? = (st' ++ c)[ℓ]? := by
  rw [List.getElem?_append_right hl, List.getElem?_append_right (h ▸ hl), h]

/-! ## Binding -/

/-- Binding agreeing values in both models gives states that agree, and a
fresh binding. -/
theorem StateAgrees.bind {F S : List Name} {w : Bool} {s sc : WState} {rw rc : WVal}
    (h : StateAgrees s sc) (hag : Agrees s.store rw rc)
    (hwin : ∀ ℓ π a b, rw = .window ℓ π a b → Cover S s.env ℓ)
    (hpend : w = true → Pending F s.env rw rc) (x : Name) :
    StateAgrees (s.bind w x rw) (sc.bind w x rc) ∧ ∃ b, (s.bind w x rw).env = (x, b) :: s.env ∧
      Fresh F S w s b ∧ s.store.length ≤ (s.bind w x rw).store.length ∧
      ∀ ℓ, ℓ < s.store.length → (s.bind w x rw).store[ℓ]? = s.store[ℓ]? := by
  have hview : ∀ b c, BAgrees s.store sc.store b c → (∀ ℓ, b ≠ .loc ℓ) →
      StateAgrees ⟨(x, b) :: s.env, s.store⟩ ⟨(x, c) :: sc.env, sc.store⟩ :=
    fun b c hbc hb => ⟨h.length, .cons ⟨rfl, hbc⟩ h.env,
      fun ℓ hu => h.off ℓ fun y b' hy => hu y b' (List.mem_cons_of_mem _ hy),
      fun y ℓ hy => by
        rcases List.mem_cons.1 hy with hy | hy
        · exact (hb ℓ (congrArg Prod.snd hy).symm).elim
        · exact h.locs y ℓ hy⟩
  cases w
  · cases rw with
    | val v =>
      cases rc <;> simp only [Agrees] at hag
      subst hag
      have henv : EnvAgrees (s.store ++ [some v]) (sc.store ++ [some v]) s.env sc.env :=
        Pointwise.imp_left (fun e c he hp => ⟨hp.1, hp.2.congr fun ℓ hr => by
          have hl := h.lt he (.inr hr)
          exact ⟨List.getElem?_append_left hl, List.getElem?_append_left (h.length ▸ hl)⟩⟩) h.env
      have hoff : ∀ ℓ, (∀ y b, (y, b) ∈ s.env → ¬Targets b ℓ) →
          (s.store ++ [some v])[ℓ]? = (sc.store ++ [some v])[ℓ]? := fun ℓ hu => by
        by_cases hl : ℓ < s.store.length
        · rw [List.getElem?_append_left hl, List.getElem?_append_left (h.length ▸ hl)]
          exact h.off ℓ hu
        · exact getElem?_append_eq _ h.length (by omega)
      refine ⟨⟨by simp [WState.bind, h.length], .cons ⟨rfl, by simp [BAgrees, h.length]⟩ henv,
        fun ℓ hu => hoff ℓ fun y b hy => hu y b (List.mem_cons_of_mem _ hy), fun y ℓ hy => ?_⟩,
        .loc s.store.length, rfl, ⟨rfl, Nat.le_refl _⟩, by simp [WState.bind],
        fun ℓ hℓ => List.getElem?_append_left hℓ⟩
      change (y, WBinding.loc ℓ) ∈ (x, .loc s.store.length) :: s.env at hy
      show ℓ < (s.store ++ [some v]).length
      rcases List.mem_cons.1 hy with hy | hy
      · cases hy
        simp
      · simpa using Nat.lt_succ_of_lt (h.locs y ℓ hy)
    | window ℓ π a b =>
      have hro := hag.readOnly
      have hfresh : Fresh F S false s (.view (.window ℓ π a b)) :=
        ⟨rfl, fun _ _ _ _ he => by cases he; exact hwin ℓ π a b rfl⟩
      cases rc with
      | val _ | window _ _ _ _ => simp only [Agrees] at hag
      | copied _ | pending _ _ _ _ _ =>
        exact ⟨hview _ _ hro fun _ h => (nomatch h), _, rfl, hfresh, Nat.le_refl _, fun _ _ => rfl⟩
    | copied _ | pending _ _ _ _ _ => cases rc <;> simp only [Agrees] at hag
  · obtain ⟨part, ℓ, π, a, b, rfl, rfl, hal, y, hy, hyF⟩ := hpend rfl
    obtain ⟨vs, hsrc, hb, hpart⟩ := Agrees.window hag.2.2.2.2
    have hun : ∀ z b', (z, b') ∈ s.env → ¬Targets b' ℓ := fun z b' hz ht => hal z b' hz (by
      cases b' with
      | writes r => cases r <;> simp_all [Targets, Refers]
      | _ => exact ht.elim)
    obtain ⟨c, hc, hcπ⟩ : ∃ c, cell s.store ℓ = .ok c ∧ c.get π = .ok (.list vs) := by
      unfold source at hsrc
      split at hsrc
      · exact ⟨_, by assumption, hsrc⟩
      · cases hsrc
    refine ⟨hview _ _ ⟨rfl, rfl, rfl, rfl, c, c, ?_, hc, hpart ▸ restore_slice hcπ hb⟩
      fun _ h => (nomatch h), .writes (.window ℓ π a b), rfl,
      ⟨rfl, ℓ, π, a, b, rfl, hwin ℓ π a b rfl, hal, y, hy, hyF⟩, Nat.le_refl _, fun _ _ => rfl⟩
    rw [cell_congr (h.off ℓ hun).symm]
    exact hc

/-! ## The analysis of a new binding -/

/-- The names frozen around a binding of `x` stay frozen in its scope, but
`x`'s, which the binding hides. -/
theorem mem_frozen {w : Bool} {S R W : List Name} {x z : Name} (hz : z ∈ R ++ W) (hzx : z ≠ x) :
    z ∈ hide (readsIn w S R) x ++ hide (writesIn w S W) x := by
  have hzx' : (z != x) = true := by simpa using hzx
  simp only [List.mem_append] at hz
  cases w <;> rcases hz with hz | hz <;>
    simp [hide, readsIn, writesIn, List.mem_filter, hz, hzx']

theorem Cover.cons {S : List Name} {env : List (Name × WBinding)} {ℓ : Nat} {x : Name}
    {b : WBinding} (h : Cover S env ℓ) (hb : ¬Changes b ℓ ∨ x ∈ S) : Cover S ((x, b) :: env) ℓ :=
  fun y b' hy hc => by
    rcases List.mem_cons.1 hy with hy | hy
    · cases hy
      exact hb.resolve_left fun h => h hc
    · exact h y b' hy hc

theorem Cover.tail {S : List Name} {env : List (Name × WBinding)} {ℓ : Nat} {x : Name}
    {b : WBinding} (h : Cover S ((x, b) :: env) ℓ) : Cover S env ℓ :=
  fun y b' hy => h y b' (List.mem_cons_of_mem _ hy)

theorem Targets.refers {b : WBinding} {ℓ : Nat} (h : Targets b ℓ) : Refers b ℓ := by
  cases b with
  | writes r => cases r <;> exact h
  | _ => exact h.elim

theorem Targets.changes {b : WBinding} {ℓ : Nat} (h : Targets b ℓ) : Changes b ℓ := by
  cases b with
  | writes r => cases r <;> exact h
  | _ => exact h.elim

/-- A new binding keeps what the analysis knows of the environment, with its
sources `S`: the reads of a binding that doesn't write, and the writes of a
writable one (views.reads-that-last; projections.what-view-writes and projections.writable-bindings). -/
theorem InScope.push {Γ : Sources} {R W S : List Name} {w : Bool} {x : Name} {s sc : WState}
    {b : WBinding} (hs : InScope Γ R W s.env) (hst : StateAgrees s sc)
    (hb : Fresh (R ++ W) S w s b) :
    InScope ((x, held w x S) :: Γ) (hide (readsIn w S R) x) (hide (writesIn w S W) x)
      ((x, b) :: s.env) := by
  -- The new binding changes no location that an old one views.
  have hN : ∀ y b' ℓ, (y, b') ∈ s.env → Refers b' ℓ → ¬Changes b ℓ := by
    intro y b' ℓ hy hr hc
    cases b with
    | loc ℓ₀ =>
      cases (show ℓ₀ = ℓ from hc)
      exact absurd hb.2 (by have := hst.lt hy (.inr hr); omega)
    | view _ => exact hc
    | writes r =>
      obtain ⟨-, ℓ₀, _, _, _, rfl, -, hal, -⟩ := hb
      cases (show ℓ₀ = ℓ from hc)
      exact hal y b' hy hr
  -- Only a writable binding targets, a location that no old binding views.
  have hT : ∀ ℓ, Targets b ℓ → ∀ y b', (y, b') ∈ s.env → ¬Targets b' ℓ := by
    intro ℓ ht y b' hy ht'
    cases b with
    | writes r =>
      obtain ⟨-, ℓ₀, _, _, _, rfl, -, hal, -⟩ := hb
      cases (show ℓ₀ = ℓ from ht)
      exact hal y b' hy ht'.refers
    | _ => exact ht.elim
  refine ⟨fun y z ℓ hy hz => ?_, List.Pairwise.cons (fun e he ℓ ht => hT ℓ ht e.1 e.2 he)
    hs.apart, fun y ℓ π a c hy => ?_, fun y b' ℓ hy ht z hz => ?_, .cons ⟨rfl, fun ℓ hr => ?_⟩
    (Pointwise.imp_right (fun g e he ⟨hg, hcov⟩ => ⟨hg, fun ℓ hr =>
      (hcov ℓ hr).cons (.inl (hN e.1 e.2 ℓ he hr))⟩) hs.sources)⟩
  · have hold : ∀ y ℓ, (y, WBinding.loc ℓ) ∈ s.env → b ≠ .loc ℓ := fun y ℓ hy' he => by
      rw [he] at hb
      exact absurd hb.2 (by have := hst.lt hy' (.inl (show Changes (.loc ℓ) ℓ from rfl)); omega)
    rcases List.mem_cons.1 hy with hy | hy
    · rcases List.mem_cons.1 hz with hz | hz
      · exact (congrArg Prod.fst hy).trans (congrArg Prod.fst hz).symm
      · exact absurd (congrArg Prod.snd hy).symm (hold z ℓ hz)
    · rcases List.mem_cons.1 hz with hz | hz
      · exact absurd (congrArg Prod.snd hz).symm (hold y ℓ hy)
      · exact hs.distinct y z ℓ hy hz
  · intro z b' hz hc
    by_cases hzx : z = x
    · subst hzx
      simp only [List.lookup_cons_self, Option.some.injEq] at hz
      subst hz
      rcases List.mem_cons.1 hy with hy | hy
      · cases hy
        exact hc.elim
      · exact absurd hc (hN y _ ℓ hy rfl)
    rw [lookup_cons_ne hzx] at hz
    rcases List.mem_cons.1 hy with hy | hy
    · cases hy
      obtain ⟨rfl, hcov⟩ := hb
      have := hcov ℓ π a c rfl z b' (Views.mem_of_lookup hz) hc
      simp [hide, readsIn, List.mem_filter, this, hzx]
    · exact mem_frozen (hs.guarded y ℓ π a c hy z b' hz hc) hzx
  · by_cases hzx : z = x
    · subst hzx
      simp only [List.lookup_cons_self, Option.some.injEq] at hz
      subst hz
      rcases List.mem_cons.1 hy with hy | hy
      · cases hy
        exact ht.elim
      · exact absurd hb.2 (by have := hst.lt hy (.inr ht.refers); omega)
    rw [lookup_cons_ne hzx] at hz
    have hzx' : (z != x) = true := by simpa using hzx
    rcases List.mem_cons.1 hy with hy | hy
    · rw [show b' = b from congrArg Prod.snd hy] at ht
      cases b with
      | writes r =>
        obtain ⟨rfl, ℓ₀, _, _, _, rfl, hcov, -⟩ := hb
        cases (show ℓ₀ = ℓ from ht)
        have := hcov z _ (Views.mem_of_lookup hz) rfl
        simp [hide, writesIn, List.mem_filter, this, hzx']
      | _ => exact ht.elim
    · have := hs.locked y b' ℓ hy ht z hz
      cases w <;> simp [hide, writesIn, List.mem_filter, this, hzx']
  · cases b with
    | loc _ => exact hr.elim
    | view r =>
      obtain ⟨rfl, hcov⟩ := hb
      cases r <;> simp only [Refers] at hr
      subst hr
      exact (hcov _ _ _ _ rfl).cons (.inl id)
    | writes r =>
      obtain ⟨rfl, ℓ₀, _, _, _, rfl, hcov, -⟩ := hb
      cases (show ℓ₀ = ℓ from hr)
      exact Cover.cons (fun y b' hy hc => List.mem_cons_of_mem _ (hcov y b' hy hc))
        (.inr List.mem_cons_self)

end Stilt.Writes
