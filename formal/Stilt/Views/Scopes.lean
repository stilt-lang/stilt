import Stilt.Views.State

/-!
# Scopes

A binding and its scope, in both models: a value takes a new location, which
the scope's end frees, and a view is held by its variable (expressions.scope).
The binding hides every read of a place of the same name, as `hide` does for
the loops of modes.change-while-iterating, and a view binding reads its sources for its scope
(views.reads-that-last).

When the scope ends, a value that the rest of the block gives may still be a
window. Its sources cover it, so if none is named by the binding, the window
reads no location that the scope's end frees: that is views.escaping (E0422) at work.
-/

namespace Stilt.Views

theorem mem_hide {s : Shape} {R : List Shape} {x : Name} :
    s ∈ hide R x ↔ s ∈ R ∧ s.root ≠ x := by
  simp [hide, List.mem_filter]

/-- What a binding frees when its scope ends. -/
def freeing : Binding → Store → Store
  | .loc ℓ, store => store.set ℓ none
  | .view _, store => store

theorem source_freeing {b : Binding} {store : Store} {ℓ : Nat} (π : Path) (h : b ≠ .loc ℓ) :
    source (freeing b store) ℓ π = source store ℓ π := by
  cases b with
  | loc ℓ' => exact source_set_ne _ _ fun he => h (he ▸ rfl)
  | view _ => rfl

theorem unbind_cons {s : VState} {x : Name} {b : Binding} {E : List (Name × Binding)}
    (h : s.env = (x, b) :: E) : s.unbind = ⟨E, freeing b s.store⟩ := by
  cases b <;> simp [VState.unbind, h, freeing]

/-! ## Covering a new binding -/

section Push

variable {R S T : List Shape} {x : Name} {env : List (Name × Binding)} {b : Binding}
  {ℓ : Nat} {π : Path}

theorem Covered.cons (h : Covered T env ℓ π) (hb : b ≠ .loc ℓ) :
    Covered T ((x, b) :: env) ℓ π := fun y hy => by
  rcases List.mem_cons.1 hy with he | hy
  · exact absurd (congrArg Prod.snd he).symm hb
  · exact h y hy

theorem Guarded.cons (h : Guarded R env ℓ π) (hb : b ≠ .loc ℓ) :
    Guarded (hide (S ++ R) x) ((x, b) :: env) ℓ π := fun y hy => by
  by_cases hyx : y = x
  · subst hyx
    simp only [List.lookup_cons_self, Option.some.injEq] at hy
    exact absurd hy hb
  · rw [lookup_cons_ne hyx] at hy
    exact mem_hide.2 ⟨List.mem_append_right _ (h y hy), hyx⟩

theorem Covered.guarded_cons (h : Covered S env ℓ π) (hb : b ≠ .loc ℓ) :
    Guarded (hide (S ++ R) x) ((x, b) :: env) ℓ π := fun y hy => by
  by_cases hyx : y = x
  · subst hyx
    simp only [List.lookup_cons_self, Option.some.injEq] at hy
    exact absurd hy hb
  · rw [lookup_cons_ne hyx] at hy
    exact mem_hide.2 ⟨List.mem_append_left _ (h y (mem_of_lookup hy)), hyx⟩

end Push

/-- A new binding keeps what the analysis knows of the environment, with its
sources `S` and its read: its location is new, and its sources cover the
window it holds (views.reads-that-last). -/
theorem InScope.push {Γ : Sources} {R S : List Shape} {x : Name}
    {env : List (Name × Binding)} {b : Binding} {n : Nat} (hs : InScope Γ R env)
    (hlocs : ∀ y ℓ, (y, Binding.loc ℓ) ∈ env → ℓ < n)
    (hwins : ∀ y ℓ π a c, (y, Binding.view (.window ℓ π a c)) ∈ env → ℓ < n)
    (hfresh : ∀ ℓ, b = .loc ℓ → n ≤ ℓ)
    (hview : ∀ ℓ π a c, b = .view (.window ℓ π a c) → Covered S env ℓ π) :
    InScope ((x, S) :: Γ) (hide (S ++ R) x) ((x, b) :: env) := by
  have hne : ∀ ℓ, ℓ < n → b ≠ .loc ℓ := fun ℓ hℓ he => Nat.lt_irrefl _
    (Nat.lt_of_lt_of_le hℓ (hfresh ℓ he))
  refine ⟨fun y z ℓ hy hz => ?_, fun y ℓ π a c hy => ?_, .cons ⟨rfl, fun ℓ π a c he => ?_⟩ ?_⟩
  · rcases List.mem_cons.1 hy with hy | hy <;> rcases List.mem_cons.1 hz with hz | hz
    · exact (congrArg Prod.fst hy).trans (congrArg Prod.fst hz).symm
    · exact absurd (congrArg Prod.snd hy).symm (hne ℓ (hlocs z ℓ hz))
    · exact absurd (congrArg Prod.snd hz).symm (hne ℓ (hlocs y ℓ hy))
    · exact hs.distinct y z ℓ hy hz
  · rcases List.mem_cons.1 hy with hy | hy
    · have hb : b = .view (.window ℓ π a c) := (congrArg Prod.snd hy).symm
      exact (hview ℓ π a c hb).guarded_cons (by rw [hb]; exact fun h => nomatch h)
    · exact (hs.guarded y ℓ π a c hy).cons (hne ℓ (hwins y ℓ π a c hy))
  · have hb : b = .view (.window ℓ π a c) := he
    exact (hview ℓ π a c hb).cons (by rw [hb]; exact fun h => nomatch h)
  · refine Pointwise.imp_mem (fun g e he ⟨hg, hcov⟩ => ⟨hg, fun ℓ π a c hw => ?_⟩) hs.sources
    obtain ⟨y, e⟩ := e
    simp only at hw
    subst hw
    exact (hcov ℓ π a c rfl).cons (hne ℓ (hwins y ℓ π a c he))

/-! ## Binding -/

/-- Binding agreeing values in both models gives states that agree, and a
binding with a new location or a view. -/
theorem StateAgrees.bind {sw sc : VState} {rw rc : RVal} (h : StateAgrees sw sc)
    (hag : Agrees sw.store rw rc) (x : Name) :
    StateAgrees (sw.bind x rw) (sc.bind x rc) ∧
      ∃ b, (sw.bind x rw).env = (x, b) :: sw.env ∧ (∀ ℓ, b = .loc ℓ → sw.store.length ≤ ℓ) ∧
        (∀ ℓ π a c, b = .view (.window ℓ π a c) → rw = .window ℓ π a c) ∧
        sw.store.length ≤ (sw.bind x rw).store.length ∧
        ∀ ℓ π, ℓ < sw.store.length → source (sw.bind x rw).store ℓ π = source sw.store ℓ π := by
  cases rw <;> cases rc <;> try exact False.elim hag
  · rename_i v w
    have hvw : v = w := hag
    subst hvw
    have ht := h.temp v []
    refine ⟨⟨by simp [VState.bind, h.store], .cons ⟨rfl, by simp [BAgrees, h.store]⟩ ht.1.env,
      fun y ℓ hy => ?_⟩, ?_⟩
    · rcases List.mem_cons.1 hy with hy | hy
      · cases (congrArg Prod.snd hy)
        simp [VState.bind]
      · exact ht.1.locs y ℓ hy
    · refine ⟨.loc sw.store.length, rfl, fun ℓ he => ?_, fun _ _ _ _ he => (nomatch he),
        ht.2.grows, fun ℓ π hℓ => source_append _ π hℓ⟩
      cases he
      exact Nat.le_refl _
  · refine ⟨⟨h.store, .cons ⟨rfl, hag⟩ h.env, fun y ℓ hy => ?_⟩, ?_⟩
    · rcases List.mem_cons.1 hy with hy | hy
      · exact nomatch congrArg Prod.snd hy
      · exact h.locs y ℓ hy
    · refine ⟨.view (.window _ _ _ _), rfl, fun _ he => (nomatch he), fun _ _ _ _ he => ?_,
        Nat.le_refl _, fun _ _ _ => rfl⟩
      cases he
      rfl

end Stilt.Views
