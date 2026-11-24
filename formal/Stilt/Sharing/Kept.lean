import Stilt.Sharing.Evolves

/-!
# `inout` bindings are kept

The binding of an `inout` parameter has its argument's place for home all through the call: it
never refers elsewhere (`assignWhole` redirects only a binding that isn't `inout`), `evacuate`
leaves it alone (its home is apart from every other), and an assignment keeps its home. So the
state a step ends in has, below its newer bindings, every `inout` binding of the state it began
in, where it was: what a call's end reads of each parameter is what its argument's place holds.
-/

namespace Stilt.Sharing

/-- The second list has the first's names, in order, and each `inout` binding of the first in its
place. -/
def KeptEntries : List (Name × Entry) → List (Name × Entry) → Prop
  | [], [] => True
  | a :: l, b :: l' => b.1 = a.1 ∧ (a.2.inout = true → b = a) ∧ KeptEntries l l'
  | _, _ => False

namespace KeptEntries

theorem refl : ∀ l : List (Name × Entry), KeptEntries l l
  | [] => trivial
  | _ :: l => ⟨rfl, fun _ => rfl, refl l⟩

theorem length_eq : ∀ {l l' : List (Name × Entry)}, KeptEntries l l' → l.length = l'.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [length_eq h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem names : ∀ {l l' : List (Name × Entry)}, KeptEntries l l' →
    l'.map Prod.fst = l.map Prod.fst
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [h.1, names h.2.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem trans : ∀ {l₁ l₂ l₃ : List (Name × Entry)}, KeptEntries l₁ l₂ → KeptEntries l₂ l₃ →
    KeptEntries l₁ l₃
  | [], [], [], _, _ => trivial
  | a :: _, b :: _, c :: _, h₁, h₂ => ⟨h₂.1.trans h₁.1, fun ha => by
      have hb := h₁.2.1 ha
      subst hb
      exact h₂.2.1 ha, trans h₁.2.2 h₂.2.2⟩
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | _, [], _ :: _, _, h => h.elim
  | _, _ :: _, [], _, h => h.elim

/-- Replacing a binding by one of its name that isn't `inout`, or by itself, keeps the others. -/
theorem set : ∀ {l : List (Name × Entry)} {i : Nat} {a b : Name × Entry}, l[i]? = some a →
    b.1 = a.1 → (a.2.inout = true → b = a) → KeptEntries l (l.set i b)
  | [], _, _, _, h, _, _ => by simp at h
  | _ :: l, 0, _, _, h, hn, hb => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨hn, hb, refl l⟩
  | _ :: _, _ + 1, _, _, h, hn, hb => ⟨rfl, fun _ => rfl, set (by simpa using h) hn hb⟩

/-- The binding the first list finds for a name is the one the second finds, when it is
`inout`. -/
theorem lookup : ∀ {l l' : List (Name × Entry)}, KeptEntries l l' → ∀ {y : Name} {e : Entry},
    l.lookup y = some e → e.inout = true → l'.lookup y = some e
  | [], [], _, _, _, h, _ => by simp at h
  | (z, f) :: l, (z', f') :: l', h, y, e, hl, hin => by
    obtain ⟨hz, hf, h⟩ := h
    simp only at hz
    subst z'
    by_cases hy : y = z
    · subst hy
      rw [List.lookup_cons_self, Option.some.injEq] at hl
      subst hl
      have := hf hin
      simp only [Prod.mk.injEq] at this
      rw [this.2, List.lookup_cons_self]
    · rw [lookup_cons_ne hy] at hl ⊢
      exact lookup h hl hin
  | [], _ :: _, h, _, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _, _ => h.elim

end KeptEntries

/-- `s'` has `s`'s bindings' names in order, and each `inout` binding of `s` in its place. -/
def Kept (s s' : State) : Prop := KeptEntries s.env s'.env

namespace Kept

theorem refl (s : State) : Kept s s := KeptEntries.refl s.env

theorem trans {s s₁ s₂ : State} (h₁ : Kept s s₁) (h₂ : Kept s₁ s₂) : Kept s s₂ :=
  KeptEntries.trans h₁ h₂

/-- A state whose bindings are another's, one replaced by a binding of its name that isn't
`inout` or by itself, keeps them. -/
theorem set {s s' : State} {i : Nat} {a b : Name × Entry} (henv : s'.env = s.env.set i b)
    (ha : s.env[i]? = some a) (hn : b.1 = a.1) (hb : a.2.inout = true → b = a) : Kept s s' := by
  unfold Kept
  rw [henv]
  exact KeptEntries.set ha hn hb

/-- A state with the same bindings keeps them. -/
theorem same {s s' : State} (henv : s'.env = s.env) : Kept s s' := by
  unfold Kept
  rw [henv]
  exact KeptEntries.refl _

/-- Ending the newest binding of a state with one more binding than `s` keeps the bindings of
`s` that the state kept. -/
theorem unbind {s s₀ s₁ : State} {a : Name × Entry} (h₀ : s₀.env = a :: s.env)
    (h₁ : Kept s₀ s₁) : Kept s ⟨s₁.env.tail, s₁.store⟩ := by
  unfold Kept at h₁ ⊢
  rw [h₀] at h₁
  cases hs : s₁.env with
  | nil => rw [hs] at h₁; exact h₁.elim
  | cons b l =>
    rw [hs] at h₁
    exact h₁.2.2

end Kept

/-- `evacuate` settles only bindings that refer to another's storage, so it keeps every
`inout` binding, which refers to its own home, and every name. -/
theorem Evacuated.kept {region : InPlace.Ref} {skip : Nat} {s s' : State} :
    ∀ {i : Nat} {env env' : List (Name × Entry)},
      (∀ ye ∈ env, ye.2.inout = true → ye.2.alias = none) →
      Evacuated region skip s s' i env env' → KeptEntries env env'
  | _, [], [], _, _ => trivial
  | i, (y, e) :: rest, (y', e') :: rest', hio, ⟨h₁, _, _, _, _, h₆, h₇⟩ => by
    refine ⟨h₁, fun hin => ?_, Evacuated.kept (fun ye hye => hio ye (List.mem_cons_of_mem _ hye)) h₇⟩
    have ha : e.alias = none := hio (y, e) List.mem_cons_self hin
    simp only [ha, Option.any_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at h₆
    simp [h₁, h₆]
  | _, [], _ :: _, _, h => h.elim
  | _, _ :: _, [], _, h => h.elim

end Stilt.Sharing
