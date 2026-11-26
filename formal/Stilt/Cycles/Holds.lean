import Stilt.Soundness.Arguments

/-!
# What a type holds

cycles.can-form-cycle, on the types of the core calculus as a run reads them: a type holds
itself, the types of its fields and variants, of its elements, of a map's keys and values, and
the `U` of a `Shared<U>`, and what each of those holds. A `Shared<U>` can reach itself when `U`
holds that same `Shared<U>`, a function type, or a type parameter.

Two types that a run takes for the same, `STy.Eqv`, differ only in the order and repetition
of their rows' error types, which only function types have. So types that are the same that
way are equal, or both hold a function type (`STy.Eqv.eq_or_fn`), and either way a `Shared` of
one reaches what a `Shared` of the other does.
-/

namespace Stilt

/-- cycles.can-form-cycle, holding: a type holds itself and the types of its fields and
variants, as its declaration states them at its type arguments, of its elements, of a map's
keys and values, and the `U` of a `Shared<U>`, and what each of those holds. An instance of a
generic type holds its type arguments too, which only adds to what it holds when no field
names a parameter, so a `Shared` of it may reach itself in the model where the Reference
says it can't. -/
inductive STy.Holds (D : Decls) : STy → STy → Prop
  | refl {t : STy} : STy.Holds D t t
  | list {e s : STy} : STy.Holds D e s → STy.Holds D (.list e) s
  | tuple {es : List STy} {e s : STy} : e ∈ es → STy.Holds D e s → STy.Holds D (.tuple es) s
  | key {κ σ s : STy} : STy.Holds D κ s → STy.Holds D (.map κ σ) s
  | value {κ σ s : STy} : STy.Holds D σ s → STy.Holds D (.map κ σ) s
  | set {e s : STy} : STy.Holds D e s → STy.Holds D (.set e) s
  | shared {u s : STy} : STy.Holds D u s → STy.Holds D (.shared u) s
  | record {R : Name} {as : List STy} {r : RecordDecl} {f : Name} {τ : Ty} {s : STy} :
      D.record? R = some r → (f, τ) ∈ r.fields → STy.Holds D (τ.semAt (r.typeParams.zip as)) s →
      STy.Holds D (.record R as) s
  | variant {T : Name} {as : List STy} {t : VariantDecl} {C : Name} {τs : List Ty} {τ : Ty}
      {s : STy} :
      D.variant? T = some t → (C, τs) ∈ t.ctors → τ ∈ τs →
      STy.Holds D (τ.semAt (t.typeParams.zip as)) s → STy.Holds D (.variant T as) s
  | recordArg {R : Name} {as : List STy} {a s : STy} :
      a ∈ as → STy.Holds D a s → STy.Holds D (.record R as) s
  | variantArg {T : Name} {as : List STy} {a s : STy} :
      a ∈ as → STy.Holds D a s → STy.Holds D (.variant T as) s

/-- A type holds a function type, whose values capture values of any type. -/
def STy.HoldsFn (D : Decls) (σ : STy) : Prop :=
  ∃ ps r R, STy.Holds D σ (.fn ps r R)

/-- cycles.can-form-cycle, reaching itself: a `Shared<U>` can when `U` holds that same
`Shared<U>`, a function type, or a type parameter. -/
def CanReachItself (D : Decls) (u : Ty) : Prop :=
  STy.Holds D u.sem (.shared u.sem) ∨ u.sem.HoldsFn D ∨ ∃ T, STy.Holds D u.sem (.param T)

variable {D : Decls}

theorem STy.Holds.trans {a b c : STy} (h₁ : STy.Holds D a b) (h₂ : STy.Holds D b c) :
    STy.Holds D a c := by
  induction h₁ with
  | refl => exact h₂
  | list _ ih => exact .list (ih h₂)
  | tuple hm _ ih => exact .tuple hm (ih h₂)
  | key _ ih => exact .key (ih h₂)
  | value _ ih => exact .value (ih h₂)
  | set _ ih => exact .set (ih h₂)
  | shared _ ih => exact .shared (ih h₂)
  | record hR hm _ ih => exact .record hR hm (ih h₂)
  | variant hT hC hm _ ih => exact .variant hT hC hm (ih h₂)
  | recordArg hm _ ih => exact .recordArg hm (ih h₂)
  | variantArg hm _ ih => exact .variantArg hm (ih h₂)

/-- A type holds the function types of what it holds. -/
theorem STy.HoldsFn.of {a b : STy} (h : STy.Holds D b a) : a.HoldsFn D → b.HoldsFn D
  | ⟨ps, r, R, ha⟩ => ⟨ps, r, R, h.trans ha⟩

/-- Two lists of types, equal or each with an element that holds a function type. -/
def STys.EqOrFn (D : Decls) (as bs : List STy) : Prop :=
  as = bs ∨ (∃ a ∈ as, a.HoldsFn D) ∧ ∃ b ∈ bs, b.HoldsFn D

mutual

/-- Types that a run takes for the same are equal, or both hold a function type. -/
theorem STy.Eqv.eq_or_fn : ∀ {a b : STy}, a.Eqv b → a = b ∨ a.HoldsFn D ∧ b.HoldsFn D
  | _, _, .int _ | _, _, .float _ | _, _, .bool | _, _, .str | _, _, .unit | _, _, .never
  | _, _, .param _ | _, _, .effect _ | _, _, .resume _ _ =>
    .inl rfl
  | _, _, .record _ h => (STysEqv.eq_or_fn h).imp (congrArg _)
      fun ⟨⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩ => ⟨hfa.of (.recordArg ha .refl), hfb.of (.recordArg hb .refl)⟩
  | _, _, .variant _ h => (STysEqv.eq_or_fn h).imp (congrArg _)
      fun ⟨⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩ => ⟨hfa.of (.variantArg ha .refl), hfb.of (.variantArg hb .refl)⟩
  | _, _, .list h => (STy.Eqv.eq_or_fn h).imp (congrArg _)
      fun ⟨ha, hb⟩ => ⟨ha.of (.list .refl), hb.of (.list .refl)⟩
  | _, _, .set h => (STy.Eqv.eq_or_fn h).imp (congrArg _)
      fun ⟨ha, hb⟩ => ⟨ha.of (.set .refl), hb.of (.set .refl)⟩
  | _, _, .shared h => (STy.Eqv.eq_or_fn h).imp (congrArg _)
      fun ⟨ha, hb⟩ => ⟨ha.of (.shared .refl), hb.of (.shared .refl)⟩
  | _, _, .tuple h => (STysEqv.eq_or_fn h).imp (congrArg _)
      fun ⟨⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩ => ⟨hfa.of (.tuple ha .refl), hfb.of (.tuple hb .refl)⟩
  | _, _, .map hκ hσ => by
    rcases STy.Eqv.eq_or_fn hκ with rfl | ⟨ha, hb⟩
    · rcases STy.Eqv.eq_or_fn hσ with rfl | ⟨ha, hb⟩
      · exact .inl rfl
      · exact .inr ⟨ha.of (.value .refl), hb.of (.value .refl)⟩
    · exact .inr ⟨ha.of (.key .refl), hb.of (.key .refl)⟩
  | _, _, .fn _ _ _ _ => .inr ⟨⟨_, _, _, .refl⟩, ⟨_, _, _, .refl⟩⟩

theorem STysEqv.eq_or_fn : ∀ {as bs : List STy}, STysEqv as bs → STys.EqOrFn D as bs
  | _, _, .nil => .inl rfl
  | _, _, .cons h hs => by
    rcases STy.Eqv.eq_or_fn h with rfl | ⟨ha, hb⟩
    · rcases STysEqv.eq_or_fn hs with rfl | ⟨⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩
      · exact .inl rfl
      · exact .inr ⟨⟨a, List.mem_cons_of_mem _ ha, hfa⟩, ⟨b, List.mem_cons_of_mem _ hb, hfb⟩⟩
    · exact .inr ⟨⟨_, List.mem_cons_self, ha⟩, ⟨_, List.mem_cons_self, hb⟩⟩

end

/-- Only a `Shared<B>` fits a `Shared<A>`, and `B` is `A` or both hold a function type. -/
theorem STy.Fits.shared_eq_or_fn {x σ : STy} (h : x.Fits σ) :
    ∀ {a : STy}, x = .shared a → ∃ b, σ = .shared b ∧ (b = a ∨ a.HoldsFn D ∧ b.HoldsFn D) := by
  induction h with
  | refl => intro a hx; exact ⟨a, hx, .inl rfl⟩
  | eqv hxy _ ih =>
    intro a hx
    subst hx
    obtain ⟨a', rfl, haa⟩ := hxy.shared_inv
    obtain ⟨b, rfl, hb⟩ := ih rfl
    refine ⟨b, rfl, ?_⟩
    rcases haa.eq_or_fn (D := D) with rfl | ⟨ha, ha'⟩
    · exact hb
    · rcases hb with rfl | ⟨_, hb⟩
      · exact .inr ⟨ha, ha'⟩
      · exact .inr ⟨ha, hb⟩
  | grow => intro _ hx; cases hx
  | never => intro _ hx; cases hx

end Stilt
