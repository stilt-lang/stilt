import Stilt.Typing

/-!
# The traits behind operators

`==`, `<` and interpolation apply only at a type that implements `Eq`, `Ord` or `Show`
(traits.required-traits). So `a == b` on a type parameter without the bound `Eq` has no
type, which E0318 rejects, while with the bound it has (traits.unsatisfied-bounds); a
function can't be compared (traits.built-in-impls), nor a `Shared<T>` (shared.std-sync);
maps and sets have no `Ord`, and a list of maps has `Eq` when its maps' keys are key types
and its values have `Eq` (traits.structural-impls and traits.map-equality).
-/

namespace Stilt.Examples.Bounds

private def decls : Decls := ⟨[], [], [], [], [], [], [], []⟩

/-- The scope of `fn f<T: …>`, with the bounds of `T`. -/
private def scopeWith (bounds : List Name) : RowScope :=
  ⟨[], fun _ _ => False, fun _ _ => False, [⟨"T", bounds, [], []⟩]⟩

/-- `a` and `b` of the type `τ`. -/
private def ctx (τ : Ty) : Ctx := [("a", ⟨τ, false⟩), ("b", ⟨τ, false⟩)]

private def eq : Expr := .op (.structural .eq []) [.var "a", .var "b"]

/-- `a == b` on `T: Eq` has a type. -/
example (fx : Effects) : HasType decls (scopeWith ["Eq"]) (ctx (.param "T")) fx eq .bool :=
  .op .structural (.cons (.var rfl) (.refl _) (.cons (.var rfl) (.refl _) .nil))
    (Op.keysIn_of_nil rfl) (fun p hp => by
      simp only [Op.traitsNeeded, Cmp.trait, List.mem_singleton] at hp
      subst hp
      exact ⟨fun τ => τ = .param "T", rfl, by
        rintro _ rfl
        exact ⟨⟨"T", ["Eq"], [], []⟩, List.mem_singleton_self _, rfl, List.mem_singleton_self _⟩⟩) (Op.noIo rfl)

/-- An operand of `==` has the type of the variable it reads, or one with a larger row. -/
private theorem eq_operand {s : RowScope} {σ : Ty} {fx : Effects} {τ : Ty}
    (h : HasType decls s (ctx σ) fx eq τ) :
    ∃ τ', Fits σ τ' ∧ decls.Implements s .eq τ' := by
  cases h with
  | op ho hes _ hb _ =>
    cases ho
    cases hes with
    | cons he hfit _ =>
      cases he with
      | var hl =>
        refine ⟨_, ?_, hb _ List.mem_cons_self⟩
        simp [ctx, Ctx.lookup] at hl
        rw [hl.1]
        exact hfit

/-- What a type implements at its outermost type. -/
private theorem step {s : RowScope} {t : PreludeTrait} {τ : Ty} (h : decls.Implements s t τ) :
    decls.ImplStep s t (decls.Implements s t) τ :=
  h.step

/-- Without the bound, `fn f<T>(a: T, b: T) -> bool { a == b }` has no type: `T` lacks `Eq`,
E0318 (traits.unsatisfied-bounds). -/
example (fx : Effects) (τ : Ty) : ¬HasType decls (scopeWith []) (ctx (.param "T")) fx eq τ := by
  intro h
  obtain ⟨τ', hfit, hi⟩ := eq_operand h
  cases hfit
  obtain ⟨q, hq, -, hB⟩ := step hi
  simp only [scopeWith, List.mem_singleton] at hq
  subst hq
  exact nomatch hB

/-- Functions can't be compared (traits.built-in-impls): `==` on two functions has no type. -/
example (fx : Effects) (τ : Ty) (ps : List (Mode × Ty)) (r : Ty) (ρ : Row) :
    ¬HasType decls (scopeWith []) (ctx (.fn ps r ρ)) fx eq τ := by
  intro h
  obtain ⟨τ', hfit, hi⟩ := eq_operand h
  cases hfit <;> exact (step hi).elim

/-- Nor can two handles of shared values (shared.std-sync). -/
example (fx : Effects) (τ σ : Ty) : ¬HasType decls (scopeWith []) (ctx (.shared σ)) fx eq τ := by
  intro h
  obtain ⟨τ', hfit, hi⟩ := eq_operand h
  cases hfit
  exact (step hi).elim

/-- Maps and sets have no `Ord` (traits.structural-impls and std.set-impls). -/
example (s : RowScope) (κ υ : Ty) : ¬decls.Implements s .ord (.map κ υ) := fun h => (step h).elim
example (s : RowScope) (κ : Ty) : ¬decls.Implements s .ord (.set κ) := fun h => (step h).elim

/-- A list of maps from strings to floats has `Eq`, which compares the maps in any order
(traits.structural-impls and traits.map-equality). -/
example (s : RowScope) : decls.Implements s .eq (.list (.map .str (.float .f64))) :=
  ⟨fun τ => τ = .list (.map .str (.float .f64)) ∨ τ = .map .str (.float .f64) ∨ τ = .float .f64,
    .inl rfl, by
      rintro _ (rfl | rfl | rfl)
      · exact .inr (.inl rfl)
      · exact ⟨.str, ⟨fun τ => τ = .str, rfl, by rintro _ rfl; trivial⟩, .inr (.inr rfl)⟩
      · exact nofun⟩

end Stilt.Examples.Bounds
