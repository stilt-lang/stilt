import Stilt.Soundness.Uses

/-!
# Trait methods

`Trait.m` at a type with an impl of the trait is the function of that impl,
whose signature is the method's with `Self` the type (traits.impl-signatures). In
an instance, every type is ground, so a bound that typing allowed is met by an
impl (traits.unsatisfied-bounds), and the evaluator finds the function by the
type's head (traits.qualified-calls).
-/

namespace Stilt

section

variable {D : Decls}

/-- Names are unique, so a function is found by its own name. -/
theorem find?_name_of_mem :
    ∀ {l : List FnDecl} {d : FnDecl}, (l.map (·.name)).Nodup → d ∈ l →
      l.find? (·.name == d.name) = some d
  | d₀ :: l, d, hnd, hd => by
    rw [List.find?_cons]
    rcases List.mem_cons.1 hd with rfl | hd
    · simp
    · have hne : (d₀.name == d.name) = false := by
        simp only [beq_eq_false_iff_ne]
        intro heq
        exact (List.nodup_cons.1 hnd).1 (by simp only [heq]; exact List.mem_map_of_mem hd)
      rw [hne]
      exact find?_name_of_mem (List.nodup_cons.1 hnd).2 hd

theorem Decls.WellFormed.fn?_of_mem (hD : D.WellFormed) {d : FnDecl} (hd : d ∈ D.fns) : D.fn? d.name = some d :=
  find?_name_of_mem hD.fnNames hd

/-- The function that `Trait.m` at a head finds: the impl's member, with no
type parameters or row variables and the method's signature at the head. -/
theorem Decls.WellFormed.implFn (hD : D.WellFormed) {Tr m : Name} {t : TraitDecl} {σ : Ty}
    (ht : D.trait? Tr = some t) (hm : t.methods.lookup m = some σ) {h : Head} {i : TraitImpl}
    (hi : D.traitImpl? Tr h = some i) :
    ∃ d, D.fn? (implName Tr h m) = some d ∧ d.typeParams = [] ∧ d.rowParams = [] ∧
      d.type = σ.substTys [(selfParam, h.type)] := by
  have him := List.mem_of_find?_eq_some hi
  have hp := List.find?_some hi
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  obtain ⟨t', ht', hfns⟩ := hD.traitImpls i him
  rw [ht] at ht'
  obtain rfl := Option.some.inj ht'
  obtain ⟨d, hd, rfl, htp, hrp, hty⟩ := hfns _ σ hm
  have hmem : d.qualify (implQualifier i.trait i.type) ∈ D.fns :=
    List.mem_append_right _ (List.mem_flatMap.2 ⟨i, him, List.mem_map_of_mem hd⟩)
  exact ⟨_, hD.fn?_of_mem hmem, htp, hrp, hty⟩

end

section

variable {D : Decls} {n : Nat} {scope : RowScope} {η : REnv} (hη : η.Respects scope)
  (θ : RowSubst) {Γ : Ctx} {fx : Effects}
include hη

/-- `Trait.m` at a type of an instance is a function value of the method's
type at that type. -/
theorem method_ok (hD : D.WellFormed) {Tr m : Name} {t : TraitDecl} {σ τ : Ty}
    (ht : D.trait? Tr = some t) (hm : t.methods.lookup m = some σ) (hc : τ.Closed)
    (hsat : Satisfies D scope τ Tr) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v ((σ.substTys [(selfParam, τ)]).close η))
      (eval D Copy.memory (n + 1) ((Expr.method Tr m τ).substRows θ)) := by
  rcases hsat with ⟨p, hp, _⟩ | ⟨h, hh, hi⟩
  · rw [hη.types] at hp
    exact nomatch hp
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hi
  obtain ⟨d, hd, htp, hrp, hty⟩ := hD.implFn ht hm hi
  obtain rfl := Ty.eq_of_head? hh
  have hsig := (hD.traits t (List.mem_of_find?_eq_some ht)).closed _ (mem_of_lookup hm)
  have hclosed : d.type.Closed := hty ▸ hsig.substTys fun q hq => by
    simp only [List.mem_singleton] at hq
    subst hq
    exact h.ground_type
  have hδ : (d.typeArgs []).Fits D d.scope d.scope.instantiated :=
    ⟨fun _ hq => by simp [FnDecl.typeArgs] at hq, fun _ hq => by simp [FnDecl.typeArgs] at hq,
      fun q hq => by simp [FnDecl.scope, htp] at hq,
      fun _ h => h, fun _ _ h => h, fun _ _ h => h⟩
  have hnone : ∀ v E, d.pairs v E → False := fun v E ⟨ρ, hρ, hv, _⟩ => by
    rw [hclosed ρ (FnDecl.mem_rows_of_pairs hρ)] at hv
    exact nomatch hv
  have hη' : η.Respects d.scope.instantiated :=
    ⟨fun v E hp => (hnone v E hp).elim, fun v E hp => (hnone v E hp).elim, rfl, hη.noResume⟩
  have hv : Value.Typed D (Value.function (implName Tr h m) [] []) ((σ.substTys [(selfParam, h.type)]).close η) :=
    .function hd hδ hη' (by simp [FnDecl.typeArgs, hty]; exact .refl _)
  rw [show (Expr.method Tr m h.type).substRows θ = .method Tr m h.type by
    simp [Expr.substRows, Ty.substRows_of_closed θ _ hc]]
  show Eval.Ok D Γ η _ _ (Eval.method D Tr m h.type)
  unfold Eval.method
  rw [h.head?_type]
  dsimp only
  rw [hi]
  exact Eval.Ok.pure hv

end

end Stilt
