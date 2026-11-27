import Stilt.Lenient.Typing

/-!
# The no-escape rule checks every row

On a body that passes the no-escape rule, the checker's typing is the typing
that checks every row (`Lenient.HasType.strict`), and the converse holds of
every body (`HasType.lenient`). So the leniency of effects.no-escape never lets a
row go unchecked in a program the no-escape rule accepts: "the variable can
reach such a row only through a use that breaks this rule".

The proof is a pass over the derivation beside the no-escape rule's own. Each
check that `LenientFits` makes is of an expression where the no-escape rule
allows neither a parameter nor a closure literal that names one, so the
expression carries none (`Expr.carries_eq_false`) and the check is the strict
one. The rule allows them in two places: as a callee, which is not checked
against a type, and as an argument given to a non-escaping parameter of the
function a call names, which is checked as it is (`Lenient.ArgsFit.passed`).
-/

namespace Stilt

/-- An expression where the no-escape rule allows no parameter of `N` carries
none. -/
theorem Expr.carries_eq_false {D : Decls} {N : List Name} {e : Expr}
    (h : e.noEscape D N false = true) : e.carries N = false := by
  cases e <;> simp_all [Expr.noEscape, Expr.carries]

/-- A check of an expression that carries no parameter is the strict one. -/
theorem LenientFits.fits {vs N : List Name} {e : Expr} {σ τ : Ty}
    (h : LenientFits vs N e σ τ) (hc : e.carries N = false) : Fits σ τ :=
  h.elim id fun h' => absurd h'.1 (by simp [hc])

private theorem both {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa using h

section

variable {D : Decls} {scope : RowScope} {vs : List Name}

/-- A check of an expression where the no-escape rule allows no parameter is
the strict one. -/
private theorem strictFits {N : List Name} {e : Expr} {σ τ : Ty} (h : LenientFits vs N e σ τ)
    (hne : e.noEscape D N false = true) : Fits σ τ :=
  h.fits (Expr.carries_eq_false hne)

/-- A let-else or a fallback passes the no-escape rule only if its scrutinee and its `else`
branch do. -/
private theorem noEscape_else {N : List Name} {k : Form} {e : Expr} {τ : Ty} {a : Arm}
    {x : Expr} {allowed : Bool}
    (h : (Expr.form k (.match e τ [a, ⟨.wild, [], none, x⟩])).noEscape D N allowed = true) :
    e.noEscape D N false = true ∧ x.noEscape D N false = true := by
  obtain ⟨_, _, _⟩ := a
  simp only [Expr.noEscape, armsNoEscape, Bool.and_eq_true] at h
  exact ⟨h.1, by simpa using h.2.2.1.2⟩

mutual

/-- On an expression that passes the no-escape rule, the checker's typing
checks every row. -/
theorem Lenient.HasType.strict :
    ∀ {N Γ fx e τ allowed}, Lenient.HasType D scope vs N Γ fx e τ →
      e.noEscape D N allowed = true → Stilt.HasType D scope Γ fx e τ
  | _, _, _, _, _, _, .var h, _ => .var h
  | _, _, _, _, _, _, .int h, _ => .int h
  | _, _, _, _, _, _, .bool, _ => .bool
  | _, _, _, _, _, _, .unit, _ => .unit
  | _, _, _, _, _, _, .record hr hl hw hperm hfs, hne =>
    .record hr hl hw hperm (Lenient.FieldsFit.strict hfs hne)
  | _, _, _, _, _, _, .variant ht hl hw hc hes, hne => .variant ht hl hw hc (Lenient.ExprsFit.strict hes hne)
  | _, _, _, _, _, _, .list hwf hes, hne => .list hwf (Lenient.ExprsFit.strict hes hne)
  | _, _, _, _, _, _, .op ho hes hk hb, hne => .op ho (Lenient.ExprsFit.strict hes hne) hk hb
  | _, _, _, _, _, _, .view ho hes, hne => .view ho (Lenient.ExprsFit.strict hes hne)
  | _, _, _, _, _, _, .field he hr hl hf, hne => .field (Lenient.HasType.strict he hne) hr hl hf
  | _, _, _, _, _, _, .elem he hf, hne => .elem (Lenient.HasType.strict he hne) hf
  | _, _, _, _, _, _, .index he hi hfit, hne =>
    have h := both hne
    .index (Lenient.HasType.strict he h.1) (Lenient.HasType.strict hi h.2) (strictFits hfit h.2)
  | _, _, _, _, _, _, .fnRef hf hlen hinst hres hwf hpass htys, _ => .fnRef hf hlen hinst hres hwf hpass htys
  | _, _, _, _, _, _, .method ht hm hc hwf hl hf, _ => .method ht hm hc hwf hl hf
  | _, _, _, _, _, _, .closure hnd hpt hwf hb hfit, hne =>
    have h := (both hne).2
    .closure hnd hpt hwf (Lenient.HasType.strict hb h) (strictFits hfit h)
  | _, _, _, _, _, _, .call hc ha hall, hne =>
    have h := both hne
    .call (Lenient.HasType.strict hc h.1) (Lenient.ArgsFit.strict ha h.2) hall
  | _, _, _, _, _, _, .held hnd hwf hes hb hv, hne =>
    have h := both hne
    .held hnd hwf (Lenient.ExprsFit.strict hes h.1) (Lenient.HasType.strict hb h.2) hv
  | _, _, _, _, _, _, .letElse hr hx hm, hne =>
    .letElse hr (Lenient.HasType.strict hx (noEscape_else hne).2) (Lenient.HasType.strict (allowed := false) hm hne)
  | _, _, _, _, _, _, .orElse ho h₁ h₂ hf hm, hne =>
    have h := noEscape_else hne
    .orElse ho (Lenient.HasType.strict h₁ h.1) (Lenient.HasType.strict h₂ h.2) (strictFits hf h.2)
      (Lenient.HasType.strict (allowed := false) hm hne)
  | _, _, _, _, _, _, .form hk hm, hne => .form hk (Lenient.HasType.strict (allowed := false) hm hne)
  | _, _, _, _, _, _, .letIn hwf hi hfit hb, hne =>
    have h := both hne
    .letIn hwf (Lenient.HasType.strict hi h.1) (strictFits hfit h.1)
      (Lenient.HasType.strict hb h.2)
  | _, _, _, _, _, _, .varIn hwf hi hfit hb, hne =>
    have h := both hne
    .varIn hwf (Lenient.HasType.strict hi h.1) (strictFits hfit h.1)
      (Lenient.HasType.strict hb h.2)
  | _, _, _, .assign ⟨_, _⟩ _, _, _, .assign hp he hfit, hne =>
    have h := both hne
    .assign (Lenient.PlaceFits.strict hp (both h.1).2) (Lenient.HasType.strict he h.2)
      (strictFits hfit h.2)
  | _, _, _, _, _, _, .seq ha hfit hb, hne =>
    have h := both hne
    .seq (Lenient.HasType.strict ha h.1) (strictFits hfit h.1) (Lenient.HasType.strict hb h.2)
  | _, _, _, _, _, _, .if hwf hc hfc ha hfa hb hfb, hne =>
    have h := both hne
    have h' := both h.1
    .if hwf (Lenient.HasType.strict hc h'.1) (strictFits hfc h'.1)
      (Lenient.HasType.strict ha h'.2) (strictFits hfa h'.2)
      (Lenient.HasType.strict hb h.2) (strictFits hfb h.2)
  | _, _, _, _, _, _, .match hwf he ht harms, hne =>
    have h := both hne
    .match hwf (Lenient.HasType.strict he h.1) ht (Lenient.ArmsFit.strict harms h.2)
  | _, _, _, _, _, _, .for hwf he hb hfit, hne =>
    have h := both hne
    .for hwf (Lenient.HasType.strict he h.1) (Lenient.HasType.strict hb h.2) (strictFits hfit h.2)
  | _, _, _, _, _, _, .raise hE he hfit, hne =>
    .raise hE (Lenient.HasType.strict he hne) (strictFits hfit hne)
  | _, _, _, _, _, _, .try he, hne => .try (Lenient.HasType.strict he hne)
  | _, _, _, _, _, _, .tryCatch hwfE hwf he hfe hh hfh, hne =>
    have h := both hne
    .tryCatch hwfE hwf (Lenient.HasType.strict he h.1) (strictFits hfe h.1)
      (Lenient.HasType.strict hh h.2) (strictFits hfh h.2)
  | _, _, _, _, _, _, .while hc hfc hb hfb, hne =>
    have h := both hne
    .while (Lenient.HasType.strict hc h.1) (strictFits hfc h.1) (Lenient.HasType.strict hb h.2)
      (strictFits hfb h.2)
  | _, _, _, _, _, _, .loopBreaks hb hfb, hne =>
    .loopBreaks (Lenient.HasType.strict hb hne) (strictFits hfb hne)
  | _, _, _, _, _, _, .loopForever hb hfb, hne =>
    .loopForever (Lenient.HasType.strict hb hne) (strictFits hfb hne)
  | _, _, _, _, _, _, .break h, _ => .break h
  | _, _, _, _, _, _, .continue h, _ => .continue h
  | _, _, _, _, _, _, .return he hfit, hne =>
    .return (Lenient.HasType.strict he hne) (strictFits hfit hne)
  | _, _, _, _, _, _, .perform hne' hop hA hB hm he hfit, hne =>
    .perform hne' hop hA hB hm (Lenient.HasType.strict he hne) (strictFits hfit hne)
  | _, _, _, _, _, _, .resume hr hB hR he hfit, hne =>
    .resume hr hB hR (Lenient.HasType.strict he hne) (strictFits hfit hne)
  | _, _, _, _, _, _, .withH hE heff hh hr hfs hb hops, hne =>
    have h := both hne
    .withH hE heff (Lenient.HasType.strict hh h.1) hr hfs (Lenient.HasType.strict hb h.2) hops
  | _, _, _, _, _, _, .withControl hE heff hh hr hfs hb hfit hg hops, hne =>
    have h := both hne
    .withControl hE heff (Lenient.HasType.strict hh h.1) hr hfs (Lenient.HasType.strict hb h.2)
      (strictFits hfit h.2) hg hops

theorem Lenient.ExprsFit.strict :
    ∀ {N Γ fx es τs}, Lenient.ExprsFit D scope vs N Γ fx es τs →
      exprsNoEscape D N es = true → Stilt.ExprsFit D scope Γ fx es τs
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, .cons he hfit hes, hne =>
    have h := both hne
    .cons (Lenient.HasType.strict he h.1) (strictFits hfit h.1) (Lenient.ExprsFit.strict hes h.2)

theorem Lenient.FieldsFit.strict :
    ∀ {N Γ fx fields declared}, Lenient.FieldsFit D scope vs N Γ fx fields declared →
      fieldsNoEscape D N fields = true → Stilt.FieldsFit D scope Γ fx fields declared
  | _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, .cons hl he hfit hfs, hne =>
    have h := both hne
    .cons hl (Lenient.HasType.strict he h.1) (strictFits hfit h.1)
      (Lenient.FieldsFit.strict hfs h.2)

theorem Lenient.ArgsFit.strict :
    ∀ {N passing Γ fx args ps}, Lenient.ArgsFit D scope vs N passing Γ fx args ps →
      argsNoEscape D N passing args = true → Stilt.ArgsFit D scope Γ fx args ps
  | _, _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, _, .value hm hp he hfit has, hne =>
    have h := both hne
    have he' : _ = true := hp ▸ h.1
    .value hm (Lenient.HasType.strict he h.1) (strictFits hfit he')
      (Lenient.ArgsFit.strict has h.2)
  | _, _, _, _, _, _, .passed hm _ he hfit has, hne =>
    have h := both hne
    .value hm (Lenient.HasType.strict he h.1) hfit (Lenient.ArgsFit.strict has h.2)
  | _, _, _, _, .inout ⟨_, _⟩ :: _, _, .inout hp has, hne =>
    have h := both hne
    .inout (Lenient.PlaceFits.strict hp (both h.1).2) (Lenient.ArgsFit.strict has h.2)

theorem Lenient.PlaceFits.strict :
    ∀ {N Γ fx p τ}, Lenient.PlaceFits D scope vs N Γ fx p τ →
      pathNoEscape D N p.path = true → Stilt.PlaceFits D scope Γ fx p τ
  | _, _, _, _, _, .mk hl hp, hne => .mk hl (Lenient.PathFits.strict hp hne)

theorem Lenient.PathFits.strict :
    ∀ {N Γ fx σ path τ}, Lenient.PathFits D scope vs N Γ fx σ path τ →
      pathNoEscape D N path = true → Stilt.PathFits D scope Γ fx σ path τ
  | _, _, _, _, _, _, .nil, _ => .nil
  | _, _, _, _, _, _, .field hr hl hf hp, hne => .field hr hl hf (Lenient.PathFits.strict hp hne)
  | _, _, _, _, _, _, .elem hf hp, hne => .elem hf (Lenient.PathFits.strict hp hne)
  | _, _, _, _, _, _, .index hi hfit hp, hne =>
    have h := both hne
    .index (Lenient.HasType.strict hi h.1) (strictFits hfit h.1) (Lenient.PathFits.strict hp h.2)

theorem Lenient.ArmsFit.strict :
    ∀ {N Γ fx arms σ τ}, Lenient.ArmsFit D scope vs N Γ fx arms σ τ →
      armsNoEscape D N arms = true → Stilt.ArmsFit D scope Γ fx arms σ τ
  | _, _, _, _, _, _, .nil, _ => .nil
  | _, _, _, ⟨_, _, _, _⟩ :: _, _, _, .cons hc hlen hnd hg hb hfit harms, hne =>
    have h := both hne
    have h' := both h.1
    .cons hc hlen hnd (Lenient.GuardFits.strict hg h'.1) (Lenient.HasType.strict hb h'.2)
      (strictFits hfit h'.2) (Lenient.ArmsFit.strict harms h.2)

theorem Lenient.GuardFits.strict :
    ∀ {N Γ fx g}, Lenient.GuardFits D scope vs N Γ fx g →
      guardNoEscape D N g = true → Stilt.GuardFits D scope Γ fx g
  | _, _, _, _, .none, _ => .none
  | _, _, _, _, .some hg hfit, hne =>
    .some (Lenient.HasType.strict hg hne) (strictFits hfit hne)

end

mutual

/-- The checker accepts every expression whose every row checks, whatever the
parameters in scope. -/
theorem HasType.lenient :
    ∀ {N Γ fx e τ}, HasType D scope Γ fx e τ → Lenient.HasType D scope vs N Γ fx e τ
  | _, _, _, _, _, .var h => .var h
  | _, _, _, _, _, .int h => .int h
  | _, _, _, _, _, .bool => .bool
  | _, _, _, _, _, .unit => .unit
  | _, _, _, _, _, .record hr hl hw hperm hfs => .record hr hl hw hperm (FieldsFit.lenient hfs)
  | _, _, _, _, _, .variant ht hl hw hc hes => .variant ht hl hw hc (ExprsFit.lenient hes)
  | _, _, _, _, _, .list hwf hes => .list hwf (ExprsFit.lenient hes)
  | _, _, _, _, _, .op ho hes hk hb => .op ho (ExprsFit.lenient hes) hk hb
  | _, _, _, _, _, .view ho hes => .view ho (ExprsFit.lenient hes)
  | _, _, _, _, _, .field he hr hl hf => .field (HasType.lenient he) hr hl hf
  | _, _, _, _, _, .elem he hf => .elem (HasType.lenient he) hf
  | _, _, _, _, _, .index he hi hfit => .index (HasType.lenient he) (HasType.lenient hi) (.inl hfit)
  | _, _, _, _, _, .fnRef hf hlen hinst hres hwf hpass htys => .fnRef hf hlen hinst hres hwf hpass htys
  | _, _, _, _, _, .method ht hm hc hwf hl hf => .method ht hm hc hwf hl hf
  | _, _, _, _, _, .closure hnd hpt hwf hb hfit =>
    .closure hnd hpt hwf (HasType.lenient hb) (.inl hfit)
  | _, _, _, _, _, .call hc ha hall => .call (HasType.lenient hc) (ArgsFit.lenient ha) hall
  | _, _, _, _, _, .letIn hwf hi hfit hb =>
    .letIn hwf (HasType.lenient hi) (.inl hfit) (HasType.lenient hb)
  | _, _, _, _, _, .varIn hwf hi hfit hb =>
    .varIn hwf (HasType.lenient hi) (.inl hfit) (HasType.lenient hb)
  | _, _, _, _, _, .held hnd hwf hes hb hv =>
    .held hnd hwf (ExprsFit.lenient hes) (HasType.lenient hb) hv
  | _, _, _, _, _, .letElse hr hx hm => .letElse hr (HasType.lenient hx) (HasType.lenient hm)
  | _, _, _, _, _, .orElse ho h₁ h₂ hf hm =>
    .orElse ho (HasType.lenient h₁) (HasType.lenient h₂) (.inl hf) (HasType.lenient hm)
  | _, _, _, _, _, .form hk hm => .form hk (HasType.lenient hm)
  | _, _, _, _, _, .assign hp he hfit =>
    .assign (PlaceFits.lenient hp) (HasType.lenient he) (.inl hfit)
  | _, _, _, _, _, .seq ha hfit hb => .seq (HasType.lenient ha) (.inl hfit) (HasType.lenient hb)
  | _, _, _, _, _, .if hwf hc hfc ha hfa hb hfb =>
    .if hwf (HasType.lenient hc) (.inl hfc) (HasType.lenient ha) (.inl hfa)
      (HasType.lenient hb) (.inl hfb)
  | _, _, _, _, _, .match hwf he ht harms =>
    .match hwf (HasType.lenient he) ht (ArmsFit.lenient harms)
  | _, _, _, _, _, .for hwf he hb hfit =>
    .for hwf (HasType.lenient he) (HasType.lenient hb) (.inl hfit)
  | _, _, _, _, _, .raise hE he hfit => .raise hE (HasType.lenient he) (.inl hfit)
  | _, _, _, _, _, .try he => .try (HasType.lenient he)
  | _, _, _, _, _, .tryCatch hwfE hwf he hfe hh hfh =>
    .tryCatch hwfE hwf (HasType.lenient he) (.inl hfe) (HasType.lenient hh) (.inl hfh)
  | _, _, _, _, _, .while hc hfc hb hfb =>
    .while (HasType.lenient hc) (.inl hfc) (HasType.lenient hb) (.inl hfb)
  | _, _, _, _, _, .loopBreaks hb hfb => .loopBreaks (HasType.lenient hb) (.inl hfb)
  | _, _, _, _, _, .loopForever hb hfb => .loopForever (HasType.lenient hb) (.inl hfb)
  | _, _, _, _, _, .break h => .break h
  | _, _, _, _, _, .continue h => .continue h
  | _, _, _, _, _, .return he hfit => .return (HasType.lenient he) (.inl hfit)
  | _, _, _, _, _, .perform hne hop hA hB hm he hfit =>
    .perform hne hop hA hB hm (HasType.lenient he) (.inl hfit)
  | _, _, _, _, _, .resume hr hB hR he hfit => .resume hr hB hR (HasType.lenient he) (.inl hfit)
  | _, _, _, _, _, .withH hE heff hh hr hfs hb hops =>
    .withH hE heff (HasType.lenient hh) hr hfs (HasType.lenient hb) hops
  | _, _, _, _, _, .withControl hE heff hh hr hfs hb hfit hg hops =>
    .withControl hE heff (HasType.lenient hh) hr hfs (HasType.lenient hb) (.inl hfit) hg hops

theorem ExprsFit.lenient :
    ∀ {N Γ fx es τs}, ExprsFit D scope Γ fx es τs → Lenient.ExprsFit D scope vs N Γ fx es τs
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons he hfit hes =>
    .cons (HasType.lenient he) (.inl hfit) (ExprsFit.lenient hes)

theorem FieldsFit.lenient :
    ∀ {N Γ fx fields declared}, FieldsFit D scope Γ fx fields declared →
      Lenient.FieldsFit D scope vs N Γ fx fields declared
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons hl he hfit hfs =>
    .cons hl (HasType.lenient he) (.inl hfit) (FieldsFit.lenient hfs)

theorem ArgsFit.lenient :
    ∀ {N passing Γ fx args ps}, ArgsFit D scope Γ fx args ps →
      Lenient.ArgsFit D scope vs N passing Γ fx args ps
  | _, _, _, _, _, _, .nil => .nil
  | _, passing, _, _, _, _, .value hm he hfit has =>
    if hp : passing.headD false = true then
      .passed hm hp (HasType.lenient he) hfit (ArgsFit.lenient has)
    else
      .value hm (by simpa using hp) (HasType.lenient he) (.inl hfit) (ArgsFit.lenient has)
  | _, _, _, _, _, _, .inout hp has => .inout (PlaceFits.lenient hp) (ArgsFit.lenient has)

theorem PlaceFits.lenient :
    ∀ {N Γ fx p τ}, PlaceFits D scope Γ fx p τ → Lenient.PlaceFits D scope vs N Γ fx p τ
  | _, _, _, _, _, .mk hl hp => .mk hl (PathFits.lenient hp)

theorem PathFits.lenient :
    ∀ {N Γ fx σ path τ}, PathFits D scope Γ fx σ path τ →
      Lenient.PathFits D scope vs N Γ fx σ path τ
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .field hr hl hf hp => .field hr hl hf (PathFits.lenient hp)
  | _, _, _, _, _, _, .elem hf hp => .elem hf (PathFits.lenient hp)
  | _, _, _, _, _, _, .index hi hfit hp =>
    .index (HasType.lenient hi) (.inl hfit) (PathFits.lenient hp)

theorem ArmsFit.lenient :
    ∀ {N Γ fx arms σ τ}, ArmsFit D scope Γ fx arms σ τ →
      Lenient.ArmsFit D scope vs N Γ fx arms σ τ
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, _, .cons hc hlen hnd hg hb hfit harms =>
    .cons hc hlen hnd (GuardFits.lenient hg) (HasType.lenient hb) (.inl hfit)
      (ArmsFit.lenient harms)

theorem GuardFits.lenient :
    ∀ {N Γ fx g}, GuardFits D scope Γ fx g → Lenient.GuardFits D scope vs N Γ fx g
  | _, _, _, _, .none => .none
  | _, _, _, _, .some hg hfit => .some (HasType.lenient hg) (.inl hfit)

end

end

end Stilt
