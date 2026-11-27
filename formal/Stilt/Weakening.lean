import Stilt.Typing

/-!
# Weakening

The typing judgment is preserved by bindings added below a context, which its
own bindings hide or which nothing names, and by a larger row scope, one whose
relations hold of more variables. `Stilt.WellTyped` uses the second to compare
the rules of effects.paired-row-variables and effects.passing-to-paired-variables with the ones they amend.
-/

namespace Stilt

section Weakening

variable {D : Decls} {s : RowScope}

namespace Ctx

theorem lookup_append {Γ : Ctx} (Δ : Ctx) {x : Name} {b : Binding}
    (h : Γ.lookup x = some b) : (Γ ++ Δ).lookup x = some b := by
  simp [lookup, List.lookup_append, show List.lookup x Γ = some b from h]

theorem freeze_append (Γ Δ : Ctx) : (Γ ++ Δ).freeze = Γ.freeze ++ Δ.freeze :=
  List.map_append

theorem params_append (Γ Δ : Ctx) (ps : List Param) :
    (Γ ++ Δ).params ps = Γ.params ps ++ Δ := by
  induction ps generalizing Γ with
  | nil => rfl
  | cons p ps ih => exact ih (Γ.bind p.name _)

theorem bindAll_append (Γ Δ : Ctx) (xs : List Name) (τs : List Ty) :
    (Γ ++ Δ).bindAll xs τs = Γ.bindAll xs τs ++ Δ := by
  unfold bindAll
  generalize xs.zip τs = pairs
  induction pairs generalizing Γ with
  | nil => rfl
  | cons xτ pairs ih => exact ih (Γ.bind xτ.1 _)

/-- The names of a `when` bind above every binding of the context. -/
theorem holding_append (Δ : Ctx) : ∀ (ns : List (Name × Ty)) (Γ : Ctx),
    (Γ ++ Δ).holding ns = Γ.holding ns ++ Δ
  | [], _ => rfl
  | p :: ns, Γ => holding_append Δ ns ((p.1, ⟨p.2, true⟩) :: Γ)

end Ctx

mutual

/-- Weakening: bindings added below a context, which its own bindings hide or
which nothing names, keep a derivation valid. -/
theorem HasType.weaken (Δ : Ctx) :
    ∀ {Γ fx e τ}, HasType D s Γ fx e τ → HasType D s (Γ ++ Δ) fx e τ
  | _, _, _, _, .var h => .var (Ctx.lookup_append Δ h)
  | _, _, _, _, .int h => .int h
  | _, _, _, _, .bool => .bool
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .record hr hl hw hperm hfs => .record hr hl hw hperm (FieldsFit.weaken Δ hfs)
  | _, _, _, _, .variant ht hl hw hc hes => .variant ht hl hw hc (ExprsFit.weaken Δ hes)
  | _, _, _, _, .list hwf hes => .list hwf (ExprsFit.weaken Δ hes)
  | _, _, _, _, .op ho hes hk hb => .op ho (ExprsFit.weaken Δ hes) hk hb
  | _, _, _, _, .view ho hes => .view ho (ExprsFit.weaken Δ hes)
  | _, _, _, _, .field he hr hl hf => .field (HasType.weaken Δ he) hr hl hf
  | _, _, _, _, .elem he hf => .elem (HasType.weaken Δ he) hf
  | _, _, _, _, .index he hi hfit => .index (HasType.weaken Δ he) (HasType.weaken Δ hi) hfit
  | _, _, _, _, .fnRef hf hlen hinst hres hwf hpass htys => .fnRef hf hlen hinst hres hwf hpass htys
  | _, _, _, _, .method ht hm hc hwf hf => .method ht hm hc hwf hf
  | _, _, _, _, .closure hnd hpt hwf hb hfit =>
    .closure hnd hpt hwf
      (by rw [Ctx.freeze_append, Ctx.params_append]; exact HasType.weaken Δ.freeze hb) hfit
  | _, _, _, _, .call hf has hcall => .call (HasType.weaken Δ hf) (ArgsFit.weaken Δ has) hcall
  | _, _, _, _, .letIn hwf he hfit hb =>
    .letIn hwf (HasType.weaken Δ he) hfit (HasType.weaken Δ hb)
  | _, _, _, _, .varIn hwf he hfit hb =>
    .varIn hwf (HasType.weaken Δ he) hfit (HasType.weaken Δ hb)
  | _, _, _, _, .held (ns := ns) hnd hwf hes hb hv =>
    .held hnd hwf (ExprsFit.weaken Δ hes) (Ctx.holding_append Δ ns _ ▸ HasType.weaken Δ hb) hv
  | _, _, _, _, .letElse hr hx hm => .letElse hr (HasType.weaken Δ hx) (HasType.weaken Δ hm)
  | _, _, _, _, .orElse ho h₁ h₂ hf hm =>
    .orElse ho (HasType.weaken Δ h₁) (HasType.weaken Δ h₂) hf (HasType.weaken Δ hm)
  | _, _, _, _, .assign hp he hfit => .assign (PlaceFits.weaken Δ hp) (HasType.weaken Δ he) hfit
  | _, _, _, _, .seq ha hfit hb => .seq (HasType.weaken Δ ha) hfit (HasType.weaken Δ hb)
  | _, _, _, _, .if hwf hc hfc ha hfa hb hfb =>
    .if hwf (HasType.weaken Δ hc) hfc (HasType.weaken Δ ha) hfa (HasType.weaken Δ hb) hfb
  | _, _, _, _, .match hwf he ht harms =>
    .match hwf (HasType.weaken Δ he) ht (ArmsFit.weaken Δ harms)
  | _, _, _, _, .for hwf he hb hfit => .for hwf (HasType.weaken Δ he) (HasType.weaken Δ hb) hfit
  | _, _, _, _, .raise hE he hfit => .raise hE (HasType.weaken Δ he) hfit
  | _, _, _, _, .try he => .try (HasType.weaken Δ he)
  | _, _, _, _, .tryCatch hwfE hwf he hfe hh hfh =>
    .tryCatch hwfE hwf (HasType.weaken Δ he) hfe (HasType.weaken Δ hh) hfh
  | _, _, _, _, .while hc hfc hb hfb => .while (HasType.weaken Δ hc) hfc (HasType.weaken Δ hb) hfb
  | _, _, _, _, .loopBreaks hb hfb => .loopBreaks (HasType.weaken Δ hb) hfb
  | _, _, _, _, .loopForever hb hfb => .loopForever (HasType.weaken Δ hb) hfb
  | _, _, _, _, .break h => .break h
  | _, _, _, _, .continue h => .continue h
  | _, _, _, _, .return he hfit => .return (HasType.weaken Δ he) hfit
  | _, _, _, _, .perform hne hop hA hB hm he hfit =>
    .perform hne hop hA hB hm (HasType.weaken Δ he) hfit
  | _, _, _, _, .resume hr hB hR he hfit => .resume hr hB hR (HasType.weaken Δ he) hfit
  | _, _, _, _, .withH hne heff hh hr hfs hb hops =>
    .withH hne heff (HasType.weaken Δ hh) hr hfs (HasType.weaken Δ hb) hops
  | _, _, _, _, .withControl hne heff hh hr hfs hb hfit hg hops =>
    .withControl hne heff (HasType.weaken Δ hh) hr hfs (HasType.weaken Δ hb) hfit hg hops

theorem ExprsFit.weaken (Δ : Ctx) :
    ∀ {Γ fx es τs}, ExprsFit D s Γ fx es τs → ExprsFit D s (Γ ++ Δ) fx es τs
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons he hfit hes => .cons (HasType.weaken Δ he) hfit (ExprsFit.weaken Δ hes)

theorem FieldsFit.weaken (Δ : Ctx) :
    ∀ {Γ fx fields declared}, FieldsFit D s Γ fx fields declared →
      FieldsFit D s (Γ ++ Δ) fx fields declared
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hl he hfit hfs =>
    .cons hl (HasType.weaken Δ he) hfit (FieldsFit.weaken Δ hfs)

theorem ArgsFit.weaken (Δ : Ctx) :
    ∀ {Γ fx args ps}, ArgsFit D s Γ fx args ps → ArgsFit D s (Γ ++ Δ) fx args ps
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .value hm he hfit has =>
    .value hm (HasType.weaken Δ he) hfit (ArgsFit.weaken Δ has)
  | _, _, _, _, .inout hp has => .inout (PlaceFits.weaken Δ hp) (ArgsFit.weaken Δ has)

theorem PlaceFits.weaken (Δ : Ctx) :
    ∀ {Γ fx p τ}, PlaceFits D s Γ fx p τ → PlaceFits D s (Γ ++ Δ) fx p τ
  | _, _, _, _, .mk hl hp => .mk (Ctx.lookup_append Δ hl) (PathFits.weaken Δ hp)

theorem PathFits.weaken (Δ : Ctx) :
    ∀ {Γ fx σ path τ}, PathFits D s Γ fx σ path τ → PathFits D s (Γ ++ Δ) fx σ path τ
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .field hr hl hf hp => .field hr hl hf (PathFits.weaken Δ hp)
  | _, _, _, _, _, .elem hf hp => .elem hf (PathFits.weaken Δ hp)
  | _, _, _, _, _, .index hi hfit hp =>
    .index (HasType.weaken Δ hi) hfit (PathFits.weaken Δ hp)

theorem ArmsFit.weaken (Δ : Ctx) :
    ∀ {Γ fx arms σ τ},
      ArmsFit D s Γ fx arms σ τ → ArmsFit D s (Γ ++ Δ) fx arms σ τ
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons hc hlen hnd hg hb hfit harms =>
    .cons hc hlen hnd (by rw [Ctx.bindAll_append]; exact GuardFits.weaken Δ hg)
      (by rw [Ctx.bindAll_append]; exact HasType.weaken Δ hb) hfit (ArmsFit.weaken Δ harms)

theorem GuardFits.weaken (Δ : Ctx) :
    ∀ {Γ fx g}, GuardFits D s Γ fx g → GuardFits D s (Γ ++ Δ) fx g
  | _, _, _, .none => .none
  | _, _, _, .some hg hfit => .some (HasType.weaken Δ hg) hfit

end

end Weakening

section Monotone

variable {D : Decls} {s s' : RowScope}

theorem PassesOnPairs.of_le {d : FnDecl} {σ : RowSubst} (h : PassesOnPairs s d σ)
    (hs : s.Le s') : PassesOnPairs s' d σ :=
  fun v E ρ r hp hl hr => hs.passOn r _ (h v E ρ r hp hl hr)

theorem CallAllowed.of_le {fx : Effects} {σ : Row} (h : CallAllowed s fx σ) (hs : s.Le s') :
    CallAllowed s' fx σ :=
  ⟨h.within, h.marked, fun hc v hv =>
    let ⟨E, hE, hp⟩ := h.paired hc v hv
    ⟨E, hE, hs.pairs v E hp⟩, h.resume⟩

theorem HandlerFits.of_le {fx : Effects} {eff : EffectDecl} {fields : List (Name × Ty)}
    {c : Option Ty} (h : HandlerFits s fx eff fields c) (hs : s.Le s') :
    HandlerFits s' fx eff fields c := fun o A B ho =>
  let ⟨ρ, h₁, h₂, h₃⟩ := h o A B ho
  ⟨ρ, h₁, h₂, h₃.of_le hs⟩

theorem Satisfies.of_le {τ : Ty} {B : Name} (h : Satisfies D s τ B) (hs : s.Le s') :
    Satisfies D s' τ B :=
  h.imp (fun ⟨p, hp, h⟩ => ⟨p, hs.types p hp, h⟩)
    (Or.imp id fun ⟨t, ht, hi⟩ => ⟨t, ht, hi.of_types hs.types⟩)

theorem MethodAt.of_le {τ : Ty} {Tr : Name} (h : MethodAt D s τ Tr) (hs : s.Le s') :
    MethodAt D s' τ Tr :=
  h.imp (fun ⟨hp, hsat⟩ => ⟨hp, hsat.of_le hs⟩) id

theorem TypeArgsFit.of_le {ps : List TypeParam} {τs : List Ty} (h : TypeArgsFit D s ps τs)
    (hs : s.Le s') : TypeArgsFit D s' ps τs := by
  unfold TypeArgsFit at h ⊢
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons ⟨hx.1, hx.2.1.of_le hs, fun B hB => (hx.2.2 B hB).of_le hs⟩ ih

/-- The scope without its type parameters grows with the scope. -/
theorem RowScope.Le.withoutTypes (hs : s.Le s') :
    ({ s with types := [] } : RowScope).Le { s' with types := [] } :=
  ⟨hs.vars, hs.pairs, hs.passOn, fun _ h => h⟩

mutual

/-- A larger scope keeps a derivation valid. -/
theorem HasType.of_le (hs : s.Le s') :
    ∀ {Γ fx e τ}, HasType D s Γ fx e τ → HasType D s' Γ fx e τ
  | _, _, _, _, .var h => .var h
  | _, _, _, _, .int h => .int h
  | _, _, _, _, .bool => .bool
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .record hr hl hw hperm hfs => .record hr hl (fun τ h => (hw τ h).of_le hs) hperm (FieldsFit.of_le hs hfs)
  | _, _, _, _, .variant ht hl hw hc hes => .variant ht hl (fun τ h => (hw τ h).of_le hs) hc (ExprsFit.of_le hs hes)
  | _, _, _, _, .list hwf hes => .list (hwf.of_le hs) (ExprsFit.of_le hs hes)
  | _, _, _, _, .op ho hes hk hb => .op ho (ExprsFit.of_le hs hes) hk (hb.of_types hs.types)
  | _, _, _, _, .view ho hes => .view ho (ExprsFit.of_le hs hes)
  | _, _, _, _, .field he hr hl hf => .field (HasType.of_le hs he) hr hl hf
  | _, _, _, _, .elem he hf => .elem (HasType.of_le hs he) hf
  | _, _, _, _, .index he hi hfit => .index (HasType.of_le hs he) (HasType.of_le hs hi) hfit
  | _, _, _, _, .fnRef hf hlen hinst hres hwf hpass htys =>
    .fnRef hf hlen hinst hres (hwf.of_le hs) (hpass.of_le hs) (htys.of_le hs)
  | _, _, _, _, .method ht hm hc hwf hf => .method ht hm hc (hwf.of_le hs) (hf.of_le hs)
  | _, _, _, _, .closure hnd hpt hwf hb hfit =>
    .closure hnd hpt (hwf.of_le hs) (HasType.of_le hs hb) hfit
  | _, _, _, _, .call hf has hcall =>
    .call (HasType.of_le hs hf) (ArgsFit.of_le hs has) (hcall.of_le hs)
  | _, _, _, _, .letIn hwf he hfit hb =>
    .letIn (hwf.of_le hs) (HasType.of_le hs he) hfit (HasType.of_le hs hb)
  | _, _, _, _, .varIn hwf he hfit hb =>
    .varIn (hwf.of_le hs) (HasType.of_le hs he) hfit (HasType.of_le hs hb)
  | _, _, _, _, .held hnd hwf hes hb hv =>
    .held hnd (fun p hp => (hwf p hp).of_le hs) (ExprsFit.of_le hs hes) (HasType.of_le hs hb) hv
  | _, _, _, _, .letElse hr hx hm => .letElse hr (HasType.of_le hs hx) (HasType.of_le hs hm)
  | _, _, _, _, .orElse ho h₁ h₂ hf hm =>
    .orElse ho (HasType.of_le hs h₁) (HasType.of_le hs h₂) hf (HasType.of_le hs hm)
  | _, _, _, _, .assign hp he hfit => .assign (PlaceFits.of_le hs hp) (HasType.of_le hs he) hfit
  | _, _, _, _, .seq ha hfit hb => .seq (HasType.of_le hs ha) hfit (HasType.of_le hs hb)
  | _, _, _, _, .if hwf hc hfc ha hfa hb hfb =>
    .if (hwf.of_le hs) (HasType.of_le hs hc) hfc (HasType.of_le hs ha) hfa
      (HasType.of_le hs hb) hfb
  | _, _, _, _, .match hwf he ht harms =>
    .match (hwf.of_le hs) (HasType.of_le hs he) ht (ArmsFit.of_le hs harms)
  | _, _, _, _, .for hwf he hb hfit =>
    .for (hwf.of_le hs) (HasType.of_le hs he) (HasType.of_le hs hb) hfit
  | _, _, _, _, .raise hE he hfit => .raise hE (HasType.of_le hs he) hfit
  | _, _, _, _, .try he => .try (HasType.of_le hs he)
  | _, _, _, _, .tryCatch hwfE hwf he hfe hh hfh =>
    .tryCatch (hwfE.of_le hs.withoutTypes) (hwf.of_le hs) (HasType.of_le hs he) hfe
      (HasType.of_le hs hh) hfh
  | _, _, _, _, .while hc hfc hb hfb => .while (HasType.of_le hs hc) hfc (HasType.of_le hs hb) hfb
  | _, _, _, _, .loopBreaks hb hfb => .loopBreaks (HasType.of_le hs hb) hfb
  | _, _, _, _, .loopForever hb hfb => .loopForever (HasType.of_le hs hb) hfb
  | _, _, _, _, .break h => .break h
  | _, _, _, _, .continue h => .continue h
  | _, _, _, _, .return he hfit => .return (HasType.of_le hs he) hfit
  | _, _, _, _, .perform hne hop hA hB hm he hfit =>
    .perform hne hop hA hB hm (HasType.of_le hs he) hfit
  | _, _, _, _, .resume hr hB hR he hfit => .resume hr hB hR (HasType.of_le hs he) hfit
  | _, _, _, _, .withH hne heff hh hr hfs hb hops =>
    .withH hne heff (HasType.of_le hs hh) hr (hfs.of_le hs) (HasType.of_le hs hb) hops
  | _, _, _, _, .withControl hne heff hh hr hfs hb hfit hg hops =>
    .withControl hne heff (HasType.of_le hs hh) hr (hfs.of_le hs) (HasType.of_le hs hb) hfit hg hops

theorem ExprsFit.of_le (hs : s.Le s') :
    ∀ {Γ fx es τs}, ExprsFit D s Γ fx es τs → ExprsFit D s' Γ fx es τs
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons he hfit hes => .cons (HasType.of_le hs he) hfit (ExprsFit.of_le hs hes)

theorem FieldsFit.of_le (hs : s.Le s') :
    ∀ {Γ fx fields declared}, FieldsFit D s Γ fx fields declared →
      FieldsFit D s' Γ fx fields declared
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons hl he hfit hfs =>
    .cons hl (HasType.of_le hs he) hfit (FieldsFit.of_le hs hfs)

theorem ArgsFit.of_le (hs : s.Le s') :
    ∀ {Γ fx args ps}, ArgsFit D s Γ fx args ps → ArgsFit D s' Γ fx args ps
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .value hm he hfit has =>
    .value hm (HasType.of_le hs he) hfit (ArgsFit.of_le hs has)
  | _, _, _, _, .inout hp has => .inout (PlaceFits.of_le hs hp) (ArgsFit.of_le hs has)

theorem PlaceFits.of_le (hs : s.Le s') :
    ∀ {Γ fx p τ}, PlaceFits D s Γ fx p τ → PlaceFits D s' Γ fx p τ
  | _, _, _, _, .mk hl hp => .mk hl (PathFits.of_le hs hp)

theorem PathFits.of_le (hs : s.Le s') :
    ∀ {Γ fx σ path τ}, PathFits D s Γ fx σ path τ → PathFits D s' Γ fx σ path τ
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .field hr hl hf hp => .field hr hl hf (PathFits.of_le hs hp)
  | _, _, _, _, _, .elem hf hp => .elem hf (PathFits.of_le hs hp)
  | _, _, _, _, _, .index hi hfit hp => .index (HasType.of_le hs hi) hfit (PathFits.of_le hs hp)

theorem ArmsFit.of_le (hs : s.Le s') :
    ∀ {Γ fx arms σ τ}, ArmsFit D s Γ fx arms σ τ → ArmsFit D s' Γ fx arms σ τ
  | _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, .cons hc hlen hnd hg hb hfit harms =>
    .cons hc hlen hnd (GuardFits.of_le hs hg) (HasType.of_le hs hb) hfit (ArmsFit.of_le hs harms)

theorem GuardFits.of_le (hs : s.Le s') :
    ∀ {Γ fx g}, GuardFits D s Γ fx g → GuardFits D s' Γ fx g
  | _, _, _, .none => .none
  | _, _, _, .some hg hfit => .some (HasType.of_le hs hg) hfit

end

end Monotone

end Stilt
