import Stilt.Free
import Stilt.Typing

/-!
# Strengthening

The typing judgment reads a context only at the variables an expression uses
(`Expr.free`): a context that gives each of them the same binding types the
expression alike. So a closure's body types in the context of the variables
it captures alone (expressions.capture), as a closure value holds them.
-/

namespace Stilt

namespace Ctx

theorem lookup_bind_self (Γ : Ctx) (x : Name) (b : Binding) : (Γ.bind x b).lookup x = some b := by
  simp [lookup, bind]

theorem lookup_bind_ne (Γ : Ctx) {x y : Name} (b : Binding) (h : y ≠ x) :
    (Γ.bind x b).lookup y = Γ.lookup y := by
  simp [lookup, bind, List.lookup, beq_false_of_ne h]

/-- Two contexts that agree on the variables `P` names but `x` agree on them all
once `x` is bound alike in both. -/
theorem agree_bind {Γ Γ' : Ctx} {x : Name} (b : Binding) {P : Name → Prop}
    (h : ∀ y, y ≠ x → P y → Γ.lookup y = Γ'.lookup y) :
    ∀ y, P y → (Γ.bind x b).lookup y = (Γ'.bind x b).lookup y := by
  intro y hy
  by_cases hx : y = x
  · subst hx
    simp [lookup_bind_self]
  · rw [lookup_bind_ne _ _ hx, lookup_bind_ne _ _ hx]
    exact h y hx hy

theorem lookup_freeze (Γ : Ctx) (y : Name) :
    Γ.freeze.lookup y = (Γ.lookup y).map fun b => { b with mutable := false } := by
  induction Γ with
  | nil => rfl
  | cons p Γ ih =>
    obtain ⟨x, b⟩ := p
    by_cases h : y = x
    · subst h
      simp [freeze, lookup, List.lookup]
    · simp only [freeze, lookup, List.map_cons, List.lookup, beq_false_of_ne h] at ih ⊢
      exact ih

theorem agree_freeze {Γ Γ' : Ctx} {P : Name → Prop}
    (h : ∀ y, P y → Γ.lookup y = Γ'.lookup y) :
    ∀ y, P y → Γ.freeze.lookup y = Γ'.freeze.lookup y := fun y hy => by
  rw [lookup_freeze, lookup_freeze, h y hy]

theorem agree_params {P : Name → Prop} :
    ∀ (ps : List Param) {Γ Γ' : Ctx},
      (∀ y, (ps.any (·.name == y)) = false → P y → Γ.lookup y = Γ'.lookup y) →
      ∀ y, P y → (Γ.params ps).lookup y = (Γ'.params ps).lookup y
  | [], _, _, h => fun y hy => h y rfl hy
  | p :: ps, Γ, Γ', h => by
    show ∀ y, P y →
      ((Γ.bind p.name _).params ps).lookup y = ((Γ'.bind p.name _).params ps).lookup y
    refine agree_params ps fun y hy hP =>
      agree_bind _ (P := fun y => (ps.any (·.name == y)) = false ∧ P y)
        (fun z hz ⟨hps, hP⟩ => h z ?_ hP) y ⟨hy, hP⟩
    simp only [List.any_cons, Bool.or_eq_false_iff]
    exact ⟨by simpa using Ne.symm hz, hps⟩

theorem agree_holding {P : Name → Prop} :
    ∀ (ns : List (Name × Ty)) {Γ Γ' : Ctx},
      (∀ y, (ns.any (·.1 == y)) = false → P y → Γ.lookup y = Γ'.lookup y) →
      ∀ y, P y → (Γ.holding ns).lookup y = (Γ'.holding ns).lookup y
  | [], _, _, h => fun y hy => h y rfl hy
  | p :: ns, Γ, Γ', h => by
    show ∀ y, P y →
      ((Γ.bind p.1 _).holding ns).lookup y = ((Γ'.bind p.1 _).holding ns).lookup y
    refine agree_holding ns fun y hy hP =>
      agree_bind _ (P := fun y => (ns.any (·.1 == y)) = false ∧ P y)
        (fun z hz ⟨hps, hP⟩ => h z ?_ hP) y ⟨hy, hP⟩
    simp only [List.any_cons, Bool.or_eq_false_iff]
    exact ⟨by simpa using Ne.symm hz, hps⟩

theorem agree_bindAll {P : Name → Prop} :
    ∀ (xs : List Name) (τs : List Ty) {Γ Γ' : Ctx}, xs.length = τs.length →
      (∀ y, xs.contains y = false → P y → Γ.lookup y = Γ'.lookup y) →
      ∀ y, P y → (Γ.bindAll xs τs).lookup y = (Γ'.bindAll xs τs).lookup y
  | [], [], _, _, _, h => fun y hy => h y rfl hy
  | x :: xs, τ :: τs, Γ, Γ', hl, h => by
    show ∀ y, P y →
      ((Γ.bind x _).bindAll xs τs).lookup y = ((Γ'.bind x _).bindAll xs τs).lookup y
    refine agree_bindAll xs τs (by simpa using hl) fun y hy hP =>
      agree_bind _ (P := fun y => xs.contains y = false ∧ P y)
        (fun z hz ⟨hxs, hP⟩ => h z ?_ hP) y ⟨hy, hP⟩
    simp only [List.contains_cons, Bool.or_eq_false_iff]
    exact ⟨by simpa using hz, hxs⟩

end Ctx

/-- Two contexts give each variable that `uses` names the same binding. -/
def Ctx.AgreeOn (uses : Name → Bool) (Γ Γ' : Ctx) : Prop :=
  ∀ z, uses z = true → Γ.lookup z = Γ'.lookup z

theorem Ctx.AgreeOn.mono {u v : Name → Bool} {Γ Γ' : Ctx} (h : Ctx.AgreeOn u Γ Γ')
    (huv : ∀ z, v z = true → u z = true) : Ctx.AgreeOn v Γ Γ' :=
  fun z hz => h z (huv z hz)

/-- Agreement on what a binder's scope uses, but the binder, gives agreement on its
scope once the binder is bound alike. -/
theorem Ctx.AgreeOn.bind {u v : Name → Bool} {Γ Γ' : Ctx} {x : Name} (b : Binding)
    (h : Ctx.AgreeOn u Γ Γ') (huv : ∀ z, z ≠ x → v z = true → u z = true) :
    Ctx.AgreeOn v (Γ.bind x b) (Γ'.bind x b) :=
  Ctx.agree_bind b (P := fun z => v z = true) fun z hz hv => h z (huv z hz hv)

theorem bne_of_ne' {x z : Name} (h : z ≠ x) : (x != z) = true := by simpa using Ne.symm h

/-- Whether a place is rooted in `x` or an index of it uses `x`. -/
def placeFree (x : Name) (p : Place) : Bool := p.root == x || pathFree x p.path

/-- A closure's body is typed in contexts that agree on what it captures. -/
theorem closure_agree {ps : List Param} {result : Ty} {ρ : Row} {body : Expr} {Γ Γ' : Ctx}
    (h : Ctx.AgreeOn (Expr.free · (.closure ps result ρ body)) Γ Γ') :
    Ctx.AgreeOn (body.free ·) (Γ.freeze.params ps) (Γ'.freeze.params ps) :=
  Ctx.agree_params ps (P := fun z => body.free z = true) fun z hps hz =>
    Ctx.agree_freeze (P := fun z => (ps.any (·.name == z)) = false ∧ body.free z = true)
      (fun y ⟨h₁, h₂⟩ => h y (by simp [Expr.free, h₁, h₂])) z ⟨hps, hz⟩

/-- An assignment uses the root of its place and what the place's indexes use. -/
theorem assign_agree {x : Name} {path : List Projection} {v : Expr} {Γ Γ' : Ctx}
    (h : Ctx.AgreeOn (Expr.free · (.assign ⟨x, path⟩ v)) Γ Γ') :
    Ctx.AgreeOn (placeFree · ⟨x, path⟩) Γ Γ' :=
  h.mono fun _ hz => by
    simp only [placeFree, Bool.or_eq_true] at hz
    rcases hz with hz | hz <;> simp [Expr.free, hz]

section Strengthen

/-- Shows that a part of an expression uses a variable only if the expression does. -/
local macro "uses" : tactic =>
  `(tactic| simp_all [Expr.free, exprsFree, fieldsFree, argsFree, pathFree, armsFree])

/-- Agreement on what an expression uses gives agreement on what a part of it uses. -/
local macro "part " h:term:max : term => `(Ctx.AgreeOn.mono $h fun _ _ => by uses)

/-- Agreement on what an expression uses gives agreement on what a binder's scope in it
uses, once the binder is bound alike. -/
local macro "scope " h:term:max : term =>
  `(Ctx.AgreeOn.bind _ $h fun _ hne hz => by simp [Expr.free, hz, bne_of_ne' hne])

variable {D : Decls} {s : RowScope}

mutual

/-- Strengthening: a derivation holds in every context that gives the variables
the expression uses the same bindings. -/
theorem HasType.strengthen :
    ∀ {Γ fx e τ}, HasType D s Γ fx e τ → ∀ {Γ'}, Ctx.AgreeOn (Expr.free · e) Γ Γ' →
      HasType D s Γ' fx e τ
  | _, _, _, _, .var hl, _, h => .var (by rw [← h _ (by simp [Expr.free])]; exact hl)
  | _, _, _, _, .int hk, _, _ => .int hk
  | _, _, _, _, .bool, _, _ => .bool
  | _, _, _, _, .unit, _, _ => .unit
  | _, _, _, _, .record hr hl hw hp hfs, _, h => .record hr hl hw hp (FieldsFit.strengthen hfs (part h))
  | _, _, _, _, .variant ht hl hw hc hes, _, h => .variant ht hl hw hc (ExprsFit.strengthen hes (part h))
  | _, _, _, _, .list hwf hes, _, h => .list hwf (ExprsFit.strengthen hes (part h))
  | _, _, _, _, .op ho hes hk hb, _, h => .op ho (ExprsFit.strengthen hes (part h)) hk hb
  | _, _, _, _, .view ho hes, _, h => .view ho (ExprsFit.strengthen hes (part h))
  | _, _, _, _, .field he hr hl hf, _, h => .field (HasType.strengthen he (part h)) hr hl hf
  | _, _, _, _, .elem he hf, _, h => .elem (HasType.strengthen he (part h)) hf
  | _, _, _, _, .index he hi hfit, _, h =>
    .index (HasType.strengthen he (part h)) (HasType.strengthen hi (part h)) hfit
  | _, _, _, _, .fnRef hf hl hi hr hwf hp ht, _, _ => .fnRef hf hl hi hr hwf hp ht
  | _, _, _, _, .method ht hm hc hwf hsat hp, _, _ => .method ht hm hc hwf hsat hp
  | _, _, _, _, .closure hnd hpt hwf hb hfit, _, h =>
    .closure hnd hpt hwf (HasType.strengthen hb (closure_agree h)) hfit
  | _, _, _, _, .call hf has hcall, _, h =>
    .call (HasType.strengthen hf (part h)) (ArgsFit.strengthen has (part h)) hcall
  | _, _, _, _, .letIn hwf he hfit hb, _, h =>
    .letIn hwf (HasType.strengthen he (part h)) hfit (HasType.strengthen hb (scope h))
  | _, _, _, _, .varIn hwf he hfit hb, _, h =>
    .varIn hwf (HasType.strengthen he (part h)) hfit (HasType.strengthen hb (scope h))
  | _, _, _, _, .held hnd hwf hes hb hvar, _, h =>
    .held hnd hwf (ExprsFit.strengthen hes (part h)) (HasType.strengthen hb
      (Ctx.agree_holding _ (P := fun z => _ = true) fun z hz hv => h z (by simp [Expr.free, hz, hv])))
      hvar
  | _, _, _, _, .letElse hr hx hm, _, h =>
    .letElse hr (HasType.strengthen hx (part h)) (HasType.strengthen hm (part h))
  | _, _, _, _, .orElse ho h₁ h₂ hf hm, _, h =>
    .orElse ho (HasType.strengthen h₁ (part h)) (HasType.strengthen h₂ (part h)) hf
      (HasType.strengthen hm (part h))
  | _, _, _, _, .assign (p := ⟨_, _⟩) hp he hfit, _, h =>
    .assign (PlaceFits.strengthen hp (assign_agree h)) (HasType.strengthen he (part h)) hfit
  | _, _, _, _, .seq ha hfit hb, _, h =>
    .seq (HasType.strengthen ha (part h)) hfit (HasType.strengthen hb (part h))
  | _, _, _, _, .if hwf hc hfc ha hfa hb hfb, _, h =>
    .if hwf (HasType.strengthen hc (part h)) hfc (HasType.strengthen ha (part h)) hfa
      (HasType.strengthen hb (part h)) hfb
  | _, _, _, _, .match hwf he ht harms, _, h =>
    .match hwf (HasType.strengthen he (part h)) ht (ArmsFit.strengthen harms (part h))
  | _, _, _, _, .for hwf he hb hfit, _, h =>
    .for hwf (HasType.strengthen he (part h)) (HasType.strengthen hb (scope h)) hfit
  | _, _, _, _, .raise hE he hfit, _, h => .raise hE (HasType.strengthen he (part h)) hfit
  | _, _, _, _, .try he, _, h => .try (HasType.strengthen he (part h))
  | _, _, _, _, .tryCatch hwfE hwf he hfe hh hfh, _, h =>
    .tryCatch hwfE hwf (HasType.strengthen he (part h)) hfe (HasType.strengthen hh (scope h)) hfh
  | _, _, _, _, .while hc hfc hb hfb, _, h =>
    .while (HasType.strengthen hc (part h)) hfc (HasType.strengthen hb (part h)) hfb
  | _, _, _, _, .loopBreaks hb hfb, _, h => .loopBreaks (HasType.strengthen hb (part h)) hfb
  | _, _, _, _, .loopForever hb hfb, _, h => .loopForever (HasType.strengthen hb (part h)) hfb
  | _, _, _, _, .break hb, _, _ => .break hb
  | _, _, _, _, .continue hc, _, _ => .continue hc
  | _, _, _, _, .return he hfit, _, h => .return (HasType.strengthen he (part h)) hfit
  | _, _, _, _, .perform hne hop hA hB hm he hfit, _, h =>
    .perform hne hop hA hB hm (HasType.strengthen he (part h)) hfit
  | _, _, _, _, .resume hr hB hR he hfit, _, h =>
    .resume hr hB hR (HasType.strengthen he (part h)) hfit
  | _, _, _, _, .withH hne heff hh hr hfs hb hops, _, h =>
    .withH hne heff (HasType.strengthen hh (part h)) hr hfs (HasType.strengthen hb (part h)) hops
  | _, _, _, _, .withControl hne heff hh hr hfs hb hfit hg hops, _, h =>
    .withControl hne heff (HasType.strengthen hh (part h)) hr hfs
      (HasType.strengthen hb (part h)) hfit hg hops

theorem ExprsFit.strengthen :
    ∀ {Γ fx es τs}, ExprsFit D s Γ fx es τs →
      ∀ {Γ'}, Ctx.AgreeOn (exprsFree · es) Γ Γ' →
      ExprsFit D s Γ' fx es τs
  | _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, .cons he hfit hes, _, h => .cons (HasType.strengthen he (part h)) hfit
      (ExprsFit.strengthen hes (part h))

theorem FieldsFit.strengthen :
    ∀ {Γ fx fields declared}, FieldsFit D s Γ fx fields declared →
      ∀ {Γ'}, Ctx.AgreeOn (fieldsFree · fields) Γ Γ' → FieldsFit D s Γ' fx fields declared
  | _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, .cons hl he hfit hfs, _, h => .cons hl (HasType.strengthen he (part h)) hfit
      (FieldsFit.strengthen hfs (part h))

theorem ArgsFit.strengthen :
    ∀ {Γ fx args ps}, ArgsFit D s Γ fx args ps →
      ∀ {Γ'}, Ctx.AgreeOn (argsFree · args) Γ Γ' →
      ArgsFit D s Γ' fx args ps
  | _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, .value hm he hfit has, _, h => .value hm (HasType.strengthen he (part h)) hfit
      (ArgsFit.strengthen has (part h))
  | _, _, _, _, .inout (p := ⟨_, _⟩) hp has, _, h =>
    .inout (PlaceFits.strengthen hp (h.mono fun _ hz => by
        simp only [placeFree, Bool.or_eq_true] at hz
        rcases hz with hz | hz <;> simp [argsFree, hz])) (ArgsFit.strengthen has (part h))

theorem PlaceFits.strengthen :
    ∀ {Γ fx p τ}, PlaceFits D s Γ fx p τ →
      ∀ {Γ'}, Ctx.AgreeOn (placeFree · p) Γ Γ' →
      PlaceFits D s Γ' fx p τ
  | _, _, _, _, .mk hl hp, _, h => .mk (by rw [← h _ (by simp [placeFree])]; exact hl)
      (PathFits.strengthen hp (h.mono fun _ hz => by simp [placeFree, hz]))

theorem PathFits.strengthen :
    ∀ {Γ fx σ path τ}, PathFits D s Γ fx σ path τ →
      ∀ {Γ'}, Ctx.AgreeOn (pathFree · path) Γ Γ' →
      PathFits D s Γ' fx σ path τ
  | _, _, _, _, _, .nil, _, _ => .nil
  | _, _, _, _, _, .field hr hl hf hp, _, h => .field hr hl hf (PathFits.strengthen hp (part h))
  | _, _, _, _, _, .elem hf hp, _, h => .elem hf (PathFits.strengthen hp (part h))
  | _, _, _, _, _, .index hi hfit hp, _, h => .index (HasType.strengthen hi (part h)) hfit
      (PathFits.strengthen hp (part h))

theorem ArmsFit.strengthen :
    ∀ {Γ fx arms σ τ}, ArmsFit D s Γ fx arms σ τ →
      ∀ {Γ'}, Ctx.AgreeOn (armsFree · arms) Γ Γ' →
      ArmsFit D s Γ' fx arms σ τ
  | _, _, _, _, _, .cons (arm := ⟨_, binders, guard, body⟩) hc hb hnd hg hbody hfit harms, _, h =>
    have hl : binders.length = _ := by simp only at hb; rw [hb]; exact hc.length
    .cons hc hb hnd
      (GuardFits.strengthen hg
        (Ctx.agree_bindAll binders _ hl fun _ hn hz => h _ (by
            simp only at hz
            simp [armsFree, hz, show _ ∉ binders from by simpa using hn])))
      (HasType.strengthen hbody
        (Ctx.agree_bindAll binders _ hl fun _ hn hz => h _ (by
            simp only at hz
            simp [armsFree, hz, show _ ∉ binders from by simpa using hn])))
      hfit (ArmsFit.strengthen harms (h.mono fun _ hz => by simp [armsFree, hz]))
  | _, _, _, _, _, .nil, _, _ => .nil

theorem GuardFits.strengthen :
    ∀ {Γ fx g}, GuardFits D s Γ fx g →
      ∀ {Γ'}, Ctx.AgreeOn (guardFree · g) Γ Γ' →
      GuardFits D s Γ' fx g
  | _, _, _, .none, _, _ => .none
  | _, _, _, .some hg hfit, _, h => .some (HasType.strengthen hg h) hfit

end

end Strengthen

/-! ## Instantiating row variables keeps the variables an expression uses -/

theorem Param.name_substRows (θ : RowSubst) (p : Param) : (p.substRows θ).name = p.name := rfl

mutual

theorem Expr.free_substRows (θ : RowSubst) (x : Name) :
    ∀ e : Expr, (e.substRows θ).free x = e.free x
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => rfl
  | .closure ps _ _ body => by
    simp [Expr.substRows, Expr.free, Expr.free_substRows θ x body, Function.comp_def,
      Param.name_substRows]
  | .record _ _ fs => by simp [Expr.substRows, Expr.free, fieldsFree_substRows θ x fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substRows, Expr.free, exprsFree_substRows θ x es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.substRows, Expr.free, Expr.free_substRows θ x e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b
  | .for _ _ a b | .while a b | .tryCatch a _ _ b _ => by
    simp [Expr.substRows, Expr.free, Expr.free_substRows θ x a, Expr.free_substRows θ x b]
  | .call f args _ => by
    simp [Expr.substRows, Expr.free, Expr.free_substRows θ x f, argsFree_substRows θ x args]
  | .held ns hs b => by
    simp [Expr.substRows, Expr.free, exprsFree_substRows θ x hs, Expr.free_substRows θ x b,
      Function.comp_def]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substRows, Expr.free, pathFree_substRows θ x p, Expr.free_substRows θ x v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.free, Expr.free_substRows θ x c, Expr.free_substRows θ x a,
      Expr.free_substRows θ x b]
  | .match e _ arms => by
    simp [Expr.substRows, Expr.free, Expr.free_substRows θ x e, armsFree_substRows θ x arms]

theorem exprsFree_substRows (θ : RowSubst) (x : Name) :
    ∀ es : List Expr, exprsFree x (substExprRows θ es) = exprsFree x es
  | [] => rfl
  | e :: es => by
    simp [substExprRows, exprsFree, Expr.free_substRows θ x e, exprsFree_substRows θ x es]

theorem fieldsFree_substRows (θ : RowSubst) (x : Name) :
    ∀ fs : List (Name × Expr), fieldsFree x (substFieldRows θ fs) = fieldsFree x fs
  | [] => rfl
  | (_, e) :: fs => by
    simp [substFieldRows, fieldsFree, Expr.free_substRows θ x e, fieldsFree_substRows θ x fs]

theorem argsFree_substRows (θ : RowSubst) (x : Name) :
    ∀ args : List Arg, argsFree x (substArgRows θ args) = argsFree x args
  | [] => rfl
  | .value e :: args => by
    simp [substArgRows, argsFree, Expr.free_substRows θ x e, argsFree_substRows θ x args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgRows, argsFree, pathFree_substRows θ x p, argsFree_substRows θ x args]

theorem pathFree_substRows (θ : RowSubst) (x : Name) :
    ∀ p : List Projection, pathFree x (substPathRows θ p) = pathFree x p
  | [] => rfl
  | .field _ :: p => by simp [substPathRows, pathFree, pathFree_substRows θ x p]
  | .index i :: p => by
    simp [substPathRows, pathFree, Expr.free_substRows θ x i, pathFree_substRows θ x p]

theorem armsFree_substRows (θ : RowSubst) (x : Name) :
    ∀ arms : List Arm, armsFree x (substArmRows θ arms) = armsFree x arms
  | [] => rfl
  | ⟨_, _, g, b⟩ :: arms => by
    simp [substArmRows, armsFree, guardFree_substRows θ x g, Expr.free_substRows θ x b,
      armsFree_substRows θ x arms]

theorem guardFree_substRows (θ : RowSubst) (x : Name) :
    ∀ g : Option Expr, guardFree x (substGuardRows θ g) = guardFree x g
  | none => rfl
  | some g => by simp [substGuardRows, guardFree, Expr.free_substRows θ x g]

end

/-- A closure literal with its row variables instantiated captures what it captured. -/
theorem Expr.captures_substRows (θ : RowSubst) (ps : List Param) (body : Expr) :
    Expr.captures (ps.map (Param.substRows θ)) (body.substRows θ) = Expr.captures ps body := by
  funext x
  simp [Expr.captures, Expr.free_substRows, Function.comp_def, Param.name_substRows]

/-! ## A closure's body in the context of what it captures -/

theorem lookup_captureOf {ps : List Param} {body : Expr} {z : Name}
    (hz : Expr.captures ps body z = true) (Γ : Ctx) :
    (captureOf ps body Γ).lookup z = Γ.lookup z :=
  lookup_newestOf Γ hz

/-- A closure's body types in the context of the variables it captures alone
(expressions.capture). -/
theorem HasType.captured {D : Decls} {s : RowScope} {Γ : Ctx} {fx : Effects} {ps : List Param}
    {result : Ty} {ρ : Row} {body : Expr} {σ : Ty}
    (hb : HasType D s (Γ.freeze.params ps) fx body σ) :
    HasType D s (Ctx.freeze (captureOf ps body Γ) |>.params ps) fx body σ :=
  HasType.strengthen hb (closure_agree (result := result) (ρ := ρ) fun z hz =>
    (lookup_captureOf (by rw [← Expr.free_closure z ps result ρ body]; exact hz) Γ).symm)

end Stilt
