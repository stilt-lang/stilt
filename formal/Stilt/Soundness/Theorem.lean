import Stilt.Soundness.Ops
import Stilt.Soundness.Loops
import Stilt.Soundness.Identity
import Stilt.Soundness.Handlers
import Stilt.Theorems

/-!
# Type soundness

The fundamental lemma: every instantiation of a well-typed expression,
evaluated with any fuel from a frame of its context, under an environment that
keeps its scope's promises, ends as `Outcome.Ok` says. Each step at fuel
`n + 1` rests on the lemma at fuel `n` for the parts the evaluator runs.

`main` declares no row variables and runs under the empty environment, and
its row holds no effect and no `resume` (handlers.no-effect-reaches-main), so
its outcome is one that `Outcome.Sound` allows: `TypeSoundness`, and from it
`RaiseFree`. `main` returns `()` (program.main), so a well-typed program
that returns shows `()`.
-/

namespace Stilt

section

variable {D : Decls} {n : Nat}

/-- One more unit of fuel keeps every outcome sound. -/
theorem Sound.step (hs : Sound D n) (hD : D.Typed) {scope : RowScope} :
    ∀ {Γ : Ctx} {fx : Effects} {e : Expr} {τ : Ty},
      HasType D scope Γ fx e τ → ∀ {η : REnv}, η.Respects scope → ∀ θ : RowSubst,
        Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (τ.close η))
          (eval D Copy.memory (n + 1) (e.substRows θ))
  | _, _, _, _, .var hx, _, _, θ => var_ok θ hx
  | _, _, _, _, .int h, _, _, _ => Eval.Ok.pure (.int h)
  | _, _, _, _, .bool, _, _, _ => Eval.Ok.pure .bool
  | _, _, _, _, .unit, _, _, _ => Eval.Ok.pure .unit
  | _, _, _, _, .record hR hlen _ hperm hf, _, hη, θ => record_ok hs hD.wf hη θ hR hlen hperm hf
  | _, _, _, _, .variant hT hlen _ hC hp, _, hη, θ => variant_ok hs hD.wf hη θ hT hlen hC hp
  | _, _, _, _, .list _ hes, _, hη, θ => list_ok hs hη θ hes
  | _, _, _, _, .op ho hes _ _, _, hη, θ => op_ok hs hη θ ho hes
  | _, _, _, _, .view ho hes, _, hη, θ => view_ok hs hη θ ho hes
  | _, _, _, _, .field he hR _ hf, _, hη, θ => field_ok hs hη θ hD.wf he hR hf
  | _, _, _, _, .elem he hf, _, hη, θ => elem_ok hs hη θ he hf
  | _, _, _, _, .index he hi hfit, _, hη, θ => index_ok hs hη θ he hi hfit
  | _, _, _, _, .fnRef hd hlen hinst hres _ hpass htys, _, hη, θ =>
    fnRef_ok hη θ hD.wf hd hlen hinst hres hpass htys
  | _, _, _, _, .method ht hm hc _ hsat hp, _, hη, θ => method_ok hη θ hD.wf ht hm hc hsat hp
  | _, _, _, _, .closure hnd _ _ hb hfit, _, hη, θ => closure_ok hη θ hnd hb hfit
  | _, _, _, _, .call hc ha hallow, _, hη, θ => apply_ok hs hη θ hD hc ha hallow
  | _, _, _, _, .letIn _ hi hfit hb, _, hη, θ => letIn_ok hs hη θ hi hfit hb
  | _, _, _, _, .varIn _ hi hfit hb, _, hη, θ => varIn_ok hs hη θ hi hfit hb
  | _, _, _, _, .assign hp he hfit, _, hη, θ => assign_ok hs hη θ hD.wf hp he hfit
  | _, _, _, _, .seq ha _ hb, _, hη, θ => seq_ok hs hη θ ha hb
  | _, _, _, _, .if _ hc hfc ha hfa hb hfb, _, hη, θ => if_ok hs hη θ hc hfc ha hfa hb hfb
  | _, _, _, _, .match _ he hx ha, _, hη, θ => match_ok hs hD.wf hη θ he hx ha
  | _, _, _, _, .for _ he hb _, _, hη, θ => for_ok hs hη θ he hb
  | _, _, _, _, .raise hE he hfit, _, hη, θ => raise_ok hs hη θ hE he hfit
  | _, _, _, _, .try he, _, hη, θ => try_ok hs hη θ he
  | _, _, _, _, .tryCatch _ _ he hfe hh hfh, _, hη, θ => tryCatch_ok hs hη θ he hfe hh hfh
  | _, _, _, _, .while hc hfc hb hfb, _, hη, θ => while_ok hs hη θ hc hfc hb hfb
  | _, _, _, _, .loopBreaks hb hfb, _, hη, θ => loopBreaks_ok hs hη θ hb hfb
  | _, _, _, _, .loopForever hb hfb, _, hη, θ => loopForever_ok hs hη θ hb hfb
  | _, _, _, _, .break h, _, _, θ => break_ok θ h
  | _, _, _, _, .continue h, _, _, θ => continue_ok θ h
  | _, _, _, _, .return he hfit, _, hη, θ => return_ok hs hη θ he hfit
  | _, _, _, _, .perform hne hop hA hB hE he hfit, _, hη, θ => perform_ok hs hη θ hne hop hA hB hE he hfit
  | _, _, _, _, .resume hr hB hR he hfit, _, hη, θ => resume_ok hs hη θ hr hB hR he hfit
  | _, _, _, _, .withH hne heff hh hr hfits hb _, _, hη, θ =>
    withH_ok hs hη θ hD hne heff hh hr hfits hb
  | _, _, _, _, .withControl hne heff hh hr hfits hb hfit _ _, _, hη, θ =>
    withControl_ok hs hη θ hD hne heff hh hr hfits hb hfit
  | _, _, _, _, .held hnd _ hes hb _, _, hη, θ => held_ok hs hη θ hnd hes hb

/-- The fundamental lemma, at every fuel. -/
theorem Decls.Typed.sound (hD : D.Typed) : ∀ n, Sound D n
  | 0 => fun _ _ _ _ => Eval.Ok.outOfFuel
  | n + 1 => fun h _ hη θ => Sound.step (hD.sound n) hD h hη θ

end

/-- The empty environment keeps the promises of `main`'s scope, which has no
row variables. -/
theorem REnv.respects_closed : REnv.Respects (fun _ => []) RowScope.closed where
  pairs _ _ h := nomatch h
  passOn _ _ h := nomatch h
  types := rfl
  noResume _ _ _ h := nomatch h

/-- A well-typed program's declarations check against their signatures. -/
theorem Program.WellTyped.typedDecls {p : Program} (hp : p.WellTyped) : p.decls.Typed :=
  ⟨hp.decls, hp.typedIn.fns⟩

/-- **Type soundness**: a well-typed program, run as the reference interpreter runs it,
finishes with `()`, raises an error of the type its row allows, panics, or
runs out of fuel. -/
theorem typeSoundness : TypeSoundness := by
  intro p fuel input hp
  obtain ⟨σ, hmain, hfit⟩ := hp.main
  have h := hp.typedDecls.sound fuel hmain REnv.respects_closed []
  rw [Expr.substRows_nil] at h
  have ho := h ([], World.start input) ⟨.nil, fun _ h => nomatch h⟩
  show (eval p.decls Copy.memory fuel p.main ([], World.start input)).leaveBody.Sound p.decls p.row
  revert ho
  cases eval p.decls Copy.memory fuel p.main ([], World.start input) with
  | done v _ => exact fun ⟨hv, _⟩ => (hv.fits (hfit.close _)).unit_inv
  | raised e _ =>
    intro ⟨⟨F, hF, he⟩, _⟩
    rcases Row.mem_close.1 hF with ⟨E, hE, rfl⟩ | ⟨_, _, hF⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · exact ⟨E, hE, he⟩
    · exact nomatch hF
    all_goals exact absurd trivial he.not_label
  | jumped j _ =>
    intro ⟨hj, _⟩
    cases j with
    | brk => exact Bool.false_ne_true hj
    | cont => exact Bool.false_ne_true hj
    | ret v => exact hj.unit_inv
  | panicked => exact fun _ => trivial
  | performed op =>
    intro ⟨⟨_, _, hop, _⟩, _⟩
    obtain ⟨heffs, hres⟩ := hp.unhandled
    by_cases hr : op = Operation.resume
    · subst hr
      obtain ⟨_, _, hm, _⟩ := (performsOf_resume (D := p.decls)).1 hop
      rcases Row.mem_close.1 hm with ⟨_, _, h⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
      · exact absurd (show (STy.resume _ _).IsLabel from trivial) (h ▸ Ty.close_not_label _ _)
      all_goals simp_all [Effects.body]
    · obtain ⟨hm, _⟩ := (performsOf_of_ne hr).1 hop
      rcases Row.mem_close.1 hm with ⟨_, _, h⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
      · exact absurd (show (STy.effect _).IsLabel from trivial) (h ▸ Ty.close_not_label _ _)
      all_goals simp_all [Effects.body]
  | outOfFuel => exact fun _ => trivial
  | stuck => exact id

/-- **No raise without `raise`**: a well-typed program whose row has no `raise`
label never raises. -/
theorem raiseFree : RaiseFree := raiseFree_of_typeSoundness typeSoundness

/-- A well-typed program that returns shows `()`, which holds no closure
(program.main). -/
theorem Program.WellTyped.returned_unit {p : Program} (hp : p.WellTyped) (fuel : Nat)
    (input : String) {v : Value} (h : (p.runCopy fuel input).observe = .returned v) : v = .unit := by
  have hs := typeSoundness p fuel input hp
  cases hrun : p.runCopy fuel input with
  | done w _ =>
    rw [hrun] at h hs
    cases h
    exact hs
  | _ => simp [hrun, Outcome.observe] at h

/-- No `break`, `continue` or `return` escapes a well-typed program's `main`
(expressions.break-and-continue and expressions.closure-boundaries). -/
theorem Program.WellTyped.not_jumped {p : Program} (hp : p.WellTyped) (fuel : Nat) (input : String)
    (j : Jump) : (p.runCopy fuel input).observe ≠ .jumped j := by
  have hs := typeSoundness p fuel input hp
  cases hrun : p.runCopy fuel input with
  | jumped _ _ => rw [hrun] at hs; exact hs.elim
  | _ => simp [Outcome.observe]

end Stilt
