import Stilt.Quiet.Handlers
import Stilt.Cycles.Run

/-!
# Code whose row holds no `io` neither writes nor reads the world

**Quiet code** (facts.io-and-capabilities): every instantiation of a well-typed expression
whose row reads as no `io` at run time, evaluated with any fuel from a typed state, ends with
the world's output, standard error and input as they were, and so does the rest of each
performance it makes, from the world it is resumed in (`Decls.Typed.quiet`). The operations
that read and write them, `print`, `eprint` and `std.io`'s, are natives whose rows hold `io`,
so code whose row lacks it can't run one (`HasType.op`); a call contributes its callee's row,
which fits within the row around it (effects.missing-effects); and a function value's
run-time type reads its row's `io` (`STy.io`), so a value called at a type whose row lacks
`io` was made by code whose row lacks it. So a call of such a value, on arguments of its
parameter types, keeps the world (`call_keeps`), and so does a run of a program whose `main`'s
row lacks `io`: it writes nothing and reads nothing (`Program.WellTyped.quiet`).

The proof is an induction on the fuel, case by case on the typing derivation as
`Sound.step`'s is: each form keeps the world when the parts it runs do, from the typed states
that type soundness gives the parts after the first.
-/

namespace Stilt

section

variable {D : Decls} {n : Nat}

/-- One more unit of fuel keeps the world in every quiet run. -/
theorem Quiet.step (hq : Quiet D n) (hs : Sound D n) (hD : D.Typed) {scope : RowScope} :
    ∀ {Γ : Ctx} {fx : Effects} {e : Expr} {τ : Ty},
      HasType D scope Γ fx e τ → ∀ {η : REnv}, η.Respects scope → STy.io ∉ fx.row.close η →
        ∀ θ : RowSubst, Eval.KeepsIo D Γ η (fx.exits D η) (eval D Copy.memory (n + 1) (e.substRows θ))
  | _, _, _, _, .var _, _, _, _, _ => Eval.KeepsIo.inspect
  | _, _, _, _, .int _, _, _, _, _ | _, _, _, _, .bool, _, _, _, _ | _, _, _, _, .unit, _, _, _, _ =>
    Eval.KeepsIo.pure
  | _, _, _, _, .record _ _ _ _ hf, _, hη, hio, θ =>
    Eval.KeepsIo.bind (FieldsFit.ok hs hη θ hf) (FieldsFit.keeps hq hs hη θ hf hio) fun _ _ _ _ =>
      Outcome.KeepsIo.declare
  | _, _, _, _, .variant _ _ _ _ hp, _, hη, hio, θ =>
    Eval.KeepsIo.bindAny (ExprsFit.keeps hq hs hη θ hp hio) fun _ _ => rfl
  | _, _, _, _, .list _ hes, _, hη, hio, θ =>
    Eval.KeepsIo.bindAny (ExprsFit.keeps hq hs hη θ hes hio) fun _ _ => rfl
  | _, _, _, _, .op _ hes _ _ hoio, _, hη, hio, θ => op_keeps hq hs hη θ hio hes hoio
  | _, _, _, _, .view _ hes, _, hη, hio, θ =>
    Eval.KeepsIo.bindAny (ExprsFit.keeps hq hs hη θ hes hio) fun _ _ => Outcome.KeepsIo.ofExcept_any
  | _, _, _, _, .field he _ _ _, _, hη, hio, θ | _, _, _, _, .elem he _, _, hη, hio, θ =>
    field_keeps hq hη θ hio he
  | _, _, _, _, .index he hi hfit, _, hη, hio, θ => index_keeps hq hs hη θ hio he hi hfit
  | _, _, _, _, .fnRef .., _, _, _, _ => Eval.KeepsIo.pure
  | _, _, _, _, .method .., _, _, _, _ => fun _ _ => Outcome.KeepsIo.method
  | _, _, _, _, .closure .., _, _, _, _ => Eval.KeepsIo.inspect_bind fun _ => Eval.KeepsIo.pure
  | _, _, _, _, .call hc ha hallow, _, hη, hio, θ => apply_keeps hq hs hη θ hio hD hc ha hallow
  | _, _, _, _, .letIn _ hi hfit hb, _, hη, hio, θ => letIn_keeps hq hs hη θ hio hi hfit hb
  | _, _, _, _, .varIn _ hi hfit hb, _, hη, hio, θ => varIn_keeps hq hs hη θ hio hi hfit hb
  | _, _, _, _, .assign hp he _, _, hη, hio, θ => assign_keeps hq hs hη θ hio hD.wf hp he
  | _, _, _, _, .seq ha _ hb, _, hη, hio, θ => seq_keeps hq hs hη θ hio ha hb
  | _, _, _, _, .if _ hc hfc ha _ hb _, _, hη, hio, θ => ite_keeps hq hs hη θ hio hc hfc ha hb
  | _, _, _, _, .match _ he _ ha, _, hη, hio, θ => match_keeps hq hs hη θ hio hD.wf he ha
  | _, _, _, _, .for _ he hb _, _, hη, hio, θ => for_keeps hq hs hη θ hio he hb
  | _, _, _, _, .raise _ he _, _, hη, hio, θ =>
    Eval.KeepsIo.bindAny (hq he hη hio θ) fun _ _ => rfl
  | _, _, _, _, .try he, _, hη, hio, θ => hq he hη hio θ
  | _, _, _, _, .tryCatch _ _ he _ hh _, _, hη, hio, θ => tryCatch_keeps hq hs hη θ hio he hh
  | _, _, _, _, .while hc hfc hb hfb, _, hη, hio, θ => while_keeps hq hs hη θ hio hc hfc hb hfb
  | _, fx, _, _, .loopBreaks hb hfb, _, hη, hio, θ =>
    loop_keeps (fx' := fx.inLoop) hq hη θ hio rfl (fun _ _ _ h => h) (.loopBreaks hb hfb) hb
      ((hs hb hη θ).turn (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h)
  | _, fx, _, _, .loopForever hb hfb, _, hη, hio, θ =>
    loop_keeps (fx' := { fx with continues := true, breaks := false }) hq hη θ hio rfl (fun _ _ _ h => h) (.loopForever hb hfb) hb
      ((hs hb hη θ).turn (fun _ F hF he => ⟨F, hF, he⟩) fun _ h => h)
  | _, _, _, _, .break _, _, _, _, _ | _, _, _, _, .continue _, _, _, _, _ => Eval.KeepsIo.jump
  | _, _, _, _, .return he _, _, hη, hio, θ =>
    Eval.KeepsIo.bindAny (hq he hη hio θ) fun _ _ => rfl
  | _, _, _, _, .perform _ _ _ _ _ he _, _, hη, hio, θ | _, _, _, _, .resume _ _ _ he _, _, hη, hio, θ =>
    Eval.KeepsIo.bindAny (hq he hη hio θ) fun _ _ => ⟨rfl, fun _ _ _ _ => rfl⟩
  | _, _, _, _, .withH hne heff hh hr hfits hb _, _, hη, hio, θ =>
    withH_keeps hq hs hη θ hio hD hne heff hh hr hfits hb
  | _, _, _, _, .withControl hne heff hh hr hfits hb hfit _ _, _, hη, hio, θ =>
    withControl_keeps hq hs hη θ hio hD hne heff hh hr hfits hb hfit
  | _, _, _, _, .held _ _ hes hb _, _, hη, hio, θ => held_keeps hq hs hη θ hio hes hb
  | _, _, _, _, .letElse _ _ hm, _, hη, hio, θ | _, _, _, _, .orElse _ _ _ _ hm, _, hη, hio, θ
  | _, _, _, _, .form _ hm, _, hη, hio, θ | _, _, _, _, .shaped _ hm, _, hη, hio, θ | _, _, _, _, .task _ hm, _, hη, hio, θ => by
    rw [Expr.substRows, eval_form]
    exact hq hm hη hio θ

/-- Quiet code keeps the world, at every fuel. -/
theorem Decls.Typed.quiet (hD : D.Typed) : ∀ n, Quiet D n
  | 0 => fun _ _ _ _ _ => Eval.KeepsIo.outOfFuel
  | n + 1 => fun h _ hη hio θ => Quiet.step (hD.quiet n) (hD.sound n) hD h hη hio θ

end

/-- A row without `io` and without row variables reads as no `io` label. -/
theorem Row.io_not_mem_close_closed {ρ : Row} (hio : ρ.io = false) :
    STy.io ∉ ρ.close (fun _ => []) := fun h => by
  rcases Row.mem_close.1 h with ⟨E, _, hE⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨h, _⟩
  · exact Ty.close_not_label _ E (by rw [← hE]; trivial)
  · exact nomatch h
  · exact nomatch h
  · exact nomatch h
  · rw [hio] at h; exact nomatch h

/-- What a quiet outcome ends in, as `main`'s body: the world it started in, but for cells. -/
theorem Outcome.KeepsIo.world_leaveBody {D : Decls} {X : Exits} {c : String × String × String} :
    ∀ {o : Outcome Copy.State Value}, o.KeepsIo D X c → ∀ w ∈ o.leaveBody.world, w.io = c
  | .done _ _, h, _, hw | .raised _ _, h, _, hw | .panicked _ _, h, _, hw
  | .jumped (.ret _) _, h, _, hw | .jumped .brk _, h, _, hw | .jumped .cont _, h, _, hw => by
    simp only [Outcome.leaveBody, Outcome.world, Option.mem_def, Option.some.injEq] at hw
    subst hw
    exact h
  | .performed .., _, _, hw | .outOfFuel, _, _, hw | .stuck, _, _, hw => by
    simp [Outcome.leaveBody, Outcome.world] at hw

/-- **Quiet programs** (facts.io-and-capabilities): a well-typed program whose `main`'s row
holds no `io`, run on any input with any fuel, ends with nothing written to its output or its
standard error, and its whole input unread. -/
theorem Program.WellTyped.quiet {p : Program} (hp : p.WellTyped) (hio : p.row.io = false)
    (fuel : Nat) (input : String) :
    ∀ w ∈ (p.runCopy fuel input).world, w.out = "" ∧ w.err = "" ∧ w.input = input := by
  obtain ⟨σ, hmain, _⟩ := hp.main
  have h := hp.typedDecls.quiet fuel hmain REnv.respects_closed (Row.io_not_mem_close_closed hio) []
  rw [Expr.substRows_nil] at h
  intro w hw
  have := (h ([], World.start input) ⟨.nil, fun _ h => nomatch h⟩).world_leaveBody w hw
  simp only [World.io, World.start, Prod.mk.injEq] at this
  exact this

end Stilt
