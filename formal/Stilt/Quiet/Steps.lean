import Stilt.Quiet.Outcome

/-!
# Steps that keep the world's output and input

`Quiet D n`: every instantiation of a well-typed expression whose row reads as no `io` at run
time, evaluated with fuel `n` from a typed state, keeps the world's output, standard error and
input (`Eval.KeepsIo`). The evaluator's combinators that run several expressions in turn keep
it when each expression does, which `Quiet D n` gives at the fuel they run with.
-/

namespace Stilt

/-- Evaluating any instantiation of a well-typed expression whose row reads as no `io` under
`η`, with fuel `n`, from a typed state, keeps the world's output, standard error and input. -/
def Quiet (D : Decls) (n : Nat) : Prop :=
  ∀ {scope : RowScope} {Γ : Ctx} {fx : Effects} {e : Expr} {τ : Ty},
    HasType D scope Γ fx e τ → ∀ {η : REnv}, η.Respects scope → STy.io ∉ fx.row.close η →
      ∀ θ : RowSubst, Eval.KeepsIo D Γ η (fx.exits D η) (eval D Copy.memory n (e.substRows θ))

/-- A row and the row of a `catch` operand built from it hold the same `io`. -/
theorem Row.io_not_mem_withRaise {η : REnv} {ρ : Row} {E : Ty} (h : STy.io ∉ ρ.close η) :
    STy.io ∉ (ρ.withRaise E).close η := fun hm =>
  h (Row.labels_withRaise _ hm trivial)

/-- A row and the row of a `with`'s block built from it hold the same `io`. -/
theorem Row.io_not_mem_withEffect {η : REnv} {ρ : Row} {E : Name} (h : STy.io ∉ ρ.close η) :
    STy.io ∉ (ρ.withEffect E).close η := fun hm => by
  rcases Row.close_withEffect hm with h' | h'
  · exact nomatch h'
  · exact h h'

section

variable {D : Decls} {n : Nat} (hq : Quiet D n) (hs : Sound D n) {scope : RowScope} {η : REnv}
  (hη : η.Respects scope) (θ : RowSubst)
include hq hs hη

theorem ExprsFit.keeps :
    ∀ {Γ : Ctx} {fx : Effects} {es : List Expr} {τs : List Ty}, ExprsFit D scope Γ fx es τs →
      STy.io ∉ fx.row.close η →
      Eval.KeepsIo D Γ η (fx.exits D η) (Eval.list (eval D Copy.memory n) (substExprRows θ es))
  | _, _, _, _, .nil, _ => Eval.KeepsIo.pure
  | _, _, _, _, .cons he _ hrest, hio =>
    Eval.KeepsIo.bind (hs he hη θ) (hq he hη hio θ) fun _ _ =>
      Eval.KeepsIo.bind (ExprsFit.ok hs hη θ hrest) (ExprsFit.keeps hrest hio) fun _ _ =>
        Eval.KeepsIo.pure

theorem FieldsFit.keeps :
    ∀ {Γ : Ctx} {fx : Effects} {fields : List (Name × Expr)} {declared : List (Name × Ty)},
      FieldsFit D scope Γ fx fields declared → STy.io ∉ fx.row.close η →
        Eval.KeepsIo D Γ η (fx.exits D η) (Eval.fields (eval D Copy.memory n) (substFieldRows θ fields))
  | _, _, _, _, .nil, _ => Eval.KeepsIo.pure
  | _, _, _, _, .cons _ he _ hrest, hio =>
    Eval.KeepsIo.bind (hs he hη θ) (hq he hη hio θ) fun _ _ =>
      Eval.KeepsIo.bind (FieldsFit.ok hs hη θ hrest) (FieldsFit.keeps hrest hio) fun _ _ =>
        Eval.KeepsIo.pure

variable (hD : D.WellFormed)
include hD

theorem PathFits.keeps :
    ∀ {Γ : Ctx} {fx : Effects} {σ : Ty} {ps : List Projection} {τ : Ty},
      PathFits D scope Γ fx σ ps τ → STy.io ∉ fx.row.close η →
        Eval.KeepsIo D Γ η (fx.exits D η) (Eval.path (eval D Copy.memory n) (substPathRows θ ps))
  | _, _, _, _, _, .nil, _ => Eval.KeepsIo.pure
  | _, _, _, _, _, .field _ _ _ hrest, hio =>
    Eval.KeepsIo.bind (PathFits.ok hs hD hη θ hrest) (PathFits.keeps hrest hio) fun _ _ =>
      Eval.KeepsIo.pure
  | _, _, _, _, _, .index hi hfit hrest, hio => by
    refine Eval.KeepsIo.bind (P := fun _ => True) (Eval.Ok.bind (hs hi hη θ) fun v hv => ?_)
      (Eval.KeepsIo.bind (hs hi hη θ) (hq hi hη hio θ) fun v hv => ?_) fun _ _ =>
        Eval.KeepsIo.bind (PathFits.ok hs hD hη θ hrest) (PathFits.keeps hrest hio) fun _ _ =>
          Eval.KeepsIo.pure
    · obtain ⟨k, rfl⟩ := (hv.fits (hfit.close η)).i64_inv
      exact Eval.Ok.pure (P := fun _ => True) trivial
    · obtain ⟨k, rfl⟩ := (hv.fits (hfit.close η)).i64_inv
      exact Eval.KeepsIo.pure
  | _, _, _, _, _, .elem _ hrest, hio =>
    Eval.KeepsIo.bind (PathFits.ok hs hD hη θ hrest) (PathFits.keeps hrest hio) fun _ _ =>
      Eval.KeepsIo.pure

theorem ArgsFit.keeps :
    ∀ {Γ : Ctx} {fx : Effects} {args : List Arg} {ps : List (Mode × Ty)},
      ArgsFit D scope Γ fx args ps → STy.io ∉ fx.row.close η →
        Eval.KeepsIo D Γ η (fx.exits D η) (Eval.args (eval D Copy.memory n) (substArgRows θ args))
  | _, _, _, _, .nil, _ => Eval.KeepsIo.pure
  | _, _, .value _ :: _, _ :: _, .value _ he _ hrest, hio =>
    Eval.KeepsIo.bind (hs he hη θ) (hq he hη hio θ) fun _ _ =>
      Eval.KeepsIo.bind (ArgsFit.ok hs hD hη θ hrest) (ArgsFit.keeps hrest hio) fun _ _ =>
        Eval.KeepsIo.pure
  | _, _, .inout ⟨_, _⟩ :: _, _, .inout (.mk _ hpath) hrest, hio =>
    Eval.KeepsIo.bind (PathFits.ok hs hD hη θ hpath) (PathFits.keeps hq hs hη θ hD hpath hio)
      fun _ _ => Eval.KeepsIo.bind (ArgsFit.ok hs hD hη θ hrest) (ArgsFit.keeps hrest hio)
        fun _ _ => Eval.KeepsIo.pure

end

section

variable {D : Decls} {η : REnv} {X : Exits} {α : Type}

/-- The arms of a `match` bind the payload's values, the first one outermost, which keeps
the world when the step under them does. -/
theorem Eval.KeepsIo.withVars {m : Eval Copy.State α} :
    ∀ {Γ : Ctx} {xs : List Name} {vs : List Value} {τs : List Ty}, xs.length = τs.length →
      ValuesAt D η vs τs → Eval.KeepsIo D (Γ.bindAll xs τs) η X m →
      Eval.KeepsIo D Γ η X (Eval.withVars Copy.memory (xs.zip vs) m)
  | _, [], _, [], _, .nil, h => h
  | Γ, x :: _, _, τ :: _, hl, .cons hv hvs, h =>
    Eval.KeepsIo.withVar (b := ⟨τ, false⟩) hv
      (Eval.KeepsIo.withVars (Γ := Γ.bind x ⟨τ, false⟩) (by simpa using hl) hvs h)
  | _, [], _, _ :: _, hl, _, _ => nomatch hl
  | _, _ :: _, _, [], hl, _, _ => nomatch hl

/-- Running a body on each element of a list keeps the world when each turn does. -/
theorem Eval.KeepsIo.forEach {Γ : Ctx} {f : Value → Eval Copy.State Bool} {Q : Value → Prop}
    (hok : ∀ u, Q u → Eval.Ok D Γ η X (fun _ => True) (f u))
    (hf : ∀ u, Q u → Eval.KeepsIo D Γ η X (f u)) :
    ∀ {vs : List Value}, (∀ u ∈ vs, Q u) → Eval.KeepsIo D Γ η X (Eval.forEach f vs)
  | [], _ => Eval.KeepsIo.pure
  | u :: _, hq =>
    Eval.KeepsIo.bind (hok u (hq u List.mem_cons_self)) (hf u (hq u List.mem_cons_self)) fun g _ => by
      cases g
      · exact Eval.KeepsIo.pure
      · exact Eval.KeepsIo.forEach hok hf fun w hw => hq w (List.mem_cons_of_mem _ hw)

end

end Stilt
