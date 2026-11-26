import Stilt.Exclusivity
import Stilt.Semantics
import Stilt.Soundness.Values

/-!
# Theorems

The soundness questions of the plan, as statements about the model.

Each statement is written as the definition of the proposition it claims, as
the repository's rule on proofs asks:

* `TypeSoundness`: a well-typed program finishes with `()`, raises an error
  that its row allows, panics, or runs out of fuel.
  `Stilt.Soundness.Theorem` proves it;
* `RaiseFree`: a well-typed program whose row has no `raise` never raises.
  It follows from `TypeSoundness`;
* `InPlaceAgreement`: on a well-typed program that obeys the law of
  exclusivity, copy-in, copy-out and in-place mutation can't be told apart.
  `Stilt.InPlace.Agreement` proves it.

The theorems after them are proved here: `RaiseFree` follows from
`TypeSoundness`, and the places that `inout` arguments reach at run time are
the ones that modes.overlapping-inout compares. `Stilt.Counterexamples` proves that
type soundness fails for effects.non-escaping-parameters as it was written before effects.paired-row-variables, for
effects.paired-row-variables without effects.passing-to-paired-variables, and for the checker without the no-escape rule, and
that `InPlaceAgreement` needs exclusivity.
-/

namespace Stilt

section ValueTyping

variable (D : Decls)

mutual

/-- `ValueHasType D v τ`: the run-time value `v` has the type `τ`, as the value
itself reads.

A function value has the type its literal or its declaration gives it, as the
call that made it instantiated it, with its row grown as a function value's may
be (effects.function-values). The relation doesn't look into a closure's body. It types
the values that `Stilt.Optimality` runs, which hold no functions. Type
soundness reads values by what they do instead (`Value.Typed`): a body may
write a row that holds a row variable beside a `raise` label without the
signature pairing them (effects.catch-around-row-variables checks it only under a `catch`), and an
instantiation can give such a row two `raise` labels, of which it keeps one.
So a closure's annotations, once instantiated, need not give the type it is
used at. -/
inductive ValueHasType : Value → Ty → Prop
  | int {n k} : k.Contains n → ValueHasType (.int n) (.int k)
  | float {x} : ValueHasType (.float x) (.float x.type)
  | str {s} : ValueHasType (.str s) .str
  | bool {b} : ValueHasType (.bool b) .bool
  | unit : ValueHasType .unit .unit
  | record {R args r fields} :
      D.record? R = some r →
      FieldValuesHaveTypes fields (r.fieldsAt args) →
      ValueHasType (.record R fields) (.record R args)
  | variant {T args t C τs payload} :
      D.variant? T = some t →
      (t.ctorsAt args).lookup C = some τs →
      ValuesHaveTypes payload τs →
      ValueHasType (.variant T C payload) (.variant T args)
  | list {τ vs} :
      ValuesHaveTypes vs (List.replicate vs.length τ) →
      ValueHasType (.list vs) (.list τ)
  | tuple {τs vs} :
      ValuesHaveTypes vs τs →
      ValueHasType (.tuple vs) (.tuple τs)
  | map {κ τ es d} :
      ValuesHaveTypes (es.map Prod.fst) (List.replicate es.length κ) →
      ValuesHaveTypes (es.map Prod.snd) (List.replicate es.length τ) →
      ValuesHaveTypes d.toList (List.replicate d.toList.length τ) →
      ValueHasType (.mapOf es d) (.map κ τ)
  | set {κ ks} :
      ValuesHaveTypes ks (List.replicate ks.length κ) →
      ValueHasType (.setOf ks) (.set κ)
  | closure {captured ps result ρ body τ} :
      Fits (.fn (ps.map Param.sig) result ρ) τ →
      ValueHasType (.closure captured ps result ρ body) τ
  | function {f d types rows τ} :
      D.fn? f = some d →
      types.length = d.typeParams.length →
      rows.length = d.rowParams.length →
      d.type.InstantiableBy (d.rowParams.zip rows) →
      Fits ((d.type.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows)) τ →
      ValueHasType (.function f types rows) τ

/-- Each value has the type at its position. -/
inductive ValuesHaveTypes : List Value → List Ty → Prop
  | nil : ValuesHaveTypes [] []
  | cons {v vs τ τs} :
      ValueHasType v τ → ValuesHaveTypes vs τs → ValuesHaveTypes (v :: vs) (τ :: τs)

/-- A record's fields, in the order they are declared, with their types. -/
inductive FieldValuesHaveTypes : List (Name × Value) → List (Name × Ty) → Prop
  | nil : FieldValuesHaveTypes [] []
  | cons {f v fields τ declared} :
      ValueHasType v τ → FieldValuesHaveTypes fields declared →
      FieldValuesHaveTypes ((f, v) :: fields) ((f, τ) :: declared)

end

end ValueTyping

/-- What type soundness promises of the outcome of a program whose `main` is
checked against the row `ρ`: the value `()`, which `main` returns (program.main), a raise of the error type that `ρ` allows, a panic, or running out of
fuel. Never `stuck`, and never a `break`, `continue` or `return` that escapes
`main`'s body. An error has its type as `Value.Typed` reads it: a
function value is one whose calls keep the promises of its type. -/
def Outcome.Sound {σ : Type} (D : Decls) (ρ : Row) : Outcome σ Value → Prop
  | .done v _ => v = .unit
  | .raised e _ => ∃ E, ρ.raise = some E ∧ Value.Typed D e E.sem
  | .jumped _ _ => False
  | .panicked _ _ => True
  | .performed .. => False
  | .outOfFuel => True
  | .stuck => False

/-! ## Statements -/

/-- **Type soundness**. A well-typed program, run as the reference interpreter runs it,
finishes with `()`, raises an error of the type its row allows, panics, or
runs out of fuel.

Exclusivity isn't among the hypotheses: copy-in, copy-out is sound without it.
Mutability, the other mode rule, is part of `Program.WellTyped`, and so is the
leniency of effects.non-escaping-parameters for the rows that lack an implicit variable, with
the no-escape rule that makes it safe.

A well-typed program has every row checked (`Program.WellTyped.typedIn`), and
`Stilt.Soundness.Theorem` proves it, as `typeSoundness`, with an invariant on
frames kept by induction on fuel: each variable holds a value of its type, and
a function value is one whose calls keep the promises of its type, which a
logical relation states. The case that effects.paired-row-variables and effects.passing-to-paired-variables settle is a `catch`
operand's call through a row variable `v` paired with the caught type `E`. The
invariant it needs is that the instantiation of each function at run time,
which composes the uses that led to it down from `main`, gives `v` only `E` to
raise. effects.one-error-type gives that for a concrete use, and effects.passing-to-paired-variables passes
it from the enclosing function's instantiation to a use that ends in the
enclosing function's variable. -/
def TypeSoundness : Prop :=
  ∀ (p : Program) (fuel : Nat) (input : String), p.WellTyped →
    (p.runCopy fuel input).Sound p.decls p.row

/-- Type soundness for effects.non-escaping-parameters as it was written before effects.paired-row-variables. It is
false: `Stilt.Counterexamples` proves its negation. -/
def TypeSoundnessAsRecorded : Prop :=
  ∀ (p : Program) (fuel : Nat), p.WellTypedAsRecorded →
    (p.runCopy fuel).Sound p.decls p.row

/-- Type soundness for effects.paired-row-variables without effects.passing-to-paired-variables. It is false:
`Stilt.Counterexamples` proves its negation. -/
def TypeSoundnessWithoutPassing : Prop :=
  ∀ (p : Program) (fuel : Nat), p.WellTypedWithoutPassing →
    (p.runCopy fuel).Sound p.decls p.row

/-- Type soundness for the checker without the no-escape rule, which leaves
unchecked the rows that lack an implicit variable where the variable meets
them (effects.no-escape). It is false: `Stilt.Counterexamples` proves its
negation. -/
def TypeSoundnessWithoutNoEscape : Prop :=
  ∀ (p : Program) (fuel : Nat), p.LenientIn FnDecl.scope →
    (p.runCopy fuel).Sound p.decls p.row

/-- **No raise without `raise`**. A well-typed program whose row has no `raise`
label never raises: every raise in it is handled (effects.missing-effects, effects.catch and effects.innermost-catch).
It follows from `TypeSoundness`, and `Stilt.Soundness.Theorem` proves it as
`raiseFree`. -/
def RaiseFree : Prop :=
  ∀ (p : Program) (fuel : Nat) (input : String), p.WellTyped → p.row.raise = none →
    ∀ e s, p.runCopy fuel input ≠ .raised e s

/-- **In-place agreement**. On a well-typed program that obeys the law of
exclusivity, copy-in, copy-out (the reference interpreter's model, values.inout-arguments) and
in-place mutation (a compiler's) give the same observation, with the same fuel.
This is the claim values.inout-arguments and modes.law rest on: with the exclusivity rules, the
reference interpreter's model "can't be told apart from in-place mutation".

`Stilt.InPlace.Agreement` proves it, as `inPlaceAgreement`, by a simulation
between the two states: each variable of the copy frame holds the value its
reference reaches in the store, and the references reach disjoint parts of the
store. `Path.disjoint_of_not_overlaps` gives that disjointness for the `inout`
arguments of a call from modes.overlapping-inout, and `Value.setSeq_canon` turns the callee's
writes below them into copy-in, copy-out's write-back.
`Stilt.Counterexamples.exclusivity_needed` shows that the hypothesis of
exclusivity can't be dropped. -/
def InPlaceAgreement : Prop :=
  ∀ (p : Program) (fuel : Nat) (input : String), p.WellTyped → p.Exclusive →
    (p.runCopy fuel input).shows = (p.runInPlace fuel input).shows

/-! ## Proved theorems -/

/-- The path that evaluating a place's indexes gives resolves the place. So
`Path.disjoint_of_not_overlaps` applies at run time: the `inout` arguments of a
call that modes.overlapping-inout accepts reach disjoint parts of their roots. -/
theorem Eval.path_resolves {σ : Type} {run : Expr → Eval σ Value} :
    ∀ {ps : List Projection} {s s' : σ} {r : Path},
      Eval.path run ps s = .done r s' → r.Resolves ps
  | [], _, _, _, h => by
    cases h
    trivial
  | .field f :: ps, s, _, _, h => by
    change (Eval.path run ps s).bind (fun p s => Eval.pure (.field f :: p) s) = _ at h
    obtain ⟨p, s₁, hp, h₁⟩ := Outcome.bind_eq_done h
    cases h₁
    exact ⟨rfl, Eval.path_resolves hp⟩
  | .index i :: ps, s, _, _, h => by
    change ((run i s).bind fun v s => Eval.asInt v s).bind (fun k s =>
      (Eval.path run ps s).bind fun p s => Eval.pure (.index k :: p) s) = _ at h
    obtain ⟨k, s₁, -, h₁⟩ := Outcome.bind_eq_done h
    obtain ⟨p, s₂, hp, h₂⟩ := Outcome.bind_eq_done h₁
    cases h₂
    have hrest := Eval.path_resolves hp
    exact hrest

/-- `RaiseFree` follows from `TypeSoundness`: a raise would need an error type
in the row. -/
theorem raiseFree_of_typeSoundness (h : TypeSoundness) : RaiseFree := by
  intro p fuel input hp hrow e s hrun
  have hsound := h p fuel input hp
  rw [hrun] at hsound
  obtain ⟨E, hE, _⟩ := hsound
  rw [hrow] at hE
  exact nomatch hE

end Stilt
