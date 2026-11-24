import Stilt.Lenient.Strict
import Stilt.Weakening

/-!
# Well-typed programs

Well-formed declarations, with the implicit row variables of their
non-escaping parameters, and functions and programs whose bodies the checker
accepts in the scope that a version of the rules gives them: the rules as
effects.paired-row-variables and effects.passing-to-paired-variables amend them, effects.paired-row-variables without effects.passing-to-paired-variables, and effects.catch-around-row-variables as it
was written, each with the no-escape rule. The checker leaves unchecked a row
that lacks an implicit variable where the variable meets it (effects.non-escaping-parameters;
`Stilt.Lenient.Typing`), so a program it accepts has every row checked once
the no-escape rule accepts it too (`Program.LenientIn.typedIn`). Each amendment
only adds a condition, so every program that the later rules accept, the
earlier ones accept too. The checker without the no-escape rule shows that the
leniency rests on it.
-/

namespace Stilt

/-! ## Declarations and programs -/

/-- The implicit row variables of a function's non-escaping parameters, in
order (effects.non-escaping-parameters). -/
def FnDecl.implicits (d : FnDecl) : List Name := d.params.filterMap (·.implicit)

/-- The scope of a function's body: its row variables, written and implicit,
with the pairs of its signature for both effects.catch-around-row-variables and effects.passing-to-paired-variables, and its type
parameters with their bounds. -/
def FnDecl.scope (d : FnDecl) : RowScope := ⟨d.rowParams, d.pairs, d.pairs, d.typeParams⟩

/-- The scope of a function's body under effects.paired-row-variables without effects.passing-to-paired-variables: a use may pass
a row variable on to a paired one without its pairing. -/
def FnDecl.withoutPassingScope (d : FnDecl) : RowScope :=
  ⟨d.rowParams, d.pairs, fun _ _ => True, d.typeParams⟩

/-- The scope of a function's body under effects.catch-around-row-variables as it was written,
before effects.paired-row-variables: a row that names an error type beside a variable is enough,
as if the signature paired every variable with every error type. -/
def FnDecl.recordedScope (d : FnDecl) : RowScope :=
  ⟨d.rowParams, fun _ _ => True, fun _ _ => True, d.typeParams⟩

/-- The scope of `main`, which declares no row variables and no type
parameters. -/
def RowScope.closed : RowScope := ⟨[], fun _ _ => False, fun _ _ => False, []⟩

/-- A function's body checks against its signature with every row checked:
its parameters are in scope, its effects fit its row, and its value fits its
result type. -/
def FnDecl.WellTyped (D : Decls) (scope : RowScope) (d : FnDecl) : Prop :=
  ∃ σ, HasType D scope (Ctx.params [] d.params) (Effects.body d.row d.result) d.body σ ∧
    Fits σ d.result

/-- A function's body checks against its signature as the checker checks it:
a row that lacks one of its implicit row variables is no error where the
variable meets it, that is, where one of its non-escaping parameters, or a
closure literal that names one, is checked against an expected type (effects.non-escaping-parameters and effects.closure-parameters). -/
def FnDecl.Lenient (D : Decls) (scope : RowScope) (d : FnDecl) : Prop :=
  ∃ σ, Lenient.HasType D scope d.implicits d.nonEscaping (Ctx.params [] d.params)
    (Effects.body d.row d.result) d.body σ ∧ LenientFits d.implicits d.nonEscaping d.body σ d.result

/-- A body that the checker accepts, and from which no non-escaping parameter
escapes, has every row checked. -/
theorem FnDecl.Lenient.wellTyped {D : Decls} {scope : RowScope} {d : FnDecl}
    (h : d.Lenient D scope) (hne : d.NoEscape D) : d.WellTyped D scope :=
  let ⟨σ, hbody, hfit⟩ := h
  ⟨σ, hbody.strict hne, hfit.fits (Expr.carries_eq_false hne)⟩

/-- The checker accepts every body whose every row checks. -/
theorem FnDecl.WellTyped.lenient {D : Decls} {scope : RowScope} {d : FnDecl}
    (h : d.WellTyped D scope) : d.Lenient D scope :=
  let ⟨σ, hbody, hfit⟩ := h
  ⟨σ, hbody.lenient, .inl hfit⟩

/-- The rows of a type other than its outermost one: those of its parameter
types and result type, and those inside its row's error type. -/
def Ty.innerRows : Ty → List Row
  | .fn ps r ρ => paramRows ps ++ r.rows ++ ρ.rows.tail
  | τ => τ.rows

/-- Where the implicit row variables of a function's signature are, as effects.row-variables and effects.non-escaping-parameters put them. -/
structure FnDecl.ImplicitRows (d : FnDecl) : Prop where
  /-- They are among the function's row variables, which a use instantiates. -/
  listed : ∀ v ∈ d.implicits, v ∈ d.rowParams
  /-- Each parameter has a fresh one. -/
  fresh : d.implicits.Nodup
  /-- A non-escaping parameter is a `let` parameter of function type, whose
  row holds its implicit variable and no other. No other row of its type holds
  a row variable, since none may be written there (E0509). -/
  param : ∀ p ∈ d.params, ∀ v, p.implicit = some v →
    p.mode = .let ∧ ∃ ps r ρ, p.type = .fn ps r ρ ∧ ρ.vars = [v] ∧
      ∀ σ ∈ p.type.innerRows, σ.vars = []
  /-- The function's own row holds every implicit variable. -/
  own : ∀ v ∈ d.implicits, v ∈ d.row.vars
  /-- No other row of the signature holds one: implicit variables are never
  written. -/
  elsewhere : ∀ v ∈ d.implicits,
    (∀ p ∈ d.params, p.implicit ≠ some v → ∀ σ ∈ p.type.rows, v ∉ σ.vars) ∧
      (∀ σ ∈ d.result.rows, v ∉ σ.vars) ∧ ∀ σ ∈ d.row.rows.tail, v ∉ σ.vars
  /-- A row of the signature holds at most one row variable that it writes. -/
  written : ∀ σ ∈ d.type.rows, (σ.vars.filter (· ∉ d.implicits)).length ≤ 1

/-- A function without non-escaping parameters has no implicit row variables,
so its signature only needs rows that write at most one variable. -/
theorem FnDecl.implicitRows_of_none {d : FnDecl} (h : ∀ p ∈ d.params, p.implicit = none)
    (hw : ∀ σ ∈ d.type.rows, σ.vars.length ≤ 1) : d.ImplicitRows := by
  have hnil : d.implicits = [] := by
    simp only [FnDecl.implicits, List.filterMap_eq_nil_iff]
    exact h
  refine ⟨by simp [hnil], by simp [hnil], fun p hp v hv => ?_, by simp [hnil], by simp [hnil],
    fun σ hσ => by rw [hnil, List.filter_eq_self.2 (by simp)]; exact hw σ hσ⟩
  rw [h p hp] at hv
  exact nomatch hv

/-- `Self` in an `impl` block of the type named `T`: the record or variant
type of that name (traits.impl-blocks). -/
def Decls.selfType? (D : Decls) (T : Name) : Option Ty :=
  if (D.record? T).isSome then some (.record T)
  else if (D.variant? T).isSome then some (.variant T) else none

/-- Where `self` stands, as traits.impl-blocks and traits.methods puts it: an `impl` block is for a
type of the program, a function at the top level takes no `self`, and a
function of an `impl` block takes it, if at all, as its first parameter,
whose type is the block's. -/
structure Decls.Receivers (D : Decls) : Prop where
  types : ∀ i ∈ D.impls, (D.selfType? i.type).isSome
  functions : ∀ d ∈ D.functions, ∀ p ∈ d.params, p.name ≠ selfName
  later : ∀ i ∈ D.impls, ∀ d ∈ i.fns, ∀ p ∈ d.params.drop 1, p.name ≠ selfName
  first : ∀ i ∈ D.impls, ∀ d ∈ i.fns, ∀ p ∈ d.params.take 1,
    p.name = selfName → D.selfType? i.type = some p.type

/-- Declarations without `impl` blocks, whose functions take no `self`. -/
theorem Decls.receivers_of_nil {D : Decls} (himpls : D.impls = [])
    (hself : ∀ d ∈ D.functions, ∀ p ∈ d.params, p.name ≠ selfName) : D.Receivers :=
  ⟨by simp [himpls], hself, by simp [himpls], by simp [himpls]⟩

/-- The scope of a trait's signatures: `Self` alone, and no row variable. -/
def TraitDecl.scope : RowScope := ⟨[], fun _ _ => False, fun _ _ => False, [⟨selfParam, []⟩]⟩

/-- A trait's functions are methods, which take `self` first, and their
signatures name no row variable and no type parameter but `Self`
(traits.declaring-trait). Generic methods, functions without `self`, defaults and a
trait's own parameters are outside the calculus. -/
structure TraitDecl.WellFormed (t : TraitDecl) : Prop where
  receivers : ∀ mσ ∈ t.methods, ∃ m ps r ρ, mσ.2 = .fn ((m, .param selfParam) :: ps) r ρ
  closed : ∀ mσ ∈ t.methods, mσ.2.Closed
  signatures : ∀ mσ ∈ t.methods, mσ.2.WellFormed TraitDecl.scope

/-- An impl gives each method of its trait a function with no type parameters
or row variables, whose signature is the trait's with `Self` replaced by the
impl's type (traits.impl-members and traits.impl-signatures). -/
def TraitImpl.Implements (D : Decls) (i : TraitImpl) : Prop :=
  ∃ t, D.trait? i.trait = some t ∧ ∀ m σ, t.methods.lookup m = some σ →
    ∃ d ∈ i.fns, d.name = m ∧ d.typeParams = [] ∧ d.rowParams = [] ∧
      d.type = σ.substTys [(selfParam, i.type.type)]

/-- The conditions on declarations that declarations.function-declarations and declarations.unique-names states, as far as the calculus
needs them: names are unique where declarations.unique-names says so, so a type's `impl` blocks
define each name once (traits.inherent-names), only functions declare row variables
(effects.row-variables) and type parameters (declarations.function-declarations), their non-escaping parameters have implicit ones (effects.non-escaping-parameters),
only methods take `self` (traits.methods), and each trait impl implements its
trait (traits.impl-members). -/
structure Decls.WellFormed (D : Decls) : Prop where
  recordNames : (D.records.map (·.name)).Nodup
  fieldNames : ∀ r ∈ D.records, (r.fields.map Prod.fst).Nodup
  fieldsClosed : ∀ r ∈ D.records, ∀ f ∈ r.fields, f.2.Closed
  fieldsConcrete : ∀ r ∈ D.records, ∀ f ∈ r.fields, f.2.Concrete
  variantNames : (D.variants.map (·.name)).Nodup
  ctorNames : ∀ t ∈ D.variants, (t.ctors.map Prod.fst).Nodup
  payloadsClosed : ∀ t ∈ D.variants, ∀ c ∈ t.ctors, ∀ τ ∈ c.2, τ.Closed
  payloadsConcrete : ∀ t ∈ D.variants, ∀ c ∈ t.ctors, ∀ τ ∈ c.2, τ.Concrete
  fnNames : (D.fns.map (·.name)).Nodup
  paramNames : ∀ d ∈ D.fns, (d.params.map Param.name).Nodup
  rowParams : ∀ d ∈ D.fns, d.rowParams.Nodup
  typeParams : ∀ d ∈ D.fns, (d.typeParams.map TypeParam.name).Nodup
  signatures : ∀ d ∈ D.fns, d.type.WellFormed d.scope
  implicitRows : ∀ d ∈ D.fns, d.ImplicitRows
  receivers : D.Receivers
  traits : ∀ t ∈ D.traits, t.WellFormed
  traitImpls : ∀ i ∈ D.traitImpls, i.Implements D

/-- A program is typed when its declarations are well formed, every
function's body checks with every row checked in the scope that `scopeOf`
gives it, and `main` checks against `()` and its row, as `fn main() / row`
(program.main). `main` declares no row variables, so its row holds none
(effects.row-variables), and is a subset of `{io, raise<E>}`: it holds no
user-defined effect and no `resume` (handlers.no-effect-reaches-main). program.main also asks for
`E: Show`, a trait of the prelude, which the model leaves out. -/
structure Program.TypedIn (p : Program) (scopeOf : FnDecl → RowScope) : Prop where
  decls : p.decls.WellFormed
  fns : ∀ d ∈ p.decls.fns, d.WellTyped p.decls (scopeOf d)
  closed : (Ty.fn [] .unit p.row).Closed
  unhandled : p.row.effects = [] ∧ p.row.resume = none
  main : ∃ σ, HasType p.decls .closed [] (Effects.body p.row .unit) p.main σ ∧ Fits σ .unit

/-- A program that the checker accepts: `Program.TypedIn`, with every
function's body checked as effects.non-escaping-parameters checks it (`FnDecl.Lenient`). `main`
has no parameters, so nothing in it is lenient. -/
structure Program.LenientIn (p : Program) (scopeOf : FnDecl → RowScope) : Prop where
  decls : p.decls.WellFormed
  fns : ∀ d ∈ p.decls.fns, d.Lenient p.decls (scopeOf d)
  closed : (Ty.fn [] .unit p.row).Closed
  unhandled : p.row.effects = [] ∧ p.row.resume = none
  main : ∃ σ, HasType p.decls .closed [] (Effects.body p.row .unit) p.main σ ∧ Fits σ .unit

/-- A well-typed program: the checker accepts it, with a row that lacks an
implicit variable no error where the variable meets it (effects.non-escaping-parameters);
inside a `catch`, a call through a row variable needs the signature to pair the
variable with the caught type (effects.catch-around-row-variables); a use of a function passes a
row variable on to a paired one only with its pairing (effects.passing-to-paired-variables); and no
non-escaping parameter escapes (effects.no-escape). -/
structure Program.WellTyped (p : Program) : Prop extends Program.LenientIn p FnDecl.scope where
  noEscape : p.NoEscape

/-- A program that effects.paired-row-variables accepts without effects.passing-to-paired-variables: a use of a function may pass
a row variable on to a paired one without its pairing. -/
structure Program.WellTypedWithoutPassing (p : Program) : Prop
    extends Program.LenientIn p FnDecl.withoutPassingScope where
  noEscape : p.NoEscape

/-- A program that effects.catch-around-row-variables accepts as it was written, before effects.catch-around-row-variables amended
effects.catch-around-row-variables: inside a `catch`, a call through a row variable needs only a `raise`
label beside it. -/
structure Program.WellTypedAsRecorded (p : Program) : Prop
    extends Program.LenientIn p FnDecl.recordedScope where
  noEscape : p.NoEscape

/-! ## The no-escape rule checks every row -/

/-- A program that the checker and the no-escape rule accept has every row
checked: the variable can reach a row that lacks it only through a use that
breaks the no-escape rule (effects.no-escape). -/
theorem Program.LenientIn.typedIn {p : Program} {scopeOf : FnDecl → RowScope}
    (h : p.LenientIn scopeOf) (hne : p.NoEscape) : p.TypedIn scopeOf :=
  ⟨h.decls, fun d hd => (h.fns d hd).wellTyped (hne d hd), h.closed, h.unhandled, h.main⟩

/-- The checker accepts every program whose every row checks. -/
theorem Program.TypedIn.lenientIn {p : Program} {scopeOf : FnDecl → RowScope}
    (h : p.TypedIn scopeOf) : p.LenientIn scopeOf :=
  ⟨h.decls, fun d hd => (h.fns d hd).lenient, h.closed, h.unhandled, h.main⟩

/-- A well-typed program has every row checked. -/
theorem Program.WellTyped.typedIn {p : Program} (h : p.WellTyped) : p.TypedIn FnDecl.scope :=
  h.toLenientIn.typedIn h.noEscape

/-- A program whose every row checks, and from which no non-escaping parameter
escapes, is well typed. -/
theorem Program.TypedIn.wellTyped {p : Program} (h : p.TypedIn FnDecl.scope)
    (hne : p.NoEscape) : p.WellTyped :=
  ⟨h.lenientIn, hne⟩

/-! ## How the rules compare -/

/-- A body typed in a scope is typed in a larger one. -/
theorem FnDecl.WellTyped.of_le {D : Decls} {s s' : RowScope} {d : FnDecl}
    (h : d.WellTyped D s) (hs : s.Le s') : d.WellTyped D s' :=
  let ⟨σ, hbody, hfit⟩ := h
  ⟨σ, HasType.of_le hs hbody, hfit⟩

/-- A program typed in some scopes is typed in larger ones. -/
theorem Program.TypedIn.of_le {p : Program} {scopeOf scopeOf' : FnDecl → RowScope}
    (h : p.TypedIn scopeOf) (hle : ∀ d, (scopeOf d).Le (scopeOf' d)) : p.TypedIn scopeOf' :=
  ⟨h.decls, fun d hd => (h.fns d hd).of_le (hle d), h.closed, h.unhandled, h.main⟩

/-- effects.passing-to-paired-variables only adds a condition to effects.paired-row-variables. -/
theorem FnDecl.scope_le_withoutPassingScope (d : FnDecl) : d.scope.Le d.withoutPassingScope :=
  ⟨fun _ h => h, fun _ _ h => h, fun _ _ _ => trivial, fun _ h => h⟩

/-- effects.paired-row-variables only adds a condition to effects.catch-around-row-variables as it was written. -/
theorem FnDecl.withoutPassingScope_le_recordedScope (d : FnDecl) : d.withoutPassingScope.Le d.recordedScope :=
  ⟨fun _ h => h, fun _ _ _ => trivial, fun _ _ h => h, fun _ h => h⟩

/-- effects.passing-to-paired-variables only narrows effects.paired-row-variables: every program it accepts, effects.paired-row-variables accepts too. -/
theorem Program.WellTyped.withoutPassing {p : Program} (h : p.WellTyped) : p.WellTypedWithoutPassing :=
  ⟨(h.typedIn.of_le FnDecl.scope_le_withoutPassingScope).lenientIn, h.noEscape⟩

/-- effects.paired-row-variables only narrows effects.catch-around-row-variables: every program it accepts, the rule as
it was written accepts too. -/
theorem Program.WellTypedWithoutPassing.asRecorded {p : Program} (h : p.WellTypedWithoutPassing) :
    p.WellTypedAsRecorded :=
  ⟨((h.toLenientIn.typedIn h.noEscape).of_le FnDecl.withoutPassingScope_le_recordedScope).lenientIn,
    h.noEscape⟩

/-- Every program the model accepts, effects.catch-around-row-variables as it was written accepts. -/
theorem Program.WellTyped.asRecorded {p : Program} (h : p.WellTyped) :
    p.WellTypedAsRecorded :=
  h.withoutPassing.asRecorded

end Stilt
