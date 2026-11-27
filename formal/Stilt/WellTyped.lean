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
  /-- A row of the signature holds at most one row variable that it writes
  (effects.repeated-elements). -/
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
  if (D.record? T).isSome then some (.record T [])
  else if (D.variant? T).isSome then some (.variant T []) else none

/-- `Self` in an `impl` block: the record or variant type that the block names, at the
block's type parameters, one for each of the type's. A block with another number of them is
E0302 (traits.impl-blocks). -/
def Decls.blockType? (D : Decls) (i : ImplDecl) : Option Ty :=
  let args := i.typeParams.map fun p => Ty.param p.name
  match D.record? i.type, D.variant? i.type with
  | some r, _ => if r.typeParams.length = args.length then some (.record i.type args) else none
  | none, some v => if v.typeParams.length = args.length then some (.variant i.type args) else none
  | none, none => none

/-- Where `self` stands, as traits.impl-blocks and traits.methods puts it: an `impl` block is for a
type of the program, at the block's type parameters, a function at the top level takes no
`self`, and a function of an `impl` block takes it, if at all, as its first parameter,
whose type is the block's. -/
structure Decls.Receivers (D : Decls) : Prop where
  types : ∀ i ∈ D.impls, (D.blockType? i).isSome
  functions : ∀ d ∈ D.functions, ∀ p ∈ d.params, p.name ≠ selfName
  later : ∀ i ∈ D.impls, ∀ d ∈ i.fns, ∀ p ∈ d.params.drop 1, p.name ≠ selfName
  first : ∀ i ∈ D.impls, ∀ d ∈ i.fns, ∀ p ∈ d.params.take 1,
    p.name = selfName → D.blockType? i = some p.type

/-- Declarations without `impl` blocks, whose functions take no `self`. -/
theorem Decls.receivers_of_nil {D : Decls} (himpls : D.impls = [])
    (hself : ∀ d ∈ D.functions, ∀ p ∈ d.params, p.name ≠ selfName) : D.Receivers :=
  ⟨by simp [himpls], hself, by simp [himpls], by simp [himpls]⟩

/-- The scope of a trait's signatures: `Self` and the trait's own parameters, without bounds,
and no row variable (traits.trait-parameters). -/
def TraitDecl.scope (t : TraitDecl) : RowScope :=
  ⟨[], fun _ _ => False, fun _ _ => False, ⟨selfParam, [], []⟩ :: t.params.map (⟨·, [], []⟩)⟩

/-- A trait's functions are methods, which take `self` first, of type `Self`, and functions
without `self` (traits.functions-without-self), and their signatures name no row variable
and no type parameter but `Self` and the trait's parameters, which are distinct
(traits.declaring-trait and traits.trait-parameters). Generic methods, defaults and
constants are outside the calculus. -/
structure TraitDecl.WellFormed (t : TraitDecl) : Prop where
  functions : ∀ mσ ∈ t.methods, ∃ ps r ρ, mσ.2 = .fn ps r ρ
  closed : ∀ mσ ∈ t.methods, mσ.2.Closed
  signatures : ∀ mσ ∈ t.methods, mσ.2.WellFormed t.scope
  params : (selfParam :: t.params).Nodup

/-- The number of type parameters of the constructor that a head names. -/
def Decls.arity (D : Decls) : Head → Nat
  | .record R => ((D.record? R).map (·.typeParams.length)).getD 0
  | .variant T => ((D.variant? T).map (·.typeParams.length)).getD 0
  | _ => 0

/-- An impl gives each method of its trait a function with no type parameters of its own
or row variables, whose signature is the trait's with `Self` replaced by the
impl's type and each trait parameter by the impl's argument for it (traits.impl-members and
traits.impl-signatures). Its type is its constructor at its parameters, one for each of the
constructor's, or it is E0302 (traits.implementing-trait). It gives one argument for each of the
trait's parameters, or it is E0300, each a type that names only the impl's parameters
(traits.trait-arguments). The bounds of its parameters write no trait arguments. -/
def TraitImpl.Implements (D : Decls) (i : TraitImpl) : Prop :=
  ∃ t, D.trait? i.trait = some t ∧ i.args.length = t.params.length ∧
    (∀ a ∈ i.args, a.Closed ∧ ∀ T ∈ a.params, T ∈ i.typeParams.map TypeParam.name) ∧
    i.typeParams.length = D.arity i.type ∧ (∀ p ∈ i.typeParams, p.args = []) ∧
    ∀ m σ, t.methods.lookup m = some σ →
    ∃ d ∈ i.fns, d.name = m ∧ d.typeParams = [] ∧ d.rowParams = [] ∧
      d.type = σ.substTys ((selfParam, i.selfType) :: t.params.zip i.args)

/-- A bound that writes its trait's arguments writes one for each of the trait's parameters,
or it is E0300, and they name only the function's type parameters (traits.bound-arguments). -/
def Decls.BoundArgs (D : Decls) : Prop :=
  ∀ d ∈ D.fns, ∀ p ∈ d.typeParams, ∀ B args, p.argsOf B = some args →
    B ∈ p.bounds ∧ (∃ t, D.trait? B = some t ∧ args.length = t.params.length) ∧
      ∀ a ∈ args, ∀ T ∈ a.params, T ∈ d.typeParams.map TypeParam.name

/-- The constants declared before a constant, as the bindings its value reads: each of its
type, and immutable. -/
def constCtx (cs : List ConstDecl) : Ctx := cs.reverse.map fun c => (c.name, ⟨c.type, false⟩)

/-- Each constant's value is a constant expression (declarations.constant-expressions) of
the type it declares (declarations.constant-declarations), checked with only the constants
declared before it in scope. So no constant names itself or a later one, and constants
never name one another in a cycle (declarations.constant-cycles): the program lists its
constants in an order of their uses, which only constants without a cycle have. A
constant expression performs nothing, and is no function's body. -/
def Decls.ConstsTyped (D : Decls) : Prop :=
  ∀ pre c post, D.consts = pre ++ c :: post →
    c.value.IsConstant ∧ c.type.WellFormed .closed ∧
      ∃ σ, HasType D .closed (constCtx pre) (Effects.body Row.pure .never) c.value σ ∧
        Fits σ c.type

/-- The names of the type namespace: those of the records, the variant types, the traits
and the effects (declarations.namespaces). -/
def Decls.typeNames (D : Decls) : List Name :=
  D.records.map (·.name) ++ D.variants.map (·.name) ++ D.traits.map (·.name) ++
    D.effects.map (·.name)

/-- Each effect that a row of the type names, at any depth, is an effect of the program:
an `Upper` name in a row that names no effect is E0211 (handlers.effects-in-rows). -/
def Ty.EffectsIn (D : Decls) (τ : Ty) : Prop :=
  ∀ ρ ∈ τ.rows, ∀ E ∈ ρ.effects, E ∈ D.effects.map (·.name)

/-- The types that the declarations write name only effects of the program
(handlers.effects-in-rows): those of record fields, variant payloads, function signatures,
the operations of effects and the methods of traits. The types that a body writes are
outside this check. -/
structure Decls.EffectsDeclared (D : Decls) : Prop where
  fields : ∀ r ∈ D.records, ∀ f ∈ r.fields, f.2.EffectsIn D
  payloads : ∀ t ∈ D.variants, ∀ c ∈ t.ctors, ∀ τ ∈ c.2, τ.EffectsIn D
  signatures : ∀ d ∈ D.fns, d.type.EffectsIn D
  operations : ∀ e ∈ D.effects, ∀ o ∈ e.ops, o.2.1.EffectsIn D ∧ o.2.2.EffectsIn D
  methods : ∀ t ∈ D.traits, ∀ m ∈ t.methods, m.2.EffectsIn D

/-- The head of the record or variant type named `T`. -/
def Decls.headOf? (D : Decls) (T : Name) : Option Head :=
  if (D.record? T).isSome then some (.record T)
  else if (D.variant? T).isSome then some (.variant T) else none

/-- The record or variant type named `T` at its own type parameters, with them. -/
def Decls.ownType? (D : Decls) (T : Name) : Option (Ty × List Name) :=
  match D.record? T, D.variant? T with
  | some r, _ => some (.record T (r.typeParams.map .param), r.typeParams)
  | none, some v => some (.variant T (v.typeParams.map .param), v.typeParams)
  | none, none => none

/-- The names of the functions of the trait `Tr`: those its declaration declares, and for a
trait of the prelude those that `std.prelude` declares. -/
def Decls.traitFns (D : Decls) (Tr : Name) : List Name :=
  ((D.trait? Tr).map fun t => t.methods.map Prod.fst).getD [] ++
    ((PreludeTrait.ofName? Tr).map PreludeTrait.fns).getD []

/-- The type named `T` implements the prelude trait `t` through its structural impl: a
generic type when it would with every type parameter implementing `t` (traits.name-clashes). -/
def Decls.StructurallyImplements (D : Decls) (T : Name) (t : PreludeTrait) : Prop :=
  ∃ τ ps, D.ownType? T = some (τ, ps) ∧
    D.Implements ⟨[], fun _ _ => False, fun _ _ => False, ps.map (⟨·, [t.name], []⟩)⟩ t τ

/-- No inherent function of a type has the name of a function of a trait that the type
implements, through an impl that the program writes or through a structural impl: either is
E0308 (traits.name-clashes). The calculus has no constants, so no constant of a trait
clashes. -/
def Decls.NoNameClashes (D : Decls) : Prop :=
  ∀ i ∈ D.impls, ∀ d ∈ i.fns,
    (∀ ti ∈ D.traitImpls, D.headOf? i.type = some ti.type → d.name ∉ D.traitFns ti.trait) ∧
      ∀ t, D.StructurallyImplements i.type t → d.name ∉ t.fns

/-- The conditions on declarations that declarations.function-declarations and declarations.unique-names states, as far as the calculus
needs them: names are unique where declarations.unique-names says so, so a type's `impl` blocks
define each name once (traits.inherent-names), only functions declare row variables
(effects.row-variables), a record or variant type's fields and payloads name only its own type
parameters, outside their rows (declarations.type-parameters), functions declare type
parameters (declarations.function-declarations), their non-escaping parameters have implicit ones (effects.non-escaping-parameters),
only methods take `self` (traits.methods), each trait impl implements its
trait and holds no other member (traits.impl-members), a trait has one impl per type
(traits.coherence), no inherent function hides a trait's (traits.name-clashes), and each effect declares operations, each once
(handlers.declaring-effect). The value namespace's other half, variants of one name in
two types, is outside the calculus, which names a variant by its type and its own name. -/
structure Decls.WellFormed (D : Decls) : Prop where
  recordNames : (D.records.map (·.name)).Nodup
  fieldNames : ∀ r ∈ D.records, (r.fields.map Prod.fst).Nodup
  fieldsClosed : ∀ r ∈ D.records, ∀ f ∈ r.fields, f.2.Closed
  fieldRows : ∀ r ∈ D.records, ∀ f ∈ r.fields, ∀ ρ ∈ f.2.rows, ρ.ParamFree
  variantNames : (D.variants.map (·.name)).Nodup
  ctorNames : ∀ t ∈ D.variants, (t.ctors.map Prod.fst).Nodup
  payloadsClosed : ∀ t ∈ D.variants, ∀ c ∈ t.ctors, ∀ τ ∈ c.2, τ.Closed
  payloadRows : ∀ t ∈ D.variants, ∀ c ∈ t.ctors, ∀ τ ∈ c.2, ∀ ρ ∈ τ.rows, ρ.ParamFree
  paramsDeclared : D.ParamsDeclared
  fnNames : (D.fns.map (·.name)).Nodup
  paramNames : ∀ d ∈ D.fns, (d.params.map Param.name).Nodup
  rowParams : ∀ d ∈ D.fns, d.rowParams.Nodup
  /-- A function's type parameters have distinct names, those of a function of an `impl`
  block with the block's before its own, so it declares no generic with the name of one of
  the block's: E0208 (traits.inherent-names). -/
  typeParams : ∀ d ∈ D.fns, (d.typeParams.map TypeParam.name).Nodup
  signatures : ∀ d ∈ D.fns, d.type.WellFormed d.scope
  implicitRows : ∀ d ∈ D.fns, d.ImplicitRows
  receivers : D.Receivers
  traits : ∀ t ∈ D.traits, t.WellFormed
  traitImpls : ∀ i ∈ D.traitImpls, i.Implements D
  /-- The type namespace holds each name once: a record, a variant type, a trait and an
  effect of one name are E0208 (declarations.namespaces and declarations.unique-names). -/
  typeNames : D.typeNames.Nodup
  /-- An effect has one or more operations (E0518), each named once in it (E0208)
  (handlers.declaring-effect). -/
  effectOps : ∀ e ∈ D.effects, e.ops ≠ [] ∧ (e.ops.map Prod.fst).Nodup
  /-- A trait has at most one impl per type: a second is E0304 (traits.coherence). -/
  coherent : (D.traitImpls.map fun i => (i.trait, i.type)).Nodup
  /-- An impl holds no member that its trait doesn't declare: one is E0306
  (traits.impl-members). -/
  implMembers : ∀ i ∈ D.traitImpls, ∀ d ∈ i.fns,
    ∃ t, D.trait? i.trait = some t ∧ d.name ∈ t.methods.map Prod.fst
  /-- The rows of declared types name only declared effects (E0211,
  handlers.effects-in-rows). -/
  effectsDeclared : D.EffectsDeclared
  /-- Each constant is declared once, under its name or its `Type.NAME`
  (declarations.unique-names), and its type names no type parameter: those of an inherent
  block with type parameters aren't in scope there, which is E0211
  (declarations.impl-constants). -/
  constNames : (D.consts.map (·.name)).Nodup
  constTypes : ∀ c ∈ D.consts, c.type.params = []
  consts : D.ConstsTyped
  /-- No inherent function hides a function of a trait that its type implements (E0308,
  traits.name-clashes). -/
  nameClashes : D.NoNameClashes
  /-- A bound's arguments are one for each of its trait's parameters (E0300,
  traits.bound-arguments). -/
  boundArgs : D.BoundArgs

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
