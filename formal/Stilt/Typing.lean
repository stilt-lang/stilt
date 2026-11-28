import Stilt.Generics
import Stilt.Ops
import Stilt.Patterns
import Stilt.Typing.Uses
import Stilt.Typing.Context
import Stilt.Typing.Else
import Stilt.Typing.Shapes
import Stilt.Syntax.Forms
import Stilt.Typing.Io
import Stilt.Typing.Tasks

/-!
# Typing

The typing judgment `Γ ⊢ e : τ` of the calculus, under a context that records
the mutability of each variable and an `Effects` that records the row the
expression's effects must fit in.

The judgment states the checks of the Reference's expressions and its declarations for the expressions of the
calculus, the effect checks of effects.rows, effects.marking and effects.catch (rows, marking with `try`, and the `catch`
rules, with effects.catch-around-row-variables as effects.paired-row-variables and effects.passing-to-paired-variables amend it), the condition that effects.passing-to-paired-variables
puts on the uses of generic functions, and the mutability rule of modes.what-can-be-modified
(modes.what-can-be-modified). Exclusivity, the rest of modes.law, is in `Stilt.Exclusivity`.

The judgment checks every row, those that lack a non-escaping parameter's
implicit row variable included. effects.non-escaping-parameters lets the checker leave those
unchecked where the variable meets them (`Stilt.Lenient.Typing`), and on a
body that passes the no-escape rule the two agree (`Stilt.Lenient.Strict`).
Type soundness is proved of this judgment.

The contexts and effects it reads are in `Stilt.Typing.Context`, what a use of a generic
function asks of its arguments in `Stilt.Typing.Uses`, and what a let-else and an `Option`
fallback ask of their parts in `Stilt.Typing.Else`.
`Stilt.Weakening` shows that the judgment survives a larger context and a
larger row scope, and `Stilt.WellTyped` types declarations and programs with
it.
-/

namespace Stilt

section

variable (D : Decls) (scope : RowScope)

mutual

/-- `HasType D scope Γ fx e τ`: in the declarations `D`, a body whose row
variables `scope` describes gives `e` the type `τ` in the context `Γ`, and
`e`'s effects are allowed where `fx` holds.

Where an expression is checked against an expected type, its own type only
needs to fit that type (`Fits`): this is where `Never` converts and where the
row of a function value grows (declarations.never; effects.function-values). -/
inductive HasType : Ctx → Effects → Expr → Ty → Prop
  | var {Γ fx x τ mutable} :
      Γ.lookup x = some ⟨τ, mutable⟩ →
      HasType Γ fx (.var x) τ
  /-- An integer literal takes the integer type its context expects, which
  must hold it (numbers.integer-literals and numbers.negative-literals). -/
  | int {Γ fx k n} : k.Contains n → HasType Γ fx (.int n) (.int k)
  | bool {Γ fx b} : HasType Γ fx (.bool b) .bool
  | unit {Γ fx} : HasType Γ fx .unit .unit
  /-- Every field is given exactly once (expressions.struct-literal-fields), each checked
  against its declared type at the literal's type arguments, one for each of the record's
  type parameters (declarations.type-parameters and declarations.type-arguments). -/
  | record {Γ fx R args r fields} :
      D.record? R = some r →
      args.length = r.typeParams.length → (∀ τ ∈ args, τ.WellFormed scope) →
      (fields.map Prod.fst).Perm (r.fields.map Prod.fst) →
      FieldsFit Γ fx fields (r.fieldsAt args) →
      HasType Γ fx (.record R args fields) (.record R args)
  /-- A variant's payload fits its declared types at the literal's type arguments, one
  for each of the variant type's type parameters (declarations.type-parameters and
  declarations.type-arguments). -/
  | variant {Γ fx T args t C τs payload} :
      D.variant? T = some t →
      args.length = t.typeParams.length → (∀ τ ∈ args, τ.WellFormed scope) →
      (t.ctorsAt args).lookup C = some τs →
      ExprsFit Γ fx payload τs →
      HasType Γ fx (.variant T args C payload) (.variant T args)
  | list {Γ fx τ es} :
      τ.WellFormed scope →
      ExprsFit Γ fx es (List.replicate es.length τ) →
      HasType Γ fx (.list τ es) (.list τ)
  /-- A built-in operation's operands fit the types its signature gives them
  (values.left-to-right); a function of maps or sets finds keys of key types (std.map-key-bounds),
  and the operands' types implement the prelude traits that the operation stands behind
  (traits.required-traits). An operation that reads or writes the world's output or input is a
  call of a native whose row holds `io`, so the row it sits in holds `io` too, or it is E0502
  (effects.missing-effects and facts.io-and-capabilities). -/
  | op {Γ fx o es τs τ} :
      o.Sig τs τ →
      ExprsFit Γ fx es τs → o.KeysIn D τs τ → o.BoundsIn D scope τs →
      (o.io = true → fx.row.io = true) →
      HasType Γ fx (.op o es) τ
  /-- A view's operands fit `View.all`, `View.of` or `v.view` (views.making-view). -/
  | view {Γ fx es τs τ} :
      Op.Sig .view τs τ →
      ExprsFit Γ fx es τs →
      HasType Γ fx (.view es) τ
  /-- `e.f` requires a record type with a field `f` (types.field-access), whose type is
  its declared type at the record type's arguments. -/
  | field {Γ fx e R args r f τ} :
      HasType Γ fx e (.record R args) →
      D.record? R = some r → args.length = r.typeParams.length →
      (r.fieldsAt args).lookup f = some τ →
      HasType Γ fx (.field e f) τ
  /-- `e.n` requires a tuple type with more than `n` elements, whose field
  `n` is the element at that position (types.field-access). -/
  | elem {Γ fx e τs f τ} :
      HasType Γ fx e (.tuple τs) →
      (positions τs).lookup f = some τ →
      HasType Γ fx (.field e f) τ
  /-- `xs[i]` takes an `i64` index (std.lists). Only a list is indexed so, and a map through
  `MapOp.index` at its key type; an array is a list in the calculus. Nothing else has an index
  rule (expressions.indexing, E0317): `v[i]` on a view of a list is a form, the index of the
  view's `copy` (`Form.Shaped`). -/
  | index {Γ fx e i τ σ} :
      HasType Γ fx e (.list τ) →
      HasType Γ fx i σ → Fits σ .i64 →
      HasType Γ fx (.index e i) τ
  /-- A use of a function, called or taken as a value, with its type
  parameters instantiated by types that meet their bounds (traits.unsatisfied-bounds), and its row variables
  instantiated so that every row of its type keeps one `raise` label (effects.row-variables, effects.one-error-type and effects.inference), by rows without `resume`, which only an operation's body names (handlers.resume-outside-operation), and that passes on a row variable to a paired one only
  with its pairing (effects.passing-to-paired-variables). The rule holds in closure literals too,
  since the scope is the enclosing function's. Where the signature pairs `v` with `E`, every
  row the use gives `v` raises only the type the use gives `E`
  (effects.what-paired-variable-may-raise). The function may be the one whose body holds the
  use, at type arguments other than its own type parameters (polymorphism.recursion). -/
  | fnRef {Γ fx f d types rows} :
      D.fn? f = some d →
      rows.length = d.rowParams.length →
      d.type.InstantiableBy (d.rowParams.zip rows) → (∀ ρ ∈ rows, ρ.resume = none) →
      ((d.type.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows)).WellFormed scope →
      PassesOnPairs scope d (d.rowParams.zip rows) →
      TypeArgsFit D scope d.typeParams types →
      HasType Γ fx (.fnRef f types rows)
        ((d.type.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows))
  /-- `Trait.m` at a type that implements the trait, a type parameter through
  a bound included: a function value of the method's type with `Self` that
  type, whose first parameter is the receiver (traits.qualified-calls). A method call
  through a bound calls it with the receiver first (traits.method-resolution). A function
  of the trait without `self` is named on a type the same way, as `T.empty()` on a type
  parameter bounded by the trait and `i64.empty()` on a type with an impl, and `T.empty` is
  a function value (traits.functions-without-self); the calculus leaves out a trait's
  constants and defaults. The trait's parameters are the arguments that the bound or the
  impl gives them (traits.trait-arguments and traits.bound-arguments). Of `Eq`,
  `Ord` and `Show`, it names the impls that the program writes, which `==`, `<` and an
  interpolation at their types call (`MethodAt`); their built-in and structural impls are
  the calculus's operations. -/
  | method {Γ fx Tr t m σ τ args} :
      D.trait? Tr = some t →
      t.methods.lookup m = some σ →
      τ.Closed → τ.WellFormed scope → args.length = t.params.length → MethodAt D scope τ Tr args →
      HasType Γ fx (.method Tr m τ) (σ.substTys ((selfParam, τ) :: t.params.zip args))
  /-- A closure's body sees copies of the variables in scope, which it can't
  modify (expressions.capture), and its effects fit the closure's own row, not the
  row around it (effects.missing-effects). Its parameters are never non-escaping
  (effects.closure-parameters). The `try` around a closure literal marks the calls in it (effects.marking);
  a `catch` around it does not reach into it (effects.catch-around-row-variables). An `inout`
  parameter is no capture: the body may modify it, and the closure's type has `inout` there
  (expressions.inout-closure-parameters). -/
  | closure {Γ fx ps result ρ body σ} :
      (ps.map Param.name).Nodup →
      ps.all (·.implicit.isNone) = true →
      (Ty.fn (ps.map Param.sig) result ρ).WellFormed scope →
      HasType (Γ.freeze.params ps) ⟨ρ, fx.marked, false, result, false, false⟩ body σ →
      Fits σ result →
      HasType Γ fx (.closure ps result ρ body) (.fn (ps.map Param.sig) result ρ)
  | call {Γ fx callee args ps result σ} :
      HasType Γ fx callee (.fn ps result σ) →
      ArgsFit Γ fx args ps →
      CallAllowed scope fx σ →
      HasType Γ fx (.call callee args result) result
  | letIn {Γ fx x τ init body σ σ'} :
      τ.WellFormed scope →
      HasType Γ fx init σ → Fits σ τ →
      HasType (Γ.bind x ⟨τ, false⟩) fx body σ' →
      HasType Γ fx (.letIn x τ init body) σ'
  | varIn {Γ fx x τ init body σ σ'} :
      τ.WellFormed scope →
      HasType Γ fx init σ → Fits σ τ →
      HasType (Γ.bind x ⟨τ, true⟩) fx body σ' →
      HasType Γ fx (.varIn x τ init body) σ'
  | assign {Γ fx p e τ σ} :
      PlaceFits Γ fx p τ →
      HasType Γ fx e σ → Fits σ τ →
      HasType Γ fx (.assign p e) .unit
  /-- A statement before the last one of its block has type `()` or `Never`
  (expressions.statements and expressions.unused-values). -/
  | seq {Γ fx a b σ τ} :
      HasType Γ fx a σ → Fits σ .unit →
      HasType Γ fx b τ →
      HasType Γ fx (.seq a b) τ
  | «if» {Γ fx c τ a b σc σa σb} :
      τ.WellFormed scope →
      HasType Γ fx c σc → Fits σc .bool →
      HasType Γ fx a σa → Fits σa τ →
      HasType Γ fx b σb → Fits σb τ →
      HasType Γ fx (.if c τ a b) τ
  /-- Each arm's pattern fits the scrutinee's type, and the arms cover every
  value of it (patterns.match, patterns.algorithm and
  patterns.non-exhaustive-matches). So a `match` with no arms is one on a type without
  values (patterns.empty-matches). -/
  | «match» {Γ fx e σ τ arms} :
      τ.WellFormed scope →
      HasType Γ fx e σ →
      Exhaustive D (armRows arms) [σ] →
      ArmsFit Γ fx arms σ τ →
      HasType Γ fx (.match e τ arms) τ
  /-- The loop binds each element immutably, and its body has type `()` or
  `Never` (expressions.loop-types and expressions.for-iterables). -/
  | «for» {Γ fx x τ e body σ} :
      τ.WellFormed scope →
      HasType Γ fx e (.list τ) →
      HasType (Γ.bind x ⟨τ, false⟩) fx.inLoop body σ → Fits σ .unit →
      HasType Γ fx (.for x τ e body) .unit
  /-- `raise e` has type `Never` and performs `raise<E>`, where `E` is the
  error type of the row (effects.one-error-type and effects.raise). It needs no mark (effects.marking). -/
  | raise {Γ fx e E σ} :
      fx.row.raise = some E →
      HasType Γ fx e σ → Fits σ E →
      HasType Γ fx (.raise e) .never
  /-- `try e` has the type and the effects of `e` (effects.marking): it marks raising calls
  and does nothing else, so `try r` on a `Result` is still a `Result` (effects.result). -/
  | «try» {Γ fx e τ} :
      HasType Γ { fx with marked := true } e τ →
      HasType Γ fx (.try e) τ
  /-- The operand of `try e catch x => h` may raise `E`, which the arm binds;
  the arm's own effects go to the context (effects.catch). The arm is not part
  of the operand (effects.marking). The operand is checked for this `catch` wherever it
  sits, inside a closure literal too (effects.catch-around-row-variables). `E` names no type
  parameter: generic error types are outside the calculus. -/
  | tryCatch {Γ fx e E x h τ σ σ'} :
      E.WellFormed { scope with types := [] } →
      τ.WellFormed scope →
      HasType Γ ⟨fx.row.withRaise E, true, true, fx.result, fx.breaks, fx.continues⟩ e σ →
      Fits σ τ →
      HasType (Γ.bind x ⟨E, false⟩) fx h σ' → Fits σ' τ →
      HasType Γ fx (.tryCatch e E x h τ) τ
  /-- A `while`'s head is outside its body, which a `break` may exit; it has
  type `()` (expressions.break-and-continue and expressions.loop-types). -/
  | «while» {Γ fx c body σc σ} :
      HasType Γ fx c σc → Fits σc .bool →
      HasType Γ fx.inLoop body σ → Fits σ .unit →
      HasType Γ fx (.while c body) .unit
  /-- A `loop` whose body a `break` may exit has type `()`
  (expressions.loop-types). -/
  | loopBreaks {Γ fx body σ} :
      HasType Γ fx.inLoop body σ → Fits σ .unit →
      HasType Γ fx (.loop body) .unit
  /-- A `loop` whose body holds no `break` that exits it has type `Never`
  (expressions.loop-types): it ends only by raising, returning or panicking. -/
  | loopForever {Γ fx body σ} :
      HasType Γ { fx with continues := true, breaks := false } body σ → Fits σ .unit →
      HasType Γ fx (.loop body) .never
  /-- `break` and `continue` act on the innermost loop whose body holds them,
  and have type `Never` (expressions.break-and-continue and declarations.never). -/
  | «break» {Γ fx} : fx.breaks = true → HasType Γ fx .break .never
  | «continue» {Γ fx} : fx.continues = true → HasType Γ fx .continue .never
  /-- `return e` ends the function or closure whose body holds it, and its value
  fits that body's result type (expressions.closure-boundaries). -/
  | «return» {Γ fx e σ} :
      HasType Γ fx e σ → Fits σ fx.result →
      HasType Γ fx (.return e) .never
  /-- `E.op(e)` performs an operation of an effect that the row holds, on an
  argument of the operation's parameter type, and has its result type; the
  types an effect declares name no type parameter and no row variable
  (handlers.performing-operation and handlers.effects-in-rows). -/
  | perform {Γ fx op e A B σ} :
      op ≠ Operation.resume →
      D.operation? op = some (A, B) → A.Ground → B.Ground →
      op.effect ∈ fx.row.effects →
      HasType Γ fx e σ → Fits σ A →
      HasType Γ fx (.perform op e) B
  /-- `resume(e)`, in the body of an operation of a handler that takes control,
  takes the operation's result type and has the handler's type `R`
  (handlers.resuming). -/
  | resume {Γ fx e B R σ} :
      fx.row.resume = some (B, R) → B.Ground → R.Ground →
      HasType Γ fx e σ → Fits σ B →
      HasType Γ fx (.perform Operation.resume e) R
  /-- `with h { block }` of a handler that resumes every performance has its
  block's type; the block may perform the handler's effect (handlers.with). The handler
  implements no operation that the effect doesn't declare (E0511,
  handlers.handler-literals). -/
  | withH {Γ fx E eff h R r b τ} :
      E ≠ Operation.resume.effect → D.effect? E = some eff →
      HasType Γ fx h (.record R []) → D.record? R = some r →
      HandlerFits scope fx eff r.fields none →
      HasType Γ { fx with row := fx.row.withEffect E } b τ → (∀ f ∈ r.fields, f.1 ∈ eff.ops.map Prod.fst) →
      HasType Γ fx (.withH E false h b) τ
  /-- A `with` of a handler that takes control has the handler's type, which
  its block's fits (handlers.resuming). The handler implements no operation that the
  effect doesn't declare (E0511, handlers.handler-literals). -/
  | withControl {Γ fx E eff h R r b σ τ} :
      E ≠ Operation.resume.effect → D.effect? E = some eff →
      HasType Γ fx h (.record R []) → D.record? R = some r →
      HandlerFits scope fx eff r.fields (some τ) →
      HasType Γ { fx with row := fx.row.withEffect E } b σ → Fits σ τ → τ.Ground →
      (∀ f ∈ r.fields, f.1 ∈ eff.ops.map Prod.fst) →
      HasType Γ fx (.withH E true h b) τ
  /-- `when a, b { block }`: each handle a binding of a `Shared<T>` of its name's `T`, the names
  distinct, and the block typed with each name a `var` of its `T`; anything else is E0433
  (shared.when). -/
  | held {Γ fx ns hs body σ} :
      (ns.map Prod.fst).Nodup → (∀ p ∈ ns, p.2.WellFormed scope) →
      ExprsFit Γ fx hs (ns.map fun p => .shared p.2) →
      HasType (Γ.holding ns) fx body σ →
      (∀ h ∈ hs, ∃ x, h = .var x) →
      HasType Γ fx (.held ns hs body) σ
  /-- `let P = e else x` with a refutable `P` is a let-else, not the fallback
  (patterns.let-else, expressions.let-else and patterns.else-after-pattern): when the value of
  `e` matches `P`, the rest of the block runs with its bindings, and otherwise `x` runs, which has
  type `Never`, so a branch of another type is E0311. It means, and is typed as,
  `match e { P => rest, _ => x }` (`Expr.letElse`). The elaborated `P` names the variant type of
  each of its variants, which the Reference reads against the annotation or the type of `e`. -/
  | letElse {Γ fx e τ p bs rest x} :
      ¬ p.Irrefutable D → HasType Γ fx x .never →
      HasType Γ fx (.match e τ [⟨p, bs, none, rest⟩, ⟨.wild, [], none, x⟩]) τ →
      HasType Γ fx (.form .letElse (.match e τ [⟨p, bs, none, rest⟩, ⟨.wild, [], none, x⟩])) τ
  /-- `e₁ else e₂` requires `e₁` to have type `Option<T>`, the prelude's, so a `Result` must be
  converted with `.ok()` first, and `e₂` to have type `T` or `Never`, or it is E0311
  (expressions.option-fallback). Its value is the value inside a `Some`, and `e₂` runs only on a
  `None`: it means, and is typed as, `match e₁ { Some(v) => v, _ => e₂ }` (`Expr.orElse`). -/
  | orElse {Γ fx e₁ T τ v e₂ σ} :
      D.IsOption T → HasType Γ fx e₁ (.variant T [τ]) → HasType Γ fx e₂ σ → Fits σ τ →
      HasType Γ fx (.match e₁ τ [⟨.variant T "Some" [.bind v], [v], none, .var v⟩, ⟨.wild, [], none, e₂⟩]) τ →
      HasType Γ fx
        (.form .orElse (.match e₁ τ [⟨.variant T "Some" [.bind v], [v], none, .var v⟩, ⟨.wild, [], none, e₂⟩])) τ
  /-- A form of projections is typed as the calls it means (`Stilt.Projections`), and
  `Program.Projections` checks the rules of projections on it (projections.yield and
  projections.call-is-place); so is a form of writable views, whose rules `Program.ViewsWrite`
  checks (`Stilt.Writable`). -/
  | form {Γ fx k m τ} : k.meant = true → HasType Γ fx m τ → HasType Γ fx (.form k m) τ
  /-- A compound assignment, an integer literal at a float type and a field read through an
  `Option` are typed as the expression they mean, which has the shape that `Form.Shaped` gives:
  `place op= e` runs as values.compound-assignment-order orders it, an integer literal takes a
  float type that represents it exactly (numbers.integer-literals), and `e.f` reads the field
  of the value inside the `Option` of `e`, evaluated once (types.fields-through-option), at
  `Option<U>` (types.option-field-types); a record update builds its record from `base` and
  the fields written, evaluated in that order (`Expr.Update`); and an assignment through a map's
  element reads the element as `m[k]` does and stores the changed copy back
  (`Expr.ThroughElement`); and `v[i]` on a view of a list reads the element of the viewed part,
  as the index of its `copy`. -/
  | shaped {Γ fx k m τ} : k.Shaped m → HasType Γ fx m τ → HasType Γ fx (.form k m) τ
  /-- A form of tasks, scopes or lazy values is typed as the code it means in the sequential
  run, which its own rules shape (`TaskForm`, tasks.sequential-run). -/
  | task {Γ fx k m τ} : TaskForm D k m τ → HasType Γ fx m τ → HasType Γ fx (.form k m) τ

/-- Each expression fits the type at its position. -/
inductive ExprsFit : Ctx → Effects → List Expr → List Ty → Prop
  | nil {Γ fx} : ExprsFit Γ fx [] []
  | cons {Γ fx e es σ τ τs} :
      HasType Γ fx e σ → Fits σ τ →
      ExprsFit Γ fx es τs →
      ExprsFit Γ fx (e :: es) (τ :: τs)

/-- Each written field fits the type its record declares for it. -/
inductive FieldsFit : Ctx → Effects → List (Name × Expr) → List (Name × Ty) → Prop
  | nil {Γ fx declared} : FieldsFit Γ fx [] declared
  | cons {Γ fx f e fields declared σ τ} :
      declared.lookup f = some τ →
      HasType Γ fx e σ → Fits σ τ →
      FieldsFit Γ fx fields declared →
      FieldsFit Γ fx ((f, e) :: fields) declared

/-- Each argument fits its parameter. An `inout` argument is a place of
exactly the parameter's type, row included, since the callee may store a
value of that type in it (effects.inout-function-arguments). -/
inductive ArgsFit : Ctx → Effects → List Arg → List (Mode × Ty) → Prop
  | nil {Γ fx} : ArgsFit Γ fx [] []
  | value {Γ fx e args m τ σ ps} :
      m ≠ .inout →
      HasType Γ fx e σ → Fits σ τ →
      ArgsFit Γ fx args ps →
      ArgsFit Γ fx (.value e :: args) ((m, τ) :: ps)
  | inout {Γ fx p args τ ps} :
      PlaceFits Γ fx p τ →
      ArgsFit Γ fx args ps →
      ArgsFit Γ fx (.inout p :: args) ((.inout, τ) :: ps)

/-- A place that can be modified, of type `τ`: it is rooted in a `var`
binding or an `inout` parameter (expressions.mutable-places; modes.what-can-be-modified).
Values are data, so a value appears to change only through such a place
(values.value-semantics). -/
inductive PlaceFits : Ctx → Effects → Place → Ty → Prop
  | mk {Γ fx x path σ τ} :
      Γ.lookup x = some ⟨σ, true⟩ →
      PathFits Γ fx σ path τ →
      PlaceFits Γ fx ⟨x, path⟩ τ

/-- Following the projections of a place from a value of type `σ` reaches a
value of type `τ`. No projection reaches into a `str`, so no part of a string can be
assigned (values.strings). -/
inductive PathFits : Ctx → Effects → Ty → List Projection → Ty → Prop
  | nil {Γ fx τ} : PathFits Γ fx τ [] τ
  | field {Γ fx R args r f path τ τ'} :
      D.record? R = some r → args.length = r.typeParams.length →
      (r.fieldsAt args).lookup f = some τ →
      PathFits Γ fx τ path τ' →
      PathFits Γ fx (.record R args) (.field f :: path) τ'
  | index {Γ fx i path σ τ τ'} :
      HasType Γ fx i σ → Fits σ .i64 →
      PathFits Γ fx τ path τ' →
      PathFits Γ fx (.list τ) (.index i :: path) τ'
  /-- A tuple field, `.0`, of a tuple with more elements than its position
  (modes.places; types.field-access). -/
  | elem {Γ fx τs f path τ τ'} :
      (positions τs).lookup f = some τ →
      PathFits Γ fx τ path τ' →
      PathFits Γ fx (.tuple τs) (.field f :: path) τ'

/-- Each arm's pattern fits the scrutinee's type `σ`, its distinct names
are bound immutably (patterns.pattern-types and patterns.var-bindings), its guard and its
body see them (patterns.match), and its body fits the type of the `match` (patterns.arm-types). -/
inductive ArmsFit : Ctx → Effects → List Arm → Ty → Ty → Prop
  | nil {Γ fx σ τ} : ArmsFit Γ fx [] σ τ
  | cons {Γ fx arm arms σ σs τ ρ} :
      PatFits D arm.pattern σ σs →
      arm.binders = arm.pattern.binders →
      arm.binders.Nodup →
      GuardFits (Γ.bindAll arm.binders σs) fx arm.guard →
      HasType (Γ.bindAll arm.binders σs) fx arm.body ρ → Fits ρ τ →
      ArmsFit Γ fx arms σ τ →
      ArmsFit Γ fx (arm :: arms) σ τ

/-- An arm's guard, if it has one, is a condition: a `bool`, or `Never`
(patterns.guards and expressions.conditions). -/
inductive GuardFits : Ctx → Effects → Option Expr → Prop
  | none {Γ fx} : GuardFits Γ fx none
  | some {Γ fx g ρ} : HasType Γ fx g ρ → Fits ρ .bool → GuardFits Γ fx (some g)

end

end

end Stilt
