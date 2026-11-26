import Stilt.Generics
import Stilt.Ops
import Stilt.Patterns

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

`Stilt.Weakening` shows that the judgment survives a larger context and a
larger row scope, and `Stilt.WellTyped` types declarations and programs with
it.
-/

namespace Stilt

/-- What a typing context knows about a variable: its type, and whether the
body may modify it. Only `var` bindings and `inout` parameters can be modified
(modes.what-can-be-modified). -/
structure Binding where
  type : Ty
  mutable : Bool

/-- A typing context. The newest binding comes first and hides older ones
with the same name (expressions.shadowing). -/
abbrev Ctx := List (Name × Binding)

namespace Ctx

/-- The binding a name refers to. -/
def lookup (Γ : Ctx) (x : Name) : Option Binding := List.lookup x Γ

/-- Adds a binding. -/
def bind (Γ : Ctx) (x : Name) (b : Binding) : Ctx := (x, b) :: Γ

/-- The context of a closure body, before its parameters: every variable is
captured by copy and can't be modified (expressions.capture). -/
def freeze (Γ : Ctx) : Ctx := Γ.map fun (x, b) => (x, { b with mutable := false })

/-- Adds a function's or closure's parameters. Only `inout` parameters can be
modified (modes.what-can-be-modified). -/
def params (Γ : Ctx) (ps : List Param) : Ctx :=
  ps.foldl (fun Γ p => Γ.bind p.name ⟨p.type, p.mode = .inout⟩) Γ

/-- Adds the names of a `when`, each a `var` of its value (shared.when). -/
def holding (Γ : Ctx) (names : List (Name × Ty)) : Ctx :=
  names.foldl (fun Γ p => Γ.bind p.1 ⟨p.2, true⟩) Γ

/-- Adds the immutable bindings of a pattern (modes.what-can-be-modified). -/
def bindAll (Γ : Ctx) (xs : List Name) (τs : List Ty) : Ctx :=
  (xs.zip τs).foldl (fun Γ (x, τ) => Γ.bind x ⟨τ, false⟩) Γ

end Ctx

/-- Where an expression sits, as far as its effects are concerned (effects.rows). -/
structure Effects where
  /-- The row its effects must fit in (effects.missing-effects). -/
  row : Row
  /-- Whether it is inside the operand of a `try`, which marks its raising
  calls, closures included (effects.marking). -/
  marked : Bool
  /-- Whether it is inside the operand of a `try … catch` and outside every
  closure literal in that operand (effects.catch-around-row-variables). The `catch` it
  belongs to is the nearest one, whose error type is `row.raise`. -/
  catching : Bool
  /-- The result type of the function or closure whose body holds it, which a
  `return` fits (expressions.closure-boundaries). The program's `main`
  expression is no body, and its result type is `Never`, which no `return`'s
  value has. -/
  result : Ty
  /-- Whether it is inside the body of a loop that a `break` may exit
  (expressions.break-and-continue and expressions.loop-types). -/
  breaks : Bool
  /-- Whether it is inside the body of a loop (expressions.break-and-continue). -/
  continues : Bool

/-- Where the body of a function or a closure whose row is `row` and whose
result type is `result` sits: outside every `try` and every loop. -/
def Effects.body (row : Row) (result : Ty) : Effects := ⟨row, false, false, result, false, false⟩

/-- The body of a loop that a `break` may exit. -/
def Effects.inLoop (fx : Effects) : Effects := { fx with breaks := true, continues := true }

/-- A call whose callee has the row `σ`, as instantiated at the call, may be
made where `fx` holds, in a body whose row variables `scope` describes. -/
structure CallAllowed (scope : RowScope) (fx : Effects) (σ : Row) : Prop where
  /-- A call contributes its callee's row, which must fit (effects.missing-effects). -/
  within : σ.Within fx.row
  /-- A call that can raise is marked by a `try` (effects.marking). -/
  marked : σ.raise.isSome = true → fx.marked = true
  /-- Inside the operand of a `catch`, a call whose row holds a row variable,
  written or implicit, could raise any error type through it (effects.catch).
  It is allowed only if the row also holds `raise<E>` and the signature pairs
  each such variable with `E` (effects.catch-around-row-variables). The row may have been written
  in the body or formed by an instantiation: the check is on the row as the
  call sees it. -/
  paired : fx.catching = true → ∀ v ∈ σ.vars, ∃ E, σ.raise = some E ∧ scope.pairs v E
  /-- No call is of the body of an operation of a handler that takes control,
  whose row holds `resume`: only a `with` calls it, as no code but such a body
  names `resume` and no closure holds one (handlers.resume-outside-operation and
  handlers.resume-at-most-once). -/
  resume : σ.resume = none

/-- The signature pairs `v` with `E`: some row of its parameter types, at any
depth, or its own row holds both `v` and `raise<E>` (effects.paired-row-variables). The rows
are those of the elaborated signature, so a non-escaping parameter's implicit
variable, which its own row and the function's hold, is paired with `E` when
either names `raise<E>`. -/
def FnDecl.pairs (d : FnDecl) (v : Name) (E : Ty) : Prop :=
  ∃ ρ ∈ paramRows (d.params.map Param.sig) ++ [d.row], v ∈ ρ.vars ∧ ρ.raise = some E

/-- A use of `d` that instantiates its row variables with `s` passes on a row
variable of the enclosing function only with its pairing: where `d` pairs `v`
with `E` and `s` gives `v` a row that holds `r`, written or implicit, the
enclosing scope pairs `r` with the type the use gives `E` (effects.passing-to-paired-variables).

With effects.one-error-type, which leaves each row of the instantiated signature one
`raise` label, this keeps `v` from adding any error type but `E`: a concrete
instantiation is limited by effects.one-error-type, and one that holds `r` is limited by the
pairing of `r`, which every use of the enclosing function checks in turn. -/
def PassesOnPairs (scope : RowScope) (d : FnDecl) (s : RowSubst) : Prop :=
  ∀ v E ρ r, d.pairs v E → s.lookup v = some ρ → r ∈ ρ.vars →
    scope.passOn r (E.substRows s)

/-- `τ` implements the trait `B`, as far as a body whose type parameters
`scope` describes knows: a type parameter through its bounds, which are all
the body knows of it, and a type with a head through the program's impl of `B`
for that head (traits.unsatisfied-bounds and traits.implementing-trait). -/
def Satisfies (D : Decls) (scope : RowScope) (τ : Ty) (B : Name) : Prop :=
  (∃ p ∈ scope.types, τ = .param p.name ∧ B ∈ p.bounds) ∨
    ∃ h, τ.head? = some h ∧ (D.traitImpl? B h).isSome

/-- The type arguments of a use of a function, one for each of its type
parameters: closed, well formed where the use is, and meeting the parameter's
bounds (traits.unsatisfied-bounds). -/
def TypeArgsFit (D : Decls) (scope : RowScope) (ps : List TypeParam) (τs : List Ty) : Prop :=
  Forall₂ (fun p τ => τ.Closed ∧ τ.WellFormed scope ∧ ∀ B ∈ p.bounds, Satisfies D scope τ B) ps τs

/-- The row of a `with`'s block: the row around it, with the handler's effect
(handlers.with). -/
def Row.withEffect (ρ : Row) (E : Name) : Row := { ρ with effects := E :: ρ.effects }

/-- A handler's fields, `fields` of its record type, implement each operation
of the effect `eff`: under the operation's name, a function of its argument
type that ends with its result type, or with the `with`'s type `R` for a
handler that takes control, whose row's `resume` then takes the operation's
result type and gives `R`. The row, but for its `resume`, holds what a call
where `fx` holds may perform (handlers.handler-literals, handlers.handler-types
and handlers.resuming). -/
def HandlerFits (scope : RowScope) (fx : Effects) (eff : EffectDecl)
    (fields : List (Name × Ty)) (control : Option Ty) : Prop :=
  ∀ o A B, eff.ops.lookup o = some (A, B) → ∃ ρ,
    fields.lookup o = some (.fn [(.let, A)] (control.getD B) ρ) ∧
      ρ.resume = control.map (B, ·) ∧ CallAllowed scope fx { ρ with resume := none }

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
  against its declared type. -/
  | record {Γ fx R r fields} :
      D.record? R = some r →
      (fields.map Prod.fst).Perm (r.fields.map Prod.fst) →
      FieldsFit Γ fx fields r.fields →
      HasType Γ fx (.record R fields) (.record R)
  | variant {Γ fx T t C τs payload} :
      D.variant? T = some t →
      t.ctors.lookup C = some τs →
      ExprsFit Γ fx payload τs →
      HasType Γ fx (.variant T C payload) (.variant T)
  | list {Γ fx τ es} :
      τ.WellFormed scope →
      ExprsFit Γ fx es (List.replicate es.length τ) →
      HasType Γ fx (.list τ es) (.list τ)
  /-- A built-in operation's operands fit the types its signature gives them
  (values.left-to-right). -/
  | op {Γ fx o es τs τ} :
      o.Sig τs τ →
      ExprsFit Γ fx es τs →
      HasType Γ fx (.op o es) τ
  /-- A view's operands fit `View.all`, `View.of` or `v.view` (views.making-view). -/
  | view {Γ fx es τs τ} :
      Op.Sig .view τs τ →
      ExprsFit Γ fx es τs →
      HasType Γ fx (.view es) τ
  /-- `e.f` requires a record type with a field `f` (types.field-access). -/
  | field {Γ fx e R r f τ} :
      HasType Γ fx e (.record R) →
      D.record? R = some r →
      r.fields.lookup f = some τ →
      HasType Γ fx (.field e f) τ
  /-- `e.n` requires a tuple type with more than `n` elements, whose field
  `n` is the element at that position (types.field-access). -/
  | elem {Γ fx e τs f τ} :
      HasType Γ fx e (.tuple τs) →
      (positions τs).lookup f = some τ →
      HasType Γ fx (.field e f) τ
  /-- `xs[i]` takes an `i64` index (std.lists). -/
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
  through a bound calls it with the receiver first (traits.method-resolution). -/
  | method {Γ fx Tr t m σ τ} :
      D.trait? Tr = some t →
      t.methods.lookup m = some σ →
      τ.Closed → τ.WellFormed scope → Satisfies D scope τ Tr →
      HasType Γ fx (.method Tr m τ) (σ.substTys [(selfParam, τ)])
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
  /-- `try e` has the type and the effects of `e` (effects.marking). -/
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
  block's type; the block may perform the handler's effect (handlers.with). -/
  | withH {Γ fx E eff h R r b τ} :
      E ≠ Operation.resume.effect → D.effect? E = some eff →
      HasType Γ fx h (.record R) → D.record? R = some r →
      HandlerFits scope fx eff r.fields none →
      HasType Γ { fx with row := fx.row.withEffect E } b τ →
      HasType Γ fx (.withH E false h b) τ
  /-- A `with` of a handler that takes control has the handler's type, which
  its block's fits (handlers.resuming). -/
  | withControl {Γ fx E eff h R r b σ τ} :
      E ≠ Operation.resume.effect → D.effect? E = some eff →
      HasType Γ fx h (.record R) → D.record? R = some r →
      HandlerFits scope fx eff r.fields (some τ) →
      HasType Γ { fx with row := fx.row.withEffect E } b σ → Fits σ τ → τ.Ground →
      HasType Γ fx (.withH E true h b) τ
  /-- `when a, b { block }`: each handle a `Shared<T>` of its name's `T`, the names
  distinct, and the block typed with each name a `var` of its `T` (shared.when). -/
  | held {Γ fx ns hs body σ} :
      (ns.map Prod.fst).Nodup → (∀ p ∈ ns, p.2.WellFormed scope) →
      ExprsFit Γ fx hs (ns.map fun p => .shared p.2) →
      HasType (Γ.holding ns) fx body σ →
      HasType Γ fx (.held ns hs body) σ

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
  | field {Γ fx R r f path τ τ'} :
      D.record? R = some r →
      r.fields.lookup f = some τ →
      PathFits Γ fx τ path τ' →
      PathFits Γ fx (.record R) (.field f :: path) τ'
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
are bound immutably (patterns.pattern-types and patterns.var-bindings), and its
body fits the type of the `match` (patterns.arm-types). -/
inductive ArmsFit : Ctx → Effects → List Arm → Ty → Ty → Prop
  | nil {Γ fx σ τ} : ArmsFit Γ fx [] σ τ
  | cons {Γ fx arm arms σ σs τ ρ} :
      PatFits D arm.pattern σ σs →
      arm.binders = arm.pattern.binders →
      arm.binders.Nodup →
      HasType (Γ.bindAll arm.binders σs) fx arm.body ρ → Fits ρ τ →
      ArmsFit Γ fx arms σ τ →
      ArmsFit Γ fx (arm :: arms) σ τ

end

end

end Stilt
