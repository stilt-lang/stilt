import Stilt.Typing
import Stilt.NoEscape

/-!
# The checker's typing

effects.no-escape makes a row that doesn't hold a non-escaping parameter's
implicit row variable, where the variable meets it, no error of its own: "the
variable can reach such a row only through a use that breaks this rule", the
no-escape rule, whose error the checker reports instead (E0508).

`Lenient.HasType` is the typing judgment of `Stilt.Typing` with that leniency.
The variable meets a row where the parameter's type meets an expected type: an
occurrence of the parameter, or a closure literal that names it, checked
against a type whose row lacks the variable. Rows that a program writes never
hold the variable, and inferred ones hold it only where the parameter's type
has flowed from such an occurrence. So there, and only there, the check lets
the row lack the function's implicit variables (`LenientFits`). Three places
keep the variable:

* a call through the parameter performs its row where the call is, and the
  `catch` rules of effects.catch-around-row-variables read it there;
* a closure literal's row holds the effects of its body, which become part of
  its type (effects.inference);
* an argument given to a non-escaping parameter of the function a call names
  instantiates that parameter's implicit variable with what the argument's row
  holds beyond the row written (effects.non-escaping-parameters), so the parameter's row holds the
  argument's, which is checked as it is.

The judgment carries the non-escaping parameters in scope, which a binder of
the same name hides, as the no-escape rule does (expressions.shadowing).
`Stilt.Lenient.Strict` shows that, on a body that passes the no-escape rule,
it checks every row.
-/

namespace Stilt

/-- The row without the variables `vs`. -/
def Row.without (ρ : Row) (vs : List Name) : Row := { ρ with vars := ρ.vars.filter (· ∉ vs) }

/-- Whether `e` carries one of the non-escaping parameters `N`: it is an
occurrence of one, or a closure literal that names one, as the no-escape rule
sees them (effects.no-escape). -/
def Expr.carries (N : List Name) : Expr → Bool
  | .var x | .move x => N.contains x
  | .closure ps _ _ body => body.names (N.removeAll (ps.map Param.name))
  | _ => false

/-- `e`, of type `σ`, checked against the expected type `τ`, in a body whose
non-escaping parameters in scope are `N` and whose implicit row variables are
`vs`. Its type fits `τ`, or `e` carries a parameter and its type fits `τ` once
its row loses the implicit variables: a row that lacks one is no error where
the variable meets it (effects.no-escape). -/
def LenientFits (vs N : List Name) (e : Expr) (σ τ : Ty) : Prop :=
  Fits σ τ ∨ e.carries N = true ∧ ∃ ps r ρ, σ = .fn ps r ρ ∧ Fits (.fn ps r (ρ.without vs)) τ

namespace Lenient

section

variable (D : Decls) (scope : RowScope) (vs : List Name)

mutual

/-- `Lenient.HasType D scope vs N Γ fx e τ`: the checker gives `e` the type
`τ`, as `HasType` does, with every check against an expected type lenient
where a parameter of `N` meets it (`LenientFits`). -/
inductive HasType : List Name → Ctx → Effects → Expr → Ty → Prop
  | var {N Γ fx x τ mutable} :
      Γ.lookup x = some ⟨τ, mutable⟩ →
      HasType N Γ fx (.var x) τ
  | int {N Γ fx k n} : k.Contains n → HasType N Γ fx (.int n) (.int k)
  | bool {N Γ fx b} : HasType N Γ fx (.bool b) .bool
  | unit {N Γ fx} : HasType N Γ fx .unit .unit
  | record {N Γ fx R r fields} :
      D.record? R = some r →
      (fields.map Prod.fst).Perm (r.fields.map Prod.fst) →
      FieldsFit N Γ fx fields r.fields →
      HasType N Γ fx (.record R fields) (.record R)
  | variant {N Γ fx T t C τs payload} :
      D.variant? T = some t →
      t.ctors.lookup C = some τs →
      ExprsFit N Γ fx payload τs →
      HasType N Γ fx (.variant T C payload) (.variant T)
  | list {N Γ fx τ es} :
      τ.WellFormed scope →
      ExprsFit N Γ fx es (List.replicate es.length τ) →
      HasType N Γ fx (.list τ es) (.list τ)
  | op {N Γ fx o es τs τ} :
      o.Sig τs τ →
      ExprsFit N Γ fx es τs →
      HasType N Γ fx (.op o es) τ
  | view {N Γ fx es τs τ} :
      Op.Sig .view τs τ →
      ExprsFit N Γ fx es τs →
      HasType N Γ fx (.view es) τ
  | field {N Γ fx e R r f τ} :
      HasType N Γ fx e (.record R) →
      D.record? R = some r →
      r.fields.lookup f = some τ →
      HasType N Γ fx (.field e f) τ
  | elem {N Γ fx e τs f τ} :
      HasType N Γ fx e (.tuple τs) →
      (positions τs).lookup f = some τ →
      HasType N Γ fx (.field e f) τ
  | index {N Γ fx e i τ σ} :
      HasType N Γ fx e (.list τ) →
      HasType N Γ fx i σ → LenientFits vs N i σ .i64 →
      HasType N Γ fx (.index e i) τ
  | fnRef {N Γ fx f d types rows} :
      D.fn? f = some d →
      rows.length = d.rowParams.length →
      d.type.InstantiableBy (d.rowParams.zip rows) → (∀ ρ ∈ rows, ρ.resume = none) →
      ((d.type.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows)).WellFormed scope →
      PassesOnPairs scope d (d.rowParams.zip rows) →
      TypeArgsFit D scope d.typeParams types →
      HasType N Γ fx (.fnRef f types rows)
        ((d.type.substTys (d.typeArgs types)).substRows (d.rowParams.zip rows))
  | method {N Γ fx Tr t m σ τ} :
      D.trait? Tr = some t →
      t.methods.lookup m = some σ →
      τ.Closed → τ.WellFormed scope → Satisfies D scope τ Tr →
      HasType N Γ fx (.method Tr m τ) (σ.substTys [(selfParam, τ)])
  /-- A closure's parameters hide the parameters of `N` with their names. -/
  | closure {N Γ fx ps result ρ body σ} :
      (ps.map Param.name).Nodup →
      ps.all (·.implicit.isNone) = true →
      (Ty.fn (ps.map Param.sig) result ρ).WellFormed scope →
      HasType (N.removeAll (ps.map Param.name)) (Γ.freeze.params ps) ⟨ρ, fx.marked, false, result, false, false⟩
        body σ →
      LenientFits vs (N.removeAll (ps.map Param.name)) body σ result →
      HasType N Γ fx (.closure ps result ρ body) (.fn (ps.map Param.sig) result ρ)
  /-- The arguments learn which parameters of the callee are non-escaping
  (`Decls.passing`). -/
  | call {N Γ fx callee args ps result σ} :
      HasType N Γ fx callee (.fn ps result σ) →
      ArgsFit N (D.passing callee) Γ fx args ps →
      CallAllowed scope fx σ →
      HasType N Γ fx (.call callee args result) result
  | letIn {N Γ fx x τ init body σ σ'} :
      τ.WellFormed scope →
      HasType N Γ fx init σ → LenientFits vs N init σ τ →
      HasType (N.removeAll [x]) (Γ.bind x ⟨τ, false⟩) fx body σ' →
      HasType N Γ fx (.letIn x τ init body) σ'
  | varIn {N Γ fx x τ init body σ σ'} :
      τ.WellFormed scope →
      HasType N Γ fx init σ → LenientFits vs N init σ τ →
      HasType (N.removeAll [x]) (Γ.bind x ⟨τ, true⟩) fx body σ' →
      HasType N Γ fx (.varIn x τ init body) σ'
  | assign {N Γ fx p e τ σ} :
      PlaceFits N Γ fx p τ →
      HasType N Γ fx e σ → LenientFits vs N e σ τ →
      HasType N Γ fx (.assign p e) .unit
  | seq {N Γ fx a b σ τ} :
      HasType N Γ fx a σ → LenientFits vs N a σ .unit →
      HasType N Γ fx b τ →
      HasType N Γ fx (.seq a b) τ
  | «if» {N Γ fx c τ a b σc σa σb} :
      τ.WellFormed scope →
      HasType N Γ fx c σc → LenientFits vs N c σc .bool →
      HasType N Γ fx a σa → LenientFits vs N a σa τ →
      HasType N Γ fx b σb → LenientFits vs N b σb τ →
      HasType N Γ fx (.if c τ a b) τ
  | «match» {N Γ fx e σ τ arms} :
      τ.WellFormed scope →
      HasType N Γ fx e σ →
      Exhaustive D (armRows arms) [σ] →
      ArmsFit N Γ fx arms σ τ →
      HasType N Γ fx (.match e τ arms) τ
  | «for» {N Γ fx x τ e body σ} :
      τ.WellFormed scope →
      HasType N Γ fx e (.list τ) →
      HasType (N.removeAll [x]) (Γ.bind x ⟨τ, false⟩) fx.inLoop body σ →
      LenientFits vs (N.removeAll [x]) body σ .unit →
      HasType N Γ fx (.for x τ e body) .unit
  | raise {N Γ fx e E σ} :
      fx.row.raise = some E →
      HasType N Γ fx e σ → LenientFits vs N e σ E →
      HasType N Γ fx (.raise e) .never
  | «try» {N Γ fx e τ} :
      HasType N Γ { fx with marked := true } e τ →
      HasType N Γ fx (.try e) τ
  | tryCatch {N Γ fx e E x h τ σ σ'} :
      E.WellFormed { scope with types := [] } →
      τ.WellFormed scope →
      HasType N Γ ⟨fx.row.withRaise E, true, true, fx.result, fx.breaks, fx.continues⟩ e σ →
      LenientFits vs N e σ τ →
      HasType (N.removeAll [x]) (Γ.bind x ⟨E, false⟩) fx h σ' →
      LenientFits vs (N.removeAll [x]) h σ' τ →
      HasType N Γ fx (.tryCatch e E x h τ) τ
  | «while» {N Γ fx c body σc σ} :
      HasType N Γ fx c σc → LenientFits vs N c σc .bool →
      HasType N Γ fx.inLoop body σ → LenientFits vs N body σ .unit →
      HasType N Γ fx (.while c body) .unit
  | loopBreaks {N Γ fx body σ} :
      HasType N Γ fx.inLoop body σ → LenientFits vs N body σ .unit →
      HasType N Γ fx (.loop body) .unit
  | loopForever {N Γ fx body σ} :
      HasType N Γ { fx with continues := true, breaks := false } body σ →
      LenientFits vs N body σ .unit →
      HasType N Γ fx (.loop body) .never
  | «break» {N Γ fx} : fx.breaks = true → HasType N Γ fx .break .never
  | «continue» {N Γ fx} : fx.continues = true → HasType N Γ fx .continue .never
  | «return» {N Γ fx e σ} :
      HasType N Γ fx e σ → LenientFits vs N e σ fx.result →
      HasType N Γ fx (.return e) .never
  | perform {N Γ fx op e A B σ} :
      op ≠ Operation.resume →
      D.operation? op = some (A, B) → A.Ground → B.Ground →
      op.effect ∈ fx.row.effects →
      HasType N Γ fx e σ → LenientFits vs N e σ A →
      HasType N Γ fx (.perform op e) B
  | resume {N Γ fx e B R σ} :
      fx.row.resume = some (B, R) → B.Ground → R.Ground →
      HasType N Γ fx e σ → LenientFits vs N e σ B →
      HasType N Γ fx (.perform Operation.resume e) R
  | withH {N Γ fx E eff h R r b τ} :
      E ≠ Operation.resume.effect → D.effect? E = some eff →
      HasType N Γ fx h (.record R) → D.record? R = some r →
      HandlerFits scope fx eff r.fields none →
      HasType N Γ { fx with row := fx.row.withEffect E } b τ →
      (∀ f ∈ r.fields, f.1 ∈ eff.ops.map Prod.fst) →
      HasType N Γ fx (.withH E false h b) τ
  | withControl {N Γ fx E eff h R r b σ τ} :
      E ≠ Operation.resume.effect → D.effect? E = some eff →
      HasType N Γ fx h (.record R) → D.record? R = some r →
      HandlerFits scope fx eff r.fields (some τ) →
      HasType N Γ { fx with row := fx.row.withEffect E } b σ → LenientFits vs N b σ τ →
      τ.Ground → (∀ f ∈ r.fields, f.1 ∈ eff.ops.map Prod.fst) →
      HasType N Γ fx (.withH E true h b) τ
  | held {N Γ fx ns hs body σ} :
      (ns.map Prod.fst).Nodup → (∀ p ∈ ns, p.2.WellFormed scope) →
      ExprsFit N Γ fx hs (ns.map fun p => .shared p.2) →
      HasType (N.removeAll (ns.map Prod.fst)) (Γ.holding ns) fx body σ →
      (∀ h ∈ hs, ∃ x, h = .var x) →
      HasType N Γ fx (.held ns hs body) σ

/-- Each expression is checked against the type at its position. -/
inductive ExprsFit : List Name → Ctx → Effects → List Expr → List Ty → Prop
  | nil {N Γ fx} : ExprsFit N Γ fx [] []
  | cons {N Γ fx e es σ τ τs} :
      HasType N Γ fx e σ → LenientFits vs N e σ τ →
      ExprsFit N Γ fx es τs →
      ExprsFit N Γ fx (e :: es) (τ :: τs)

/-- Each written field is checked against the type its record declares for
it. -/
inductive FieldsFit : List Name → Ctx → Effects → List (Name × Expr) → List (Name × Ty) → Prop
  | nil {N Γ fx declared} : FieldsFit N Γ fx [] declared
  | cons {N Γ fx f e fields declared σ τ} :
      declared.lookup f = some τ →
      HasType N Γ fx e σ → LenientFits vs N e σ τ →
      FieldsFit N Γ fx fields declared →
      FieldsFit N Γ fx ((f, e) :: fields) declared

/-- Each argument is checked against its parameter, given for each parameter,
in order, whether it is a non-escaping parameter of the function the call
names. -/
inductive ArgsFit : List Name → List Bool → Ctx → Effects → List Arg → List (Mode × Ty) → Prop
  | nil {N passing Γ fx} : ArgsFit N passing Γ fx [] []
  | value {N passing Γ fx e args m τ σ ps} :
      m ≠ .inout →
      passing.headD false = false →
      HasType N Γ fx e σ → LenientFits vs N e σ τ →
      ArgsFit N passing.tail Γ fx args ps →
      ArgsFit N passing Γ fx (.value e :: args) ((m, τ) :: ps)
  /-- An argument given to a non-escaping parameter of the function the call
  names: the use instantiates the parameter's implicit variable with what the
  argument's row holds beyond the row written (effects.non-escaping-parameters), so the
  argument's type fits the parameter's as it is. -/
  | passed {N passing Γ fx e args m τ σ ps} :
      m ≠ .inout →
      passing.headD false = true →
      HasType N Γ fx e σ → Fits σ τ →
      ArgsFit N passing.tail Γ fx args ps →
      ArgsFit N passing Γ fx (.value e :: args) ((m, τ) :: ps)
  | inout {N passing Γ fx p args τ ps} :
      PlaceFits N Γ fx p τ →
      ArgsFit N passing.tail Γ fx args ps →
      ArgsFit N passing Γ fx (.inout p :: args) ((.inout, τ) :: ps)

/-- A place that can be modified, of type `τ`. -/
inductive PlaceFits : List Name → Ctx → Effects → Place → Ty → Prop
  | mk {N Γ fx x path σ τ} :
      Γ.lookup x = some ⟨σ, true⟩ →
      PathFits N Γ fx σ path τ →
      PlaceFits N Γ fx ⟨x, path⟩ τ

/-- Following the projections of a place from a value of type `σ` reaches a
value of type `τ`. -/
inductive PathFits : List Name → Ctx → Effects → Ty → List Projection → Ty → Prop
  | nil {N Γ fx τ} : PathFits N Γ fx τ [] τ
  | field {N Γ fx R r f path τ τ'} :
      D.record? R = some r →
      r.fields.lookup f = some τ →
      PathFits N Γ fx τ path τ' →
      PathFits N Γ fx (.record R) (.field f :: path) τ'
  | index {N Γ fx i path σ τ τ'} :
      HasType N Γ fx i σ → LenientFits vs N i σ .i64 →
      PathFits N Γ fx τ path τ' →
      PathFits N Γ fx (.list τ) (.index i :: path) τ'
  | elem {N Γ fx τs f path τ τ'} :
      (positions τs).lookup f = some τ →
      PathFits N Γ fx τ path τ' →
      PathFits N Γ fx (.tuple τs) (.field f :: path) τ'

/-- Each arm, whose binders hide the parameters of `N` with their names, is
checked against the type of the `match`. -/
inductive ArmsFit : List Name → Ctx → Effects → List Arm → Ty → Ty → Prop
  | nil {N Γ fx σ τ} : ArmsFit N Γ fx [] σ τ
  | cons {N Γ fx arm arms σ σs τ ρ} :
      PatFits D arm.pattern σ σs →
      arm.binders = arm.pattern.binders →
      arm.binders.Nodup →
      HasType (N.removeAll arm.binders) (Γ.bindAll arm.binders σs) fx arm.body ρ →
      LenientFits vs (N.removeAll arm.binders) arm.body ρ τ →
      ArmsFit N Γ fx arms σ τ →
      ArmsFit N Γ fx (arm :: arms) σ τ

end

end

end Lenient

end Stilt
