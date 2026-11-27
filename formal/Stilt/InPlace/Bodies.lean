import Stilt.Exclusivity
import Stilt.Typing

/-!
# Bodies

What in-place agreement needs of a body besides the law of exclusivity: that
each closure literal in it names its parameters once each. Copy-in, copy-out
writes an `inout` argument back from the callee's variable of the parameter's
name, so a later parameter of the same name would be written back in its
place. Typing rules that out (expressions.closures), and so does every program the
model accepts.

A call instantiates the body of a generic function (`Expr.substRows`), and
both conditions survive that: they look at places, calls and parameter names,
never at the types it rewrites.
-/

namespace Stilt

mutual

/-- Every closure literal in `e` names each of its parameters once. -/
def Expr.distinctParams : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => true
  | .record _ _ fields => fieldsDistinctParams fields
  | .variant _ _ _ es => exprsDistinctParams es
  | .list _ es => exprsDistinctParams es
  | .op _ es | .view es => exprsDistinctParams es
  | .field e _ => e.distinctParams
  | .index e i => e.distinctParams && i.distinctParams
  | .closure ps _ _ body => decide (ps.map Param.name).Nodup && body.distinctParams
  | .call callee args _ => callee.distinctParams && argsDistinctParams args
  | .letIn _ _ init body => init.distinctParams && body.distinctParams
  | .varIn _ _ init body => init.distinctParams && body.distinctParams
  | .assign ⟨_, path⟩ value => pathDistinctParams path && value.distinctParams
  | .seq a b => a.distinctParams && b.distinctParams
  | .if c _ a b => c.distinctParams && a.distinctParams && b.distinctParams
  | .match e _ arms => e.distinctParams && armsDistinctParams arms
  | .for _ _ e body => e.distinctParams && body.distinctParams
  | .raise e => e.distinctParams
  | .try e | .form _ e => e.distinctParams
  | .tryCatch e _ _ handler _ => e.distinctParams && handler.distinctParams
  | .while c body => c.distinctParams && body.distinctParams
  | .loop body => body.distinctParams
  | .return e => e.distinctParams
  | .perform _ e => e.distinctParams
  | .withH _ _ h b => h.distinctParams && b.distinctParams
  | .held _ hs body => exprsDistinctParams hs && body.distinctParams

/-- Every expression of a list has `distinctParams`. -/
def exprsDistinctParams : List Expr → Bool
  | [] => true
  | e :: es => e.distinctParams && exprsDistinctParams es

/-- Every field of a record literal has `distinctParams`. -/
def fieldsDistinctParams : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.distinctParams && fieldsDistinctParams fields

/-- Every argument of a call, and every index of an `inout` place, has
`distinctParams`. -/
def argsDistinctParams : List Arg → Bool
  | [] => true
  | .value e :: args => e.distinctParams && argsDistinctParams args
  | .inout ⟨_, path⟩ :: args => pathDistinctParams path && argsDistinctParams args

/-- Every index of a place has `distinctParams`. -/
def pathDistinctParams : List Projection → Bool
  | [] => true
  | .field _ :: path => pathDistinctParams path
  | .index i :: path => i.distinctParams && pathDistinctParams path

/-- Every arm of a `match` has `distinctParams`. -/
def armsDistinctParams : List Arm → Bool
  | [] => true
  | ⟨_, _, guard, body⟩ :: arms =>
    guardDistinctParams guard && body.distinctParams && armsDistinctParams arms

/-- An arm's guard has `distinctParams`. -/
def guardDistinctParams : Option Expr → Bool
  | none => true
  | some g => g.distinctParams

end

/-! ## Typing gives distinct parameters -/

section Typing

variable {D : Decls} {s : RowScope}

mutual

/-- A well-typed expression's closure literals name their parameters once each
(declarations.unique-names). -/
theorem HasType.distinctParams :
    ∀ {Γ fx e τ}, HasType D s Γ fx e τ → e.distinctParams = true
  | _, _, _, _, .var _ => rfl
  | _, _, _, _, .int _ => rfl
  | _, _, _, _, .bool => rfl
  | _, _, _, _, .unit => rfl
  | _, _, _, _, .record _ _ _ _ hfs => FieldsFit.distinctParams hfs
  | _, _, _, _, .variant _ _ _ _ hes => ExprsFit.distinctParams hes
  | _, _, _, _, .list _ hes => ExprsFit.distinctParams hes
  | _, _, _, _, .op _ hes _ _ _ => ExprsFit.distinctParams hes
  | _, _, _, _, .view _ hes => ExprsFit.distinctParams hes
  | _, _, _, _, .field he _ _ _ => by simpa [Expr.distinctParams] using HasType.distinctParams he
  | _, _, _, _, .elem he _ => by simpa [Expr.distinctParams] using HasType.distinctParams he
  | _, _, _, _, .index he hi _ => by
    simp [Expr.distinctParams, HasType.distinctParams he, HasType.distinctParams hi]
  | _, _, _, _, .fnRef .. | _, _, _, _, .method .. => rfl
  | _, _, _, _, .closure hnd _ _ hb _ => by
    simp [Expr.distinctParams, hnd, HasType.distinctParams hb]
  | _, _, _, _, .call hf has _ => by
    simp [Expr.distinctParams, HasType.distinctParams hf, ArgsFit.distinctParams has]
  | _, _, _, _, .letIn _ he _ hb => by
    simp [Expr.distinctParams, HasType.distinctParams he, HasType.distinctParams hb]
  | _, _, _, _, .varIn _ he _ hb => by
    simp [Expr.distinctParams, HasType.distinctParams he, HasType.distinctParams hb]
  | _, _, _, _, .held _ _ hes hb _ => by
    simp [Expr.distinctParams, ExprsFit.distinctParams hes, HasType.distinctParams hb]
  | _, _, _, _, .form _ hm | _, _, _, _, .shaped _ hm => by simpa [Expr.distinctParams] using HasType.distinctParams hm
  | _, _, _, _, .letElse _ _ hm | _, _, _, _, .orElse _ _ _ _ hm => by simpa [Expr.distinctParams] using HasType.distinctParams hm
  | _, _, .assign ⟨_, _⟩ _, _, .assign hp he _ => by
    simp [Expr.distinctParams, PlaceFits.distinctParams hp, HasType.distinctParams he]
  | _, _, _, _, .seq ha _ hb => by
    simp [Expr.distinctParams, HasType.distinctParams ha, HasType.distinctParams hb]
  | _, _, _, _, .if _ hc _ ha _ hb _ => by
    simp [Expr.distinctParams, HasType.distinctParams hc, HasType.distinctParams ha,
      HasType.distinctParams hb]
  | _, _, _, _, .match _ he _ harms => by
    simp [Expr.distinctParams, HasType.distinctParams he, ArmsFit.distinctParams harms]
  | _, _, _, _, .for _ he hb _ => by
    simp [Expr.distinctParams, HasType.distinctParams he, HasType.distinctParams hb]
  | _, _, _, _, .raise _ he _ => by simpa [Expr.distinctParams] using HasType.distinctParams he
  | _, _, _, _, .try he => by simpa [Expr.distinctParams] using HasType.distinctParams he
  | _, _, _, _, .tryCatch _ _ he _ hh _ => by
    simp [Expr.distinctParams, HasType.distinctParams he, HasType.distinctParams hh]
  | _, _, _, _, .while hc _ hb _ => by
    simp [Expr.distinctParams, HasType.distinctParams hc, HasType.distinctParams hb]
  | _, _, _, _, .loopBreaks hb _ | _, _, _, _, .loopForever hb _ => by
    simpa [Expr.distinctParams] using HasType.distinctParams hb
  | _, _, _, _, .break _ | _, _, _, _, .continue _ => rfl
  | _, _, _, _, .return he _ => by simpa [Expr.distinctParams] using HasType.distinctParams he
  | _, _, _, _, .perform _ _ _ _ _ he _ | _, _, _, _, .resume _ _ _ he _ => by
    simpa [Expr.distinctParams] using HasType.distinctParams he
  | _, _, _, _, .withH _ _ hh _ _ hb _ | _, _, _, _, .withControl _ _ hh _ _ hb _ _ _ => by
    simp [Expr.distinctParams, HasType.distinctParams hh, HasType.distinctParams hb]

theorem ExprsFit.distinctParams :
    ∀ {Γ fx es τs}, ExprsFit D s Γ fx es τs → exprsDistinctParams es = true
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons he _ hes => by
    simp [exprsDistinctParams, HasType.distinctParams he, ExprsFit.distinctParams hes]

theorem FieldsFit.distinctParams :
    ∀ {Γ fx fields declared}, FieldsFit D s Γ fx fields declared →
      fieldsDistinctParams fields = true
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .cons _ he _ hfs => by
    simp [fieldsDistinctParams, HasType.distinctParams he, FieldsFit.distinctParams hfs]

theorem ArgsFit.distinctParams :
    ∀ {Γ fx args ps}, ArgsFit D s Γ fx args ps → argsDistinctParams args = true
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .value _ he _ has => by
    simp [argsDistinctParams, HasType.distinctParams he, ArgsFit.distinctParams has]
  | _, _, .inout ⟨_, _⟩ :: _, _, .inout hp has => by
    simp [argsDistinctParams, PlaceFits.distinctParams hp, ArgsFit.distinctParams has]

theorem PlaceFits.distinctParams :
    ∀ {Γ fx p τ}, PlaceFits D s Γ fx p τ → pathDistinctParams p.path = true
  | _, _, _, _, .mk _ hp => PathFits.distinctParams hp

theorem PathFits.distinctParams :
    ∀ {Γ fx σ path τ}, PathFits D s Γ fx σ path τ → pathDistinctParams path = true
  | _, _, _, _, _, .nil => rfl
  | _, _, _, _, _, .field _ _ _ hp => by
    simpa [pathDistinctParams] using PathFits.distinctParams hp
  | _, _, _, _, _, .index hi _ hp => by
    simp [pathDistinctParams, HasType.distinctParams hi, PathFits.distinctParams hp]
  | _, _, _, _, _, .elem _ hp => by
    simpa [pathDistinctParams] using PathFits.distinctParams hp

theorem ArmsFit.distinctParams :
    ∀ {Γ fx arms σ τ}, ArmsFit D s Γ fx arms σ τ → armsDistinctParams arms = true
  | _, _, _, _, _, .nil => rfl
  | _, _, ⟨_, _, _, _⟩ :: _, _, _, .cons _ _ _ hg hb _ harms => by
    simp [armsDistinctParams, GuardFits.distinctParams hg, HasType.distinctParams hb,
      ArmsFit.distinctParams harms]

theorem GuardFits.distinctParams :
    ∀ {Γ fx g}, GuardFits D s Γ fx g → guardDistinctParams g = true
  | _, _, _, .none => rfl
  | _, _, _, .some hg _ => HasType.distinctParams hg

end

end Typing

/-! ## Instantiation keeps both conditions -/

section Instantiation

variable (s : RowSubst)

theorem fields_substPathRows (path : List Projection) :
    (substPathRows s path).filterMap Projection.fieldName? =
      path.filterMap Projection.fieldName? := by
  induction path with
  | nil => rfl
  | cons p path ih =>
    cases p <;> simp [substPathRows, Projection.fieldName?, ih, List.filterMap_cons]

theorem shape_substPathRows (x : Name) (path : List Projection) :
    (Place.mk x (substPathRows s path)).shape = (Place.mk x path).shape := by
  simp [Place.shape, fields_substPathRows]

theorem inoutShapes_substArgRows (args : List Arg) :
    inoutShapes (substArgRows s args) = inoutShapes args := by
  induction args with
  | nil => rfl
  | cons a args ih =>
    cases a with
    | value e => simpa [substArgRows, inoutShapes] using ih
    | inout p =>
      obtain ⟨x, path⟩ := p
      simp [substArgRows, inoutShapes, ih, shape_substPathRows]

/-- The shape of the place an expression is, if it is one. -/
def Expr.placeShape (e : Expr) : Option Shape := e.place?.map Place.shape

theorem placeShape_field (e : Expr) (f : Name) :
    (Expr.field e f).placeShape = e.placeShape.map fun sh => ⟨sh.root, sh.fields ++ [f]⟩ := by
  simp only [Expr.placeShape, Expr.place?, Option.map_map]
  congr 1
  funext p
  simp [Place.shape, Projection.fieldName?, List.filterMap_append]

theorem placeShape_index (e i : Expr) : (Expr.index e i).placeShape = e.placeShape := by
  simp only [Expr.placeShape, Expr.place?, Option.map_map]
  congr 1
  funext p
  exact Place.shape_index p.root p.path i

theorem placeShape_substRows : ∀ e : Expr, (e.substRows s).placeShape = e.placeShape
  | .var _ | .move _ => rfl
  | .field e f => by
    rw [show (Expr.field e f).substRows s = .field (e.substRows s) f by simp [Expr.substRows],
      placeShape_field, placeShape_field, placeShape_substRows e]
  | .index e i => by
    rw [show (Expr.index e i).substRows s = .index (e.substRows s) (i.substRows s) by
      simp [Expr.substRows], placeShape_index, placeShape_index, placeShape_substRows e]
  | .int _ | .bool _ | .unit | .record .. | .variant .. | .list .. | .op .. | .view _ | .fnRef .. | .method .. | .closure ..
  | .call .. | .letIn .. | .varIn .. | .assign ⟨_, _⟩ _ | .seq .. | .if .. | .match .. | .for ..
  | .raise _ | .perform _ _ | .try _ | .form _ _ | .tryCatch .. | .while .. | .loop _ | .break | .continue
  | .return _ | .withH .. | .held .. => by
    simp [Expr.substRows, Expr.placeShape, Expr.place?]

theorem iterated_substRows (e : Expr) : iterated (e.substRows s) = iterated e := by
  have := placeShape_substRows s e
  simp only [Expr.placeShape] at this
  simp [iterated, this]

mutual

/-- Instantiating a body's row variables keeps it exclusive. -/
theorem Expr.exclusive_substRows :
    ∀ (e : Expr) (r : List Shape), (e.substRows s).exclusive r = e.exclusive r
  | .var _, _ | .move _, _ | .int _, _ | .bool _, _ | .unit, _ | .break, _ | .continue, _
  | .fnRef .., _ | .method .., _ => rfl
  | .record _ _ fields, r => fieldsExclusive_substRows fields r
  | .variant _ _ _ es, r => exprsExclusive_substRows es r
  | .list _ es, r => exprsExclusive_substRows es r
  | .op _ es, r | .view es, r => exprsExclusive_substRows es r
  | .field e _, r => by simpa [Expr.substRows, Expr.exclusive] using Expr.exclusive_substRows e r
  | .index e i, r => by
    simp [Expr.substRows, Expr.exclusive, Expr.exclusive_substRows e r,
      Expr.exclusive_substRows i r]
  | .closure _ _ _ body, _ => by
    simpa [Expr.substRows, Expr.exclusive] using Expr.exclusive_substRows body []
  | .call f args _, r => by
    simp [Expr.substRows, Expr.exclusive, Expr.exclusive_substRows f r,
      argsExclusive_substRows args r, inoutShapes_substArgRows]
  | .letIn x _ init body, r => by
    simp [Expr.substRows, Expr.exclusive, Expr.exclusive_substRows init r,
      Expr.exclusive_substRows body (hide r x)]
  | .varIn x _ init body, r => by
    simp [Expr.substRows, Expr.exclusive, Expr.exclusive_substRows init r,
      Expr.exclusive_substRows body (hide r x)]
  | .assign ⟨_, path⟩ v, r => by
    simp [Expr.substRows, Expr.exclusive, pathExclusive_substRows path r,
      Expr.exclusive_substRows v r, shape_substPathRows]
  | .seq a b, r | .withH _ _ a b, r => by
    simp [Expr.substRows, Expr.exclusive, Expr.exclusive_substRows a r,
      Expr.exclusive_substRows b r]
  | .held _ hs body, r => by
    simp [Expr.substRows, Expr.exclusive, exprsExclusive_substRows hs r,
      Expr.exclusive_substRows body, Function.comp_def]
  | .if c _ a b, r => by
    simp [Expr.substRows, Expr.exclusive, Expr.exclusive_substRows c r,
      Expr.exclusive_substRows a r, Expr.exclusive_substRows b r]
  | .match e _ arms, r => by
    simp [Expr.substRows, Expr.exclusive, Expr.exclusive_substRows e r,
      armsExclusive_substRows arms r]
  | .for x _ e body, r => by
    simp [Expr.substRows, Expr.exclusive, Expr.exclusive_substRows e r, iterated_substRows,
      Expr.exclusive_substRows body (hide (iterated e ++ r) x)]
  | .raise e, r => by simpa [Expr.substRows, Expr.exclusive] using Expr.exclusive_substRows e r
  | .try e, r | .form _ e, r => by simpa [Expr.substRows, Expr.exclusive] using Expr.exclusive_substRows e r
  | .tryCatch e _ x h _, r => by
    simp [Expr.substRows, Expr.exclusive, Expr.exclusive_substRows e r,
      Expr.exclusive_substRows h (hide r x)]
  | .while c body, r => by
    simp [Expr.substRows, Expr.exclusive, Expr.exclusive_substRows c r,
      Expr.exclusive_substRows body r]
  | .loop e, r | .return e, r | .perform _ e, r => by
    simpa [Expr.substRows, Expr.exclusive] using Expr.exclusive_substRows e r

theorem exprsExclusive_substRows :
    ∀ (es : List Expr) (r : List Shape), exprsExclusive r (substExprRows s es) = exprsExclusive r es
  | [], _ => rfl
  | e :: es, r => by
    simp [substExprRows, exprsExclusive, Expr.exclusive_substRows e r,
      exprsExclusive_substRows es r]

theorem fieldsExclusive_substRows :
    ∀ (fields : List (Name × Expr)) (r : List Shape),
      fieldsExclusive r (substFieldRows s fields) = fieldsExclusive r fields
  | [], _ => rfl
  | (_, e) :: fields, r => by
    simp [substFieldRows, fieldsExclusive, Expr.exclusive_substRows e r,
      fieldsExclusive_substRows fields r]

theorem argsExclusive_substRows :
    ∀ (args : List Arg) (r : List Shape),
      argsExclusive r (substArgRows s args) = argsExclusive r args
  | [], _ => rfl
  | .value e :: args, r => by
    simp [substArgRows, argsExclusive, Expr.exclusive_substRows e r,
      argsExclusive_substRows args r]
  | .inout ⟨_, path⟩ :: args, r => by
    simp [substArgRows, argsExclusive, pathExclusive_substRows path r,
      argsExclusive_substRows args r]

theorem pathExclusive_substRows :
    ∀ (path : List Projection) (r : List Shape),
      pathExclusive r (substPathRows s path) = pathExclusive r path
  | [], _ => rfl
  | .field _ :: path, r => by
    simpa [substPathRows, pathExclusive] using pathExclusive_substRows path r
  | .index i :: path, r => by
    simp [substPathRows, pathExclusive, Expr.exclusive_substRows i r,
      pathExclusive_substRows path r]

theorem armsExclusive_substRows :
    ∀ (arms : List Arm) (r : List Shape),
      armsExclusive r (substArmRows s arms) = armsExclusive r arms
  | [], _ => rfl
  | ⟨_, binders, g, body⟩ :: arms, r => by
    simp [substArmRows, armsExclusive, guardExclusive_substRows g (binders.foldl hide r),
      Expr.exclusive_substRows body (binders.foldl hide r), armsExclusive_substRows arms r]

theorem guardExclusive_substRows :
    ∀ (g : Option Expr) (r : List Shape), guardExclusive r (substGuardRows s g) = guardExclusive r g
  | none, _ => rfl
  | some g, r => by simp [substGuardRows, guardExclusive, Expr.exclusive_substRows g r]

end

mutual

/-- Instantiating a body's row variables keeps its parameter names. -/
theorem Expr.distinctParams_substRows :
    ∀ e : Expr, (e.substRows s).distinctParams = e.distinctParams
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => rfl
  | .record _ _ fields => fieldsDistinctParams_substRows fields
  | .variant _ _ _ es => exprsDistinctParams_substRows es
  | .list _ es => exprsDistinctParams_substRows es
  | .op _ es | .view es => exprsDistinctParams_substRows es
  | .field e _ => by
    simpa [Expr.substRows, Expr.distinctParams] using Expr.distinctParams_substRows e
  | .index e i => by
    simp [Expr.substRows, Expr.distinctParams, Expr.distinctParams_substRows e,
      Expr.distinctParams_substRows i]
  | .closure ps _ _ body => by
    simp [Expr.substRows, Expr.distinctParams, Expr.distinctParams_substRows body,
      Param.substRows, Function.comp_def]
  | .call f args _ => by
    simp [Expr.substRows, Expr.distinctParams, Expr.distinctParams_substRows f,
      argsDistinctParams_substRows args]
  | .letIn _ _ init body => by
    simp [Expr.substRows, Expr.distinctParams, Expr.distinctParams_substRows init,
      Expr.distinctParams_substRows body]
  | .varIn _ _ init body => by
    simp [Expr.substRows, Expr.distinctParams, Expr.distinctParams_substRows init,
      Expr.distinctParams_substRows body]
  | .assign ⟨_, path⟩ v => by
    simp [Expr.substRows, Expr.distinctParams, pathDistinctParams_substRows path,
      Expr.distinctParams_substRows v]
  | .seq a b | .withH _ _ a b => by
    simp [Expr.substRows, Expr.distinctParams, Expr.distinctParams_substRows a,
      Expr.distinctParams_substRows b]
  | .held _ hs body => by
    simp [Expr.substRows, Expr.distinctParams, exprsDistinctParams_substRows hs,
      Expr.distinctParams_substRows body]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.distinctParams, Expr.distinctParams_substRows c,
      Expr.distinctParams_substRows a, Expr.distinctParams_substRows b]
  | .match e _ arms => by
    simp [Expr.substRows, Expr.distinctParams, Expr.distinctParams_substRows e,
      armsDistinctParams_substRows arms]
  | .for _ _ e body => by
    simp [Expr.substRows, Expr.distinctParams, Expr.distinctParams_substRows e,
      Expr.distinctParams_substRows body]
  | .raise e => by
    simpa [Expr.substRows, Expr.distinctParams] using Expr.distinctParams_substRows e
  | .try e | .form _ e => by
    simpa [Expr.substRows, Expr.distinctParams] using Expr.distinctParams_substRows e
  | .tryCatch e _ _ h _ => by
    simp [Expr.substRows, Expr.distinctParams, Expr.distinctParams_substRows e,
      Expr.distinctParams_substRows h]
  | .while c body => by
    simp [Expr.substRows, Expr.distinctParams, Expr.distinctParams_substRows c,
      Expr.distinctParams_substRows body]
  | .loop e | .return e | .perform _ e => by
    simpa [Expr.substRows, Expr.distinctParams] using Expr.distinctParams_substRows e

theorem exprsDistinctParams_substRows :
    ∀ es : List Expr, exprsDistinctParams (substExprRows s es) = exprsDistinctParams es
  | [] => rfl
  | e :: es => by
    simp [substExprRows, exprsDistinctParams, Expr.distinctParams_substRows e,
      exprsDistinctParams_substRows es]

theorem fieldsDistinctParams_substRows :
    ∀ fields : List (Name × Expr),
      fieldsDistinctParams (substFieldRows s fields) = fieldsDistinctParams fields
  | [] => rfl
  | (_, e) :: fields => by
    simp [substFieldRows, fieldsDistinctParams, Expr.distinctParams_substRows e,
      fieldsDistinctParams_substRows fields]

theorem argsDistinctParams_substRows :
    ∀ args : List Arg, argsDistinctParams (substArgRows s args) = argsDistinctParams args
  | [] => rfl
  | .value e :: args => by
    simp [substArgRows, argsDistinctParams, Expr.distinctParams_substRows e,
      argsDistinctParams_substRows args]
  | .inout ⟨_, path⟩ :: args => by
    simp [substArgRows, argsDistinctParams, pathDistinctParams_substRows path,
      argsDistinctParams_substRows args]

theorem pathDistinctParams_substRows :
    ∀ path : List Projection, pathDistinctParams (substPathRows s path) = pathDistinctParams path
  | [] => rfl
  | .field _ :: path => by
    simpa [substPathRows, pathDistinctParams] using pathDistinctParams_substRows path
  | .index i :: path => by
    simp [substPathRows, pathDistinctParams, Expr.distinctParams_substRows i,
      pathDistinctParams_substRows path]

theorem armsDistinctParams_substRows :
    ∀ arms : List Arm, armsDistinctParams (substArmRows s arms) = armsDistinctParams arms
  | [] => rfl
  | ⟨_, _, g, body⟩ :: arms => by
    simp [substArmRows, armsDistinctParams, guardDistinctParams_substRows g,
      Expr.distinctParams_substRows body, armsDistinctParams_substRows arms]

theorem guardDistinctParams_substRows :
    ∀ g : Option Expr, guardDistinctParams (substGuardRows s g) = guardDistinctParams g
  | none => rfl
  | some g => by simp [substGuardRows, guardDistinctParams, Expr.distinctParams_substRows g]

end

end Instantiation

end Stilt
