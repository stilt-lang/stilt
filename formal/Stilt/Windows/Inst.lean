import Stilt.Rows
import Stilt.Rows.Types
import Stilt.Generics.Commute
import Stilt.Sources
import Stilt.Modes.Uses
import Stilt.InPlace.Bodies

/-!
# Instances of a body

A function's body runs with its type parameters and row variables instantiated, while the
checks of views read the body as it is declared. `Expr.Inst D e e'` says that `e'` is `e` with
some of its types replaced, in a way that the model of windows can only keep fewer windows than
the checks of `e` track: wherever `e'` writes a type that may hold a view, `e` writes one too,
and wherever `e'` writes a view type, `e` writes one or a type parameter (`TyInst`); each
closure literal names its parameters once, as typing makes it (expressions.closures), and each
call's `inout` arguments name disjoint places, as the law makes them (modes.law, E0402). Every
instantiation of such a body by types and rows is an instance of it (`Expr.inst_subst`).
-/

namespace Stilt

/-- A type written where another was: the model keeps a view in a binding of the second only
if the first may hold one, and a call's result only if the first may be a view. -/
def TyInst (D : Decls) (τ τ' : Ty) : Prop :=
  (τ'.holdsView D = true → τ.holdsView D = true) ∧ (τ'.isView D = true → τ.mayBeView D = true)

/-- A parameter written where another was: the same name and mode, its type an instance, a
function type where the other is one. -/
def ParamInst (D : Decls) (p p' : Param) : Prop :=
  p'.mode = p.mode ∧ p'.name = p.name ∧ TyInst D p.type p'.type ∧ (p.type.isFn → p'.type.isFn)

/-- Parameters, each an instance of its own. -/
inductive ParamsInst (D : Decls) : List Param → List Param → Prop
  | nil : ParamsInst D [] []
  | cons {p p' : Param} {ps ps' : List Param} :
      ParamInst D p p' → ParamsInst D ps ps' → ParamsInst D (p :: ps) (p' :: ps')

mutual

/-- `e'` is `e` with some of its types replaced by instances. -/
inductive Expr.Inst (D : Decls) : Expr → Expr → Prop
  | var (x : Name) : Expr.Inst D (.var x) (.var x)
  | move (x : Name) : Expr.Inst D (.move x) (.move x)
  | int (k : Int) : Expr.Inst D (.int k) (.int k)
  | bool (b : Bool) : Expr.Inst D (.bool b) (.bool b)
  | unit : Expr.Inst D .unit .unit
  | record (R : Name) {fs fs' : List (Name × Expr)} :
      FieldsInst D fs fs' → Expr.Inst D (.record R fs) (.record R fs')
  | variant (T C : Name) {es es' : List Expr} :
      ExprsInst D es es' → Expr.Inst D (.variant T C es) (.variant T C es')
  | list (τ τ' : Ty) {es es' : List Expr} :
      ExprsInst D es es' → Expr.Inst D (.list τ es) (.list τ' es')
  | op (o o' : Op) {es es' : List Expr} : ExprsInst D es es' → Expr.Inst D (.op o es) (.op o' es')
  | view {es es' : List Expr} : ExprsInst D es es' → Expr.Inst D (.view es) (.view es')
  | field {e e' : Expr} (f : Name) : Expr.Inst D e e' → Expr.Inst D (.field e f) (.field e' f)
  | index {e e' i i' : Expr} :
      Expr.Inst D e e' → Expr.Inst D i i' → Expr.Inst D (.index e i) (.index e' i')
  | fnRef (f : Name) (tys tys' : List Ty) (rows rows' : List Row) :
      Expr.Inst D (.fnRef f tys rows) (.fnRef f tys' rows')
  | method (t m : Name) (τ τ' : Ty) : Expr.Inst D (.method t m τ) (.method t m τ')
  | closure {ps ps' : List Param} {r r' : Ty} (ρ ρ' : Row) {b b' : Expr} :
      (ps.map Param.name).Nodup → ParamsInst D ps ps' → TyInst D r r' → Expr.Inst D b b' →
      Expr.Inst D (.closure ps r ρ b) (.closure ps' r' ρ' b')
  | call {f f' : Expr} {as as' : List Arg} {τ τ' : Ty} :
      pairwiseDisjoint (inoutShapes as) = true → Expr.Inst D f f' → ArgsInst D as as' → TyInst D τ τ' →
      Expr.Inst D (.call f as τ) (.call f' as' τ')
  | letIn (x : Name) {τ τ' : Ty} {e e' b b' : Expr} :
      TyInst D τ τ' → Expr.Inst D e e' → Expr.Inst D b b' →
      Expr.Inst D (.letIn x τ e b) (.letIn x τ' e' b')
  | varIn (x : Name) {τ τ' : Ty} {e e' b b' : Expr} :
      TyInst D τ τ' → Expr.Inst D e e' → Expr.Inst D b b' →
      Expr.Inst D (.varIn x τ e b) (.varIn x τ' e' b')
  | assign (x : Name) {ps ps' : List Projection} {e e' : Expr} :
      PathInst D ps ps' → Expr.Inst D e e' → Expr.Inst D (.assign ⟨x, ps⟩ e) (.assign ⟨x, ps'⟩ e')
  | seq {a a' b b' : Expr} :
      Expr.Inst D a a' → Expr.Inst D b b' → Expr.Inst D (.seq a b) (.seq a' b')
  | «if» {c c' a a' b b' : Expr} (τ τ' : Ty) :
      Expr.Inst D c c' → Expr.Inst D a a' → Expr.Inst D b b' →
      Expr.Inst D (.if c τ a b) (.if c' τ' a' b')
  | «match» {e e' : Expr} (τ τ' : Ty) {arms arms' : List Arm} :
      Expr.Inst D e e' → ArmsInst D arms arms' → Expr.Inst D (.match e τ arms) (.match e' τ' arms')
  | «for» (x : Name) (τ τ' : Ty) {e e' b b' : Expr} :
      Expr.Inst D e e' → Expr.Inst D b b' → Expr.Inst D (.for x τ e b) (.for x τ' e' b')
  | raise {e e' : Expr} : Expr.Inst D e e' → Expr.Inst D (.raise e) (.raise e')
  | «try» {e e' : Expr} : Expr.Inst D e e' → Expr.Inst D (.try e) (.try e')
  | tryCatch {e e' h h' : Expr} (E E' : Ty) (x : Name) (τ τ' : Ty) :
      Expr.Inst D e e' → Expr.Inst D h h' →
      Expr.Inst D (.tryCatch e E x h τ) (.tryCatch e' E' x h' τ')
  | «while» {c c' b b' : Expr} :
      Expr.Inst D c c' → Expr.Inst D b b' → Expr.Inst D (.while c b) (.while c' b')
  | «loop» {b b' : Expr} : Expr.Inst D b b' → Expr.Inst D (.loop b) (.loop b')
  | «break» : Expr.Inst D .break .break
  | «continue» : Expr.Inst D .continue .continue
  | «return» {e e' : Expr} : Expr.Inst D e e' → Expr.Inst D (.return e) (.return e')
  | perform (op : Operation) {e e' : Expr} :
      Expr.Inst D e e' → Expr.Inst D (.perform op e) (.perform op e')
  | withH (E : Name) (c : Bool) {h h' b b' : Expr} :
      Expr.Inst D h h' → Expr.Inst D b b' → Expr.Inst D (.withH E c h b) (.withH E c h' b')
  | held {ns ns' : List (Name × Ty)} {hs hs' : List Expr} {b b' : Expr} :
      ns'.map Prod.fst = ns.map Prod.fst → ExprsInst D hs hs' → Expr.Inst D b b' →
      Expr.Inst D (.held ns hs b) (.held ns' hs' b')

/-- Expressions, each an instance of its own. -/
inductive ExprsInst (D : Decls) : List Expr → List Expr → Prop
  | nil : ExprsInst D [] []
  | cons {e e' : Expr} {es es' : List Expr} :
      Expr.Inst D e e' → ExprsInst D es es' → ExprsInst D (e :: es) (e' :: es')

/-- The fields of a record literal, each an instance of its own. -/
inductive FieldsInst (D : Decls) : List (Name × Expr) → List (Name × Expr) → Prop
  | nil : FieldsInst D [] []
  | cons (f : Name) {e e' : Expr} {fs fs' : List (Name × Expr)} :
      Expr.Inst D e e' → FieldsInst D fs fs' → FieldsInst D ((f, e) :: fs) ((f, e') :: fs')

/-- The arguments of a call, each an instance of its own. -/
inductive ArgsInst (D : Decls) : List Arg → List Arg → Prop
  | nil : ArgsInst D [] []
  | value {e e' : Expr} {as as' : List Arg} :
      Expr.Inst D e e' → ArgsInst D as as' → ArgsInst D (.value e :: as) (.value e' :: as')
  | inout (x : Name) {ps ps' : List Projection} {as as' : List Arg} :
      PathInst D ps ps' → ArgsInst D as as' →
      ArgsInst D (.inout ⟨x, ps⟩ :: as) (.inout ⟨x, ps'⟩ :: as')

/-- The projections of a place, each index an instance of its own. -/
inductive PathInst (D : Decls) : List Projection → List Projection → Prop
  | nil : PathInst D [] []
  | field (f : Name) {ps ps' : List Projection} :
      PathInst D ps ps' → PathInst D (.field f :: ps) (.field f :: ps')
  | index {i i' : Expr} {ps ps' : List Projection} :
      Expr.Inst D i i' → PathInst D ps ps' → PathInst D (.index i :: ps) (.index i' :: ps')

/-- The arms of a `match`, each body an instance of its own. -/
inductive ArmsInst (D : Decls) : List Arm → List Arm → Prop
  | nil : ArmsInst D [] []
  | cons (pat : Pattern) (xs : List Name) {b b' : Expr} {arms arms' : List Arm} :
      Expr.Inst D b b' → ArmsInst D arms arms' →
      ArmsInst D (⟨pat, xs, b⟩ :: arms) (⟨pat, xs, b'⟩ :: arms')

end

/-! ## Types -/

theorem Ty.isView_substRows (D : Decls) (s : RowSubst) (τ : Ty) :
    (τ.substRows s).isView D = τ.isView D := by
  cases τ <;> rfl

theorem Ty.holdsView_substRows (D : Decls) (s : RowSubst) (τ : Ty) :
    (τ.substRows s).holdsView D = τ.holdsView D := by
  cases τ <;> rfl

theorem Ty.holdsView_of_substTys (D : Decls) (s : TySubst) (τ : Ty)
    (h : (τ.substTys s).holdsView D = true) : τ.holdsView D = true := by
  revert h
  cases τ <;> simp [Ty.holdsView, Ty.isView, Ty.substTys]

theorem Ty.mayBeView_of_substTys (D : Decls) (s : TySubst) (τ : Ty)
    (h : (τ.substTys s).isView D = true) : τ.mayBeView D = true := by
  revert h
  cases τ <;> simp [Ty.mayBeView, Ty.isView, Ty.substTys]

/-- Instantiating the type parameters and the row variables of a type gives an instance. -/
theorem TyInst.subst (D : Decls) (σ : TySubst) (ρ : RowSubst) (τ : Ty) :
    TyInst D τ ((τ.substTys σ).substRows ρ) :=
  ⟨fun h => Ty.holdsView_of_substTys D σ τ (by rwa [Ty.holdsView_substRows] at h),
    fun h => Ty.mayBeView_of_substTys D σ τ (by rwa [Ty.isView_substRows] at h)⟩

theorem ParamInst.subst (D : Decls) (σ : TySubst) (ρ : RowSubst) (p : Param) :
    ParamInst D p ((p.substTys σ).substRows ρ) :=
  ⟨rfl, rfl, TyInst.subst D σ ρ p.type, by
    cases h : p.type <;> simp [Ty.isFn, Param.substTys, Param.substRows, h, Ty.substTys,
      Ty.substRows]⟩

theorem TyInst.refl (D : Decls) (τ : Ty) : TyInst D τ τ :=
  ⟨id, fun h => by revert h; cases τ <;> simp [Ty.mayBeView, Ty.isView]⟩

theorem paramsInst_subst (D : Decls) (σ : TySubst) (ρ : RowSubst) :
    ∀ ps : List Param, ParamsInst D ps ((ps.map (Param.substTys σ)).map (Param.substRows ρ))
  | [] => .nil
  | p :: ps => .cons (ParamInst.subst D σ ρ p) (paramsInst_subst D σ ρ ps)


/-! ## Instantiations are instances -/

private theorem both {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true :=
  Bool.and_eq_true a b ▸ h

variable (D : Decls) (σ : TySubst) (ρ : RowSubst)

mutual

theorem Expr.inst_subst : ∀ (e : Expr) (r : List Shape), e.distinctParams = true →
    e.exclusive r = true → Expr.Inst D e ((e.substTys σ).substRows ρ)
  | .var x, _, _, _ => .var x
  | .move x, _, _, _ => .move x
  | .int k, _, _, _ => .int k
  | .bool b, _, _, _ => .bool b
  | .unit, _, _, _ => .unit
  | .record R fs, r, h, x => .record R (fieldsInst_subst fs r h x)
  | .variant T C es, r, h, x => .variant T C (exprsInst_subst es r h x)
  | .list τ es, r, h, x => .list _ _ (exprsInst_subst es r h x)
  | .op o es, r, h, x => .op _ _ (exprsInst_subst es r h x)
  | .view es, r, h, x => .view (exprsInst_subst es r h x)
  | .field e f, r, h, x => .field f (Expr.inst_subst e r h x)
  | .index e i, r, h, x => .index (Expr.inst_subst e r (both h).1 (both x).1)
      (Expr.inst_subst i r (both h).2 (both x).2)
  | .fnRef f tys rows, _, _, _ => .fnRef f _ _ _ _
  | .method t m τ, _, _, _ => .method t m _ _
  | .closure ps r' ρ' b, _, h, x =>
    .closure _ _ (of_decide_eq_true (both h).1) (paramsInst_subst D σ ρ ps)
      (TyInst.subst D σ ρ r') (Expr.inst_subst b [] (both h).2 x)
  | .call f as τ, r, h, x => .call (both x).2
      (Expr.inst_subst f r (both h).1 (both (both (both x).1).1).1)
      (argsInst_subst as r (both h).2 (both (both (both x).1).1).2)
      ⟨Ty.holdsView_of_substTys D σ τ, Ty.mayBeView_of_substTys D σ τ⟩
  | .letIn y τ e b, r, h, x => .letIn y (TyInst.subst D σ ρ τ)
      (Expr.inst_subst e r (both h).1 (both x).1)
      (Expr.inst_subst b (hide r y) (both h).2 (both x).2)
  | .varIn y τ e b, r, h, x => .varIn y (TyInst.subst D σ ρ τ)
      (Expr.inst_subst e r (both h).1 (both x).1)
      (Expr.inst_subst b (hide r y) (both h).2 (both x).2)
  | .assign ⟨y, ps⟩ e, r, h, x =>
    .assign y (pathInst_subst ps r (both h).1 (both (both x).1).1)
      (Expr.inst_subst e r (both h).2 (both (both x).1).2)
  | .seq a b, r, h, x => .seq (Expr.inst_subst a r (both h).1 (both x).1)
      (Expr.inst_subst b r (both h).2 (both x).2)
  | .if c τ a b, r, h, x => .if _ _ (Expr.inst_subst c r (both (both h).1).1 (both (both x).1).1)
      (Expr.inst_subst a r (both (both h).1).2 (both (both x).1).2)
      (Expr.inst_subst b r (both h).2 (both x).2)
  | .match e τ arms, r, h, x => .match _ _ (Expr.inst_subst e r (both h).1 (both x).1)
      (armsInst_subst arms r (both h).2 (both x).2)
  | .for y τ e b, r, h, x => .for y _ _ (Expr.inst_subst e r (both h).1 (both x).1)
      (Expr.inst_subst b _ (both h).2 (both x).2)
  | .raise e, r, h, x => .raise (Expr.inst_subst e r h x)
  | .try e, r, h, x => .try (Expr.inst_subst e r h x)
  | .tryCatch e E y hd τ, r, h, x =>
    .tryCatch _ _ y _ _ (Expr.inst_subst e r (both h).1 (both x).1)
      (Expr.inst_subst hd (hide r y) (both h).2 (both x).2)
  | .while c b, r, h, x => .while (Expr.inst_subst c r (both h).1 (both x).1)
      (Expr.inst_subst b r (both h).2 (both x).2)
  | .loop b, r, h, x => .loop (Expr.inst_subst b r h x)
  | .break, _, _, _ => .break
  | .continue, _, _, _ => .continue
  | .return e, r, h, x => .return (Expr.inst_subst e r h x)
  | .perform op e, r, h, x => .perform op (Expr.inst_subst e r h x)
  | .withH E c hd b, r, h, x => .withH E c (Expr.inst_subst hd r (both h).1 (both x).1)
      (Expr.inst_subst b r (both h).2 (both x).2)
  | .held ns hs b, r, h, x => .held (by simp [List.map_map, Function.comp_def])
      (exprsInst_subst hs r (both h).1 (both x).1) (Expr.inst_subst b _ (both h).2 (both x).2)

theorem exprsInst_subst : ∀ (es : List Expr) (r : List Shape), exprsDistinctParams es = true →
    exprsExclusive r es = true → ExprsInst D es (substExprRows ρ (substExprTys σ es))
  | [], _, _, _ => .nil
  | e :: es, r, h, x =>
    .cons (Expr.inst_subst e r (both h).1 (both x).1) (exprsInst_subst es r (both h).2 (both x).2)

theorem fieldsInst_subst : ∀ (fs : List (Name × Expr)) (r : List Shape),
    fieldsDistinctParams fs = true → fieldsExclusive r fs = true →
    FieldsInst D fs (substFieldRows ρ (substFieldTys σ fs))
  | [], _, _, _ => .nil
  | (f, e) :: fs, r, h, x => .cons f (Expr.inst_subst e r (both h).1 (both x).1)
      (fieldsInst_subst fs r (both h).2 (both x).2)

theorem argsInst_subst : ∀ (as : List Arg) (r : List Shape), argsDistinctParams as = true →
    argsExclusive r as = true → ArgsInst D as (substArgRows ρ (substArgTys σ as))
  | [], _, _, _ => .nil
  | .value e :: as, r, h, x => .value (Expr.inst_subst e r (both h).1 (both x).1)
      (argsInst_subst as r (both h).2 (both x).2)
  | .inout ⟨y, ps⟩ :: as, r, h, x => .inout y (pathInst_subst ps r (both h).1 (both x).1)
      (argsInst_subst as r (both h).2 (both x).2)

theorem pathInst_subst : ∀ (ps : List Projection) (r : List Shape), pathDistinctParams ps = true →
    pathExclusive r ps = true → PathInst D ps (substPathRows ρ (substPathTys σ ps))
  | [], _, _, _ => .nil
  | .field f :: ps, r, h, x => .field f (pathInst_subst ps r h x)
  | .index i :: ps, r, h, x => .index (Expr.inst_subst i r (both h).1 (both x).1)
      (pathInst_subst ps r (both h).2 (both x).2)

theorem armsInst_subst : ∀ (arms : List Arm) (r : List Shape), armsDistinctParams arms = true →
    armsExclusive r arms = true → ArmsInst D arms (substArmRows ρ (substArmTys σ arms))
  | [], _, _, _ => .nil
  | ⟨pat, xs, b⟩ :: arms, r, h, x => .cons pat xs (Expr.inst_subst b _ (both h).1 (both x).1)
      (armsInst_subst arms r (both h).2 (both x).2)

end

end Stilt
