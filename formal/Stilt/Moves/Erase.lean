import Stilt.Free
import Stilt.Moves.Marking
import Stilt.InPlace.Bodies

/-!
# Erasing the marks

`Expr.erase` turns every last use back into a read. The marks are what the
compiler infers from a body, so a program with marks is checked as the
program it came from: typing, the law of exclusivity and the parameter names
of closures look at its erasure, and are the same with the marks. A
well-typed program has no marks, since typing has no rule for one.
-/

namespace Stilt

mutual

/-- Reads every marked variable as an ordinary variable. -/
def Expr.erase : Expr → Expr
  | .var x | .move x => .var x
  | .int n => .int n
  | .bool b => .bool b
  | .unit => .unit
  | .record R τs fields => .record R τs (eraseFields fields)
  | .variant T τs C es => .variant T τs C (eraseExprs es)
  | .list τ es => .list τ (eraseExprs es)
  | .op o es => .op o (eraseExprs es)
  | .view es => .view (eraseExprs es)
  | .field e f => .field e.erase f
  | .index e i => .index e.erase i.erase
  | .fnRef f types rows => .fnRef f types rows
  | .method t m τ => .method t m τ
  | .closure ps r ρ body => .closure ps r ρ body.erase
  | .call f args τ => .call f.erase (eraseArgs args) τ
  | .letIn x τ init body => .letIn x τ init.erase body.erase
  | .varIn x τ init body => .varIn x τ init.erase body.erase
  | .assign ⟨x, path⟩ v => .assign ⟨x, erasePath path⟩ v.erase
  | .seq a b => .seq a.erase b.erase
  | .if c τ a b => .if c.erase τ a.erase b.erase
  | .match e τ arms => .match e.erase τ (eraseArms arms)
  | .for x τ e body => .for x τ e.erase body.erase
  | .raise e => .raise e.erase
  | .try e => .try e.erase
  | .form fm e => .form fm e.erase
  | .tryCatch e E x h τ => .tryCatch e.erase E x h.erase τ
  | .while c body => .while c.erase body.erase
  | .loop body => .loop body.erase
  | .break => .break
  | .continue => .continue
  | .return e => .return e.erase
  | .perform op e => .perform op e.erase
  | .withH E c h b => .withH E c h.erase b.erase
  | .held ns hs body => .held ns (eraseExprs hs) body.erase

/-- Erases the marks of a list of expressions. -/
def eraseExprs : List Expr → List Expr
  | [] => []
  | e :: es => e.erase :: eraseExprs es

/-- Erases the marks of the fields of a record literal. -/
def eraseFields : List (Name × Expr) → List (Name × Expr)
  | [] => []
  | (f, e) :: fields => (f, e.erase) :: eraseFields fields

/-- Erases the marks of a call's arguments. -/
def eraseArgs : List Arg → List Arg
  | [] => []
  | .value e :: args => .value e.erase :: eraseArgs args
  | .inout ⟨x, path⟩ :: args => .inout ⟨x, erasePath path⟩ :: eraseArgs args

/-- Erases the marks of the indexes of a place. -/
def erasePath : List Projection → List Projection
  | [] => []
  | .field f :: path => .field f :: erasePath path
  | .index i :: path => .index i.erase :: erasePath path

/-- Erases the marks of the arms of a `match`. -/
def eraseArms : List Arm → List Arm
  | [] => []
  | ⟨C, binders, guard, body⟩ :: arms => ⟨C, binders, eraseGuard guard, body.erase⟩ :: eraseArms arms

/-- Erases the marks of an arm's guard. -/
def eraseGuard : Option Expr → Option Expr
  | none => none
  | some g => some g.erase

end

/-- Erases the marks of a function's body. -/
def FnDecl.erase (d : FnDecl) : FnDecl := { d with body := d.body.erase }

theorem FnDecl.erase_qualify (T : Name) (d : FnDecl) : (d.qualify T).erase = d.erase.qualify T :=
  rfl

/-- Erases the marks of every body of the program. -/
def Program.erase (p : Program) : Program :=
  { p with decls := p.decls.mapFns FnDecl.erase, main := p.main.erase }

/-- Erasing reaches every function, methods included. -/
theorem Program.erase_fns (p : Program) : p.erase.decls.fns = p.decls.fns.map FnDecl.erase :=
  Decls.fns_mapFns FnDecl.erase_qualify _

/-! ## Marking erases to the same program -/

mutual

theorem Expr.erase_markMoves :
    ∀ (e : Expr) (L : Live) (b : Bool), (e.markMoves L b).erase = e.erase
  | .var x, L, b | .move x, L, b => by
    simp only [Expr.markMoves]
    split <;> rfl
  | .int _, _, _ | .bool _, _, _ | .unit, _, _ | .break, _, _ | .continue, _, _
  | .fnRef .., _, _ | .method .., _, _ => rfl
  | .closure _ _ _ body, _, _ => by simp [Expr.markMoves, Expr.erase, Expr.erase_markMoves body]
  | .record _ _ fs, L, _ => by simp [Expr.markMoves, Expr.erase, eraseFields_mark fs L]
  | .variant _ _ _ es, L, _ | .list _ es, L, _ | .op _ es, L, _ | .view es, L, _ => by
    simp [Expr.markMoves, Expr.erase, eraseExprs_mark es L]
  | .field e _, L, _ | .raise e, L, _ | .perform _ e, L, _ | .try e, L, _ | .form _ e, L, _ | .loop e, L, _ | .return e, L, _ => by
    simp [Expr.markMoves, Expr.erase, Expr.erase_markMoves e]
  | .index a b, L, _ | .seq a b, L, _ | .withH _ _ a b, L, _ | .letIn _ _ a b, L, _ | .varIn _ _ a b, L, _
  | .for _ _ a b, L, _ | .while a b, L, _ | .tryCatch a _ _ b _, L, _ => by
    simp [Expr.markMoves, Expr.erase, Expr.erase_markMoves a, Expr.erase_markMoves b]
  | .held _ hs b, L, _ => by
    simp [Expr.markMoves, Expr.erase, eraseExprs_mark hs, Expr.erase_markMoves b]
  | .call f args _, L, _ => by
    simp [Expr.markMoves, Expr.erase, Expr.erase_markMoves f, eraseArgs_mark args]
  | .assign ⟨x, p⟩ v, L, _ => by
    simp [Expr.markMoves, Expr.erase, erasePath_mark p, Expr.erase_markMoves v]
  | .if c _ a b, L, _ => by
    simp [Expr.markMoves, Expr.erase, Expr.erase_markMoves c, Expr.erase_markMoves a,
      Expr.erase_markMoves b]
  | .match e _ arms, L, _ => by
    simp [Expr.markMoves, Expr.erase, Expr.erase_markMoves e, eraseArms_mark arms]

theorem eraseExprs_mark : ∀ (es : List Expr) (L : Live), eraseExprs (markExprs L es) = eraseExprs es
  | [], _ => rfl
  | e :: es, L => by simp [markExprs, eraseExprs, Expr.erase_markMoves e, eraseExprs_mark es L]

theorem eraseFields_mark : ∀ (fs : List (Name × Expr)) (L : Live),
    eraseFields (markFields L fs) = eraseFields fs
  | [], _ => rfl
  | (_, e) :: fs, L => by
    simp [markFields, eraseFields, Expr.erase_markMoves e, eraseFields_mark fs L]

theorem eraseArgs_mark : ∀ (args : List Arg) (L : Live), eraseArgs (markArgs L args) = eraseArgs args
  | [], _ => rfl
  | .value e :: args, L => by
    simp [markArgs, eraseArgs, Expr.erase_markMoves e, eraseArgs_mark args L]
  | .inout ⟨_, p⟩ :: args, L => by
    simp [markArgs, eraseArgs, erasePath_mark p, eraseArgs_mark args L]

theorem erasePath_mark : ∀ (p : List Projection) (L : Live), erasePath (markPath L p) = erasePath p
  | [], _ => rfl
  | .field _ :: p, L => by simp [markPath, erasePath, erasePath_mark p L]
  | .index i :: p, L => by simp [markPath, erasePath, Expr.erase_markMoves i, erasePath_mark p L]

theorem eraseArms_mark : ∀ (arms : List Arm) (L : Live), eraseArms (markArms L arms) = eraseArms arms
  | [], _ => rfl
  | ⟨_, _, g, b⟩ :: arms, L => by
    simp [markArms, eraseArms, eraseGuard_mark g, Expr.erase_markMoves b, eraseArms_mark arms L]

theorem eraseGuard_mark : ∀ (g : Option Expr) (L : Live), eraseGuard (markGuard L g) = eraseGuard g
  | none, _ => rfl
  | some g, L => by simp [markGuard, eraseGuard, Expr.erase_markMoves g]

end

theorem Program.erase_markMoves (p : Program) : p.markMoves.erase = p.erase := by
  simp only [Program.erase, Program.markMoves, Decls.mapFns_mapFns, Expr.erase_markMoves]
  congr 2
  funext d
  simp [FnDecl.erase, FnDecl.markMoves, Expr.erase_markMoves]

/-! ## Checks see through the marks -/

theorem fields_erasePath (path : List Projection) :
    (erasePath path).filterMap Projection.fieldName? = path.filterMap Projection.fieldName? := by
  induction path with
  | nil => rfl
  | cons p path ih => cases p <;> simp [erasePath, Projection.fieldName?, ih, List.filterMap_cons]

theorem shape_erasePath (x : Name) (path : List Projection) :
    (Place.mk x (erasePath path)).shape = (Place.mk x path).shape := by
  simp [Place.shape, fields_erasePath]

theorem inoutShapes_eraseArgs : ∀ args : List Arg, inoutShapes (eraseArgs args) = inoutShapes args
  | [] => rfl
  | .value _ :: args => by simpa [eraseArgs, inoutShapes] using inoutShapes_eraseArgs args
  | .inout ⟨x, path⟩ :: args => by
    simp [eraseArgs, inoutShapes, inoutShapes_eraseArgs args, shape_erasePath]

theorem placeShape_erase : ∀ e : Expr, e.erase.placeShape = e.placeShape
  | .var _ | .move _ => rfl
  | .field e f => by
    rw [show (Expr.field e f).erase = .field e.erase f from rfl, placeShape_field,
      placeShape_field, placeShape_erase e]
  | .index e i => by
    rw [show (Expr.index e i).erase = .index e.erase i.erase from rfl, placeShape_index,
      placeShape_index, placeShape_erase e]
  | .int _ | .bool _ | .unit | .record .. | .variant .. | .list .. | .op .. | .view _ | .fnRef .. | .method .. | .closure ..
  | .call .. | .letIn .. | .varIn .. | .assign ⟨_, _⟩ _ | .seq .. | .if .. | .match .. | .for ..
  | .raise _ | .perform _ _ | .try _ | .form _ _ | .tryCatch .. | .while .. | .loop _ | .break | .continue
  | .return _ | .withH .. | .held .. => by
    simp [Expr.erase, Expr.placeShape, Expr.place?]

theorem iterated_erase (e : Expr) : iterated e.erase = iterated e := by
  have := placeShape_erase e
  simp only [Expr.placeShape] at this
  simp [iterated, this]

mutual

theorem Expr.exclusive_erase : ∀ (e : Expr) (r : List Shape), e.erase.exclusive r = e.exclusive r
  | .var _, _ | .move _, _ | .int _, _ | .bool _, _ | .unit, _ | .break, _ | .continue, _
  | .fnRef .., _ | .method .., _ => rfl
  | .record _ _ fs, r => by simp [Expr.erase, Expr.exclusive, fieldsExclusive_erase fs r]
  | .variant _ _ _ es, r | .list _ es, r | .op _ es, r | .view es, r => by
    simp [Expr.erase, Expr.exclusive, exprsExclusive_erase es r]
  | .field e _, r | .raise e, r | .perform _ e, r | .try e, r | .form _ e, r | .loop e, r | .return e, r => by
    simp [Expr.erase, Expr.exclusive, Expr.exclusive_erase e r]
  | .index e i, r | .seq e i, r | .withH _ _ e i, r | .while e i, r => by
    simp [Expr.erase, Expr.exclusive, Expr.exclusive_erase e r, Expr.exclusive_erase i r]
  | .held _ hs b, r => by
    simp [Expr.erase, Expr.exclusive, exprsExclusive_erase hs r, Expr.exclusive_erase b]
  | .closure _ _ _ b, _ => by simp [Expr.erase, Expr.exclusive, Expr.exclusive_erase b []]
  | .call f args _, r => by
    simp [Expr.erase, Expr.exclusive, Expr.exclusive_erase f r, argsExclusive_erase args r,
      inoutShapes_eraseArgs]
  | .letIn x _ i b, r | .varIn x _ i b, r | .tryCatch i _ x b _, r => by
    simp [Expr.erase, Expr.exclusive, Expr.exclusive_erase i r, Expr.exclusive_erase b (hide r x)]
  | .assign ⟨_, p⟩ v, r => by
    simp [Expr.erase, Expr.exclusive, pathExclusive_erase p r, Expr.exclusive_erase v r,
      shape_erasePath]
  | .if c _ a b, r => by
    simp [Expr.erase, Expr.exclusive, Expr.exclusive_erase c r, Expr.exclusive_erase a r,
      Expr.exclusive_erase b r]
  | .match e _ arms, r => by
    simp [Expr.erase, Expr.exclusive, Expr.exclusive_erase e r, armsExclusive_erase arms r]
  | .for x _ e b, r => by
    simp [Expr.erase, Expr.exclusive, Expr.exclusive_erase e r, iterated_erase,
      Expr.exclusive_erase b (hide (iterated e ++ r) x)]

theorem exprsExclusive_erase : ∀ (es : List Expr) (r : List Shape),
    exprsExclusive r (eraseExprs es) = exprsExclusive r es
  | [], _ => rfl
  | e :: es, r => by
    simp [eraseExprs, exprsExclusive, Expr.exclusive_erase e r, exprsExclusive_erase es r]

theorem fieldsExclusive_erase : ∀ (fs : List (Name × Expr)) (r : List Shape),
    fieldsExclusive r (eraseFields fs) = fieldsExclusive r fs
  | [], _ => rfl
  | (_, e) :: fs, r => by
    simp [eraseFields, fieldsExclusive, Expr.exclusive_erase e r, fieldsExclusive_erase fs r]

theorem argsExclusive_erase : ∀ (args : List Arg) (r : List Shape),
    argsExclusive r (eraseArgs args) = argsExclusive r args
  | [], _ => rfl
  | .value e :: args, r => by
    simp [eraseArgs, argsExclusive, Expr.exclusive_erase e r, argsExclusive_erase args r]
  | .inout ⟨_, p⟩ :: args, r => by
    simp [eraseArgs, argsExclusive, pathExclusive_erase p r, argsExclusive_erase args r]

theorem pathExclusive_erase : ∀ (p : List Projection) (r : List Shape),
    pathExclusive r (erasePath p) = pathExclusive r p
  | [], _ => rfl
  | .field _ :: p, r => by simpa [erasePath, pathExclusive] using pathExclusive_erase p r
  | .index i :: p, r => by
    simp [erasePath, pathExclusive, Expr.exclusive_erase i r, pathExclusive_erase p r]

theorem armsExclusive_erase : ∀ (arms : List Arm) (r : List Shape),
    armsExclusive r (eraseArms arms) = armsExclusive r arms
  | [], _ => rfl
  | ⟨_, bs, g, b⟩ :: arms, r => by
    simp [eraseArms, armsExclusive, guardExclusive_erase g (bs.foldl hide r),
      Expr.exclusive_erase b (bs.foldl hide r), armsExclusive_erase arms r]

theorem guardExclusive_erase : ∀ (g : Option Expr) (r : List Shape),
    guardExclusive r (eraseGuard g) = guardExclusive r g
  | none, _ => rfl
  | some g, r => by simp [eraseGuard, guardExclusive, Expr.exclusive_erase g r]

end

end Stilt

/-! ## Erasing keeps the variables an expression uses -/

namespace Stilt

mutual

theorem Expr.free_erase (x : Name) : ∀ e : Expr, e.erase.free x = e.free x
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef .. | .method .. => rfl
  | .closure _ _ _ body => by simp [Expr.erase, Expr.free, Expr.free_erase x body]
  | .record _ _ fs => by simp [Expr.erase, Expr.free, fieldsFree_erase x fs]
  | .variant _ _ _ es | .list _ es | .op _ es | .view es => by simp [Expr.erase, Expr.free, exprsFree_erase x es]
  | .field e _ | .raise e | .perform _ e | .try e | .form _ e | .loop e | .return e => by
    simp [Expr.erase, Expr.free, Expr.free_erase x e]
  | .index a b | .seq a b | .withH _ _ a b | .letIn _ _ a b | .varIn _ _ a b
  | .for _ _ a b | .while a b | .tryCatch a _ _ b _ => by
    simp [Expr.erase, Expr.free, Expr.free_erase x a, Expr.free_erase x b]
  | .call f args _ => by simp [Expr.erase, Expr.free, Expr.free_erase x f, argsFree_erase x args]
  | .assign ⟨_, p⟩ v => by simp [Expr.erase, Expr.free, pathFree_erase x p, Expr.free_erase x v]
  | .if c _ a b => by
    simp [Expr.erase, Expr.free, Expr.free_erase x c, Expr.free_erase x a, Expr.free_erase x b]
  | .match e _ arms => by simp [Expr.erase, Expr.free, Expr.free_erase x e, armsFree_erase x arms]
  | .held _ hs b => by simp [Expr.erase, Expr.free, exprsFree_erase x hs, Expr.free_erase x b]

theorem exprsFree_erase (x : Name) : ∀ es : List Expr, exprsFree x (eraseExprs es) = exprsFree x es
  | [] => rfl
  | e :: es => by simp [eraseExprs, exprsFree, Expr.free_erase x e, exprsFree_erase x es]

theorem fieldsFree_erase (x : Name) :
    ∀ fs : List (Name × Expr), fieldsFree x (eraseFields fs) = fieldsFree x fs
  | [] => rfl
  | (_, e) :: fs => by simp [eraseFields, fieldsFree, Expr.free_erase x e, fieldsFree_erase x fs]

theorem argsFree_erase (x : Name) : ∀ args : List Arg, argsFree x (eraseArgs args) = argsFree x args
  | [] => rfl
  | .value e :: args => by simp [eraseArgs, argsFree, Expr.free_erase x e, argsFree_erase x args]
  | .inout ⟨_, p⟩ :: args => by
    simp [eraseArgs, argsFree, pathFree_erase x p, argsFree_erase x args]

theorem pathFree_erase (x : Name) : ∀ p : List Projection, pathFree x (erasePath p) = pathFree x p
  | [] => rfl
  | .field _ :: p => by simp [erasePath, pathFree, pathFree_erase x p]
  | .index i :: p => by simp [erasePath, pathFree, Expr.free_erase x i, pathFree_erase x p]

theorem armsFree_erase (x : Name) : ∀ arms : List Arm, armsFree x (eraseArms arms) = armsFree x arms
  | [] => rfl
  | ⟨_, _, g, b⟩ :: arms => by
    simp [eraseArms, armsFree, guardFree_erase x g, Expr.free_erase x b, armsFree_erase x arms]

theorem guardFree_erase (x : Name) : ∀ g : Option Expr, guardFree x (eraseGuard g) = guardFree x g
  | none => rfl
  | some g => by simp [eraseGuard, guardFree, Expr.free_erase x g]

end

/-- A closure literal captures, with its marks erased, the variables it captured. -/
theorem Expr.captures_erase (ps : List Param) (body : Expr) :
    Expr.captures ps body.erase = Expr.captures ps body := by
  funext x
  simp [Expr.captures, Expr.free_erase]

end Stilt
