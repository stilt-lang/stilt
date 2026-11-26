import Stilt.Places

/-!
# Renaming variables

`Expr.rename g` writes every variable of an expression as `g` gives it: those it reads, the
roots of the places it writes or passes `inout`, and those it binds. The law of exclusivity
reads it to treat several names as one (shared.names-that-may-be-one-place): a `when`'s
block with the names of one type written as the first of them.
-/

namespace Stilt

/-- A parameter whose name `g` gives. -/
def Param.rename (g : Name → Name) (p : Param) : Param := { p with name := g p.name }

mutual

/-- `e` with every variable written as `g` gives it. -/
def Expr.rename (g : Name → Name) : Expr → Expr
  | .var x => .var (g x)
  | .move x => .move (g x)
  | .int n => .int n
  | .bool b => .bool b
  | .unit => .unit
  | .break => .break
  | .continue => .continue
  | .fnRef f tys rows => .fnRef f tys rows
  | .method t m τ => .method t m τ
  | .record R τs fields => .record R τs (renameFields g fields)
  | .variant T τs C es => .variant T τs C (renameExprs g es)
  | .list τ es => .list τ (renameExprs g es)
  | .op o es => .op o (renameExprs g es)
  | .view es => .view (renameExprs g es)
  | .field e f => .field (e.rename g) f
  | .index e i => .index (e.rename g) (i.rename g)
  | .closure ps r ρ body => .closure (ps.map (Param.rename g)) r ρ (body.rename g)
  | .call f args τ => .call (f.rename g) (renameArgs g args) τ
  | .letIn x τ e body => .letIn (g x) τ (e.rename g) (body.rename g)
  | .varIn x τ e body => .varIn (g x) τ (e.rename g) (body.rename g)
  | .assign ⟨x, path⟩ e => .assign ⟨g x, renamePath g path⟩ (e.rename g)
  | .seq a b => .seq (a.rename g) (b.rename g)
  | .if c τ a b => .if (c.rename g) τ (a.rename g) (b.rename g)
  | .match e τ arms => .match (e.rename g) τ (renameArms g arms)
  | .for x τ e body => .for (g x) τ (e.rename g) (body.rename g)
  | .raise e => .raise (e.rename g)
  | .try e => .try (e.rename g)
  | .tryCatch e E x h τ => .tryCatch (e.rename g) E (g x) (h.rename g) τ
  | .while c body => .while (c.rename g) (body.rename g)
  | .loop body => .loop (body.rename g)
  | .return e => .return (e.rename g)
  | .perform op e => .perform op (e.rename g)
  | .withH E c h b => .withH E c (h.rename g) (b.rename g)
  | .held ns hs body => .held (ns.map fun p => (g p.1, p.2)) (renameExprs g hs) (body.rename g)

def renameExprs (g : Name → Name) : List Expr → List Expr
  | [] => []
  | e :: es => e.rename g :: renameExprs g es

def renameFields (g : Name → Name) : List (Name × Expr) → List (Name × Expr)
  | [] => []
  | (f, e) :: fields => (f, e.rename g) :: renameFields g fields

def renameArgs (g : Name → Name) : List Arg → List Arg
  | [] => []
  | .value e :: args => .value (e.rename g) :: renameArgs g args
  | .inout ⟨x, path⟩ :: args => .inout ⟨g x, renamePath g path⟩ :: renameArgs g args

def renamePath (g : Name → Name) : List Projection → List Projection
  | [] => []
  | .field f :: path => .field f :: renamePath g path
  | .index i :: path => .index (i.rename g) :: renamePath g path

/-- The arms of a `match`, each binder written as `g` gives it; a pattern's names are where
its binders say they are. -/
def renameArms (g : Name → Name) : List Arm → List Arm
  | [] => []
  | ⟨p, binders, body⟩ :: arms => ⟨p, binders.map g, body.rename g⟩ :: renameArms g arms

end

end Stilt
