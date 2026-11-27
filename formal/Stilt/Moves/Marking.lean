import Stilt.Moves.Analysis

/-!
# Marking last uses

`Expr.markMoves` marks each argument and each initializer of `let` or `var`
that is a variable at its last use, as the compiler infers it (values.passing-values). Every mark it makes passes `Expr.movesOk`.
-/

namespace Stilt

mutual

/-- Marks the last uses in `e` (facts.last-use, as `Expr.movesOk` reads it),
when `after` holds the variables that what follows `e` mentions. `pos` says whether `e` is an argument or an initializer,
the two positions where a last use may hand its storage over. Each part is
marked with what follows it, as `Expr.movesOk` checks it. -/
def Expr.markMoves (after : Live) (pos : Bool) : Expr → Expr
  | .var x | .move x => if pos && !after.mem x then .move x else .var x
  | .int n => .int n
  | .bool b => .bool b
  | .unit => .unit
  | .record R τs fields => .record R τs (markFields after fields)
  | .variant T τs C es => .variant T τs C (markExprs after es)
  | .list τ es => .list τ (markExprs after es)
  | .op o es => .op o (markExprs after es)
  | .view es => .view (markExprs after es)
  | .field e f => .field (e.markMoves after false) f
  | .index e i => .index (e.markMoves (after.union i.mentions) false) (i.markMoves after false)
  | .fnRef f types rows => .fnRef f types rows
  | .method t m τ => .method t m τ
  | .closure ps r ρ body => .closure ps r ρ (body.markMoves (inoutLive ps) false)
  | .call f args τ =>
    .call (f.markMoves (after.union (argsMentions args)) false)
      (markArgs (after.union (Live.ofList (inoutRoots args))) args) τ
  | .letIn x τ init body =>
    .letIn x τ (init.markMoves (after.union (body.mentions.erase x)) true)
      (body.markMoves (after.erase x) false)
  | .varIn x τ init body =>
    .varIn x τ (init.markMoves (after.union (body.mentions.erase x)) true)
      (body.markMoves (after.erase x) false)
  | .assign ⟨x, path⟩ v =>
    .assign ⟨x, markPath ((Live.one x).union (after.union v.mentions)) path⟩
      (v.markMoves ((Live.one x).union after) false)
  | .seq a b => .seq (a.markMoves (after.union b.mentions) false) (b.markMoves after false)
  | .if c τ a b =>
    .if (c.markMoves (after.union (a.mentions.union b.mentions)) false) τ
      (a.markMoves after false) (b.markMoves after false)
  | .match e τ arms =>
    .match (e.markMoves (after.union (armsMentions arms)) false) τ (markArms after arms)
  | .for x τ e body =>
    .for x τ (e.markMoves (after.union (body.mentions.erase x)) false)
      (body.markMoves ((after.union body.mentions).erase x) false)
  | .raise e => .raise (e.markMoves after false)
  | .try e => .try (e.markMoves after false)
  | .form fm e => .form fm (e.markMoves after false)
  | .tryCatch e E x h τ => .tryCatch (e.markMoves (after.union (h.mentions.erase x)) false) E x
      (h.markMoves (after.erase x) false) τ
  | .while c body =>
    let again := after.union (c.mentions.union body.mentions)
    .while (c.markMoves again false) (body.markMoves again false)
  | .loop body => .loop (body.markMoves (after.union body.mentions) false)
  | .break => .break
  | .continue => .continue
  | .return e => .return (e.markMoves after false)
  | .perform op e => .perform op (e.markMoves after false)
  | .withH E c h b => .withH E c (h.markMoves (after.union b.mentions) false) (b.markMoves after false)
  | .held ns hs body =>
    .held ns (markExprs (after.union (body.mentions.eraseAll (ns.map (·.1)))) hs)
      (body.markMoves (after.union (Live.ofList (ns.map (·.1)))) false)

/-- Marks the last uses in a list of expressions, evaluated in order. -/
def markExprs (after : Live) : List Expr → List Expr
  | [] => []
  | e :: es => e.markMoves (after.union (exprsMentions es)) false :: markExprs after es

/-- Marks the last uses in the fields of a record literal. -/
def markFields (after : Live) : List (Name × Expr) → List (Name × Expr)
  | [] => []
  | (f, e) :: fields =>
    (f, e.markMoves (after.union (fieldsMentions fields)) false) :: markFields after fields

/-- Marks the last uses in a call's arguments: each value argument that is a
variable at its last use. -/
def markArgs (after : Live) : List Arg → List Arg
  | [] => []
  | .value e :: args => .value (e.markMoves (after.union (argsMentions args)) true) ::
      markArgs after args
  | .inout ⟨x, path⟩ :: args =>
    .inout ⟨x, markPath (after.union (argsMentions args)) path⟩ :: markArgs after args

/-- Marks the last uses in the indexes of a place. -/
def markPath (after : Live) : List Projection → List Projection
  | [] => []
  | .field f :: path => .field f :: markPath after path
  | .index i :: path =>
    .index (i.markMoves (after.union (pathMentions path)) false) :: markPath after path

/-- Marks the last uses in the arms of a `match`. -/
def markArms (after : Live) : List Arm → List Arm
  | [] => []
  | ⟨C, binders, guard, body⟩ :: arms =>
    ⟨C, binders,
      markGuard ((((after.union (armsMentions arms)).eraseAll binders).union body.mentions).union
        (guardMentions guard)) guard,
      body.markMoves (after.eraseAll binders) false⟩ :: markArms after arms

/-- Marks the last uses in an arm's guard. -/
def markGuard (after : Live) : Option Expr → Option Expr
  | none => none
  | some g => some (g.markMoves after false)

end

/-- Marks the last uses of a function's body, which hands its `inout`
parameters back. -/
def FnDecl.markMoves (d : FnDecl) : FnDecl :=
  { d with body := d.body.markMoves (inoutLive d.params) false }

theorem FnDecl.markMoves_qualify (T : Name) (d : FnDecl) :
    (d.qualify T).markMoves = d.markMoves.qualify T := rfl

/-- Marks the last uses of every body of the program. -/
def Program.markMoves (p : Program) : Program :=
  { p with
    decls := p.decls.mapFns FnDecl.markMoves
    main := p.main.markMoves .empty false }

/-- Marking reaches every function, methods included. -/
theorem Program.markMoves_fns (p : Program) :
    p.markMoves.decls.fns = p.decls.fns.map FnDecl.markMoves :=
  Decls.fns_mapFns FnDecl.markMoves_qualify _

/-! ## Marking keeps what is mentioned -/

mutual

theorem Expr.mentions_markMoves :
    ∀ (e : Expr) (L : Live) (b : Bool), (e.markMoves L b).mentions = e.mentions
  | .var x, L, b | .move x, L, b => by
    simp only [Expr.markMoves]
    split <;> rfl
  | .int _, _, _ | .bool _, _, _ | .unit, _, _ | .fnRef .., _, _ | .method .., _, _ => rfl
  | .closure _ _ _ body, _, _ => by simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves body]
  | .record _ _ fs, L, _ => by simp [Expr.markMoves, Expr.mentions, fieldsMentions_mark fs L]
  | .variant _ _ _ es, L, _ => by simp [Expr.markMoves, Expr.mentions, exprsMentions_mark es L]
  | .list _ es, L, _ => by simp [Expr.markMoves, Expr.mentions, exprsMentions_mark es L]
  | .op _ es, L, _ | .view es, L, _ => by simp [Expr.markMoves, Expr.mentions, exprsMentions_mark es L]
  | .field e _, L, _ => by simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves e]
  | .index e i, L, _ => by
    simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves e, Expr.mentions_markMoves i]
  | .call f args _, L, _ => by
    simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves f, argsMentions_mark args]
  | .letIn x _ i b, L, _ | .varIn x _ i b, L, _ => by
    simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves i, Expr.mentions_markMoves b]
  | .held _ hs b, L, _ => by
    simp [Expr.markMoves, Expr.mentions, exprsMentions_mark hs, Expr.mentions_markMoves b]
  | .assign ⟨x, p⟩ v, L, _ => by
    simp [Expr.markMoves, Expr.mentions, pathMentions_mark p, Expr.mentions_markMoves v]
  | .seq a b, L, _ | .withH _ _ a b, L, _ => by
    simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves a, Expr.mentions_markMoves b]
  | .if c _ a b, L, _ => by
    simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves c, Expr.mentions_markMoves a,
      Expr.mentions_markMoves b]
  | .match e _ arms, L, _ => by
    simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves e, armsMentions_mark arms]
  | .for x _ e b, L, _ => by
    simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves e, Expr.mentions_markMoves b]
  | .raise e, L, _ | .perform _ e, L, _ | .try e, L, _ | .form _ e, L, _ => by
    simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves e]
  | .tryCatch e _ x h _, L, _ => by
    simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves e, Expr.mentions_markMoves h]
  | .while c b, L, _ => by
    simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves c, Expr.mentions_markMoves b]
  | .loop b, L, _ | .return b, L, _ => by
    simp [Expr.markMoves, Expr.mentions, Expr.mentions_markMoves b]
  | .break, _, _ | .continue, _, _ => rfl

theorem exprsMentions_mark : ∀ (es : List Expr) (L : Live),
    exprsMentions (markExprs L es) = exprsMentions es
  | [], _ => rfl
  | e :: es, L => by
    simp [markExprs, exprsMentions, Expr.mentions_markMoves e, exprsMentions_mark es L]

theorem fieldsMentions_mark : ∀ (fs : List (Name × Expr)) (L : Live),
    fieldsMentions (markFields L fs) = fieldsMentions fs
  | [], _ => rfl
  | (_, e) :: fs, L => by
    simp [markFields, fieldsMentions, Expr.mentions_markMoves e, fieldsMentions_mark fs L]

theorem argsMentions_mark : ∀ (args : List Arg) (L : Live),
    argsMentions (markArgs L args) = argsMentions args
  | [], _ => rfl
  | .value e :: args, L => by
    simp [markArgs, argsMentions, Expr.mentions_markMoves e, argsMentions_mark args L]
  | .inout ⟨_, p⟩ :: args, L => by
    simp [markArgs, argsMentions, pathMentions_mark p, argsMentions_mark args L]

theorem pathMentions_mark : ∀ (p : List Projection) (L : Live),
    pathMentions (markPath L p) = pathMentions p
  | [], _ => rfl
  | .field _ :: p, L => by simp [markPath, pathMentions, pathMentions_mark p L]
  | .index i :: p, L => by
    simp [markPath, pathMentions, Expr.mentions_markMoves i, pathMentions_mark p L]

theorem armsMentions_mark : ∀ (arms : List Arm) (L : Live),
    armsMentions (markArms L arms) = armsMentions arms
  | [], _ => rfl
  | ⟨_, _, g, b⟩ :: arms, L => by
    simp [markArms, armsMentions, guardMentions_mark g, Expr.mentions_markMoves b,
      armsMentions_mark arms L]

theorem guardMentions_mark : ∀ (g : Option Expr) (L : Live),
    guardMentions (markGuard L g) = guardMentions g
  | none, _ => rfl
  | some g, L => by simp [markGuard, guardMentions, Expr.mentions_markMoves g]

end

theorem inoutRoots_markArgs : ∀ (L : Live) (args : List Arg),
    inoutRoots (markArgs L args) = inoutRoots args
  | _, [] => rfl
  | L, .value _ :: args => by simp [markArgs, inoutRoots, inoutRoots_markArgs L args]
  | L, .inout ⟨_, _⟩ :: args => by simp [markArgs, inoutRoots, inoutRoots_markArgs L args]

/-! ## Every mark is a last use -/

section

open Expr

mutual

theorem Expr.movesOk_markMoves :
    ∀ (e : Expr) (L : Live) (b : Bool), (e.markMoves L b).movesOk L = true
  | .var x, L, b | .move x, L, b => by
    simp only [Expr.markMoves]
    split
    · rename_i h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      simp [Expr.movesOk, h.2]
    · rfl
  | .int _, _, _ | .bool _, _, _ | .unit, _, _ | .fnRef .., _, _ | .method .., _, _ => rfl
  | .closure _ _ _ body, _, _ => Expr.movesOk_markMoves body _ false
  | .record _ _ fs, L, _ => fieldsMovesOk_mark fs L
  | .variant _ _ _ es, L, _ | .list _ es, L, _ | .op _ es, L, _ | .view es, L, _ => exprsMovesOk_mark es L
  | .field e _, L, _ => Expr.movesOk_markMoves e L false
  | .index e i, L, _ => by
    simp [Expr.markMoves, Expr.movesOk, mentions_markMoves, Expr.movesOk_markMoves e,
      Expr.movesOk_markMoves i]
  | .call f args _, L, _ => by
    simp [Expr.markMoves, Expr.movesOk, argsMentions_mark, inoutRoots_markArgs,
      Expr.movesOk_markMoves f, argsMovesOk_mark args]
  | .held _ hs b, L, _ => by
    simp [Expr.markMoves, Expr.movesOk, mentions_markMoves, exprsMovesOk_mark hs,
      Expr.movesOk_markMoves b]
  | .letIn x _ i b, L, _ | .varIn x _ i b, L, _ => by
    simp [Expr.markMoves, Expr.movesOk, mentions_markMoves, Expr.movesOk_markMoves i,
      Expr.movesOk_markMoves b]
  | .assign ⟨x, p⟩ v, L, _ => by
    simp [Expr.markMoves, Expr.movesOk, mentions_markMoves, pathMovesOk_mark p,
      Expr.movesOk_markMoves v]
  | .seq a b, L, _ | .withH _ _ a b, L, _ => by
    simp [Expr.markMoves, Expr.movesOk, mentions_markMoves, Expr.movesOk_markMoves a,
      Expr.movesOk_markMoves b]
  | .if c _ a b, L, _ => by
    simp [Expr.markMoves, Expr.movesOk, mentions_markMoves, Expr.movesOk_markMoves c,
      Expr.movesOk_markMoves a, Expr.movesOk_markMoves b]
  | .match e _ arms, L, _ => by
    simp [Expr.markMoves, Expr.movesOk, armsMentions_mark, Expr.movesOk_markMoves e,
      armsMovesOk_mark arms]
  | .for x _ e b, L, _ => by
    simp [Expr.markMoves, Expr.movesOk, mentions_markMoves, Expr.movesOk_markMoves e,
      Expr.movesOk_markMoves b]
  | .raise e, L, _ | .perform _ e, L, _ | .try e, L, _ | .form _ e, L, _ => Expr.movesOk_markMoves e L false
  | .tryCatch e _ x h _, L, _ => by
    simp [Expr.markMoves, Expr.movesOk, mentions_markMoves, Expr.movesOk_markMoves e,
      Expr.movesOk_markMoves h]
  | .while c b, L, _ => by
    simp [Expr.markMoves, Expr.movesOk, mentions_markMoves, Expr.movesOk_markMoves c,
      Expr.movesOk_markMoves b]
  | .loop b, L, _ => by
    simp [Expr.markMoves, Expr.movesOk, mentions_markMoves, Expr.movesOk_markMoves b]
  | .return e, L, _ => Expr.movesOk_markMoves e L false
  | .break, _, _ | .continue, _, _ => rfl

theorem exprsMovesOk_mark : ∀ (es : List Expr) (L : Live),
    exprsMovesOk L (markExprs L es) = true
  | [], _ => rfl
  | e :: es, L => by
    simp [markExprs, exprsMovesOk, exprsMentions_mark, Expr.movesOk_markMoves e,
      exprsMovesOk_mark es L]

theorem fieldsMovesOk_mark : ∀ (fs : List (Name × Expr)) (L : Live),
    fieldsMovesOk L (markFields L fs) = true
  | [], _ => rfl
  | (_, e) :: fs, L => by
    simp [markFields, fieldsMovesOk, fieldsMentions_mark, Expr.movesOk_markMoves e,
      fieldsMovesOk_mark fs L]

theorem argsMovesOk_mark : ∀ (args : List Arg) (L : Live),
    argsMovesOk L (markArgs L args) = true
  | [], _ => rfl
  | .value e :: args, L => by
    simp [markArgs, argsMovesOk, argsMentions_mark, Expr.movesOk_markMoves e,
      argsMovesOk_mark args L]
  | .inout ⟨_, p⟩ :: args, L => by
    simp [markArgs, argsMovesOk, argsMentions_mark, pathMovesOk_mark p, argsMovesOk_mark args L]

theorem pathMovesOk_mark : ∀ (p : List Projection) (L : Live),
    pathMovesOk L (markPath L p) = true
  | [], _ => rfl
  | .field _ :: p, L => pathMovesOk_mark p L
  | .index i :: p, L => by
    simp [markPath, pathMovesOk, pathMentions_mark, Expr.movesOk_markMoves i, pathMovesOk_mark p L]

theorem armsMovesOk_mark : ∀ (arms : List Arm) (L : Live),
    armsMovesOk L (markArms L arms) = true
  | [], _ => rfl
  | ⟨_, _, g, b⟩ :: arms, L => by
    simp [markArms, armsMovesOk, armsMentions_mark, mentions_markMoves, guardMentions_mark,
      guardMovesOk_mark g,
      Expr.movesOk_markMoves b, armsMovesOk_mark arms L]

theorem guardMovesOk_mark : ∀ (g : Option Expr) (L : Live),
    guardMovesOk L (markGuard L g) = true
  | none, _ => rfl
  | some g, L => by simp [markGuard, guardMovesOk, Expr.movesOk_markMoves g]

end

end

/-- Every mark that `Program.markMoves` makes is a last use. -/
theorem Program.markMoves_justified (p : Program) : p.markMoves.MovesJustified := by
  refine ⟨fun d hd => ?_, Expr.movesOk_markMoves _ _ _⟩
  rw [Program.markMoves_fns, List.mem_map] at hd
  obtain ⟨d, -, rfl⟩ := hd
  exact Expr.movesOk_markMoves _ _ _

end Stilt
