import Stilt.Free

/-!
# Last uses

The analysis that marks the last use of a variable, and the check that a
program's marks are last uses.

A body's variables are mentioned where they are read, written, passed or
bound. A read of `x` is a last use when nothing evaluated after it, up to the
end of the body, mentions `x` (facts.last-use). A loop's body is followed by
its next turn, so a variable that a loop mentions has no last use inside it.
Leaving a body uses its `inout` parameters, which go back to the caller
(values.passing-values), so an `inout` parameter has no last use. A closure
literal mentions what its body mentions but its parameters: a use inside the
literal counts as a use at the literal, and those hold every variable the
literal captures (expressions.capture, `Expr.mentions_of_captures`), the only
ones it reads when it is made. A binder `let x` or `var x` ends the scope of
the earlier `x` for the rest of its body, so `var x = x` is the last use of
the earlier `x` when nothing after the binding mentions it.

The analysis goes by names and by evaluation order. A binder mentions its
name, so a later binding of `x` and a binding of `x` inside a later closure
literal count as uses of an earlier `x`; a loop's next turn mentions what its
body binds, so a binding declared inside a loop has no last use there either;
and a `move x` of an inner `x` counts the uses after its block of the `x` it
hides. There the analysis is stricter than facts.last-use. A branch of an
`if` or an arm of a `match` is followed by what follows the whole expression,
not by the other branches, which never run after it: there it is less strict,
and the theorem proves those marks safe too.

`Expr.markMoves` marks each argument and each initializer that is a variable
at its last use; `Expr.movesOk` checks that every mark of a body is one. Only
a mark at those two positions changes what a model of memory may do, and the
check accepts any subset of the marks the analysis makes.
-/

namespace Stilt

/-- A set of variables, those of a list. -/
structure Live where
  names : List Name

namespace Live

/-- Whether the set holds `x`. -/
def mem (L : Live) (x : Name) : Bool := L.names.contains x

/-- No variable. -/
def empty : Live := ⟨[]⟩

/-- One variable. -/
def one (x : Name) : Live := ⟨[x]⟩

/-- The variables of a list. -/
def ofList (xs : List Name) : Live := ⟨xs⟩

/-- The variables of either set. -/
def union (a b : Live) : Live := ⟨a.names ++ b.names⟩

/-- The variables of `L` but `x`. -/
def erase (L : Live) (x : Name) : Live := ⟨L.names.filter (· != x)⟩

/-- Leaves out the names. -/
def eraseAll (L : Live) (xs : List Name) : Live := xs.foldl erase L

/-- Every variable of `L` is in `L'`. -/
def Sub (L L' : Live) : Prop := ∀ x, L.mem x = true → L'.mem x = true

@[simp] theorem mem_union (a b : Live) (x : Name) : (a.union b).mem x = (a.mem x || b.mem x) := by
  simp [mem, union]

@[simp] theorem mem_one (x y : Name) : (one x).mem y = true ↔ y = x := by
  simp [mem, one]

@[simp] theorem mem_empty (x : Name) : empty.mem x = false := rfl

theorem mem_erase {L : Live} {x y : Name} (h : (L.erase y).mem x = true) : L.mem x = true := by
  simp only [mem, erase, List.contains_iff_mem, List.mem_filter] at h ⊢
  exact h.1

theorem mem_erase_of_ne {L : Live} {x y : Name} (h : L.mem x = true) (hne : x ≠ y) :
    (L.erase y).mem x = true := by
  simp only [mem, erase, List.contains_iff_mem, List.mem_filter, bne_iff_ne, ne_eq] at h ⊢
  exact ⟨h, hne⟩

theorem Sub.refl (L : Live) : L.Sub L := fun _ => id

theorem Sub.trans {a b c : Live} (h₁ : a.Sub b) (h₂ : b.Sub c) : a.Sub c :=
  fun x h => h₂ x (h₁ x h)

theorem sub_union_left (a b : Live) : a.Sub (a.union b) :=
  fun x h => by simp [h]

theorem sub_union_right (a b : Live) : b.Sub (a.union b) :=
  fun x h => by simp [h]

theorem Sub.union {a b c : Live} (h₁ : a.Sub c) (h₂ : b.Sub c) : (a.union b).Sub c := by
  intro x h
  simp only [mem_union, Bool.or_eq_true] at h
  exact h.elim (h₁ x) (h₂ x)

theorem erase_sub (L : Live) (y : Name) : (L.erase y).Sub L :=
  fun _ h => mem_erase h

theorem empty_sub (L : Live) : empty.Sub L :=
  fun _ h => absurd h (by simp)

theorem mem_eraseAll : ∀ {L : Live} {xs : List Name} {x : Name}, L.mem x = true → x ∉ xs →
    (L.eraseAll xs).mem x = true
  | _, [], _, h, _ => h
  | L, y :: ys, x, h, hx =>
    mem_eraseAll (L := L.erase y) (xs := ys) (mem_erase_of_ne h fun e => hx (by subst e; simp))
      fun h' => hx (List.mem_cons_of_mem _ h')

theorem eraseAll_sub : ∀ (L : Live) (xs : List Name), (L.eraseAll xs).Sub L
  | _, [] => Sub.refl _
  | L, y :: ys => (eraseAll_sub (L.erase y) ys).trans (erase_sub L y)

@[simp] theorem mem_ofList (xs : List Name) (x : Name) : (ofList xs).mem x = true ↔ x ∈ xs := by
  simp [mem, ofList]

end Live

/-- Proves that one union of sets of variables is within another. -/
macro "live_sub" : tactic => `(tactic| exact fun _ h => by
    simp only [Live.mem_union, Live.mem_ofList, Live.mem_one, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, Bool.or_eq_true] at h ⊢; grind)

/-- The variables a body hands back to its caller when it ends: its `inout`
parameters (values.passing-values and values.inout-arguments). -/
def inoutLive (ps : List Param) : Live :=
  Live.ofList ((ps.filter (·.mode == .inout)).map Param.name)

/-- The roots of a call's `inout` arguments, which the call uses when it
starts (modes.durations). -/
def inoutRoots : List Arg → List Name
  | [] => []
  | .inout p :: args => p.root :: inoutRoots args
  | .value _ :: args => inoutRoots args

mutual

/-- The variables an expression mentions: those it reads, writes, passes or
binds. A closure literal mentions those its body mentions but its parameters,
among which are the variables it captures (expressions.capture). -/
def Expr.mentions : Expr → Live
  | .var x | .move x => .one x
  | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _ | .method _ _ _ => .empty
  | .record _ fields => fieldsMentions fields
  | .variant _ _ es => exprsMentions es
  | .list _ es => exprsMentions es
  | .op _ es | .view es => exprsMentions es
  | .field e _ => e.mentions
  | .index e i => e.mentions.union i.mentions
  | .closure ps _ _ body => body.mentions.eraseAll (ps.map Param.name)
  | .call f args _ => f.mentions.union (argsMentions args)
  | .letIn x _ init body => (Live.one x).union (init.mentions.union body.mentions)
  | .varIn x _ init body => (Live.one x).union (init.mentions.union body.mentions)
  | .assign ⟨x, path⟩ v => (Live.one x).union ((pathMentions path).union v.mentions)
  | .seq a b => a.mentions.union b.mentions
  | .if c _ a b => c.mentions.union (a.mentions.union b.mentions)
  | .match e _ arms => e.mentions.union (armsMentions arms)
  | .for x _ e body => (Live.one x).union (e.mentions.union body.mentions)
  | .raise e => e.mentions
  | .try e => e.mentions
  | .tryCatch e _ x h _ => (Live.one x).union (e.mentions.union h.mentions)
  | .while c body => c.mentions.union body.mentions
  | .loop body => body.mentions
  | .return e => e.mentions
  | .perform _ e => e.mentions
  | .withH _ _ h b => h.mentions.union b.mentions
  | .held ns hs body => (Live.ofList (ns.map (·.1))).union ((exprsMentions hs).union body.mentions)

/-- The variables a list of expressions mentions. -/
def exprsMentions : List Expr → Live
  | [] => .empty
  | e :: es => e.mentions.union (exprsMentions es)

/-- The variables the fields of a record literal mention. -/
def fieldsMentions : List (Name × Expr) → Live
  | [] => .empty
  | (_, e) :: fields => e.mentions.union (fieldsMentions fields)

/-- The variables a call's arguments mention, the roots of its `inout`
places included. -/
def argsMentions : List Arg → Live
  | [] => .empty
  | .value e :: args => e.mentions.union (argsMentions args)
  | .inout ⟨x, path⟩ :: args => (Live.one x).union ((pathMentions path).union (argsMentions args))

/-- The variables the indexes of a place mention. -/
def pathMentions : List Projection → Live
  | [] => .empty
  | .field _ :: path => pathMentions path
  | .index i :: path => i.mentions.union (pathMentions path)

/-- The variables the arms of a `match` mention, their binders included. -/
def armsMentions : List Arm → Live
  | [] => .empty
  | ⟨_, binders, body⟩ :: arms =>
    (Live.ofList binders).union (body.mentions.union (armsMentions arms))

end

mutual

/-- Whether every mark in `e` is a last use (facts.last-use), when `after` holds
the variables that what follows `e` in its body mentions. Each part of `e` is checked with
what follows it: the parts after it in `e`, in the order values.left-to-right gives,
then `after`. A jump goes to the end of its loop or its body, whose variables
`after` already holds, so the parts a jump skips only make the check stricter. The arguments of a call are followed by the roots of its `inout`
arguments, which the call uses when it starts (modes.durations), a loop's body
by its next iteration, and a `catch` operand by the arm. A closure literal is
followed by what follows it, and its body is a body of its own. The check
goes by names and by evaluation order, as the module's doc says, so it is
stricter than facts.last-use where a binder reuses a name, and less strict
across the branches of an `if` or a `match`. -/
def Expr.movesOk (after : Live) : Expr → Bool
  | .var _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _ | .method _ _ _ => true
  | .move x => !after.mem x
  | .record _ fields => fieldsMovesOk after fields
  | .variant _ _ es => exprsMovesOk after es
  | .list _ es => exprsMovesOk after es
  | .op _ es | .view es => exprsMovesOk after es
  | .field e _ => e.movesOk after
  | .index e i => e.movesOk (after.union i.mentions) && i.movesOk after
  | .closure ps _ _ body => body.movesOk (inoutLive ps)
  | .call f args _ =>
    f.movesOk (after.union (argsMentions args)) &&
      argsMovesOk (after.union (Live.ofList (inoutRoots args))) args
  | .letIn x _ init body =>
    init.movesOk (after.union (body.mentions.erase x)) && body.movesOk after
  | .varIn x _ init body =>
    init.movesOk (after.union (body.mentions.erase x)) && body.movesOk after
  | .assign ⟨x, path⟩ v =>
    pathMovesOk ((Live.one x).union (after.union v.mentions)) path &&
      v.movesOk ((Live.one x).union after)
  | .seq a b => a.movesOk (after.union b.mentions) && b.movesOk after
  | .if c _ a b =>
    c.movesOk (after.union (a.mentions.union b.mentions)) && a.movesOk after && b.movesOk after
  | .match e _ arms => e.movesOk (after.union (armsMentions arms)) && armsMovesOk after arms
  | .for _ _ e body =>
    e.movesOk (after.union body.mentions) && body.movesOk (after.union body.mentions)
  | .raise e => e.movesOk after
  | .try e => e.movesOk after
  | .tryCatch e _ _ h _ => e.movesOk (after.union h.mentions) && h.movesOk after
  | .while c body =>
    let again := after.union (c.mentions.union body.mentions)
    c.movesOk again && body.movesOk again
  | .loop body => body.movesOk (after.union body.mentions)
  | .return e => e.movesOk after
  | .perform _ e => e.movesOk after
  | .withH _ _ h b => h.movesOk (after.union b.mentions) && b.movesOk after
  | .held ns hs body =>
    exprsMovesOk (after.union (body.mentions.eraseAll (ns.map (·.1)))) hs &&
      body.movesOk (after.union (Live.ofList (ns.map (·.1))))

/-- Whether the marks of a list of expressions, evaluated in order, are last
uses. -/
def exprsMovesOk (after : Live) : List Expr → Bool
  | [] => true
  | e :: es => e.movesOk (after.union (exprsMentions es)) && exprsMovesOk after es

/-- Whether the marks of the fields of a record literal are last uses. -/
def fieldsMovesOk (after : Live) : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields =>
    e.movesOk (after.union (fieldsMentions fields)) && fieldsMovesOk after fields

/-- Whether the marks of a call's arguments are last uses. -/
def argsMovesOk (after : Live) : List Arg → Bool
  | [] => true
  | .value e :: args => e.movesOk (after.union (argsMentions args)) && argsMovesOk after args
  | .inout ⟨_, path⟩ :: args =>
    pathMovesOk (after.union (argsMentions args)) path && argsMovesOk after args

/-- Whether the marks of the indexes of a place are last uses. -/
def pathMovesOk (after : Live) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathMovesOk after path
  | .index i :: path => i.movesOk (after.union (pathMentions path)) && pathMovesOk after path

/-- Whether the marks of the arms of a `match` are last uses. -/
def armsMovesOk (after : Live) : List Arm → Bool
  | [] => true
  | ⟨_, _, body⟩ :: arms => body.movesOk after && armsMovesOk after arms

end

/-! ## The variables a closure captures -/

/-- Solves a case of `Expr.mentions_of_free` from the cases of its parts. -/
macro "mentions_case" : tactic => `(tactic| (
  simp only [Expr.free, Expr.mentions, exprsFree, fieldsFree, argsFree, pathFree, armsFree,
    exprsMentions, fieldsMentions, argsMentions, pathMentions, armsMentions, Live.mem_union,
    Live.mem_one, Live.mem_ofList, Live.mem_empty, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq, Bool.not_eq_true', List.contains_iff_mem] at *
  grind))

mutual

/-- A variable an expression uses is one it mentions. -/
theorem Expr.mentions_of_free (x : Name) : ∀ e : Expr, e.free x = true → e.mentions.mem x = true
  | .var _, h | .move _, h => by mentions_case
  | .int _, h | .bool _, h | .unit, h | .break, h | .continue, h | .fnRef .., h | .method .., h =>
    by simp [Expr.free] at h
  | .closure ps _ _ body, h => by
    simp only [Expr.free, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at h
    exact Live.mem_eraseAll (Expr.mentions_of_free x body h.2) fun hx => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact h.1 p hp rfl
  | .record _ fs, h => by have := fieldsMentions_of_free x fs; mentions_case
  | .variant _ _ es, h | .list _ es, h | .op _ es, h | .view es, h => by
    have := exprsMentions_of_free x es; mentions_case
  | .field e _, h | .raise e, h | .perform _ e, h | .try e, h | .loop e, h | .return e, h => by
    have := Expr.mentions_of_free x e; mentions_case
  | .index a b, h | .seq a b, h | .withH _ _ a b, h | .letIn _ _ a b, h | .varIn _ _ a b, h
  | .for _ _ a b, h | .while a b, h | .tryCatch a _ _ b _, h => by
    have := Expr.mentions_of_free x a; have := Expr.mentions_of_free x b; mentions_case
  | .call f args _, h => by
    have := Expr.mentions_of_free x f; have := argsMentions_of_free x args; mentions_case
  | .assign ⟨_, p⟩ v, h => by
    have := pathMentions_of_free x p; have := Expr.mentions_of_free x v; mentions_case
  | .if c _ a b, h => by
    have := Expr.mentions_of_free x c; have := Expr.mentions_of_free x a
    have := Expr.mentions_of_free x b; mentions_case
  | .match e _ arms, h => by
    have := Expr.mentions_of_free x e; have := armsMentions_of_free x arms; mentions_case
  | .held ns hs b, h => by
    have := exprsMentions_of_free x hs; have := Expr.mentions_of_free x b; mentions_case

theorem exprsMentions_of_free (x : Name) :
    ∀ es : List Expr, exprsFree x es = true → (exprsMentions es).mem x = true
  | [], h => by simp [exprsFree] at h
  | e :: es, h => by
    have := Expr.mentions_of_free x e; have := exprsMentions_of_free x es; mentions_case

theorem fieldsMentions_of_free (x : Name) :
    ∀ fs : List (Name × Expr), fieldsFree x fs = true → (fieldsMentions fs).mem x = true
  | [], h => by simp [fieldsFree] at h
  | (_, e) :: fs, h => by
    have := Expr.mentions_of_free x e; have := fieldsMentions_of_free x fs; mentions_case

theorem argsMentions_of_free (x : Name) :
    ∀ args : List Arg, argsFree x args = true → (argsMentions args).mem x = true
  | [], h => by simp [argsFree] at h
  | .value e :: args, h => by
    have := Expr.mentions_of_free x e; have := argsMentions_of_free x args; mentions_case
  | .inout ⟨_, p⟩ :: args, h => by
    have := pathMentions_of_free x p; have := argsMentions_of_free x args; mentions_case

theorem pathMentions_of_free (x : Name) :
    ∀ p : List Projection, pathFree x p = true → (pathMentions p).mem x = true
  | [], h => by simp [pathFree] at h
  | .field _ :: p, h => by have := pathMentions_of_free x p; mentions_case
  | .index i :: p, h => by
    have := Expr.mentions_of_free x i; have := pathMentions_of_free x p; mentions_case

theorem armsMentions_of_free (x : Name) :
    ∀ arms : List Arm, armsFree x arms = true → (armsMentions arms).mem x = true
  | [], h => by simp [armsFree] at h
  | ⟨_, _, b⟩ :: arms, h => by
    have := Expr.mentions_of_free x b; have := armsMentions_of_free x arms; mentions_case

end

/-- A closure literal mentions every variable it captures (expressions.capture). -/
theorem Expr.mentions_of_captures {ps : List Param} {result : Ty} {ρ : Row} {body : Expr}
    {x : Name} (h : Expr.captures ps body x = true) :
    (Expr.closure ps result ρ body).mentions.mem x = true := by
  rw [← Expr.free_closure x ps result ρ body] at h
  exact Expr.mentions_of_free x _ h

/-- Every mark of the program is a last use: in each function's body, which
hands its `inout` parameters back, and in `main`. -/
def Program.MovesJustified (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns, d.body.movesOk (inoutLive d.params) = true) ∧
    p.main.movesOk .empty = true

end Stilt
