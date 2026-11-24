import Stilt.Declarations

/-!
# Last uses

The analysis that marks the last use of a variable, and the check that a
program's marks are last uses.

A body's variables are mentioned where they are read, written, passed or
bound. A read of `x` is a last use when nothing evaluated after it, up to the
end of the body, mentions `x`. Leaving a body uses its `inout` parameters,
which go back to the caller (values.passing-values), so an `inout` parameter has no
last use. A closure literal captures the variables it uses (expressions.capture);
the analysis counts it as mentioning every variable in scope, conservatively. A binder `let x` or `var x` ends the scope of the
earlier `x` for the rest of its body, so `var x = x` is the last use of the
earlier `x` when nothing after the binding mentions it.

`Expr.markMoves` marks each argument and each initializer that is a variable
at its last use; `Expr.movesOk` checks that every mark of a body is one. Only
a mark at those two positions changes what a model of memory may do, and the
check accepts any subset of the marks the analysis makes.
-/

namespace Stilt

/-- A set of variables: every variable, or those of a list. -/
structure Live where
  all : Bool
  names : List Name

namespace Live

/-- Whether the set holds `x`. -/
def mem (L : Live) (x : Name) : Bool := L.all || L.names.contains x

/-- No variable. -/
def empty : Live := ⟨false, []⟩

/-- Every variable. -/
def every : Live := ⟨true, []⟩

/-- One variable. -/
def one (x : Name) : Live := ⟨false, [x]⟩

/-- The variables of a list. -/
def ofList (xs : List Name) : Live := ⟨false, xs⟩

/-- The variables of either set. -/
def union (a b : Live) : Live := ⟨a.all || b.all, a.names ++ b.names⟩

/-- The variables of `L` but `x`, unless `L` holds every variable. -/
def erase (L : Live) (x : Name) : Live := ⟨L.all, L.names.filter (· != x)⟩

/-- Leaves out the names. -/
def eraseAll (L : Live) (xs : List Name) : Live := xs.foldl erase L

/-- Every variable of `L` is in `L'`. -/
def Sub (L L' : Live) : Prop :=
  (L.all = true → L'.all = true) ∧ ∀ x, L.mem x = true → L'.mem x = true

@[simp] theorem mem_union (a b : Live) (x : Name) : (a.union b).mem x = (a.mem x || b.mem x) := by
  simp only [mem, union, List.contains_append]
  cases a.all <;> cases b.all <;> simp

@[simp] theorem mem_one (x y : Name) : (one x).mem y = true ↔ y = x := by
  simp [mem, one]

@[simp] theorem mem_empty (x : Name) : empty.mem x = false := rfl

@[simp] theorem mem_every (x : Name) : every.mem x = true := rfl

@[simp] theorem union_all (a b : Live) : (a.union b).all = (a.all || b.all) := rfl

theorem mem_of_all {L : Live} (h : L.all = true) (x : Name) : L.mem x = true := by
  simp [mem, h]

theorem mem_erase {L : Live} {x y : Name} (h : (L.erase y).mem x = true) : L.mem x = true := by
  simp only [mem, erase, Bool.or_eq_true, List.contains_iff_mem, List.mem_filter] at h ⊢
  exact h.imp id And.left

theorem mem_erase_of_ne {L : Live} {x y : Name} (h : L.mem x = true) (hne : x ≠ y) :
    (L.erase y).mem x = true := by
  simp only [mem, erase, Bool.or_eq_true, List.contains_iff_mem, List.mem_filter, bne_iff_ne,
    ne_eq] at h ⊢
  rcases h with h | h
  · exact .inl h
  · exact .inr ⟨h, hne⟩

theorem Sub.refl (L : Live) : L.Sub L := ⟨id, fun _ => id⟩

theorem Sub.trans {a b c : Live} (h₁ : a.Sub b) (h₂ : b.Sub c) : a.Sub c :=
  ⟨fun h => h₂.1 (h₁.1 h), fun x h => h₂.2 x (h₁.2 x h)⟩

theorem sub_union_left (a b : Live) : a.Sub (a.union b) :=
  ⟨fun h => by simp [h], fun x h => by simp [h]⟩

theorem sub_union_right (a b : Live) : b.Sub (a.union b) :=
  ⟨fun h => by simp [h], fun x h => by simp [h]⟩

theorem Sub.union {a b c : Live} (h₁ : a.Sub c) (h₂ : b.Sub c) : (a.union b).Sub c := by
  refine ⟨fun h => ?_, fun x h => ?_⟩
  · simp only [union_all, Bool.or_eq_true] at h
    exact h.elim h₁.1 h₂.1
  · simp only [mem_union, Bool.or_eq_true] at h
    exact h.elim (h₁.2 x) (h₂.2 x)

@[simp] theorem erase_all (L : Live) (y : Name) : (L.erase y).all = L.all := rfl

theorem erase_sub (L : Live) (y : Name) : (L.erase y).Sub L :=
  ⟨id, fun _ h => mem_erase h⟩

theorem empty_sub (L : Live) : empty.Sub L :=
  ⟨fun h => absurd h (by simp [empty]), fun _ h => absurd h (by simp)⟩

@[simp] theorem mem_ofList (xs : List Name) (x : Name) : (ofList xs).mem x = true ↔ x ∈ xs := by
  simp [mem, ofList]

@[simp] theorem ofList_all (xs : List Name) : (ofList xs).all = false := rfl

@[simp] theorem one_all (x : Name) : (one x).all = false := rfl

@[simp] theorem empty_all : empty.all = false := rfl

@[simp] theorem every_all : every.all = true := rfl

end Live

/-- Proves that one union of sets of variables is within another. -/
macro "live_sub" : tactic => `(tactic| exact ⟨fun h => by
    simp only [Live.union_all, Live.ofList_all, Live.one_all, Live.empty_all, Live.every_all,
      Bool.or_eq_true] at h ⊢; grind,
  fun _ h => by
    simp only [Live.mem_union, Live.mem_ofList, Live.mem_one, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, Bool.or_eq_true] at h ⊢; grind⟩)

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
binds, and every variable if it holds a closure literal. -/
def Expr.mentions : Expr → Live
  | .var x | .move x => .one x
  | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _ | .method _ _ _ => .empty
  | .record _ fields => fieldsMentions fields
  | .variant _ _ es => exprsMentions es
  | .list _ es => exprsMentions es
  | .op _ es | .view es => exprsMentions es
  | .field e _ => e.mentions
  | .index e i => e.mentions.union i.mentions
  | .closure _ _ _ _ => .every
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

/-- Whether every mark in `e` is a last use, when `after` holds the variables
that what follows `e` in its body mentions. Each part of `e` is checked with
what follows it: the parts after it in `e`, in the order values.left-to-right gives,
then `after`. A jump goes to the end of its loop or its body, whose variables
`after` already holds, so the parts a jump skips only make the check stricter. The arguments of a call are followed by the roots of its `inout`
arguments, which the call uses when it starts (modes.durations), a loop's body
by its next iteration, and a `catch` operand by the arm. A closure's body is a
body of its own. -/
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

/-- Every mark of the program is a last use: in each function's body, which
hands its `inout` parameters back, and in `main`. -/
def Program.MovesJustified (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns, d.body.movesOk (inoutLive d.params) = true) ∧
    p.main.movesOk .empty = true

end Stilt
