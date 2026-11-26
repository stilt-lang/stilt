import Stilt.Exclusivity
import Stilt.WellTyped

/-!
# Receivers

A method call `recv.m(args)` is the call `T.m(recv, args)` of the method as a
function, whose first parameter is the receiver (traits.method-resolution and traits.qualified-calls). The
receiver is the call's first argument: it is evaluated before the others
(modes.durations), and it is passed in the mode of `self`. So the receiver of a
method that takes `inout self` is a modification that lasts for the whole call,
as an `inout` argument is, and a receiver taken by `self` is a read that ends
before the call starts, as a `let` argument is (modes.kinds-of-access and modes.durations).

This module states what that gives, as modes.overlapping-inout reads it: the shapes
that a call rule judges start with the receiver's, the law forbids an `inout`
argument that overlaps an `inout self` receiver, and the receiver of an `inout
self` method is a place that can be modified, of the block's type. Every
theorem about programs covers method calls, since they are calls.
-/

namespace Stilt

/-! ## The receiver in the law of exclusivity -/

/-- The receiver of an `inout self` method is the first place that its call
modifies. -/
theorem inoutShapes_inoutReceiver (p : Place) (args : List Arg) :
    inoutShapes (.inout p :: args) = p.shape :: inoutShapes args := rfl

/-- A receiver taken by `self` modifies nothing. -/
theorem inoutShapes_valueReceiver (e : Expr) (args : List Arg) :
    inoutShapes (.value e :: args) = inoutShapes args := rfl

/-- No two shapes of a list that starts with `s` overlap exactly when `s`
overlaps none of the rest, and no two of the rest overlap. -/
theorem pairwiseDisjoint_cons_iff (s : Shape) (ss : List Shape) :
    pairwiseDisjoint (s :: ss) = true ↔
      (∀ t ∈ ss, s.overlaps t = false) ∧ pairwiseDisjoint ss = true := by
  simp [pairwiseDisjoint]

/-- **The law at a method call with `inout self`** (modes.overlapping-inout). The call
obeys the law exactly when its receiver's indexes and its arguments do, the
receiver overlaps no `inout` argument and no two `inout` arguments overlap
(E0402), and neither the receiver nor an `inout` argument modifies a place
that a loop around the call reads (E0404). -/
theorem Expr.exclusive_inoutReceiver (T m : Name) (rows : List Row) (p : Place)
    (args : List Arg) (result : Ty) (reading : List Shape) :
    (Expr.methodCall T m rows (.inout p) args result).exclusive reading = true ↔
      (pathExclusive reading p.path = true ∧ argsExclusive reading args = true) ∧
        (unread reading p.shape = true ∧ (inoutShapes args).all (unread reading) = true) ∧
        (∀ s ∈ inoutShapes args, p.shape.overlaps s = false) ∧
        pairwiseDisjoint (inoutShapes args) = true := by
  obtain ⟨x, path⟩ := p
  simp only [Expr.methodCall, Expr.exclusive, argsExclusive, inoutShapes_inoutReceiver,
    List.all_cons, pairwiseDisjoint_cons_iff, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨-, h₁, h₂⟩, h₃, h₄⟩, h₅, h₆⟩
    exact ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩, h₅, h₆⟩
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩, h₅, h₆⟩
    exact ⟨⟨⟨trivial, h₁, h₂⟩, h₃, h₄⟩, h₅, h₆⟩

/-- **The law at a method call with `self`** (modes.durations and modes.overlapping-inout). The
receiver is a read that ends once it is evaluated, before the call starts, so
it takes no part in modes.overlapping-inout: the call obeys the law exactly when its receiver
and its arguments do, no two `inout` arguments overlap, and none modifies a
place that a loop around the call reads. -/
theorem Expr.exclusive_valueReceiver (T m : Name) (rows : List Row) (e : Expr)
    (args : List Arg) (result : Ty) (reading : List Shape) :
    (Expr.methodCall T m rows (.value e) args result).exclusive reading = true ↔
      (e.exclusive reading = true ∧ argsExclusive reading args = true) ∧
        (inoutShapes args).all (unread reading) = true ∧
        pairwiseDisjoint (inoutShapes args) = true := by
  simp only [Expr.methodCall, Expr.exclusive, argsExclusive, inoutShapes_valueReceiver,
    Bool.and_eq_true]
  constructor
  · rintro ⟨⟨⟨-, h₁, h₂⟩, h₃⟩, h₄⟩
    exact ⟨⟨h₁, h₂⟩, h₃, h₄⟩
  · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
    exact ⟨⟨⟨trivial, h₁, h₂⟩, h₃⟩, h₄⟩

/-! ## The receiver in typing -/

/-- `Self` is a record or variant type, which has no rows to instantiate. -/
theorem Decls.selfType?_substRows {D : Decls} {T : Name} {τ : Ty} (h : D.selfType? T = some τ)
    (s : RowSubst) : τ.substRows s = τ := by
  unfold Decls.selfType? at h
  split at h
  · cases h
    rfl
  · split at h
    · cases h
      rfl
    · cases h

section Typing

variable {D : Decls} {scope : RowScope} {Γ : Ctx} {fx : Effects} {T m : Name}
  {rows : List Row} {recv : Arg} {args : List Arg} {σ τ : Ty} {d : FnDecl} {mode : Mode}
  {x : Name} {τs : Ty} {imp : Option Name} {ps : List Param}

/-- What typing knows of a method call: the receiver fits the type of `self`
as the call instantiates it, in its mode. -/
theorem HasType.methodCall_inv
    (h : HasType D scope Γ fx (Expr.methodCall T m rows recv args σ) τ)
    (hd : D.fn? (qualify T m) = some d) (hps : d.params = ⟨mode, x, τs, imp⟩ :: ps) :
    ∃ rest, ArgsFit D scope Γ fx (recv :: args)
      ((mode, τs.substRows (d.rowParams.zip rows)) :: rest) := by
  unfold Expr.methodCall at h
  cases h with
  | call hcallee hargs _ =>
    rename_i params _ _
    generalize hty : Ty.fn params _ _ = ty at hcallee
    cases hcallee with
    | fnRef hd' =>
      rw [hd] at hd'
      cases hd'
      simp only [FnDecl.typeArgs, List.zip_nil_right, Ty.substTys_nil, FnDecl.type, Ty.substRows,
        hps, List.map_cons, Param.sig, substParamRows, Ty.fn.injEq] at hty
      rw [hty.1] at hargs
      exact ⟨_, hargs⟩

/-- **The receiver of an `inout self` method is a place that can be
modified**, of the block's type exactly (expressions.inout-arguments; modes.kinds-of-access and modes.what-can-be-modified): rooted in a `var` binding or an `inout` parameter, and passed
`inout`. -/
theorem HasType.inoutReceiver
    (h : HasType D scope Γ fx (Expr.methodCall T m rows recv args σ) τ)
    (hd : D.fn? (qualify T m) = some d) (hps : d.params = ⟨.inout, x, τs, imp⟩ :: ps)
    (hself : D.selfType? T = some τs) :
    ∃ p, recv = .inout p ∧ PlaceFits D scope Γ fx p τs := by
  obtain ⟨rest, hargs⟩ := h.methodCall_inv hd hps
  rw [Decls.selfType?_substRows hself] at hargs
  cases hargs with
  | value hm => exact absurd rfl hm
  | inout hp => exact ⟨_, rfl, hp⟩

/-- **The receiver of a `self` method is a value** of the block's type, an
independent copy, as a `let` argument is (values.passing-values; modes.durations). -/
theorem HasType.valueReceiver
    (h : HasType D scope Γ fx (Expr.methodCall T m rows recv args σ) τ)
    (hd : D.fn? (qualify T m) = some d) (hps : d.params = ⟨.let, x, τs, imp⟩ :: ps)
    (hself : D.selfType? T = some τs) :
    ∃ e σ, recv = .value e ∧ HasType D scope Γ fx e σ ∧ Fits σ τs := by
  obtain ⟨rest, hargs⟩ := h.methodCall_inv hd hps
  rw [Decls.selfType?_substRows hself] at hargs
  cases hargs with
  | value _ he hfit => exact ⟨_, _, rfl, he, hfit⟩

end Typing

/-! ## The required tests of modes.law -/

section RequiredTests

private def place (x : Name) (path : List Projection := []) : Place := ⟨x, path⟩

/-- `recv.m(args)`, for a method of `T` with no row variables. -/
private def send (T m : Name) (recv : Arg) (args : List Arg) (result : Ty := .unit) : Expr :=
  Expr.methodCall T m [] recv args result

/-- `a.f(inout a.b)`, where `f` takes `inout self`, is rejected (E0402). -/
example : (send "A" "f" (.inout (place "a")) [.inout (place "a" [.field "b"])]).exclusive [] =
    false := by
  decide

/-- `a.b.f(inout a)`, the other way round, is rejected too. -/
example : (send "B" "f" (.inout (place "a" [.field "b"])) [.inout (place "a")]).exclusive [] =
    false := by
  decide

/-- `a.b.f(inout a.c)` is accepted: the places don't overlap. -/
example :
    (send "B" "f" (.inout (place "a" [.field "b"])) [.inout (place "a" [.field "c"])]).exclusive
      [] = true := by
  decide

/-- `a.g(inout a.b)`, where `g` takes `self`, is accepted: the receiver is read
before the call starts (modes.durations). -/
example : (send "A" "g" (.value (.var "a")) [.inout (place "a" [.field "b"])]).exclusive [] =
    true := by
  decide

/-- `xs.push(xs.len())` is accepted: the argument is read before the call
starts. -/
example :
    (send "List" "push" (.inout (place "xs"))
      [.value (send "List" "len" (.value (.var "xs")) [])]).exclusive [] = true := by
  decide

/-- `xs.push(xs[0])` is accepted. -/
example :
    (send "List" "push" (.inout (place "xs")) [.value (.index (.var "xs") (.int 0))]).exclusive
      [] = true := by
  decide

/-- `for item in cart.items { cart.remove(item) }`, where `remove` takes
`inout self`, is rejected (E0404): the receiver contains the iterated
place. -/
example :
    (Expr.for "item" .i64 (.field (.var "cart") "items")
      (send "Cart" "remove" (.inout (place "cart")) [.value (.var "item")])).exclusive [] =
      false := by
  decide

/-- `for x in xs.enumerate(0) { xs.push(x) }` is accepted: the loop iterates a
value that isn't a place. -/
example :
    (Expr.for "x" .i64 (send "List" "enumerate" (.value (.var "xs")) [.value (.int 0)])
      (send "List" "push" (.inout (place "xs")) [.value (.var "x")])).exclusive [] = true := by
  decide

/-- `type Counter = { n: i64 }`. -/
private def counterDecls : Decls := ⟨[⟨"Counter", [("n", .i64)]⟩], [], [], [], [], [], []⟩

/-- The body of a method of `Counter` whose receiver takes `mode`. -/
private def receiverCtx (mode : Mode) : Ctx :=
  Ctx.params [] [⟨mode, selfName, .record "Counter", none⟩]

private theorem counter_wellFormed (scope : RowScope) : (Ty.record "Counter").WellFormed scope :=
  let h := (Head.record "Counter").ground_type
  Ty.Closed.wellFormed h.1 h.2.1 h.2.2 (Head.viewsViewable_type _) scope

/-- Modifying a receiver taken by `self` is rejected: `self.n = 0` doesn't
type (modes.what-can-be-modified). -/
example (scope : RowScope) (fx : Effects) (τ : Ty) :
    ¬HasType counterDecls scope (receiverCtx .let) fx
      (.assign ⟨selfName, [.field "n"]⟩ (.int 0)) τ := by
  intro h
  cases h with
  | assign hp _ _ =>
    cases hp with
    | mk hl _ => simp [receiverCtx, Ctx.params, Ctx.lookup, Ctx.bind] at hl

/-- Rebinding it is accepted: `var c = self; c.n = 0` (modes.what-can-be-modified). -/
example (scope : RowScope) (fx : Effects) :
    HasType counterDecls scope (receiverCtx .let) fx
      (.varIn "c" (.record "Counter") (.var selfName) (.assign ⟨"c", [.field "n"]⟩ (.int 0)))
      .unit :=
  .varIn (counter_wellFormed scope) (.var rfl) (.refl _)
    (.assign (.mk rfl (.field rfl rfl .nil)) (.int (by decide)) (.refl _))

/-- An `inout self` receiver can be modified: `self.n = 0` types (modes.what-can-be-modified). -/
example (scope : RowScope) (fx : Effects) :
    HasType counterDecls scope (receiverCtx .inout) fx
      (.assign ⟨selfName, [.field "n"]⟩ (.int 0)) .unit :=
  .assign (.mk rfl (.field rfl rfl .nil)) (.int (by decide)) (.refl _)

end RequiredTests

end Stilt
