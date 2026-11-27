import Stilt.Theorems
import Stilt.InPlace.Agreement

/-!
# Call rules

The law of exclusivity with its call rule as a parameter. The call rule of modes.overlapping-inout
judges a call by the shapes of its `inout` arguments: it rejects the call when
two of them overlap (E0402). A `CallRule` is any judgment of that kind, and
`Expr.exclusiveWith` is the pass of `Stilt.Exclusivity` with that judgment in
place of the Reference's's. The check that a loop's place isn't modified (E0404) stays
as it is.

A rule is sound when every well-typed program that obeys it gives the same
observation under copy-in, copy-out and in place (values.inout-arguments; modes.law).
The call rule is sound, by `inPlaceAgreement`.
`Stilt.Optimality.Theorem` proves that it is the greatest sound rule. A rule
may also be asked to be sound under another order of write-back
(`CallRule.SoundWith`), and `Stilt.Optimality.Theorem` proves that modes.overlapping-inout
bounds those rules too.
-/

namespace Stilt

/-- A rule that judges a call by the shapes of its `inout` arguments, in
order, a method call's `inout self` receiver first, as modes.overlapping-inout does
(E0402). It sees each place with its indexes removed (modes.overlap), and nothing
else of the call. -/
abbrev CallRule := List Shape → Bool

mutual

/-- The pass of `Expr.exclusive` (modes.law, modes.overlapping-inout and modes.closures), with `rule` judging
the `inout` arguments of each call in place of the overlapping-inout paragraph's ban on overlapping
ones. A modification of a place that a loop around it reads is still rejected
(modes.change-while-iterating, E0404). -/
def Expr.exclusiveWith (rule : CallRule) (reading : List Shape) : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => true
  | .record _ _ fields => fieldsExclusiveWith rule reading fields
  | .variant _ _ _ es => exprsExclusiveWith rule reading es
  | .list _ es => exprsExclusiveWith rule reading es
  | .op _ es | .view es => exprsExclusiveWith rule reading es
  | .field e _ => e.exclusiveWith rule reading
  | .index e i => e.exclusiveWith rule reading && i.exclusiveWith rule reading
  | .closure _ _ _ body => body.exclusiveWith rule []
  | .call callee args _ =>
    callee.exclusiveWith rule reading && argsExclusiveWith rule reading args &&
      (inoutShapes args).all (unread reading) && rule (inoutShapes args)
  | .letIn x _ init body =>
    init.exclusiveWith rule reading && body.exclusiveWith rule (hide reading x)
  | .varIn x _ init body =>
    init.exclusiveWith rule reading && body.exclusiveWith rule (hide reading x)
  | .assign ⟨root, path⟩ value =>
    pathExclusiveWith rule reading path && value.exclusiveWith rule reading &&
      unread reading (Place.mk root path).shape
  | .seq a b => a.exclusiveWith rule reading && b.exclusiveWith rule reading
  | .if c _ a b =>
    c.exclusiveWith rule reading && a.exclusiveWith rule reading &&
      b.exclusiveWith rule reading
  | .match e _ arms => e.exclusiveWith rule reading && armsExclusiveWith rule reading arms
  | .for x _ e body =>
    e.exclusiveWith rule reading && body.exclusiveWith rule (hide (iterated e ++ reading) x)
  | .raise e => e.exclusiveWith rule reading
  | .try e | .form _ e => e.exclusiveWith rule reading
  | .tryCatch e _ x handler _ =>
    e.exclusiveWith rule reading && handler.exclusiveWith rule (hide reading x)
  | .while c body => c.exclusiveWith rule reading && body.exclusiveWith rule reading
  | .loop body => body.exclusiveWith rule reading
  | .return e => e.exclusiveWith rule reading
  | .perform _ e => e.exclusiveWith rule reading
  | .withH _ _ h b => h.exclusiveWith rule reading && b.exclusiveWith rule reading
  | .held ns hs body =>
    exprsExclusiveWith rule reading hs && body.exclusiveWith rule ((ns.map Prod.fst).foldl hide reading)

/-- Whether every expression of a list obeys the law under `rule`. -/
def exprsExclusiveWith (rule : CallRule) (reading : List Shape) : List Expr → Bool
  | [] => true
  | e :: es => e.exclusiveWith rule reading && exprsExclusiveWith rule reading es

/-- Whether every field of a record literal obeys the law under `rule`. -/
def fieldsExclusiveWith (rule : CallRule) (reading : List Shape) :
    List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.exclusiveWith rule reading && fieldsExclusiveWith rule reading fields

/-- Whether the arguments of a call obey the law under `rule` while they are
evaluated. -/
def argsExclusiveWith (rule : CallRule) (reading : List Shape) : List Arg → Bool
  | [] => true
  | .value e :: args => e.exclusiveWith rule reading && argsExclusiveWith rule reading args
  | .inout ⟨_, path⟩ :: args =>
    pathExclusiveWith rule reading path && argsExclusiveWith rule reading args

/-- Whether the indexes of a place obey the law under `rule`. -/
def pathExclusiveWith (rule : CallRule) (reading : List Shape) : List Projection → Bool
  | [] => true
  | .field _ :: path => pathExclusiveWith rule reading path
  | .index i :: path => i.exclusiveWith rule reading && pathExclusiveWith rule reading path

/-- Whether the arms of a `match` obey the law under `rule`. -/
def armsExclusiveWith (rule : CallRule) (reading : List Shape) : List Arm → Bool
  | [] => true
  | ⟨_, binders, guard, body⟩ :: arms =>
    guardExclusiveWith rule (binders.foldl hide reading) guard &&
      body.exclusiveWith rule (binders.foldl hide reading) && armsExclusiveWith rule reading arms

/-- Whether an arm's guard obeys the law under `rule`. -/
def guardExclusiveWith (rule : CallRule) (reading : List Shape) : Option Expr → Bool
  | none => true
  | some g => g.exclusiveWith rule reading

end

/-- Every body of the program obeys the law of exclusivity with `rule` as its
call rule: each function's body, and `main`. -/
def Program.ExclusiveWith (rule : CallRule) (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns, d.body.exclusiveWith rule [] = true) ∧
    p.main.exclusiveWith rule [] = true

/-! ## modes.overlapping-inout as a call rule -/

mutual

/-- The pass of `Stilt.Exclusivity` is the parametrized pass with the overlapping-inout paragraph's
call rule, `pairwiseDisjoint` (modes.overlapping-inout). -/
theorem Expr.exclusive_eq_with :
    ∀ (e : Expr) (r : List Shape), e.exclusive r = e.exclusiveWith pairwiseDisjoint r
  | .var _, _ | .move _, _ | .int _, _ | .bool _, _ | .unit, _ | .fnRef .., _ | .method .., _
  | .break, _ | .continue, _ => rfl
  | .record _ _ fields, r => fieldsExclusive_eq_with fields r
  | .loop e, r | .return e, r | .perform _ e, r => Expr.exclusive_eq_with e r
  | .withH _ _ h b, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, Expr.exclusive_eq_with h r,
      Expr.exclusive_eq_with b r]
  | .held ns hs b, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, exprsExclusive_eq_with hs r,
      Expr.exclusive_eq_with b]
  | .while c body, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, Expr.exclusive_eq_with c r,
      Expr.exclusive_eq_with body r]
  | .variant _ _ _ es, r => exprsExclusive_eq_with es r
  | .list _ es, r => exprsExclusive_eq_with es r
  | .op _ es, r | .view es, r => exprsExclusive_eq_with es r
  | .field e _, r => Expr.exclusive_eq_with e r
  | .index e i, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, Expr.exclusive_eq_with e r,
      Expr.exclusive_eq_with i r]
  | .closure _ _ _ body, _ => Expr.exclusive_eq_with body []
  | .call f args _, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, Expr.exclusive_eq_with f r,
      argsExclusive_eq_with args r]
  | .letIn x _ init body, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, Expr.exclusive_eq_with init r,
      Expr.exclusive_eq_with body (hide r x)]
  | .varIn x _ init body, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, Expr.exclusive_eq_with init r,
      Expr.exclusive_eq_with body (hide r x)]
  | .assign ⟨_, path⟩ v, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, pathExclusive_eq_with path r,
      Expr.exclusive_eq_with v r]
  | .seq a b, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, Expr.exclusive_eq_with a r,
      Expr.exclusive_eq_with b r]
  | .if c _ a b, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, Expr.exclusive_eq_with c r,
      Expr.exclusive_eq_with a r, Expr.exclusive_eq_with b r]
  | .match e _ arms, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, Expr.exclusive_eq_with e r,
      armsExclusive_eq_with arms r]
  | .for x _ e body, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, Expr.exclusive_eq_with e r,
      Expr.exclusive_eq_with body (hide (iterated e ++ r) x)]
  | .raise e, r => Expr.exclusive_eq_with e r
  | .try e, r | .form _ e, r => Expr.exclusive_eq_with e r
  | .tryCatch e _ x h _, r => by
    simp [Expr.exclusive, Expr.exclusiveWith, Expr.exclusive_eq_with e r,
      Expr.exclusive_eq_with h (hide r x)]

theorem exprsExclusive_eq_with :
    ∀ (es : List Expr) (r : List Shape),
      exprsExclusive r es = exprsExclusiveWith pairwiseDisjoint r es
  | [], _ => rfl
  | e :: es, r => by
    simp [exprsExclusive, exprsExclusiveWith, Expr.exclusive_eq_with e r,
      exprsExclusive_eq_with es r]

theorem fieldsExclusive_eq_with :
    ∀ (fields : List (Name × Expr)) (r : List Shape),
      fieldsExclusive r fields = fieldsExclusiveWith pairwiseDisjoint r fields
  | [], _ => rfl
  | (_, e) :: fields, r => by
    simp [fieldsExclusive, fieldsExclusiveWith, Expr.exclusive_eq_with e r,
      fieldsExclusive_eq_with fields r]

theorem argsExclusive_eq_with :
    ∀ (args : List Arg) (r : List Shape),
      argsExclusive r args = argsExclusiveWith pairwiseDisjoint r args
  | [], _ => rfl
  | .value e :: args, r => by
    simp [argsExclusive, argsExclusiveWith, Expr.exclusive_eq_with e r,
      argsExclusive_eq_with args r]
  | .inout ⟨_, path⟩ :: args, r => by
    simp [argsExclusive, argsExclusiveWith, pathExclusive_eq_with path r,
      argsExclusive_eq_with args r]

theorem pathExclusive_eq_with :
    ∀ (path : List Projection) (r : List Shape),
      pathExclusive r path = pathExclusiveWith pairwiseDisjoint r path
  | [], _ => rfl
  | .field _ :: path, r => pathExclusive_eq_with path r
  | .index i :: path, r => by
    simp [pathExclusive, pathExclusiveWith, Expr.exclusive_eq_with i r,
      pathExclusive_eq_with path r]

theorem armsExclusive_eq_with :
    ∀ (arms : List Arm) (r : List Shape),
      armsExclusive r arms = armsExclusiveWith pairwiseDisjoint r arms
  | [], _ => rfl
  | ⟨_, binders, g, body⟩ :: arms, r => by
    simp [armsExclusive, armsExclusiveWith, guardExclusive_eq_with g (binders.foldl hide r),
      Expr.exclusive_eq_with body (binders.foldl hide r), armsExclusive_eq_with arms r]

theorem guardExclusive_eq_with :
    ∀ (g : Option Expr) (r : List Shape),
      guardExclusive r g = guardExclusiveWith pairwiseDisjoint r g
  | none, _ => rfl
  | some g, r => by simp [guardExclusive, guardExclusiveWith, Expr.exclusive_eq_with g r]

end

/-- The law of exclusivity is the parametrized law with the overlapping-inout paragraph's call rule
(modes.overlapping-inout). -/
theorem Expr.exclusive_eq_exclusiveWith : Expr.exclusive = Expr.exclusiveWith pairwiseDisjoint :=
  funext fun r => funext fun e => Expr.exclusive_eq_with e r

/-- A program obeys the law of exclusivity exactly when it obeys the
parametrized law with the overlapping-inout paragraph's call rule (modes.overlapping-inout). -/
theorem Program.exclusive_iff_exclusiveWith (p : Program) :
    p.Exclusive ↔ p.ExclusiveWith pairwiseDisjoint := by
  simp [Program.Exclusive, Program.ExclusiveWith, Expr.exclusive_eq_exclusiveWith]

/-! ## Rules that accept less -/

section Mono

variable {r₁ r₂ : CallRule}

mutual

/-- A program that obeys the law under a call rule obeys it under every rule
that accepts at least as much. -/
theorem Expr.exclusiveWith_mono (hle : ∀ ss, r₁ ss = true → r₂ ss = true) :
    ∀ (e : Expr) (r : List Shape), e.exclusiveWith r₁ r = true → e.exclusiveWith r₂ r = true
  | .var _, _, _ | .move _, _, _ | .int _, _, _ | .bool _, _, _ | .unit, _, _ | .fnRef .., _, _
  | .method .., _, _ | .break, _, _ | .continue, _, _ => rfl
  | .loop e, r, h | .return e, r, h => Expr.exclusiveWith_mono hle e r h
  | .while c body, r, h => by
    simp only [Expr.exclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.exclusiveWith_mono hle c r h.1, Expr.exclusiveWith_mono hle body r h.2⟩
  | .held _ hs b, r, h => by
    simp only [Expr.exclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨exprsExclusiveWith_mono hle hs r h.1, Expr.exclusiveWith_mono hle b _ h.2⟩
  | .record _ _ fields, r, h => fieldsExclusiveWith_mono hle fields r h
  | .variant _ _ _ es, r, h => exprsExclusiveWith_mono hle es r h
  | .list _ es, r, h => exprsExclusiveWith_mono hle es r h
  | .op _ es, r, h | .view es, r, h => exprsExclusiveWith_mono hle es r h
  | .field e _, r, h => Expr.exclusiveWith_mono hle e r h
  | .index e i, r, h => by
    simp only [Expr.exclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.exclusiveWith_mono hle e r h.1, Expr.exclusiveWith_mono hle i r h.2⟩
  | .closure _ _ _ body, _, h => Expr.exclusiveWith_mono hle body [] h
  | .call f args _, r, h => by
    simp only [Expr.exclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨Expr.exclusiveWith_mono hle f r h.1.1.1,
      argsExclusiveWith_mono hle args r h.1.1.2⟩, h.1.2⟩, hle _ h.2⟩
  | .letIn x _ init body, r, h | .varIn x _ init body, r, h => by
    simp only [Expr.exclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.exclusiveWith_mono hle init r h.1,
      Expr.exclusiveWith_mono hle body (hide r x) h.2⟩
  | .assign ⟨_, path⟩ v, r, h => by
    simp only [Expr.exclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨⟨pathExclusiveWith_mono hle path r h.1.1, Expr.exclusiveWith_mono hle v r h.1.2⟩,
      h.2⟩
  | .seq a b, r, h | .withH _ _ a b, r, h => by
    simp only [Expr.exclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.exclusiveWith_mono hle a r h.1, Expr.exclusiveWith_mono hle b r h.2⟩
  | .if c _ a b, r, h => by
    simp only [Expr.exclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨⟨Expr.exclusiveWith_mono hle c r h.1.1, Expr.exclusiveWith_mono hle a r h.1.2⟩,
      Expr.exclusiveWith_mono hle b r h.2⟩
  | .match e _ arms, r, h => by
    simp only [Expr.exclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.exclusiveWith_mono hle e r h.1, armsExclusiveWith_mono hle arms r h.2⟩
  | .for x _ e body, r, h => by
    simp only [Expr.exclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.exclusiveWith_mono hle e r h.1,
      Expr.exclusiveWith_mono hle body (hide (iterated e ++ r) x) h.2⟩
  | .raise e, r, h | .perform _ e, r, h | .try e, r, h | .form _ e, r, h => Expr.exclusiveWith_mono hle e r h
  | .tryCatch e _ x hd _, r, h => by
    simp only [Expr.exclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.exclusiveWith_mono hle e r h.1, Expr.exclusiveWith_mono hle hd (hide r x) h.2⟩

theorem exprsExclusiveWith_mono (hle : ∀ ss, r₁ ss = true → r₂ ss = true) :
    ∀ (es : List Expr) (r : List Shape),
      exprsExclusiveWith r₁ r es = true → exprsExclusiveWith r₂ r es = true
  | [], _, _ => rfl
  | e :: es, r, h => by
    simp only [exprsExclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.exclusiveWith_mono hle e r h.1, exprsExclusiveWith_mono hle es r h.2⟩

theorem fieldsExclusiveWith_mono (hle : ∀ ss, r₁ ss = true → r₂ ss = true) :
    ∀ (fields : List (Name × Expr)) (r : List Shape),
      fieldsExclusiveWith r₁ r fields = true → fieldsExclusiveWith r₂ r fields = true
  | [], _, _ => rfl
  | (_, e) :: fields, r, h => by
    simp only [fieldsExclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.exclusiveWith_mono hle e r h.1, fieldsExclusiveWith_mono hle fields r h.2⟩

theorem argsExclusiveWith_mono (hle : ∀ ss, r₁ ss = true → r₂ ss = true) :
    ∀ (args : List Arg) (r : List Shape),
      argsExclusiveWith r₁ r args = true → argsExclusiveWith r₂ r args = true
  | [], _, _ => rfl
  | .value e :: args, r, h => by
    simp only [argsExclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.exclusiveWith_mono hle e r h.1, argsExclusiveWith_mono hle args r h.2⟩
  | .inout ⟨_, path⟩ :: args, r, h => by
    simp only [argsExclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨pathExclusiveWith_mono hle path r h.1, argsExclusiveWith_mono hle args r h.2⟩

theorem pathExclusiveWith_mono (hle : ∀ ss, r₁ ss = true → r₂ ss = true) :
    ∀ (path : List Projection) (r : List Shape),
      pathExclusiveWith r₁ r path = true → pathExclusiveWith r₂ r path = true
  | [], _, _ => rfl
  | .field _ :: path, r, h => pathExclusiveWith_mono hle path r h
  | .index i :: path, r, h => by
    simp only [pathExclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.exclusiveWith_mono hle i r h.1, pathExclusiveWith_mono hle path r h.2⟩

theorem armsExclusiveWith_mono (hle : ∀ ss, r₁ ss = true → r₂ ss = true) :
    ∀ (arms : List Arm) (r : List Shape),
      armsExclusiveWith r₁ r arms = true → armsExclusiveWith r₂ r arms = true
  | [], _, _ => rfl
  | ⟨_, binders, g, body⟩ :: arms, r, h => by
    simp only [armsExclusiveWith, Bool.and_eq_true] at h ⊢
    exact ⟨⟨guardExclusiveWith_mono hle g (binders.foldl hide r) h.1.1,
      Expr.exclusiveWith_mono hle body (binders.foldl hide r) h.1.2⟩,
      armsExclusiveWith_mono hle arms r h.2⟩

theorem guardExclusiveWith_mono (hle : ∀ ss, r₁ ss = true → r₂ ss = true) :
    ∀ (g : Option Expr) (r : List Shape),
      guardExclusiveWith r₁ r g = true → guardExclusiveWith r₂ r g = true
  | none, _, _ => rfl
  | some g, r, h => Expr.exclusiveWith_mono hle g r h

end

theorem Program.ExclusiveWith.mono {p : Program} (h : p.ExclusiveWith r₁)
    (hle : ∀ ss, r₁ ss = true → r₂ ss = true) : p.ExclusiveWith r₂ :=
  ⟨fun d hd => Expr.exclusiveWith_mono hle _ [] (h.1 d hd),
    Expr.exclusiveWith_mono hle _ [] h.2⟩

end Mono

/-! ## Sound rules -/

/-- A call rule is sound when every well-typed program that obeys the law of
exclusivity with the rule, with E0404 as modes.change-while-iterating states it, gives the
same observation under copy-in, copy-out (the reference interpreter's model, values.inout-arguments)
and in-place mutation, with every fuel. This is what the Reference asks of its rules:
under them, copy-in, copy-out "can't be told apart from in-place mutation". -/
def CallRule.Sound (rule : CallRule) : Prop :=
  ∀ p : Program, p.WellTyped → p.ExclusiveWith rule →
    ∀ fuel, (p.runCopy fuel).observe = (p.runInPlace fuel).observe

/-- A call rule is sound under the write-back order `w` when every well-typed
program that obeys the law of exclusivity with the rule gives the same
observation under copy-in, copy-out, writing `inout` arguments back in the
order `w`, and in place, with every fuel. -/
def CallRule.SoundWith (w : WriteBack) (rule : CallRule) : Prop :=
  ∀ p : Program, p.WellTyped → p.ExclusiveWith rule →
    ∀ fuel, (p.runCopyWith w fuel).observe = (p.runInPlace fuel).observe

/-- Under the order of values.inout-argument-order, soundness is `CallRule.Sound`. -/
theorem CallRule.soundWith_leftToRight (rule : CallRule) :
    rule.SoundWith .leftToRight ↔ rule.Sound :=
  Iff.rfl

/-- A rule that accepts no more than a sound rule is sound. -/
theorem CallRule.Sound.of_le {r₁ r₂ : CallRule} (h : r₂.Sound)
    (hle : ∀ ss, r₁ ss = true → r₂ ss = true) : r₁.Sound :=
  fun p hwt hex fuel => h p hwt (hex.mono hle) fuel

/-- The call rule of modes.overlapping-inout is a sound call rule: this is `inPlaceAgreement`. -/
theorem pairwiseDisjoint_sound : CallRule.Sound pairwiseDisjoint :=
  fun p hwt hex fuel =>
    inPlaceAgreement_observe p fuel "" hwt ((Program.exclusive_iff_exclusiveWith p).2 hex)

end Stilt
