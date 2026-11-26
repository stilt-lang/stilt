import Stilt.Modes.Escape
import Stilt.Modes.Fixpoint

/-!
# Rounds that only grow

A round of consumption reads the previous round's only where a call passes a
value to a parameter, and a parameter that one round consumes stays consumed
in the next: `Expr.leaves` asks no less when more parameters are consumed and
more of a value leaves (values.consumed-parameters). A round of `once` parameters reads
the previous round's where a call passes a parameter on, and a use that one
round counts as a single call stays one in the next when more parameters are
`once`: `Expr.use` is at most what it was, and is none exactly when it was
(modes.once-parameters). `Stilt.Modes.Solved` uses both to show that the rounds
reach their fixed points.
-/

namespace Stilt

/-- Whatever part of a value leaves in `o` leaves in `o'` too. -/
def OutLe (o o' : Option (List Sel)) : Prop := ∀ s, o = some s → o' = some s

theorem OutLe.refl (o : Option (List Sel)) : OutLe o o := fun _ => id

theorem OutLe.map {o o' : Option (List Sel)} (h : OutLe o o') (f : List Sel → List Sel) :
    OutLe (o.map f) (o'.map f) := by
  intro s hs
  cases o with
  | none => cases hs
  | some t =>
    rw [h t rfl]
    exact hs

theorem OutLe.isSome {o o' : Option (List Sel)} (h : OutLe o o') (ho : o.isSome = true) :
    o'.isSome = true := by
  cases o with
  | none => cases ho
  | some t => rw [h t rfl]; rfl

theorem consumesArg_mono {C C' : Consumed} (h : ParamSet.Le C C') (f : Expr) (n : Nat)
    (hc : consumesArg C f n = true) : consumesArg C' f n = true := by
  cases f <;> first | rfl | exact h _ _ hc

/-- The context of an argument, from whether its parameter is consumed. -/
theorem OutLe.ite {c c' : Bool} (h : c = true → c' = true) :
    OutLe (if c then some [] else none) (if c' then some [] else none) := by
  intro s hs
  cases c with
  | false => cases hs
  | true => simp only [h rfl, ite_true] at hs ⊢; exact hs

/-- The context of an initializer, from whether its binding's value leaves. -/
theorem OutLe.iteP {c c' : Prop} [Decidable c] [Decidable c'] (h : c → c') :
    OutLe (if c then some [] else none) (if c' then some [] else none) := by
  intro s hs
  by_cases hc : c
  · simp only [hc, h hc, ite_true] at hs ⊢
    exact hs
  · simp [hc] at hs

/-- The same question about a binding, with more parameters consumed. -/
abbrev Leaving.with (L : Leaving) (C' : Consumed) : Leaving := { L with consumed := C' }

mutual

theorem Expr.leaves_mono : ∀ (e : Expr) (L : Leaving) (C' : Consumed) (o o' : Option (List Sel)),
    ParamSet.Le L.consumed C' → OutLe o o' → e.leaves L o = true →
      e.leaves (L.with C') o' = true
  | .var _, L, C', o, o', _, ho, h | .move _, L, C', o, o', _, ho, h => by
    simp only [Expr.leaves, Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    cases o with
    | none => cases h.2
    | some s => rw [ho s rfl]; exact h.2
  | .int _, _, _, _, _, _, _, h | .bool _, _, _, _, _, _, _, h | .unit, _, _, _, _, _, _, h
  | .break, _, _, _, _, _, _, h | .continue, _, _, _, _, _, _, h
  | .fnRef .., _, _, _, _, _, _, h => by simp [Expr.leaves] at h
  | .record _ _ fs, L, C', _, _, hC, _, h => fieldsLeave_mono fs L C' hC h
  | .variant _ _ _ es, L, C', _, _, hC, _, h | .list _ es, L, C', _, _, hC, _, h | .op _ es, L, C', _, _, hC, _, h | .view es, L, C', _, _, hC, _, h =>
    exprsLeave_mono es L C' hC h
  | .field e f, L, C', o, o', hC, ho, h => Expr.leaves_mono e L C' _ _ hC (ho.map _) h
  | .index e i, L, C', o, o', hC, ho, h => by
    simp only [Expr.leaves, Bool.or_eq_true] at h ⊢
    exact h.imp (Expr.leaves_mono e L C' _ _ hC (ho.map _))
      (Expr.leaves_mono i L C' _ _ hC (OutLe.refl _))
  | .closure .., L, C', o, o', hC, ho, h => by
    simp only [Expr.leaves, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
    exact ⟨h.1, h.2.imp_right (ho.isSome ·)⟩
  | .call f args _, L, C', o, o', hC, ho, h => by
    simp only [Expr.leaves, Bool.or_eq_true] at h ⊢
    exact h.imp (Expr.leaves_mono f L C' _ _ hC (OutLe.refl _))
      (argsLeave_mono args L C' _ _ 0 hC (consumesArg_mono hC f))
  | .letIn y _ init body, L, C', o, o', hC, ho, h
  | .varIn y _ init body, L, C', o, o', hC, ho, h => by
    simp only [Expr.leaves, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    refine h.imp (Expr.leaves_mono init L C' _ _ hC (OutLe.iteP fun hc => ?_))
      (And.imp_right (Expr.leaves_mono body (L.hide [y]) C' o o' hC ho))
    first
      | exact hc.imp_right (Expr.leaves_mono body ((L.hide [y]).about y) C' o o' hC ho)
      | exact hc.imp id
          (And.imp_right (Expr.leaves_mono body ((L.hide [y]).about y) C' o o' hC ho))
  | .assign ⟨_, p⟩ v, L, C', _, _, hC, _, h => by
    simp only [Expr.leaves, Bool.or_eq_true] at h ⊢
    exact h.imp (pathLeave_mono p L C' hC) (Expr.leaves_mono v L C' _ _ hC (OutLe.refl _))
  | .seq a b, L, C', o, o', hC, ho, h | .withH _ _ a b, L, C', o, o', hC, ho, h => by
    simp only [Expr.leaves, Bool.or_eq_true] at h ⊢
    exact h.imp (Expr.leaves_mono a L C' _ _ hC (OutLe.refl _)) (Expr.leaves_mono b L C' _ _ hC ho)
  | .perform _ e, L, C', _, _, hC, _, h => Expr.leaves_mono e L C' _ _ hC (OutLe.refl _) h
  | .held ns es body, L, C', o, o', hC, ho, h => by
    simp only [Expr.leaves, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    exact h.imp (exprsLeave_mono es L C' hC)
      (And.imp_right (Expr.leaves_mono body (L.hide (ns.map (·.1))) C' o o' hC ho))
  | .if c _ a b, L, C', o, o', hC, ho, h => by
    simp only [Expr.leaves, Bool.or_eq_true] at h ⊢
    exact h.imp (Or.imp (Expr.leaves_mono c L C' _ _ hC (OutLe.refl _))
      (Expr.leaves_mono a L C' _ _ hC ho)) (Expr.leaves_mono b L C' _ _ hC ho)
  | .match e _ arms, L, C', o, o', hC, ho, h => by
    simp only [Expr.leaves, Bool.or_eq_true] at h ⊢
    exact h.imp (Expr.leaves_mono e L C' _ _ hC (OutLe.refl _))
      (armsLeave_mono arms L C' o o' hC ho)
  | .for y _ e body, L, C', _, _, hC, _, h => by
    simp only [Expr.leaves, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    exact h.imp (Expr.leaves_mono e L C' _ _ hC (OutLe.refl _))
      (And.imp_right (Expr.leaves_mono body (L.hide [y]) C' _ _ hC (OutLe.refl _)))
  | .raise e, L, C', _, _, hC, _, h => Expr.leaves_mono e L C' _ _ hC (OutLe.refl _) h
  | .try e, L, C', o, o', hC, ho, h | .form _ e, L, C', o, o', hC, ho, h => Expr.leaves_mono e L C' o o' hC ho h
  | .tryCatch e _ y hd _, L, C', o, o', hC, ho, h => by
    simp only [Expr.leaves, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    exact h.imp (Expr.leaves_mono e L C' o o' hC ho)
      (And.imp_right (Expr.leaves_mono hd (L.hide [y]) C' o o' hC ho))
  | .while c body, L, C', _, _, hC, _, h => by
    simp only [Expr.leaves, Bool.or_eq_true] at h ⊢
    exact h.imp (Expr.leaves_mono c L C' _ _ hC (OutLe.refl _))
      (Expr.leaves_mono body L C' _ _ hC (OutLe.refl _))
  | .loop body, L, C', _, _, hC, _, h => Expr.leaves_mono body L C' _ _ hC (OutLe.refl _) h
  | .return e, L, C', _, _, hC, _, h => Expr.leaves_mono e L C' _ _ hC (OutLe.refl _) h

theorem exprsLeave_mono : ∀ (es : List Expr) (L : Leaving) (C' : Consumed),
    ParamSet.Le L.consumed C' → exprsLeave L es = true → exprsLeave (L.with C') es = true
  | [], _, _, _, h => by simp [exprsLeave] at h
  | e :: es, L, C', hC, h => by
    simp only [exprsLeave, Bool.or_eq_true] at h ⊢
    exact h.imp (Expr.leaves_mono e L C' _ _ hC (OutLe.refl _)) (exprsLeave_mono es L C' hC)

theorem fieldsLeave_mono : ∀ (fs : List (Name × Expr)) (L : Leaving) (C' : Consumed),
    ParamSet.Le L.consumed C' → fieldsLeave L fs = true → fieldsLeave (L.with C') fs = true
  | [], _, _, _, h => by simp [fieldsLeave] at h
  | (_, e) :: fs, L, C', hC, h => by
    simp only [fieldsLeave, Bool.or_eq_true] at h ⊢
    exact h.imp (Expr.leaves_mono e L C' _ _ hC (OutLe.refl _)) (fieldsLeave_mono fs L C' hC)

theorem argsLeave_mono : ∀ (args : List Arg) (L : Leaving) (C' : Consumed) (c c' : Nat → Bool)
    (n : Nat), ParamSet.Le L.consumed C' → (∀ m, c m = true → c' m = true) →
      argsLeave L c n args = true → argsLeave (L.with C') c' n args = true
  | [], _, _, _, _, _, _, _, h => by simp [argsLeave] at h
  | .value e :: args, L, C', c, c', n, hC, hc, h => by
    simp only [argsLeave, Bool.or_eq_true] at h ⊢
    exact h.imp (Expr.leaves_mono e L C' _ _ hC (OutLe.ite (hc n)))
      (argsLeave_mono args L C' c c' _ hC hc)
  | .inout ⟨_, p⟩ :: args, L, C', c, c', n, hC, hc, h => by
    simp only [argsLeave, Bool.or_eq_true] at h ⊢
    exact h.imp (pathLeave_mono p L C' hC) (argsLeave_mono args L C' c c' _ hC hc)

theorem pathLeave_mono : ∀ (p : List Projection) (L : Leaving) (C' : Consumed),
    ParamSet.Le L.consumed C' → pathLeave L p = true → pathLeave (L.with C') p = true
  | [], _, _, _, h => by simp [pathLeave] at h
  | .field _ :: p, L, C', hC, h => pathLeave_mono p L C' hC h
  | .index i :: p, L, C', hC, h => by
    simp only [pathLeave, Bool.or_eq_true] at h ⊢
    exact h.imp (Expr.leaves_mono i L C' _ _ hC (OutLe.refl _)) (pathLeave_mono p L C' hC)

theorem armsLeave_mono :
    ∀ (arms : List Arm) (L : Leaving) (C' : Consumed) (o o' : Option (List Sel)),
    ParamSet.Le L.consumed C' → OutLe o o' → armsLeave L o arms = true →
      armsLeave (L.with C') o' arms = true
  | [], _, _, _, _, _, _, h => by simp [armsLeave] at h
  | ⟨_, bs, b⟩ :: arms, L, C', o, o', hC, ho, h => by
    simp only [armsLeave, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    exact h.imp (And.imp_right (Expr.leaves_mono b (L.hide bs) C' o o' hC ho))
      (armsLeave_mono arms L C' o o' hC ho)

end

/-! ## Uses with more `once` parameters -/

/-- `a` counts no more uses than `b`, and none exactly when `b` does. -/
def Use.Below (a b : Use) : Prop := (a = .none ↔ b = .none) ∧ (b = .once → a = .once)

theorem Use.Below.refl (a : Use) : a.Below a := ⟨Iff.rfl, id⟩

theorem Use.Below.add {a b c d : Use} (h₁ : a.Below b) (h₂ : c.Below d) :
    (a.add c).Below (b.add d) := by
  obtain ⟨h₁, h₁'⟩ := h₁
  obtain ⟨h₂, h₂'⟩ := h₂
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [Use.Below, Use.add]

theorem Use.Below.again {a b : Use} (h : a.Below b) : a.again.Below b.again := by
  obtain ⟨h, h'⟩ := h
  cases a <;> cases b <;> simp_all [Use.Below, Use.again]

theorem Use.Below.cond (c : Bool) {a b a' b' : Use} (h₁ : a.Below b) (h₂ : a'.Below b') :
    (if c then a else a').Below (if c then b else b') := by
  cases c
  · exact h₂
  · exact h₁

/-- A pass to a parameter that one round makes `once` is one use in the next
too. -/
theorem Use.Below.pass {c c' : Bool} (h : c = true → c' = true) :
    (if c' then Use.once else .many).Below (if c then .once else .many) := by
  cases c <;> cases c' <;> simp_all [Use.Below]

theorem passesOnce_mono {O O' : OnceParams} (h : ParamSet.Le O O') (f : Expr) (n : Nat)
    (ho : passesOnce O f n = true) : passesOnce O' f n = true := by
  cases f <;> first | exact h _ _ ho | cases ho

mutual

theorem Expr.use_below : ∀ (e : Expr) (O O' : OnceParams) (f : Name), ParamSet.Le O O' →
    (e.use O' f).Below (e.use O f)
  | .var _, _, _, _, _ | .move _, _, _, _, _ | .int _, _, _, _, _ | .bool _, _, _, _, _
  | .unit, _, _, _, _ | .break, _, _, _, _ | .continue, _, _, _, _ | .fnRef .., _, _, _, _
  | .method .., _, _, _, _ => Use.Below.refl _
  | .record _ _ fs, O, O', f, h => fieldsUse_below fs O O' f h
  | .variant _ _ _ es, O, O', f, h | .list _ es, O, O', f, h | .op _ es, O, O', f, h | .view es, O, O', f, h => exprsUse_below es O O' f h
  | .field e _, O, O', f, h | .raise e, O, O', f, h | .perform _ e, O, O', f, h | .try e, O, O', f, h | .form _ e, O, O', f, h
  | .return e, O, O', f, h => Expr.use_below e O O' f h
  | .while c body, O, O', f, h =>
    ((Expr.use_below c O O' f h).add (Expr.use_below body O O' f h)).again
  | .loop body, O, O', f, h => (Expr.use_below body O O' f h).again
  | .index a b, O, O', f, h | .seq a b, O, O', f, h =>
    (Expr.use_below a O O' f h).add (Expr.use_below b O O' f h)
  | .withH _ _ a b, O, O', f, h =>
    (Expr.use_below a O O' f h).add (Expr.use_below b O O' f h).again
  | .closure _ _ _ body, O, O', f, h =>
    Use.Below.cond _ (Use.Below.refl _) (Expr.use_below body O O' f h).again
  | .call g args _, O, O', f, h =>
    (Use.Below.cond _ (Use.Below.refl _) (Expr.use_below g O O' f h)).add
      (argsUse_below args O O' f _ _ 0 h (passesOnce_mono h g))
  | .letIn _ _ a b, O, O', f, h | .varIn _ _ a b, O, O', f, h =>
    (Expr.use_below a O O' f h).add
      (Use.Below.cond _ (Use.Below.refl _) (Expr.use_below b O O' f h))
  | .assign ⟨_, p⟩ v, O, O', f, h =>
    (Use.Below.refl _).add ((pathUse_below p O O' f h).add (Expr.use_below v O O' f h))
  | .if c _ a b, O, O', f, h =>
    (Expr.use_below c O O' f h).add
      ((Expr.use_below a O O' f h).add (Expr.use_below b O O' f h))
  | .match e _ arms, O, O', f, h => (Expr.use_below e O O' f h).add (armsUse_below arms O O' f h)
  | .for _ _ e body, O, O', f, h =>
    (Expr.use_below e O O' f h).add
      (Use.Below.cond _ (Use.Below.refl _) (Expr.use_below body O O' f h).again)
  | .tryCatch e _ _ hd _, O, O', f, h =>
    (Expr.use_below e O O' f h).add
      (Use.Below.cond _ (Use.Below.refl _) (Expr.use_below hd O O' f h))
  | .held _ es body, O, O', f, h =>
    (exprsUse_below es O O' f h).add (Use.Below.cond _ (Use.Below.refl _) (Expr.use_below body O O' f h))

theorem exprsUse_below : ∀ (es : List Expr) (O O' : OnceParams) (f : Name), ParamSet.Le O O' →
    (exprsUse O' f es).Below (exprsUse O f es)
  | [], _, _, _, _ => Use.Below.refl _
  | e :: es, O, O', f, h => (Expr.use_below e O O' f h).add (exprsUse_below es O O' f h)

theorem fieldsUse_below : ∀ (fs : List (Name × Expr)) (O O' : OnceParams) (f : Name),
    ParamSet.Le O O' → (fieldsUse O' f fs).Below (fieldsUse O f fs)
  | [], _, _, _, _ => Use.Below.refl _
  | (_, e) :: fs, O, O', f, h => (Expr.use_below e O O' f h).add (fieldsUse_below fs O O' f h)

theorem argsUse_below : ∀ (args : List Arg) (O O' : OnceParams) (f : Name) (c c' : Nat → Bool)
    (n : Nat), ParamSet.Le O O' → (∀ m, c m = true → c' m = true) →
      (argsUse O' f c' n args).Below (argsUse O f c n args)
  | [], _, _, _, _, _, _, _, _ => Use.Below.refl _
  | .value e :: args, O, O', f, c, c', n, h, hc =>
    (Use.Below.cond _ (Use.Below.pass (hc n)) (Expr.use_below e O O' f h)).add
      (argsUse_below args O O' f c c' _ h hc)
  | .inout ⟨_, p⟩ :: args, O, O', f, c, c', _, h, hc =>
    (Use.Below.refl _).add ((pathUse_below p O O' f h).add (argsUse_below args O O' f c c' _ h hc))

theorem pathUse_below :
    ∀ (p : List Projection) (O O' : OnceParams) (f : Name), ParamSet.Le O O' →
    (pathUse O' f p).Below (pathUse O f p)
  | [], _, _, _, _ => Use.Below.refl _
  | .field _ :: p, O, O', f, h => pathUse_below p O O' f h
  | .index i :: p, O, O', f, h => (Expr.use_below i O O' f h).add (pathUse_below p O O' f h)

theorem armsUse_below : ∀ (arms : List Arm) (O O' : OnceParams) (f : Name), ParamSet.Le O O' →
    (armsUse O' f arms).Below (armsUse O f arms)
  | [], _, _, _, _ => Use.Below.refl _
  | ⟨_, _, b⟩ :: arms, O, O', f, h =>
    (Use.Below.cond _ (Use.Below.refl _) (Expr.use_below b O O' f h)).add
      (armsUse_below arms O O' f h)

end

end Stilt