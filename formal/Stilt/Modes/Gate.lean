import Stilt.Modes.Traverse
import Stilt.Moves.Erase

/-!
# Gated marks

Gating a body keeps some of its marks and reads the others as variables, so
it changes nothing that a check of the body reads: the gated body erases to the
body (`Expr.erase_gate`), mentions what it mentions (`Expr.mentions_gate`), and
every mark it keeps is a last use if every mark of the body was one
(`Expr.movesOk_gate`). This is the sense in which `MovingAgreement` holds "for
every subset" of the marks that `Program.markMoves` makes, whatever decides the
subset (values.passing-values).
-/

namespace Stilt

section

variable {κ : Type} (child : κ → Expr → Nat → κ) (keep : κ → Name → Bool)

mutual

theorem Expr.erase_gate : ∀ (e : Expr) (k : κ), (e.gate child keep k).erase = e.erase
  | .var _, _ | .int _, _ | .bool _, _ | .unit, _ | .fnRef .., _ | .method .., _ | .break, _
  | .continue, _ => rfl
  | .move x, k => by
    simp only [Expr.gate]
    split <;> rfl
  | .record _ _ fs, k => by simp [Expr.gate, Expr.erase, eraseFields_gate fs]
  | .variant _ _ _ es, k | .list _ es, k | .op _ es, k | .view es, k => by simp [Expr.gate, Expr.erase, eraseExprs_gate es]
  | .field a _, k | .closure _ _ _ a, k | .raise a, k | .perform _ a, k | .try a, k | .loop a, k | .return a, k => by
    simp [Expr.gate, Expr.erase, Expr.erase_gate a]
  | .index a b, k | .letIn _ _ a b, k | .varIn _ _ a b, k | .seq a b, k | .withH _ _ a b, k | .for _ _ a b, k
  | .while a b, k | .tryCatch a _ _ b _, k => by
    simp [Expr.gate, Expr.erase, Expr.erase_gate a, Expr.erase_gate b]
  | .call f args _, k => by simp [Expr.gate, Expr.erase, Expr.erase_gate f, eraseArgs_gate args]
  | .assign ⟨_, p⟩ v, k => by simp [Expr.gate, Expr.erase, erasePath_gate p, Expr.erase_gate v]
  | .if c _ a b, k => by
    simp [Expr.gate, Expr.erase, Expr.erase_gate c, Expr.erase_gate a, Expr.erase_gate b]
  | .held _ hs b, k => by simp [Expr.gate, Expr.erase, eraseExprs_gate hs, Expr.erase_gate b]
  | .match s _ arms, k => by simp [Expr.gate, Expr.erase, Expr.erase_gate s, eraseArms_gate arms]

theorem eraseExprs_gate : ∀ (es : List Expr) (kf : Nat → κ) (n : Nat),
    eraseExprs (gateExprs child keep kf n es) = eraseExprs es
  | [], _, _ => rfl
  | e :: es, kf, n => by simp [gateExprs, eraseExprs, Expr.erase_gate e, eraseExprs_gate es]

theorem eraseFields_gate : ∀ (fs : List (Name × Expr)) (kf : Nat → κ) (n : Nat),
    eraseFields (gateFields child keep kf n fs) = eraseFields fs
  | [], _, _ => rfl
  | (_, e) :: fs, kf, n => by
    simp [gateFields, eraseFields, Expr.erase_gate e, eraseFields_gate fs]

theorem eraseArgs_gate : ∀ (args : List Arg) (kf : Nat → κ) (n : Nat),
    eraseArgs (gateArgs child keep kf n args) = eraseArgs args
  | [], _, _ => rfl
  | .value e :: args, kf, n => by
    simp [gateArgs, eraseArgs, Expr.erase_gate e, eraseArgs_gate args]
  | .inout ⟨_, p⟩ :: args, kf, n => by
    simp [gateArgs, eraseArgs, erasePath_gate p, eraseArgs_gate args]

theorem erasePath_gate : ∀ (p : List Projection) (k : κ),
    erasePath (gatePath child keep k p) = erasePath p
  | [], _ => rfl
  | .field _ :: p, k => by simp [gatePath, erasePath, erasePath_gate p]
  | .index i :: p, k => by simp [gatePath, erasePath, Expr.erase_gate i, erasePath_gate p]

theorem eraseArms_gate : ∀ (arms : List Arm) (kf : Nat → κ) (n : Nat),
    eraseArms (gateArms child keep kf n arms) = eraseArms arms
  | [], _, _ => rfl
  | ⟨_, _, b⟩ :: arms, kf, n => by
    simp [gateArms, eraseArms, Expr.erase_gate b, eraseArms_gate arms]

end

mutual

theorem Expr.mentions_gate : ∀ (e : Expr) (k : κ), (e.gate child keep k).mentions = e.mentions
  | .var _, _ | .int _, _ | .bool _, _ | .unit, _ | .fnRef .., _ | .method .., _
  | .break, _ | .continue, _ => rfl
  | .closure _ _ _ body, k => by simp [Expr.gate, Expr.mentions, Expr.mentions_gate body]
  | .move x, k => by
    simp only [Expr.gate]
    split <;> rfl
  | .record _ _ fs, k => by simp [Expr.gate, Expr.mentions, fieldsMentions_gate fs]
  | .variant _ _ _ es, k | .list _ es, k | .op _ es, k | .view es, k => by
    simp [Expr.gate, Expr.mentions, exprsMentions_gate es]
  | .field a _, k | .raise a, k | .perform _ a, k | .try a, k | .loop a, k | .return a, k => by
    simp [Expr.gate, Expr.mentions, Expr.mentions_gate a]
  | .index a b, k | .letIn _ _ a b, k | .varIn _ _ a b, k | .seq a b, k | .withH _ _ a b, k | .for _ _ a b, k
  | .while a b, k | .tryCatch a _ _ b _, k => by
    simp [Expr.gate, Expr.mentions, Expr.mentions_gate a, Expr.mentions_gate b]
  | .call f args _, k => by
    simp [Expr.gate, Expr.mentions, Expr.mentions_gate f, argsMentions_gate args]
  | .held _ hs b, k => by simp [Expr.gate, Expr.mentions, exprsMentions_gate hs, Expr.mentions_gate b]
  | .assign ⟨_, p⟩ v, k => by
    simp [Expr.gate, Expr.mentions, pathMentions_gate p, Expr.mentions_gate v]
  | .if c _ a b, k => by
    simp [Expr.gate, Expr.mentions, Expr.mentions_gate c, Expr.mentions_gate a,
      Expr.mentions_gate b]
  | .match s _ arms, k => by
    simp [Expr.gate, Expr.mentions, Expr.mentions_gate s, armsMentions_gate arms]

theorem exprsMentions_gate : ∀ (es : List Expr) (kf : Nat → κ) (n : Nat),
    exprsMentions (gateExprs child keep kf n es) = exprsMentions es
  | [], _, _ => rfl
  | e :: es, kf, n => by
    simp [gateExprs, exprsMentions, Expr.mentions_gate e, exprsMentions_gate es]

theorem fieldsMentions_gate : ∀ (fs : List (Name × Expr)) (kf : Nat → κ) (n : Nat),
    fieldsMentions (gateFields child keep kf n fs) = fieldsMentions fs
  | [], _, _ => rfl
  | (_, e) :: fs, kf, n => by
    simp [gateFields, fieldsMentions, Expr.mentions_gate e, fieldsMentions_gate fs]

theorem argsMentions_gate : ∀ (args : List Arg) (kf : Nat → κ) (n : Nat),
    argsMentions (gateArgs child keep kf n args) = argsMentions args
  | [], _, _ => rfl
  | .value e :: args, kf, n => by
    simp [gateArgs, argsMentions, Expr.mentions_gate e, argsMentions_gate args]
  | .inout ⟨_, p⟩ :: args, kf, n => by
    simp [gateArgs, argsMentions, pathMentions_gate p, argsMentions_gate args]

theorem pathMentions_gate : ∀ (p : List Projection) (k : κ),
    pathMentions (gatePath child keep k p) = pathMentions p
  | [], _ => rfl
  | .field _ :: p, k => by simp [gatePath, pathMentions, pathMentions_gate p]
  | .index i :: p, k => by
    simp [gatePath, pathMentions, Expr.mentions_gate i, pathMentions_gate p]

theorem armsMentions_gate : ∀ (arms : List Arm) (kf : Nat → κ) (n : Nat),
    armsMentions (gateArms child keep kf n arms) = armsMentions arms
  | [], _, _ => rfl
  | ⟨_, _, b⟩ :: arms, kf, n => by
    simp [gateArms, armsMentions, Expr.mentions_gate b, armsMentions_gate arms]

end

theorem inoutRoots_gateArgs : ∀ (kf : Nat → κ) (n : Nat) (args : List Arg),
    inoutRoots (gateArgs child keep kf n args) = inoutRoots args
  | _, _, [] => rfl
  | kf, n, .value _ :: args => by simp [gateArgs, inoutRoots, inoutRoots_gateArgs kf _ args]
  | kf, n, .inout ⟨_, _⟩ :: args => by
    simp [gateArgs, inoutRoots, inoutRoots_gateArgs kf _ args]

mutual

theorem Expr.movesOk_gate : ∀ (e : Expr) (k : κ) (L : Live), e.movesOk L = true →
    (e.gate child keep k).movesOk L = true
  | .var _, _, _, _ | .int _, _, _, _ | .bool _, _, _, _ | .unit, _, _, _ | .fnRef .., _, _, _
  | .method .., _, _, _ | .break, _, _, _ | .continue, _, _, _ => rfl
  | .move x, k, L, h => by
    simp only [Expr.gate]
    split
    · exact h
    · rfl
  | .record _ _ fs, k, L, h => by
    simp only [Expr.gate, Expr.movesOk] at h ⊢
    exact fieldsMovesOk_gate fs _ 0 L h
  | .variant _ _ _ es, k, L, h | .list _ es, k, L, h | .op _ es, k, L, h | .view es, k, L, h => by
    simp only [Expr.gate, Expr.movesOk] at h ⊢
    exact exprsMovesOk_gate es _ 0 L h
  | .field a _, k, L, h | .raise a, k, L, h | .perform _ a, k, L, h | .try a, k, L, h | .closure _ _ _ a, k, L, h
  | .return a, k, L, h => by
    simp only [Expr.gate, Expr.movesOk] at h ⊢
    exact Expr.movesOk_gate a _ _ h
  | .loop a, k, L, h => by
    simp only [Expr.gate, Expr.movesOk, Expr.mentions_gate] at h ⊢
    exact Expr.movesOk_gate a _ _ h
  | .index a b, k, L, h | .seq a b, k, L, h | .withH _ _ a b, k, L, h | .tryCatch a _ _ b _, k, L, h
  | .while a b, k, L, h => by
    simp only [Expr.gate, Expr.movesOk, Expr.mentions_gate, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.movesOk_gate a _ _ h.1, Expr.movesOk_gate b _ _ h.2⟩
  | .letIn _ _ a b, k, L, h | .varIn _ _ a b, k, L, h | .for _ _ a b, k, L, h => by
    simp only [Expr.gate, Expr.movesOk, Expr.mentions_gate, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.movesOk_gate a _ _ h.1, Expr.movesOk_gate b _ _ h.2⟩
  | .held _ hs b, k, L, h => by
    simp only [Expr.gate, Expr.movesOk, Expr.mentions_gate, Bool.and_eq_true] at h ⊢
    exact ⟨exprsMovesOk_gate hs _ 0 _ h.1, Expr.movesOk_gate b _ _ h.2⟩
  | .call f args _, k, L, h => by
    simp only [Expr.gate, Expr.movesOk, argsMentions_gate, inoutRoots_gateArgs,
      Bool.and_eq_true] at h ⊢
    exact ⟨Expr.movesOk_gate f _ _ h.1, argsMovesOk_gate args _ 1 _ h.2⟩
  | .assign ⟨_, p⟩ v, k, L, h => by
    simp only [Expr.gate, Expr.movesOk, Expr.mentions_gate, Bool.and_eq_true] at h ⊢
    exact ⟨pathMovesOk_gate p _ _ h.1, Expr.movesOk_gate v _ _ h.2⟩
  | .if c _ a b, k, L, h => by
    simp only [Expr.gate, Expr.movesOk, Expr.mentions_gate, Bool.and_eq_true] at h ⊢
    exact ⟨⟨Expr.movesOk_gate c _ _ h.1.1, Expr.movesOk_gate a _ _ h.1.2⟩,
      Expr.movesOk_gate b _ _ h.2⟩
  | .match s _ arms, k, L, h => by
    simp only [Expr.gate, Expr.movesOk, armsMentions_gate, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.movesOk_gate s _ _ h.1, armsMovesOk_gate arms _ 1 _ h.2⟩

theorem exprsMovesOk_gate : ∀ (es : List Expr) (kf : Nat → κ) (n : Nat) (L : Live),
    exprsMovesOk L es = true → exprsMovesOk L (gateExprs child keep kf n es) = true
  | [], _, _, _, _ => rfl
  | e :: es, kf, n, L, h => by
    simp only [gateExprs, exprsMovesOk, exprsMentions_gate, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.movesOk_gate e _ _ h.1, exprsMovesOk_gate es kf _ L h.2⟩

theorem fieldsMovesOk_gate : ∀ (fs : List (Name × Expr)) (kf : Nat → κ) (n : Nat) (L : Live),
    fieldsMovesOk L fs = true → fieldsMovesOk L (gateFields child keep kf n fs) = true
  | [], _, _, _, _ => rfl
  | (_, e) :: fs, kf, n, L, h => by
    simp only [gateFields, fieldsMovesOk, fieldsMentions_gate, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.movesOk_gate e _ _ h.1, fieldsMovesOk_gate fs kf _ L h.2⟩

theorem argsMovesOk_gate : ∀ (args : List Arg) (kf : Nat → κ) (n : Nat) (L : Live),
    argsMovesOk L args = true → argsMovesOk L (gateArgs child keep kf n args) = true
  | [], _, _, _, _ => rfl
  | .value e :: args, kf, n, L, h => by
    simp only [gateArgs, argsMovesOk, argsMentions_gate, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.movesOk_gate e _ _ h.1, argsMovesOk_gate args kf _ L h.2⟩
  | .inout ⟨_, p⟩ :: args, kf, n, L, h => by
    simp only [gateArgs, argsMovesOk, argsMentions_gate, Bool.and_eq_true] at h ⊢
    exact ⟨pathMovesOk_gate p _ _ h.1, argsMovesOk_gate args kf _ L h.2⟩

theorem pathMovesOk_gate : ∀ (p : List Projection) (k : κ) (L : Live),
    pathMovesOk L p = true → pathMovesOk L (gatePath child keep k p) = true
  | [], _, _, _ => rfl
  | .field _ :: p, k, L, h => by
    simp only [gatePath, pathMovesOk] at h ⊢
    exact pathMovesOk_gate p k L h
  | .index i :: p, k, L, h => by
    simp only [gatePath, pathMovesOk, pathMentions_gate, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.movesOk_gate i _ _ h.1, pathMovesOk_gate p k L h.2⟩

theorem armsMovesOk_gate : ∀ (arms : List Arm) (kf : Nat → κ) (n : Nat) (L : Live),
    armsMovesOk L arms = true → armsMovesOk L (gateArms child keep kf n arms) = true
  | [], _, _, _, _ => rfl
  | ⟨_, _, b⟩ :: arms, kf, n, L, h => by
    simp only [gateArms, armsMovesOk, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.movesOk_gate b _ _ h.1, armsMovesOk_gate arms kf _ L h.2⟩

end

/-- A gated mark stays exactly where the context keeps it. -/
theorem Expr.gate_move (k : κ) (x : Name) :
    (Expr.move x).gate child keep k = .move x ↔ keep k x = true := by
  simp only [Expr.gate]
  split <;> simp_all

/-- Gating keeps the law of exclusivity, which looks at places, not marks. -/
theorem Expr.exclusive_gate (e : Expr) (k : κ) (r : List Shape) :
    (e.gate child keep k).exclusive r = e.exclusive r := by
  rw [← Expr.exclusive_erase, Expr.erase_gate, Expr.exclusive_erase]

end

end Stilt
