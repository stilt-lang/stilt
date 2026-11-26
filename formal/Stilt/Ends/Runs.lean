import Stilt.Ends.Halts
import Stilt.Ends.Instances

/-!
# Runs that halt

The evaluator's steps that run expressions halt, given that running an
expression free of `div` within the fuel it needs does, from every state
(`HaltsRun`): lists of expressions, a record's fields, a place's indexes, a
call's arguments, a `match`, an assignment and a `for` loop, whose turns cost
no fuel.
-/

namespace Stilt

/-- Running an expression free of `div` whose bound is at most `k` halts, from
every state. -/
def HaltsRun {σ : Type} (lim : Limited) (B : Name → Nat) (k : Nat) (F : Nat → Expr → Eval σ Value) : Prop :=
  ∀ e, e.divFree lim = true → e.needs B ≤ k → ∀ s, Halts (fun n => F n e) (fun _ => True) s

theorem Expr.one_le_needs (B : Name → Nat) (e : Expr) : 1 ≤ e.needs B := by
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; simp [Expr.needs]
  all_goals simp [Expr.needs]

namespace Eval.Ends

variable {σ : Type}

theorem asInt (v : Value) : Eval.Ends (fun _ => True) (Eval.asInt v : Eval σ Int) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem asBool (v : Value) : Eval.Ends (fun _ => True) (Eval.asBool v : Eval σ Bool) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem asList (v : Value) : Eval.Ends (fun _ => True) (Eval.asList v : Eval σ (List Value)) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem declare (D : Decls) (R : Name) (written : List (Name × Value)) :
    Eval.Ends (fun _ => True) (Eval.declare D R written : Eval σ Value) := by
  unfold Eval.declare
  split
  · split
    · exact pure trivial
    · exact fail _
  · exact fail _

end Eval.Ends

namespace Halts

variable {σ : Type} (M : Memory σ) {lim : Limited} {B : Name → Nat} {k : Nat} {F : Nat → Expr → Eval σ Value}

section Runs

variable (h : HaltsRun lim B k F)
include h

theorem list : ∀ es : List Expr, exprsDivFree lim es = true → exprsNeeds B es ≤ k → ∀ s,
    Halts (fun n => Eval.list (F n) es) (fun _ => True) s
  | [], _, _, _ => const (Eval.Ends.pure trivial)
  | e :: es, hd, hn, s => by
    simp only [exprsDivFree, exprsNeeds, Bool.and_eq_true, Nat.max_le] at hd hn
    exact bind (h e hd.1 hn.1 s) fun _ s' _ _ =>
      bind (list es hd.2 hn.2 s') fun _ _ _ _ => const (Eval.Ends.pure trivial)

theorem fields : ∀ fs : List (Name × Expr), fieldsDivFree lim fs = true → fieldsNeeds B fs ≤ k → ∀ s,
    Halts (fun n => Eval.fields (F n) fs) (fun _ => True) s
  | [], _, _, _ => const (Eval.Ends.pure trivial)
  | (_, e) :: fs, hd, hn, s => by
    simp only [fieldsDivFree, fieldsNeeds, Bool.and_eq_true, Nat.max_le] at hd hn
    exact bind (h e hd.1 hn.1 s) fun _ s' _ _ =>
      bind (fields fs hd.2 hn.2 s') fun _ _ _ _ => const (Eval.Ends.pure trivial)

theorem path : ∀ ps : List Projection, pathDivFree lim ps = true → pathNeeds B ps ≤ k → ∀ s,
    Halts (fun n => Eval.path (F n) ps) (fun _ => True) s
  | [], _, _, _ => const (Eval.Ends.pure trivial)
  | .field _ :: ps, hd, hn, s => by
    simp only [pathDivFree, pathNeeds] at hd hn
    exact bind (path ps hd hn s) fun _ _ _ _ => const (Eval.Ends.pure trivial)
  | .index i :: ps, hd, hn, s => by
    simp only [pathDivFree, pathNeeds, Bool.and_eq_true, Nat.max_le] at hd hn
    exact bind (bind (h i hd.1 hn.1 s) fun v _ _ _ => const (Eval.Ends.asInt v)) fun _ s' _ _ =>
      bind (path ps hd.2 hn.2 s') fun _ _ _ _ => const (Eval.Ends.pure trivial)

theorem args : ∀ as : List Arg, argsDivFree lim as = true → argsNeeds B as ≤ k → ∀ s,
    Halts (fun n => Eval.args (F n) as) (fun _ => True) s
  | [], _, _, _ => const (Eval.Ends.pure trivial)
  | .value e :: as, hd, hn, s => by
    simp only [argsDivFree, argsNeeds, Bool.and_eq_true, Nat.max_le] at hd hn
    exact bind (h e hd.1 hn.1 s) fun _ s' _ _ =>
      bind (args as hd.2 hn.2 s') fun _ _ _ _ => const (Eval.Ends.pure trivial)
  | .inout ⟨_, ps⟩ :: as, hd, hn, s => by
    simp only [argsDivFree, argsNeeds, Bool.and_eq_true, Nat.max_le] at hd hn
    exact bind (path h ps hd.1 hn.1 s) fun _ s' _ _ =>
      bind (args as hd.2 hn.2 s') fun _ _ _ _ => const (Eval.Ends.pure trivial)

omit h in
theorem arms_mem : ∀ {arms : List Arm} {arm : Arm}, armsDivFree lim arms = true →
    armsNeeds B arms ≤ k → arm ∈ arms → arm.body.divFree lim = true ∧ arm.body.needs B ≤ k
  | ⟨_, _, _⟩ :: _, _, hd, hn, hm => by
    simp only [armsDivFree, armsNeeds, Bool.and_eq_true, Nat.max_le] at hd hn
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨hd.1, hn.1⟩
    · exact arms_mem hd.2 hn.2 hm

theorem select {arms : List Arm} (hd : armsDivFree lim arms = true) (hn : armsNeeds B arms ≤ k)
    (v : Value) (s : σ) : Halts (fun n => Eval.select M (F n) arms v) (fun _ => True) s := by
  unfold Eval.select
  cases hsel : selectArm arms v with
  | none => exact const (Eval.Ends.fail _)
  | some au =>
    obtain ⟨arm, us⟩ := au
    obtain ⟨hmem, -⟩ := selectArm_mem hsel
    obtain ⟨hda, hna⟩ := arms_mem hd hn hmem
    dsimp only
    split
    · exact withVars M (h _ hda hna) _ s
    · exact const (Eval.Ends.fail _)

theorem assign (x : Name) {ps : List Projection} (hd : pathDivFree lim ps = true)
    (hn : pathNeeds B ps ≤ k) {value : Expr} (hvd : value.divFree lim = true) (hvn : value.needs B ≤ k)
    (s : σ) : Halts (fun n => Eval.assign M (F n) x ps value) (fun _ => True) s :=
  bind (path h ps hd hn s) fun _ s' _ _ => bind (h value hvd hvn s') fun _ _ _ _ =>
    bind (const (Eval.Ends.update _)) fun _ _ _ _ => const (Eval.Ends.pure trivial)

theorem loop (x : Name) {e body : Expr} (hed : e.divFree lim = true) (hen : e.needs B ≤ k)
    (hbd : body.divFree lim = true) (hbn : body.needs B ≤ k) (s : σ) :
    Halts (fun n => Eval.loop M (F n) x e body) (fun _ => True) s :=
  bind (bind (h e hed hen s) fun v _ _ _ => const (Eval.Ends.asList v)) fun vs s' _ _ =>
    bind (forEach (fun v _ => withVar M x v (turn (h body hbd hbn _))) vs s') fun _ _ _ _ =>
      const (Eval.Ends.pure trivial)

end Runs

end Halts

end Stilt
