import Stilt.Rows

/-!
# The empty instantiation

Instantiating no row variable changes nothing. `main` declares none (effects.row-variables), so the fundamental lemma, which holds of every instantiation of a
well-typed expression, holds of `main` itself.
-/

namespace Stilt

mutual

theorem Ty.substRows_nil : ∀ τ : Ty, τ.substRows [] = τ
  | .int _ | .float _ | .bool | .str | .unit | .never | .param _ => rfl
  | .record _ τs | .variant _ τs => by rw [Ty.substRows, substTysRows_nil τs]
  | .list τ => by rw [Ty.substRows, Ty.substRows_nil τ]
  | .tuple τs => by rw [Ty.substRows, substTysRows_nil τs]
  | .map κ τ => by rw [Ty.substRows, Ty.substRows_nil κ, Ty.substRows_nil τ]
  | .set τ => by rw [Ty.substRows, Ty.substRows_nil τ]
  | .view τ => by rw [Ty.substRows, Ty.substRows_nil τ]
  | .shared τ => by rw [Ty.substRows, Ty.substRows_nil τ]
  | .fn ps r ρ => by
    rw [Ty.substRows, substParamRows_nil ps, Ty.substRows_nil r, Row.substRows_nil ρ]

theorem substTysRows_nil : ∀ τs : List Ty, substTysRows [] τs = τs
  | [] => rfl
  | τ :: τs => by rw [substTysRows, Ty.substRows_nil τ, substTysRows_nil τs]

theorem substParamRows_nil : ∀ ps : List (Mode × Ty), substParamRows [] ps = ps
  | [] => rfl
  | (_, τ) :: ps => by rw [substParamRows, Ty.substRows_nil τ, substParamRows_nil ps]

theorem Row.substRows_nil : ∀ ρ : Row, ρ.substRows [] = ρ
  | ⟨_, some E, _, _, _⟩ => by simp [Row.substRows, Ty.substRows_nil E]
  | ⟨_, none, _, _, _⟩ => by simp [Row.substRows]

end

theorem Param.substRows_nil (p : Param) : p.substRows [] = p := by
  simp [Param.substRows, Ty.substRows_nil]

mutual

theorem Expr.substRows_nil : ∀ e : Expr, e.substRows [] = e
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue => rfl
  | .record _ τs fields => by rw [Expr.substRows, substTysRows_nil τs, substFieldRows_nil fields]
  | .variant _ τs _ es => by rw [Expr.substRows, substTysRows_nil τs, substExprRows_nil es]
  | .list τ es => by rw [Expr.substRows, Ty.substRows_nil τ, substExprRows_nil es]
  | .op _ es | .view es => by rw [Expr.substRows, substExprRows_nil es]
  | .field e _ => by rw [Expr.substRows, Expr.substRows_nil e]
  | .index e i => by rw [Expr.substRows, Expr.substRows_nil e, Expr.substRows_nil i]
  | .fnRef _ tys rows => by
    rw [Expr.substRows, substTysRows_nil tys, show Row.substRows [] = id from funext Row.substRows_nil,
      List.map_id]
  | .method _ _ τ => by rw [Expr.substRows, Ty.substRows_nil τ]
  | .closure ps r ρ body => by
    rw [Expr.substRows, show Param.substRows [] = id from funext Param.substRows_nil, List.map_id,
      Ty.substRows_nil r, Row.substRows_nil ρ, Expr.substRows_nil body]
  | .call f args _ => by rw [Expr.substRows, Expr.substRows_nil f, substArgRows_nil args]
  | .letIn _ τ e body => by
    rw [Expr.substRows, Ty.substRows_nil τ, Expr.substRows_nil e, Expr.substRows_nil body]
  | .held ns hs body => by
    simp only [Expr.substRows, Ty.substRows_nil, substExprRows_nil hs, Expr.substRows_nil body]
    simp
  | .varIn _ τ e body => by
    rw [Expr.substRows, Ty.substRows_nil τ, Expr.substRows_nil e, Expr.substRows_nil body]
  | .assign ⟨_, path⟩ e => by rw [Expr.substRows, substPathRows_nil path, Expr.substRows_nil e]
  | .seq a b => by rw [Expr.substRows, Expr.substRows_nil a, Expr.substRows_nil b]
  | .if c τ a b => by
    rw [Expr.substRows, Expr.substRows_nil c, Ty.substRows_nil τ, Expr.substRows_nil a,
      Expr.substRows_nil b]
  | .match e τ arms => by
    rw [Expr.substRows, Expr.substRows_nil e, Ty.substRows_nil τ, substArmRows_nil arms]
  | .for _ τ e body => by
    rw [Expr.substRows, Ty.substRows_nil τ, Expr.substRows_nil e, Expr.substRows_nil body]
  | .raise e => by rw [Expr.substRows, Expr.substRows_nil e]
  | .try e | .form _ e => by rw [Expr.substRows, Expr.substRows_nil e]
  | .tryCatch e E _ h τ => by
    rw [Expr.substRows, Expr.substRows_nil e, Ty.substRows_nil E, Expr.substRows_nil h,
      Ty.substRows_nil τ]
  | .while c body => by rw [Expr.substRows, Expr.substRows_nil c, Expr.substRows_nil body]
  | .loop body => by rw [Expr.substRows, Expr.substRows_nil body]
  | .return e => by rw [Expr.substRows, Expr.substRows_nil e]
  | .perform _ e => by rw [Expr.substRows, Expr.substRows_nil e]
  | .withH _ _ h b => by rw [Expr.substRows, Expr.substRows_nil h, Expr.substRows_nil b]

theorem substExprRows_nil : ∀ es : List Expr, substExprRows [] es = es
  | [] => rfl
  | e :: es => by rw [substExprRows, Expr.substRows_nil e, substExprRows_nil es]

theorem substFieldRows_nil : ∀ fields : List (Name × Expr), substFieldRows [] fields = fields
  | [] => rfl
  | (_, e) :: fields => by rw [substFieldRows, Expr.substRows_nil e, substFieldRows_nil fields]

theorem substArgRows_nil : ∀ args : List Arg, substArgRows [] args = args
  | [] => rfl
  | .value e :: args => by rw [substArgRows, Expr.substRows_nil e, substArgRows_nil args]
  | .inout ⟨_, path⟩ :: args => by
    rw [substArgRows, substPathRows_nil path, substArgRows_nil args]

theorem substPathRows_nil : ∀ path : List Projection, substPathRows [] path = path
  | [] => rfl
  | .field _ :: path => by rw [substPathRows, substPathRows_nil path]
  | .index i :: path => by rw [substPathRows, Expr.substRows_nil i, substPathRows_nil path]

theorem substArmRows_nil : ∀ arms : List Arm, substArmRows [] arms = arms
  | [] => rfl
  | ⟨_, _, guard, body⟩ :: arms => by
    rw [substArmRows, substGuardRows_nil guard, Expr.substRows_nil body, substArmRows_nil arms]

theorem substGuardRows_nil : ∀ guard : Option Expr, substGuardRows [] guard = guard
  | none => rfl
  | some g => by rw [substGuardRows, Expr.substRows_nil g]

end

end Stilt
