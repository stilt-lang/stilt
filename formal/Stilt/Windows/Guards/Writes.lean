import Stilt.Windows.Guards.Runs

/-!
# Every in-place evaluation writes below its variables

`eval_writes`: evaluating any expression in place, with any fuel, from a valid state, ends
in states that evolved by writes below the references of its variables and by new
locations, the rests of its performances included (`Eval.Guards` with no region). An
assignment writes below its variable; a call runs its body from new locations and the
places of its `inout` arguments, so what the body writes reaches the caller only there; and
a scope's end forgets what was written to its binding's new location.

This is what a call needs of its body when the guarded regions are the caller's
(`Stilt.Windows.Guards.Eval`), whatever the body's reads.
-/

namespace Stilt

open InPlace Eval.Guards

/-- Each argument keeps the regions when every run does. -/
theorem Eval.Guards.argsKeep_of {G : List Path} {R : List Shape}
    {run : Expr → Eval (State × World) Value} (h : ∀ e, Eval.Guards G R (fun _ => True) (run e)) :
    ∀ as : List Arg, ArgsKeep G R run as
  | [] => trivial
  | .value e :: as => ⟨h e, argsKeep_of h as⟩
  | .inout ⟨_, _⟩ :: as => ⟨fun i _ => h i, argsKeep_of h as⟩

theorem Eval.Guards.declare {G : List Path} {R : List Shape} (D : Decls) (T : Name)
    (written : List (Name × Value)) :
    Eval.Guards G R (fun _ => True) (Eval.declare D T written : Eval (State × World) Value) := by
  unfold Eval.declare
  split
  · split
    · exact pure trivial
    · exact fail _
  · exact fail _

theorem Eval.Guards.method {G : List Path} {R : List Shape} (D : Decls) (t m : Name) (τ : Ty) :
    Eval.Guards G R (fun _ => True) (Eval.method D t m τ : Eval (State × World) Value) := by
  unfold Eval.method
  split
  · split
    · exact pure trivial
    · exact fail _
  · exact fail _

theorem hide_nil_sub (x : Name) (R : List Shape) : ∀ t ∈ hide ([] : List Shape) x, t ∈ R := by
  intro t ht
  simp [hide] at ht

/-- Evaluating any expression in place, with any fuel, writes only below the variables of
the state it starts from, and at new locations. -/
theorem eval_writes (D : Decls) :
    ∀ n e, Eval.Guards [] [] (fun _ => True) (eval D InPlace.memory n e)
  | 0, _ => outOfFuel
  | n + 1, e => by
    have ih := eval_writes D n
    have ihR : ∀ e R, Eval.Guards [] R (fun _ => True) (eval D InPlace.memory n e) :=
      fun e _ => (ih e).nil_any
    cases e
    case var x => exact inspect _ fun _ _ _ => trivial
    case move x => exact inspect _ fun _ _ _ => trivial
    case int k => exact pure trivial
    case bool b => exact pure trivial
    case unit => exact pure trivial
    case record R _ fs => exact bind (fields fs fun fe _ => ih fe.2) fun _ _ => declare D R _
    case variant T _ C es => exact bind (list es fun e _ => ih e) fun _ _ => pure trivial
    case list τ es => exact bind (list es fun e _ => ih e) fun _ _ => pure trivial
    case op o es => exact bind (list es fun e _ => ih e) fun _ _ => world _
    case view es =>
      exact bind (list es fun e _ => ih e) fun _ _ => ofExcept _ fun _ _ => trivial
    case field e f => exact bind (ih e) fun _ _ => ofExcept _ fun _ _ => trivial
    case index e i => exact index (ih e) (ih i)
    case fnRef f types rows => exact pure trivial
    case method t m τ => exact method D t m τ
    case closure ps result ρ body =>
      exact bind (inspect _ fun _ _ _ => trivial) fun _ _ => pure trivial
    case call callee as τ =>
      exact bind (ih callee) fun f _ => bind (args as (argsKeep_of ih as)) fun _ _ =>
        callAs D ih false f (placesAvoid_nil _ _)
    case letIn x τ init body =>
      exact bind (ih init) fun v _ => withInit x init v (ih body) (hide_nil_sub x _)
    case varIn x τ init body =>
      exact bind (ih init) fun v _ => withInit x init v (ih body) (hide_nil_sub x _)
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      exact assign x (fun i _ => ih i) (ih value) fun _ _ _ _ _ _ => avoids_nil _
    case seq a b => exact bind (ih a) fun _ _ => ih b
    case «if» c τ a b =>
      exact bind (bind (ih c) fun _ _ => asBool) fun v _ => ite v (ih a) (ih b)
    case «match» e τ arms =>
      exact bind (ih e) fun v _ => select (fun arm _ => ⟨ihR arm.body _, fun g _ => ihR g _⟩) v
    case «for» x τ e body => exact loop x (ih e) (ih body) (hide_nil_sub x _)
    case raise e => exact bind (ih e) fun v _ => throw v
    case «try» e => exact ih e
    case form _ e => exact ih e
    case tryCatch e E x h τ =>
      exact handle (ih e) fun err => withVar x err (ih h) (hide_nil_sub x _)
    case «while» c body => exact whileLoop (ih c) (ih body) (ih _)
    case «loop» body => exact loopForever (ih body) (ih _)
    case «break» => exact jump _
    case «continue» => exact jump _
    case «return» e => exact bind (ih e) fun v _ => jump _
    case perform op e => exact bind (ih e) fun v _ => perform op v
    case withH E c h b =>
      exact bind (ih h) fun hv _ => withHandler D ih E c hv (ih b)
    case held ns hs b =>
      exact bind (list hs fun e _ => ih e) fun vs _ => held _ vs (ihR b _)

end Stilt
