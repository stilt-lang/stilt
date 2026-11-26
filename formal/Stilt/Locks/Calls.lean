import Stilt.Locks.Runs

/-!
# Calls that take no cell

A call of a lock-free function value, with lock-free arguments, takes what its body takes:
entering it binds lock-free values, its body holds no site of `locks`, a closure's by the
value and a declared function's because the function is outside the set that has the fact,
and leaving it writes lock-free values back. A method names a function of an impl, which
`Expr.lockFree` asked to be outside the set (shared.locks).
-/

namespace Stilt

variable {D : Decls} {L : List Name}

namespace Eval.TakesNone

variable (w : WriteBack)

/-- A call of a function value whose body takes no cell. -/
theorem invoke {captured : List (Name × Value)} (hc : ∀ xv ∈ captured, xv.2.LockFree D L)
    {params : List Param} {passed : List Passed} (hp : ∀ q ∈ passed, q.LockFree D L)
    {body : Eval Copy.State Value} (hb : Eval.TakesNone D L (Value.LockFree D L) body) :
    Eval.TakesNone D L (Value.LockFree D L)
      (Eval.invoke (Copy.memoryWith w) captured params passed body) := by
  intro s hs
  unfold Eval.invoke
  cases hbind : bindArgs params passed with
  | none => trivial
  | some bound =>
    have hsnd := (InPlace.bindArgs_spec hbind).2
    have hbound : ∀ ya ∈ bound, ya.2.LockFree D L := fun ya hya =>
      hp _ (hsnd ▸ List.mem_map_of_mem hya)
    dsimp only
    cases he : (Copy.memoryWith w).enter s captured bound with
    | error f => exact Outcome.TakesNone.fault (.refl s.2)
    | ok callee =>
      obtain ⟨fr, hfr, rfl⟩ := Frames.withWorld_enter_ok _ he
      exact Outcome.TakesNone.leaveCall w hs
        (hb (fr, s.2)
          (Frame.LockFree.enter hs bound (fun _ hm => hc _ hm) hbound (by exact hfr)))

/-- A call of a lock-free function value, in declarations whose functions outside `L` hold no
site of `locks`. -/
theorem callAs (hD : D.LocksClosed L) {run : Expr → Eval Copy.State Value}
    (h : LockFreeRun D L run) (control : Bool) {f : Value} (hf : f.LockFree D L)
    {passed : List Passed} (hp : ∀ q ∈ passed, q.LockFree D L) :
    Eval.TakesNone D L (Value.LockFree D L)
      (Eval.callAs D (Copy.memoryWith w) run control f passed) := by
  unfold Eval.callAs
  by_cases hg : (!control && f.takesControl D) = true
  · rw [ite_eq_left hg]; exact stuck
  · rw [ite_eq_right hg]
    cases f with
    | closure captured params result ρ body =>
      cases hf with
      | closure hb hc => exact invoke w hc hp (h body hb)
    | function name types rows =>
      cases hf with
      | function hn =>
        unfold Eval.call
        dsimp only
        cases hd : D.fn? name with
        | none => exact stuck
        | some d =>
          have hname : d.name = name := by simpa using List.find?_some hd
          have hb := hD d (List.mem_of_find?_eq_some hd) (hname ▸ hn)
          refine invoke w (captured := []) (by simp) hp (h _ ?_)
          rw [Expr.lockFree_substRows, Expr.lockFree_substTys, hb]
    | _ => exact stuck

/-- `Trait.m` at a type: the function of the impl it finds, which no site of `locks` asked
to have the fact. -/
theorem method {t m : Name} (τ : Ty) (hm : D.methodLocks L t m = false) :
    Eval.TakesNone D L (Value.LockFree D L) (Eval.method D t m τ : Eval Copy.State Value) := by
  unfold Eval.method
  split
  · rename_i hd hh
    split
    · rename_i i hi
      refine pure (.function fun hmem => ?_)
      have hmem' := List.mem_of_find?_eq_some hi
      have hp := List.find?_some hi
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      have := List.any_eq_false.1 hm i hmem'
      simp [hp.1, hp.2, hmem] at this
    · exact stuck
  · exact stuck

end Eval.TakesNone

end Stilt
