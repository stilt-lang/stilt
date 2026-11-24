import Stilt.Windows.Steps
import Stilt.Windows.Through.Parts

/-!
# What leaves a call or a block under a handler

A value the checks accept holds no window, nor does a value read through its windows. A call
ends with no `return`, since it ends its body's (`noRet_callAs`), and the model of windows reads
the error a call raises through its windows when the call ends, so a clause called as that
model calls it raises an error and returns a value that hold no window (`escFree_call`;
views.escaping and handlers.with).
-/

namespace Stilt

namespace Windows

variable {D : Decls}

/-! ## Values that hold no window -/

theorem free_of_nil {v : Value} (h : ∀ w, w ∉ windowsOf v) : Free v :=
  List.eq_nil_iff_forall_not_mem.2 h

/-- A value the checks accept holds no window. -/
theorem _root_.Stilt.Value.Viewed.free {v : Value} (h : v.Viewed D) : Free v := by
  induction h with
  | record _ ih =>
    refine free_of_nil fun w hw => ?_
    obtain ⟨p, hp, hw⟩ := mem_windowsOfFields.1 hw
    rw [ih p hp] at hw
    cases hw
  | variant _ ih => exact windowsOfValues_nil_of_forall ih
  | list _ ih => exact windowsOfValues_nil_of_forall ih
  | _ => rfl

/-- What a map of windows gives holds no window when what it gives for each window holds
none. -/
theorem mapWindows_free_out {f : Nat → Path → List (Int × Int) → Except Fault Value}
    (hf : ∀ l p r d, f l p r = .ok d → Free d) {v u : Value} (h : mapWindows f v = .ok u) :
    Free u := by
  obtain ⟨v', h₁, -, h₃⟩ :=
    mapWindows_partly (g := f) (P := fun _ => False) v h fun _ _ => .inr ⟨rfl, hf _ _ _⟩
  rw [h] at h₁
  cases h₁
  exact free_of_nil fun w hw => (h₃ w hw).2

/-- A value read through its windows holds none. -/
theorem free_of_resolveAt (st : List (Option Value)) :
    ∀ (n : Nat) {v u : Value}, resolveAt st n v = .ok u → Free u
  | 0, _, _, h => mapWindows_free_out (fun _ _ _ _ h => by cases h) h
  | n + 1, _, _, h => by
    refine mapWindows_free_out (fun l p r d hd => ?_) h
    cases hp : part st l p r with
    | error _ => rw [hp] at hd; cases hd
    | ok x =>
      rw [hp] at hd
      exact free_of_resolveAt st n hd

theorem free_of_resolve {st : List (Option Value)} {v u : Value} (h : resolve st v = .ok u) :
    Free u :=
  free_of_resolveAt st _ h

/-! ## Outcomes whose escaping values hold no window -/

/-- An outcome that ends with no `return`, in each rest of a performance too. -/
def _root_.Stilt.Outcome.NoRet {σ : Type} : Outcome σ Value → Prop
  | .jumped (.ret _) _ => False
  | .performed _ _ _ k => ∀ w x, (k w x).NoRet
  | _ => True

/-- An outcome whose raised error and returned value hold no window, in each rest of a
performance too. -/
def _root_.Stilt.Outcome.EscFree : Outcome WState Value → Prop
  | .raised e _ => Free e
  | .jumped (.ret v) _ => Free v
  | .performed _ _ _ k => ∀ w x, (k w x).EscFree
  | _ => True

theorem noRet_fault {σ : Type} (f : Fault) (s : σ) :
    (Outcome.fault f s : Outcome σ Value).NoRet := by
  cases f <;> trivial

theorem escFree_fault (f : Fault) (s : WState) :
    (Outcome.fault f s : Outcome WState Value).EscFree := by
  cases f <;> trivial

/-- A call's outcome ends with no `return`: a call ends a `return` of its body. -/
theorem noRet_leaveCall {σ : Type} (M : Memory σ) (bound : List (Name × Passed)) (s : σ) :
    ∀ o : Outcome σ Value, (o.leaveCall M bound s).NoRet
  | .performed op v s' k => by
    simp only [Outcome.leaveCall]
    split
    · exact fun w x => noRet_leaveCall M bound s (k w x)
    · exact noRet_fault _ _
  | .jumped (.ret v) s' => by
    simp only [Outcome.leaveCall]
    split
    · trivial
    · exact noRet_fault _ _
  | .done .. | .raised .. | .panicked .. => by
    simp only [Outcome.leaveCall]
    split
    · trivial
    · exact noRet_fault _ _
  | .jumped .brk _ | .jumped .cont _ | .outOfFuel | .stuck => trivial

theorem noRet_invoke {σ : Type} (M : Memory σ) (captured : List (Name × Value))
    (params : List Param) (args : List Passed) (body : Eval σ Value) (s : σ) :
    (Eval.invoke M captured params args body s).NoRet := by
  unfold Eval.invoke
  split
  · trivial
  · split
    · exact noRet_fault _ _
    · exact noRet_leaveCall _ _ _ _

theorem noRet_callAs {σ : Type} (D : Decls) (M : Memory σ) (run : Expr → Eval σ Value)
    (ctl : Bool) (f : Value) (args : List Passed) (s : σ) :
    (Eval.callAs D M run ctl f args s).NoRet := by
  unfold Eval.callAs Eval.call
  split
  · exact noRet_fault _ _
  · split
    · exact noRet_invoke _ _ _ _ _ _
    · rename_i n _ _ _
      cases D.fn? n with
      | some _ => exact noRet_invoke _ _ _ _ _ _
      | none => exact noRet_fault _ _
    · exact noRet_fault _ _

/-- A call that ended, its callee's locations freed: its raised error holds no window. -/
theorem escFree_settle (n : Nat) : ∀ o : Outcome WState Value, o.NoRet → (o.settle n).EscFree
  | .done v s, _ => by
    simp only [Outcome.settle]
    split
    · trivial
    · exact escFree_fault _ _
  | .raised e s, _ => by
    simp only [Outcome.settle]
    split
    · rename_i w hw
      exact free_of_resolve hw
    · exact escFree_fault _ _
  | .jumped (.ret _) _, h => h.elim
  | .performed op v s k, h => fun w x => escFree_settle n (k w x) (h w x)
  | .jumped .brk _, _ | .jumped .cont _, _ | .panicked .., _ | .outOfFuel, _ | .stuck, _ => trivial

theorem escFree_resolveE (v : Value) (s : WState) : (resolveE v s).EscFree := by
  show (Eval.ofExcept _ s).EscFree
  unfold Eval.ofExcept
  split
  · trivial
  · exact escFree_fault _ _

theorem escFree_bind_resolveE : ∀ {o : Outcome WState Value}, o.EscFree →
    (o.bind fun v s => resolveE v s).EscFree
  | .done a s, _ => escFree_resolveE a s
  | .performed _ _ _ _, h => fun w x => escFree_bind_resolveE (h w x)
  | .raised .., h | .jumped .., h | .panicked .., h | .outOfFuel, h | .stuck, h => h

/-- A clause called as the model of windows calls it: its raised error holds no window. -/
theorem escFree_call (D : Decls) (run' : Expr → Eval WState Value) (ctl : Bool) (f : Value)
    (args : List Passed) (t : WState) : ((callSettled D run' ctl f args >>= resolveE) t).EscFree :=
  escFree_bind_resolveE (escFree_settle _ _ (noRet_callAs _ _ _ _ _ _ _))

end Windows

end Stilt
