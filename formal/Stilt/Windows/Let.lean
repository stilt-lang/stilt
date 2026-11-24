import Stilt.Windows.Scope
import Stilt.Windows.Handling.Escapes

/-!
# `let` and `var`

A binding's initializer runs, its value is kept for the binding's type (`keep`: read through its
windows unless the type keeps views), and the body runs in the binding's scope, whose reads hold
the binding's sources (views.reads-that-last). The checks give the scope: the body's value reads
no source of the binding's name (E0422), and the result's parameters drop the name.
-/

namespace Stilt

theorem Outcome.bind_assoc' {σ α β γ : Type} (o : Outcome σ α) (f : α → σ → Outcome σ β)
    (g : β → σ → Outcome σ γ) : (o.bind f).bind g = o.bind fun a s => (f a s).bind g := by
  induction o with
  | performed op v s k ih =>
    simp only [Outcome.bind]
    congr 1
    funext w x
    exact ih w x
  | _ => rfl

theorem Eval.bind_assoc' {σ α β γ : Type} (m : Eval σ α) (f : α → Eval σ β) (g : β → Eval σ γ) :
    (m >>= f) >>= g = m >>= fun a => f a >>= g :=
  funext fun s => Outcome.bind_assoc' (m s) _ _

namespace Windows

open InPlace (Ref)

variable {α β : Type} {D : Decls} {c : Ctx} {pend : List (Window × Value)}

theorem withInit_eq_in (x : Name) (init : Expr) (v : Value) (m : Eval IState α) :
    Eval.withInit InPlace.memory x init v m = Eval.withVar InPlace.memory x v m := by
  cases init <;> rfl

theorem withInit_eq_w (x : Name) (init : Expr) (v : Value) (m : Eval WState α) :
    Eval.withInit memory x init v m = Eval.withVar memory x v m := by
  cases init <;> rfl

theorem VRel.target_free {si : List Value} {sw : List (Option Value)} {w v : Value}
    (h : VRel si sw w v) : Free v :=
  free_of_resolve h.resolve

/-- A value read through its windows, on the windows' side only, as the in-place value. -/
theorem SimP.resolveRight {Q : IState → WState → Prop} {G : α → β → IState → WState → Prop}
    {v w : Value} {m : Eval IState α} {f' : Value → Eval WState β}
    (hQ : ∀ si sw, Q si sw → VRel si.1.store sw.1.store w v) (h : SimP D c pend Q G m (f' v)) :
    SimP D c pend Q G m (resolveE w >>= f') := by
  intro si sw hp hg hq
  have hr : (resolveE w >>= f') sw = f' v sw := by
    show (Eval.ofExcept (resolve sw.1.store w) sw).bind (fun a s => f' a s) = _
    rw [(hQ si sw hq).resolve]
    rfl
  rw [hr]
  exact h si sw hp hg hq

/-- A `let` or `var` binding: its initializer's value kept for its type, then its body in its
scope. -/
theorem SimP.letIn {x : Name} {τ₀ τ : Ty} (hτ : TyInst D τ₀ τ) (init init' : Expr)
    {X S : List Shape} {mi : Eval IState Value} {mi' : Eval WState Value}
    (hi : Sim D c pend X mi mi') {m : Eval IState Value} {m' : Eval WState Value}
    (hm : Sim D (c.scope x ⟨some τ₀, if τ₀.holdsView D then X else [], false⟩
      (hide ((if τ₀.holdsView D then X else []) ++ c.R) x) (c.P.filter (· != x))) pend S m m')
    (hS : ∀ s ∈ S, s.root ≠ x) :
    Sim D c pend S (mi >>= fun v => Eval.withInit InPlace.memory x init v m)
      ((mi' >>= keep D τ) >>= fun v => Eval.withInit memory x init' v m') := by
  rw [Eval.bind_assoc']
  refine SimP.bind hi fun v w => ?_
  simp only [withInit_eq_in, withInit_eq_w]
  intro si sw hp hg hq
  have hok : ScopeOk c x ⟨some τ₀, if τ₀.holdsView D then X else [], false⟩
      (hide ((if τ₀.holdsView D then X else []) ++ c.R) x) (c.P.filter (· != x)) :=
    ⟨rfl, fun t ht hx => mem_hide.2 ⟨List.mem_append_right _ ht, hx⟩,
      fun t ht => (mem_hide.1 ht).2, fun _ s hs hx => mem_hide.2 ⟨List.mem_append_left _ hs, hx⟩,
      fun y hy => (List.mem_filter.1 hy).1, fun hx => by simp at hx⟩
  have hsc := SimP.scope hok hS hm
  unfold keep
  split
  · rename_i hk
    refine hsc v w si sw hp hg ⟨hq.1, hq.2.2, ?_⟩
    have hh : τ₀.holdsView D = true := hτ.1 (by simp only [keepsView, Bool.and_eq_true] at hk; exact hk.1)
    simp only [Option.isSome_some, ↓reduceIte, hh]
    exact hq.2.1
  · refine SimP.resolveRight (fun si sw hq => hq.1) (fun si sw hp hg hq => ?_) si sw hp hg hq
    refine hsc v v si sw hp hg ⟨VRel.free hq.1.target_free, hq.2.2, ?_⟩
    simp only [Option.isSome_some, ↓reduceIte]
    intro win hw
    rw [hq.1.target_free] at hw
    cases hw

end Windows

end Stilt
