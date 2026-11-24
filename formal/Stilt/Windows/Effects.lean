import Stilt.Windows.Forms

/-!
# Raises, returns, catches, performances and handlers

The forms that leave the body or come back to it, on the relation of windows: a raised or
returned value's sources are the result's parameters (`leaves`), a caught error and a performed
value are read through their windows, and a handler's clauses are called as a call of a value
is (`CallsValues`).
-/

namespace Stilt

namespace Windows

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

/-- Calls of a closure or a function on one argument that holds no window, as a handler calls
its clauses: both models end alike, with the same value, read through its windows. -/
def CallsValues (D : Decls) (c : Ctx) (pend : List (Window × Value)) (n : Nat) : Prop :=
  ∀ ctl f, f.Viewed D → (¬NotCallable f) → ∀ v, Free v → v.Viewed D →
    SimP D c pend (fun _ _ => True) (FreeG D)
      (Eval.callAs D InPlace.memory (Stilt.eval D InPlace.memory n) ctl f [.value v])
      (callSettled D (Windows.eval D n) ctl f [.value v] >>= resolveE)

theorem SimP.raiseOf (n : Nat) (hΓ : ScopeKeeps D c.Γ) {e₀ e : Expr} (he : Expr.Inst D e₀ e)
    (ih : RunsAll D n) (hr : (Expr.raise e₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.raise e₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.raise e₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.raise e)) (Windows.eval D (n + 1) (.raise e)) := by
  simp only [Expr.viewsRead, Expr.contained, Bool.and_eq_true] at hr hc
  exact SimP.bind (ih c hΓ e₀ e he c.R pend hr hc.1) fun _ _ => SimP.throw (mem_of_leaves hc.2)

theorem SimP.returnOf (n : Nat) (hΓ : ScopeKeeps D c.Γ) {e₀ e : Expr} (he : Expr.Inst D e₀ e)
    (ih : RunsAll D n) (hr : (Expr.return e₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.return e₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.return e₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.return e))
      (Windows.eval D (n + 1) (.return e)) := by
  simp only [Expr.viewsRead, Expr.contained, Bool.and_eq_true] at hr hc
  exact SimP.bind (ih c hΓ e₀ e he c.R pend hr hc.1) fun _ _ => SimP.jumpRet (mem_of_leaves hc.2)

theorem SimP.catchOf (n : Nat) (hΓ : ScopeKeeps D c.Γ) {e₀ e h₀ h : Expr} (E₀ E : Ty) (x : Name)
    (τ₀ τ : Ty) (he : Expr.Inst D e₀ e) (hh : Expr.Inst D h₀ h) (ih : RunsAll D n)
    (hr : (Expr.tryCatch e₀ E₀ x h₀ τ₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.tryCatch e₀ E₀ x h₀ τ₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.tryCatch e₀ E₀ x h₀ τ₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.tryCatch e E x h τ))
      (Windows.eval D (n + 1) (.tryCatch e E x h τ)) := by
  simp only [Expr.viewsRead, Expr.contained, Bool.and_eq_true, List.all_eq_true,
    bne_iff_ne, ne_eq] at hr hc
  exact SimP.tryCatch (ih c hΓ e₀ e he c.R pend hr.1 hc.1.1)
    (ih (c.scope x ⟨some E₀, if E₀.holdsView D then [] else [], false⟩ (hide c.R x)
      (c.P.filter (· != x))) (hΓ.bind x E₀ []) h₀ h hh (hide c.R x) pend hr.2 hc.1.2) hc.2

theorem SimP.performOf (n : Nat) (hΓ : ScopeKeeps D c.Γ) (op : Operation) {e₀ e : Expr}
    (he : Expr.Inst D e₀ e) (ih : RunsAll D n)
    (hr : (Expr.perform op e₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.perform op e₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.perform op e₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.perform op e))
      (Windows.eval D (n + 1) (.perform op e)) := by
  simp only [Expr.viewsRead, Expr.contained] at hr hc
  refine SimP.bind (SimP.readThrough (ih c hΓ e₀ e he c.R pend hr hc)) fun v w => ?_
  intro si sw hp hg hq
  obtain ⟨rfl, hf, hv⟩ := hq
  exact SimP.perform (Q := fun _ _ => True)
    (fun _ si sw _ hu huv => ValG.free hu huv si sw) hf hv
    si sw hp hg trivial

theorem SimP.handleOf (n : Nat) (hΓ : ScopeKeeps D c.Γ) (E : Name) (ctl : Bool) {h₀ h b₀ b : Expr}
    (hh : Expr.Inst D h₀ h) (hb : Expr.Inst D b₀ b) (ih : RunsAll D n)
    (hcall : CallsValues D c pend n)
    (hr : (Expr.withH E ctl h₀ b₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.withH E ctl h₀ b₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.withH E ctl h₀ b₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.withH E ctl h b))
      (Windows.eval D (n + 1) (.withH E ctl h b)) := by
  simp only [Expr.viewsRead, Expr.contained, Bool.and_eq_true] at hr hc
  refine SimP.bind (ih c hΓ h₀ h hh c.R pend hr.1 hc.1) fun hv hv' => ?_
  intro si sw hp hg hq
  exact SimP.ofFree (SimP.withHandler (clauses_of_vrel hq.1 hq.2.2) (hcall ctl)
    (ih c hΓ b₀ b hb c.R pend hr.2 hc.2)) si sw hp hg trivial

end Windows

end Stilt
