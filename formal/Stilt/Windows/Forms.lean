import Stilt.Windows.Control
import Stilt.Windows.Handling
import Stilt.Windows.Values

/-!
# The forms that bind, choose, loop, jump and handle

Each form a step of both evaluators, on the relation of windows: from runs of its parts at the
fuel below, which keep the simulation in every context the checks read (`RunsAll`), both models
end alike, with values that the form's sources track.
-/

namespace Stilt

namespace Windows

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

/-- Runs of every expression at the fuel `n`, in every context whose scope keeps its bindings'
sources: what the main induction knows of the fuel below. -/
def RunsAll (D : Decls) (n : Nat) : Prop :=
  ∀ c' : Ctx, ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e →
    RunsIn D c' (Stilt.eval D InPlace.memory n) (Windows.eval D n) e₀ e

/-- A simulation under more reads around it is one under fewer: the reads only guard. -/
theorem SimP.widen {α β : Type} {X : List Shape} {Q : IState → WState → Prop}
    {G : α → β → IState → WState → Prop} {m : Eval IState α} {m' : Eval WState β}
    (h : SimP D { c with R := X ++ c.R } pend Q G m m') : SimP D c pend Q G m m' :=
  SimP.wait X (fun _ _ => []) (fun _ _ _ hq => h.mono (fun _ _ h' => h'.1 ▸ h'.2 ▸ hq)
    fun _ _ _ _ h => h) (fun _ _ _ _ _ h => nomatch h) fun _ _ _ _ _ _ h => nomatch h

/-- Values that fewer sources track, more track. -/
theorem Sim.sub {S S' : List Shape} {m : Eval IState Value} {m' : Eval WState Value}
    (h : Sim D c pend S m m') (hS : ∀ s ∈ S, s ∈ S') : Sim D c pend S' m m' :=
  h.mono (fun _ _ _ => trivial) fun _ _ _ _ h => ValG.sub hS h

/-- A value that holds no window, related to itself, tracked by any sources. -/
theorem ValG.free {S : List Shape} {v : Value} (hf : Free v) (hv : v.Viewed D) (si : IState)
    (sw : WState) : ValG D c S v v si sw := by
  refine ⟨VRel.free hf, fun win hw => ?_, hv⟩
  rw [hf] at hw
  cases hw

/-- A value that holds no window, the same on both sides, is tracked by any sources. -/
theorem SimP.ofFree {Q : IState → WState → Prop} {S : List Shape} {m : Eval IState Value}
    {m' : Eval WState Value} (h : SimP D c pend Q (FreeG D) m m') :
    SimP D c pend Q (ValG D c S) m m' :=
  h.mono (fun _ _ h => h) fun _ _ _ _ ⟨he, hf, hv⟩ => by
    subst he
    exact ValG.free hf hv _ _

/-- The sources that a raise or a return leaves the body with are the result's parameters. -/
theorem mem_of_leaves {P : List Name} {S : List Shape} (h : leaves P S = true) :
    ∀ s ∈ S, s ∈ P.map (fun y => (⟨y, []⟩ : Shape)) := by
  intro s hs
  have := List.all_eq_true.1 h s hs
  simp only [Bool.and_eq_true, List.contains_iff_mem, List.isEmpty_iff] at this
  obtain ⟨root, fields⟩ := s
  simp only at this
  obtain ⟨h₁, rfl⟩ := this
  exact List.mem_map.2 ⟨root, h₁, rfl⟩

/-- The value `unit`, on both sides. -/
theorem SimP.unitVal {S : List Shape} : Sim D c pend S (Pure.pure .unit) (Pure.pure .unit) :=
  SimP.const .unit rfl .unit

/-- A jump that carries no value. -/
theorem SimP.jumpPlain {α β : Type} {Q : IState → WState → Prop}
    {G : α → β → IState → WState → Prop} (j : Jump) (hj : j = .brk ∨ j = .cont) :
    SimP D c pend Q G (Eval.jump j) (Eval.jump j) := by
  intro si sw hp _ _
  rcases hj with rfl | rfl
  · exact ⟨hp, rfl, trivial⟩
  · exact ⟨hp, rfl, trivial⟩

/-- Two branches chosen by the same Boolean. -/
theorem SimP.branch {α β : Type} {G : α → β → IState → WState → Prop}
    {f : Bool → Eval IState α} {f' : Bool → Eval WState β}
    (h : ∀ b : Bool, SimP D c pend (fun _ _ => True) G (f b) (f' b)) (b b' : Bool) :
    SimP D c pend (Same b b') G (f b) (f' b') := by
  intro si sw hp hg (hq : b = b')
  subst hq
  exact h b si sw hp hg trivial

/-! ## Sequences, choices and loops -/

theorem SimP.seq (n : Nat) (hΓ : ScopeKeeps D c.Γ) {a₀ a b₀ b : Expr} (ha : Expr.Inst D a₀ a)
    (hb : Expr.Inst D b₀ b) (ih : RunsAll D n) (hr : (Expr.seq a₀ b₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.seq a₀ b₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.seq a₀ b₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.seq a b)) (Windows.eval D (n + 1) (.seq a b)) := by
  simp only [Expr.viewsRead, Expr.contained, Bool.and_eq_true] at hr hc
  exact SimP.bind (ih c hΓ a₀ a ha c.R pend hr.1 hc.1) fun _ _ =>
    (ih c hΓ b₀ b hb c.R pend hr.2 hc.2).mono (fun _ _ _ => trivial) fun _ _ _ _ h => h

theorem SimP.cond (n : Nat) (hΓ : ScopeKeeps D c.Γ) {k₀ k a₀ a b₀ b : Expr} (τ₀ τ : Ty)
    (hk : Expr.Inst D k₀ k) (ha : Expr.Inst D a₀ a) (hb : Expr.Inst D b₀ b) (ih : RunsAll D n)
    (hr : (Expr.if k₀ τ₀ a₀ b₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.if k₀ τ₀ a₀ b₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.if k₀ τ₀ a₀ b₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.if k τ a b))
      (Windows.eval D (n + 1) (.if k τ a b)) := by
  simp only [Expr.viewsRead, Expr.contained, Bool.and_eq_true] at hr hc
  refine SimP.bind (SimP.bind (ih c hΓ k₀ k hk c.R pend hr.1.1 hc.1.1) fun _ _ =>
    SimP.asBool fun _ _ h => h.1) (SimP.branch fun v => ?_)
  exact SimP.ite v (Sim.sub (ih c hΓ a₀ a ha c.R pend hr.1.2 hc.1.2)
    fun _ h => List.mem_append_left _ h) (Sim.sub (ih c hΓ b₀ b hb c.R pend hr.2 hc.2)
    fun _ h => List.mem_append_right _ h)

theorem SimP.whileLoop (n : Nat) (hΓ : ScopeKeeps D c.Γ) {k₀ k b₀ b : Expr}
    (hk : Expr.Inst D k₀ k) (hb : Expr.Inst D b₀ b) (ih : RunsAll D n)
    (hr : (Expr.while k₀ b₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.while k₀ b₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.while k₀ b₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.while k b))
      (Windows.eval D (n + 1) (.while k b)) := by
  have hl := ih c hΓ _ _ (Expr.Inst.while hk hb) c.R pend hr hc
  simp only [Expr.viewsRead, Expr.contained, Bool.and_eq_true] at hr hc
  refine SimP.bind (SimP.bind (ih c hΓ k₀ k hk c.R pend hr.1 hc.1) fun _ _ =>
    SimP.asBool fun _ _ h => h.1) (SimP.branch fun v => SimP.ite v ?_ SimP.unitVal)
  exact SimP.bind (SimP.turn (ih c hΓ b₀ b hb c.R pend hr.2 hc.2))
    (SimP.branch fun g => SimP.ite g hl SimP.unitVal)

theorem SimP.loopBody (n : Nat) (hΓ : ScopeKeeps D c.Γ) {b₀ b : Expr} (hb : Expr.Inst D b₀ b)
    (ih : RunsAll D n) (hr : (Expr.loop b₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.loop b₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.loop b₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.loop b)) (Windows.eval D (n + 1) (.loop b)) := by
  have hl := ih c hΓ _ _ (Expr.Inst.loop hb) c.R pend hr hc
  simp only [Expr.viewsRead, Expr.contained] at hr hc
  exact SimP.bind (SimP.turn (ih c hΓ b₀ b hb c.R pend hr hc))
    (SimP.branch fun g => SimP.ite g hl SimP.unitVal)

theorem SimP.forLoop (n : Nat) (hΓ : ScopeKeeps D c.Γ) {x : Name} (τ₀ τ : Ty) {e₀ e b₀ b : Expr}
    (he : Expr.Inst D e₀ e) (hb : Expr.Inst D b₀ b) (ih : RunsAll D n)
    (hr : (Expr.for x τ₀ e₀ b₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.for x τ₀ e₀ b₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.for x τ₀ e₀ b₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.for x τ e b))
      (Windows.eval D (n + 1) (.for x τ e b)) := by
  simp only [Expr.viewsRead, Expr.contained, Bool.and_eq_true] at hr hc
  exact SimP.loop (τ := τ₀) (ih c hΓ e₀ e he c.R pend hr.1 hc.1)
    (ih (c.scope x ⟨some τ₀, if τ₀.holdsView D then [] else [], false⟩
      (hide (e₀.sources D c.Γ ++ c.R) x) (c.P.filter (· != x))) (hΓ.bind x τ₀ []) b₀ b hb
      (hide (e₀.sources D c.Γ ++ c.R) x) pend hr.2 hc.2)

/-! ## Bindings and the forms that read a part -/

theorem SimP.bindLet (n : Nat) (hΓ : ScopeKeeps D c.Γ) {x : Name} {τ₀ τ : Ty} {i₀ i b₀ b : Expr}
    (hτ : TyInst D τ₀ τ) (hi : Expr.Inst D i₀ i) (hb : Expr.Inst D b₀ b) (ih : RunsAll D n)
    (hr : (Expr.letIn x τ₀ i₀ b₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.letIn x τ₀ i₀ b₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.letIn x τ₀ i₀ b₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.letIn x τ i b))
      (Windows.eval D (n + 1) (.letIn x τ i b)) := by
  simp only [Expr.viewsRead, Expr.contained, Bool.and_eq_true, List.all_eq_true,
    bne_iff_ne, ne_eq] at hr hc
  have hl : (ViewScope.bind D c.Γ x τ₀ (i₀.sources D c.Γ)).lookup x =
      some ⟨some τ₀, if τ₀.holdsView D then i₀.sources D c.Γ else [], false⟩ := by
    simp [ViewScope.bind]
  rw [hl] at hr
  exact SimP.letIn hτ i i (ih c hΓ i₀ i hi c.R pend hr.1 hc.1)
    (ih (c.scope x ⟨some τ₀, if τ₀.holdsView D then i₀.sources D c.Γ else [], false⟩
      (hide ((if τ₀.holdsView D then i₀.sources D c.Γ else []) ++ c.R) x)
      (c.P.filter (· != x))) (hΓ.bind x τ₀ (i₀.sources D c.Γ)) b₀ b hb _ pend hr.2 hc.2.1) hc.2.2

theorem SimP.bindVar (n : Nat) (hΓ : ScopeKeeps D c.Γ) {x : Name} {τ₀ τ : Ty} {i₀ i b₀ b : Expr}
    (hτ : TyInst D τ₀ τ) (hi : Expr.Inst D i₀ i) (hb : Expr.Inst D b₀ b) (ih : RunsAll D n)
    (hr : (Expr.varIn x τ₀ i₀ b₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.varIn x τ₀ i₀ b₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.varIn x τ₀ i₀ b₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.varIn x τ i b))
      (Windows.eval D (n + 1) (.varIn x τ i b)) :=
  SimP.bindLet n hΓ hτ hi hb ih hr hc

theorem SimP.fieldOf (n : Nat) (hΓ : ScopeKeeps D c.Γ) {e₀ e : Expr} (f : Name)
    (he : Expr.Inst D e₀ e) (ih : RunsAll D n)
    (hr : (Expr.field e₀ f).viewsRead D c.Γ c.R = true)
    (hc : (Expr.field e₀ f).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.field e₀ f).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.field e f))
      (Windows.eval D (n + 1) (.field e f)) :=
  Sim.sub (SimP.field (ih c hΓ e₀ e he c.R pend hr hc) f) fun _ h => nomatch h

theorem SimP.indexOf (n : Nat) (hΓ : ScopeKeeps D c.Γ) {e₀ e i₀ i : Expr}
    (he : Expr.Inst D e₀ e) (hi : Expr.Inst D i₀ i) (ih : RunsAll D n)
    (hr : (Expr.index e₀ i₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.index e₀ i₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.index e₀ i₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.index e i))
      (Windows.eval D (n + 1) (.index e i)) := by
  simp only [Expr.viewsRead, Expr.contained, Bool.and_eq_true] at hr hc
  exact Sim.sub (SimP.index (ih c hΓ e₀ e he c.R pend hr.1 hc.1)
    (SimP.widen (ih c hΓ i₀ i hi _ pend hr.2 hc.2))) fun _ h => nomatch h

theorem SimP.opOf (n : Nat) (hΓ : ScopeKeeps D c.Γ) (o₀ o : Op) {es₀ es : List Expr}
    (his : ExprsInst D es₀ es) (ih : RunsAll D n)
    (hr : (Expr.op o₀ es₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.op o₀ es₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.op o₀ es₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.op o es))
      (Windows.eval D (n + 1) (.op o es)) :=
  SimP.op (SimP.list his c pend (fun e₀ e _ he => ih c hΓ e₀ e he) hr hc) o

end Windows

end Stilt
