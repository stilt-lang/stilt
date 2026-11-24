import Stilt.Writes.Within

/-!
# The cases of the simulation

`Simulates n` says that evaluating with fuel `n` keeps the simulation: from
states that agree, an expression that obeys the law of exclusivity with the
reads and writes of views, whose writable bindings write what their views
have as sources, and whose views don't outlive their sources, ends alike in
both models (`Post`). Each lemma here proves one case of the evaluator with
fuel `n + 1` from it, stated on the step the evaluator takes.
-/

namespace Stilt.Writes

open Stilt.Views (Store bounded slice cell source Pointwise ExceptAgree Agree Model)

variable {n : Nat}

/-- Evaluating with fuel `n` keeps the simulation. -/
def Simulates (n : Nat) : Prop :=
  ∀ (e : WExpr) (Γ : Sources) (R W : List Name) (sw sc : WState),
    e.exclusive true Γ R W = true → e.contained Γ = true → e.bound = true →
    StateAgrees sw sc → InScope Γ R W sw.env →
    Agree (Post (R ++ W) (e.sources Γ) (e.writes = true) sw)
      (weval .window n e sw) (weval .copy n e sc)

theorem InScope.after {Γ : Sources} {R W F : List Name} {s₀ s : WState}
    (h : InScope Γ R W s₀.env) (hs : Steps F s₀ s) : InScope Γ R W s.env :=
  hs.env ▸ h

/-- More reads keep what the analysis knows. -/
theorem InScope.reads {Γ : Sources} {R W : List Name} {env : List (Name × WBinding)}
    (h : InScope Γ R W env) (S : List Name) : InScope Γ (S ++ R) W env :=
  ⟨h.distinct, h.apart, fun x ℓ π a b hx => (h.guarded x ℓ π a b hx).mono fun z hz => by
    simp only [List.mem_append] at hz ⊢
    rcases hz with hz | hz <;> simp [hz], h.locked, h.sources⟩

theorem mem_reads {S R W : List Name} : ∀ z ∈ R ++ W, z ∈ (S ++ R) ++ W := fun z hz => by
  simp only [List.mem_append] at hz ⊢
  rcases hz with hz | hz <;> simp [hz]

theorem lift_agrees {P : WVal → WVal → Prop} (x : Except Fault Value)
    (h : ∀ v, P (.val v) (.val v)) : ExceptAgree P (lift x) (lift x) := by
  cases x
  · exact rfl
  · exact h _

namespace Simulates

variable (ih : Simulates n)
include ih

theorem value {e : WExpr} {Γ : Sources} {R W : List Name} {sw sc : WState}
    (hex : e.exclusive true Γ R W = true) (hco : e.contained Γ = true) (hbd : e.bound = true)
    (hst : StateAgrees sw sc) (hsc : InScope Γ R W sw.env) :
    Agree (Operand (R ++ W) sw) ((weval .window n e >>= Run.asVal) sw)
      ((weval .copy n e >>= Run.asVal) sc) :=
  Agree.bind (ih e Γ R W sw sc hex hco hbd hst hsc) fun _ _ _ _ hp =>
    hp.agrees.asVal fun _ => ⟨rfl, hp.states, hp.steps⟩

theorem int {e : WExpr} {Γ : Sources} {R W : List Name} {sw sc : WState}
    (hex : e.exclusive true Γ R W = true) (hco : e.contained Γ = true) (hbd : e.bound = true)
    (hst : StateAgrees sw sc) (hsc : InScope Γ R W sw.env) :
    Agree (Operand (R ++ W) sw) ((weval .window n e >>= Run.asInt) sw)
      ((weval .copy n e >>= Run.asInt) sc) :=
  Agree.bind (ih e Γ R W sw sc hex hco hbd hst hsc) fun _ _ _ _ hp =>
    hp.agrees.asInt fun _ => ⟨rfl, hp.states, hp.steps⟩

theorem vals {Γ : Sources} {R W : List Name} : ∀ (es : List WExpr) {sw sc : WState},
    exprsExclusive true Γ R W es = true → exprsContained Γ es = true → exprsBound es = true →
    StateAgrees sw sc → InScope Γ R W sw.env →
    Agree (Operand (R ++ W) sw) (Run.vals (weval .window n) es sw)
      (Run.vals (weval .copy n) es sc)
  | [], _, _, _, _, _, hst, _ => ⟨rfl, hst, Steps.refl _ _⟩
  | e :: es, _, _, hex, hco, hbd, hst, hsc => by
    simp only [exprsExclusive, exprsContained, exprsBound, Bool.and_eq_true] at hex hco hbd
    refine Agree.bind (ih.value hex.1 hco.1 hbd.1 hst hsc) fun s₁ sc₁ v v' ho₁ => ?_
    refine Agree.bind (vals es hex.2 hco.2 hbd.2 ho₁.states (hsc.after ho₁.steps))
      fun s₂ sc₂ vs vs' ho₂ => ?_
    exact ⟨by rw [ho₁.eq, ho₂.eq], ho₂.states, ho₁.steps.trans ho₂.steps fun _ h => h⟩

end Simulates

/-! ## Forms -/

section Forms

variable (ih : Simulates n) {Γ : Sources} {R W S : List Name} {P : Prop} {sw sc : WState}
  (hst : StateAgrees sw sc) (hsc : InScope Γ R W sw.env)
include ih hst hsc

omit ih in
/-- A variable, which E0429 lets the body read (projections.what-view-writes). -/
theorem sim_var {x : Name} (hW : readable true W x = true) (hP : ¬P) :
    Agree (Post (R ++ W) ((Γ.lookup x).getD []) P sw) (Eval.inspect (fun s => s.read x) sw)
      (Eval.inspect (fun s => s.read x) sc) := by
  have hx : x ∉ W := by simpa [readable] using hW
  exact Agree.inspect (Views.ExceptAgree.mono (hst.read hsc hx) fun rw rc _ ⟨hag, hcov⟩ =>
    ⟨hst, Steps.refl _ _, hag, hcov, fun h => absurd h hP⟩)

theorem sim_list {es : List WExpr} (hP : ¬P) (hex : exprsExclusive true Γ R W es = true)
    (hco : exprsContained Γ es = true) (hbd : exprsBound es = true) :
    Agree (Post (R ++ W) S P sw)
      ((Run.vals (weval .window n) es >>= fun vs => pure (.val (.list vs))) sw)
      ((Run.vals (weval .copy n) es >>= fun vs => pure (.val (.list vs))) sc) :=
  Agree.bind (ih.vals es hex hco hbd hst hsc) fun _ _ vs vs' ho => by
    cases ho.eq
    exact Post.val ho.states ho.steps hP

/-- `e[i]`: the index is evaluated while the view `e` reads its sources
(views.reads-that-last). -/
theorem sim_index {e i : WExpr} (hP : ¬P) (he : e.exclusive true Γ R W = true)
    (hi : i.exclusive true Γ (e.sources Γ ++ R) W = true) (hce : e.contained Γ = true)
    (hci : i.contained Γ = true) (hbe : e.bound = true) (hbi : i.bound = true) :
    Agree (Post (R ++ W) S P sw)
      ((weval .window n e >>= fun r => (weval .window n i >>= Run.asInt) >>= fun k =>
        Eval.inspect fun s => r.index s.store k) sw)
      ((weval .copy n e >>= fun r => (weval .copy n i >>= Run.asInt) >>= fun k =>
        Eval.inspect fun s => r.index s.store k) sc) :=
  Agree.bind (ih e Γ R W sw sc he hce hbe hst hsc) fun s₁ sc₁ rw rc hp =>
    Agree.bind (ih.int hi hci hbi hp.states ((hsc.after hp.steps).reads _))
      fun s₂ sc₂ k k' ho => by
        cases ho.eq
        obtain ⟨x, h₁, h₂⟩ := (hp.held ho.steps).index sc₂.store k
        refine Agree.inspect ?_
        show ExceptAgree _ (rw.index s₂.store k) (rc.index sc₂.store k)
        rw [h₁, h₂]
        exact lift_agrees _ fun _ =>
          Post.val ho.states (hp.steps.trans ho.steps mem_reads) hP

theorem sim_seq {a b : WExpr} (ha : a.exclusive true Γ R W = true)
    (hb : b.exclusive true Γ R W = true) (hca : a.contained Γ = true)
    (hcb : b.contained Γ = true) (hba : a.bound = true) (hbb : b.bound = true) :
    Agree (Post (R ++ W) (b.sources Γ) (b.writes = true) sw)
      ((weval .window n a >>= fun _ => weval .window n b) sw)
      ((weval .copy n a >>= fun _ => weval .copy n b) sc) :=
  Agree.bind (ih a Γ R W sw sc ha hca hba hst hsc) fun s₁ sc₁ _ _ hp =>
    (ih b Γ R W s₁ sc₁ hb hcb hbb hp.states (hsc.after hp.steps)).mono fun _ _ _ _ hp₂ =>
      ⟨hp₂.states, hp.steps.trans hp₂.steps fun _ h => h, hp₂.agrees,
        fun ℓ π a c he => hp.steps.env ▸ hp₂.within ℓ π a c he,
        fun h => hp.steps.env ▸ hp₂.pend h⟩

theorem sim_len {v : WExpr} (hP : ¬P) (hex : v.exclusive true Γ R W = true)
    (hco : v.contained Γ = true) (hbd : v.bound = true) :
    Agree (Post (R ++ W) S P sw)
      ((weval .window n v >>= fun r => Eval.ofExcept r.len >>= fun k => pure (.val (.int k))) sw)
      ((weval .copy n v >>= fun r => Eval.ofExcept r.len >>= fun k => pure (.val (.int k))) sc) :=
  Agree.bind (ih v Γ R W sw sc hex hco hbd hst hsc) fun s₁ sc₁ rw rc hp =>
    Agree.bind (Agree.ofExcept (Q := Operand (R ++ W) sw)
      (Views.ExceptAgree.mono hp.agrees.len fun _ _ _ h => ⟨h, hp.states, hp.steps⟩))
      fun _ _ k k' ho => by
        cases ho.eq
        exact Post.val ho.states ho.steps hP

/-- `v.view(a, b)`: the offsets are evaluated while `v` reads its sources
(views.reads-that-last), and the part reads (projections.writable-views). -/
theorem sim_sub {v a b : WExpr} (hP : ¬P) (hv : v.exclusive true Γ R W = true)
    (ha : a.exclusive true Γ (v.sources Γ ++ R) W = true)
    (hb : b.exclusive true Γ (v.sources Γ ++ R) W = true) (hcv : v.contained Γ = true)
    (hca : a.contained Γ = true) (hcb : b.contained Γ = true) (hbv : v.bound = true)
    (hba : a.bound = true) (hbb : b.bound = true) :
    Agree (Post (R ++ W) (v.sources Γ) P sw)
      ((weval .window n v >>= fun r => (weval .window n a >>= Run.asInt) >>= fun s =>
        (weval .window n b >>= Run.asInt) >>= fun t => Eval.ofExcept (r.sub s t)) sw)
      ((weval .copy n v >>= fun r => (weval .copy n a >>= Run.asInt) >>= fun s =>
        (weval .copy n b >>= Run.asInt) >>= fun t => Eval.ofExcept (r.sub s t)) sc) :=
  Agree.bind (ih v Γ R W sw sc hv hcv hbv hst hsc) fun s₁ sc₁ rw rc hp => by
    have hsc₁ := (hsc.after hp.steps).reads (v.sources Γ)
    refine Agree.bind (ih.int ha hca hba hp.states hsc₁) fun s₂ sc₂ x x' ho₂ => ?_
    refine Agree.bind (ih.int hb hcb hbb ho₂.states (hsc₁.after ho₂.steps))
      fun s₃ sc₃ y y' ho₃ => ?_
    cases ho₂.eq
    cases ho₃.eq
    have hsteps := ho₂.steps.trans ho₃.steps fun _ h => h
    exact Agree.ofExcept (Views.ExceptAgree.mono (Agrees.sub (hp.held hsteps) x y)
      fun _ _ _ ⟨hag, hw⟩ =>
      ⟨ho₃.states, hp.steps.trans hsteps mem_reads, hag, fun ℓ π c d he => by
        obtain ⟨c', d', hrw⟩ := hw ℓ π c d he
        exact hp.within ℓ π c' d' hrw, fun h => absurd h hP⟩)

/-- `let` and `var`: the rest of the block runs with the binding, which holds
its initializer's sources as reads, or, when it is writable, as writes
(projections.what-view-writes and projections.writable-bindings), and gives a value that reads none of the binding
(views.escaping). -/
theorem sim_bind {w : Bool} {x : Name} {init body : WExpr}
    (hi : init.exclusive true Γ R W = true)
    (hb : body.exclusive true ((x, held w x (init.sources Γ)) :: Γ)
      (hide (readsIn w (init.sources Γ) R) x) (hide (writesIn w (init.sources Γ) W) x) = true)
    (hci : init.contained Γ = true) (hcb : body.contained ((x, held w x (init.sources Γ)) :: Γ) = true)
    (hroot : (body.sources ((x, held w x (init.sources Γ)) :: Γ)).all (· != x) = true)
    (hbi : init.bound = true) (hbb : body.bound = true) (hw : w = true → init.writes = true) :
    Agree (Post (R ++ W) (body.sources ((x, held w x (init.sources Γ)) :: Γ)) (body.writes = true) sw)
      ((weval .window n init >>= fun r => Run.within w x r (weval .window n body)) sw)
      ((weval .copy n init >>= fun r => Run.within w x r (weval .copy n body)) sc) :=
  Agree.bind (ih init Γ R W sw sc hi hci hbi hst hsc) fun s₁ sc₁ rw rc hp => by
    refine (Agree.within hp.states (hsc.after hp.steps) hp.agrees
      (fun ℓ π a b he => hp.steps.env ▸ hp.within ℓ π a b he)
      (fun h => hp.steps.env ▸ hp.pend (hw h))
      fun sw' sc' hst' hsc' => ih body _ _ _ sw' sc' hb hcb hbb hst' hsc').mono
      fun s₂ sc₂ bw bc hcl => ?_
    have hx : ∀ y ∈ body.sources ((x, held w x (init.sources Γ)) :: Γ), y ≠ x := fun y hy => by
      simpa using List.all_eq_true.1 hroot y hy
    obtain ⟨hag, hcov, hpend⟩ := hcl.value hx
    exact ⟨hcl.states, hp.steps.trans hcl.steps fun _ h => h, hag,
      fun ℓ π a b he => hp.steps.env ▸ hcov ℓ π a b he, fun h => hp.steps.env ▸ hpend h⟩

end Forms

end Stilt.Writes
