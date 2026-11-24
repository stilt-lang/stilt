import Stilt.Windows.Call.Pass

/-!
# A call

A call evaluates its callee, then its arguments from left to right, the callee's value waiting
while they run (values.left-to-right), then calls the callee's value: in the model of windows
with its `let` arguments kept for its parameters' types, its locations freed when it ends, and
its result read through unless the call's type is a view type (views.across-calls). While the
call runs, the views its value arguments pass are being read (E0423), and its `inout` arguments'
places are disjoint (E0402). Both models end alike, the call's value tracked by its sources: a
window it keeps is one an argument passed.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

theorem ArgsRel.resolved {Γ : ViewScope} {In : List (Name × Value)} {si : IState} {sw : WState} :
    ∀ {args₀ : List Arg} {ps ps' : List Passed}, ArgsRel D Γ In si sw args₀ ps ps' →
      InPlace.Sim.ArgsResolved args₀ ps
  | _, _, _, .nil => trivial
  | _, _, _, .value e _ _ _ h => by
    unfold Passed.ofArg
    split
    · exact h.resolved
    · exact h.resolved
  | _, _, _, .inout x hres h => ⟨rfl, hres, h.resolved⟩

/-- A value that can't be called is stuck when the model of windows calls it. -/
theorem call_notCallable {f : Value} (hf : NotCallable f) (run : Expr → Eval WState Value)
    (ps : List Passed) (τ : Ty) (s : WState) : Windows.call D run f ps τ s = .stuck := by
  have hpo : paramsOf D f = [] := by
    obtain ⟨h₁, h₂⟩ := hf
    unfold paramsOf
    split
    · exact absurd rfl (h₁ _ _ _ _ _)
    · exact absurd rfl (h₂ _ _ _)
    · rfl
  show ((passTo D (paramsOf D f) ps s).bind fun a s => _) = _
  rw [hpo]
  show (((Eval.callAs D memory run false f ps s).settle s.1.store.length).bind fun v s => _) = _
  rw [callAs_notCallable hf]
  rfl

/-- What a call gives, read through when its type is no view type: a value its sources track. -/
theorem SimP.result {c : Ctx} {pend : List (Window × Value)} {τ : Ty} {S : List Shape}
    {ps' : List Passed} {env : List (Name × Ref)}
    (hS : τ.isView D = true → ∀ a ∈ ps', ∀ w, a.value? = some w → ∀ win ∈ windowsOf w,
      Tracked env c.In S win)
    (u v : Value) :
    SimP D c pend (fun si₁ sw₁ => ValueG D ps' u v si₁ sw₁ ∧ sw₁.1.env = env) (ValG D c S)
      (Pure.pure u) (if τ.isView D then Pure.pure v else resolveE v) := by
  intro si sw hp _ ⟨hq, he⟩
  by_cases hv : τ.isView D = true
  · simp only [hv, ↓reduceIte]
    refine ⟨hp, rfl, hq.1, fun win hwin => ?_, hq.2.1⟩
    obtain ⟨a, ha, w, hw, w', hw', h₁, h₂⟩ := hq.2.2 win hwin
    rw [he]
    exact (hS hv a ha w hw w' hw').congr h₁ h₂
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    show Outcome.Rel _ (Outcome.done u si) (Eval.ofExcept (resolve sw.1.store v) sw)
    rw [hq.1.resolve]
    exact ⟨hp, rfl, VRel.free hq.2.1.free, fun _ h => absurd h (not_mem_of_free hq.2.1.free),
      hq.2.1⟩

/-- The call itself, once its callee and arguments are evaluated: the value passed alike, the
views the value arguments pass being read. -/
theorem SimP.callStep (hD : DeclsChecked D) {c : Ctx}
    {pend : List (Window × Value)} {n : Nat} (hΓ : ScopeKeeps D c.Γ) (ih : RunsAll D n)
    {f fw : Value} (hcl : CallLike D f fw) {args₀ : List Arg} {τ₀ τ : Ty} (hτ : TyInst D τ₀ τ)
    (hx : pairwiseDisjoint (inoutShapes args₀) = true)
    (hu : (inoutShapes args₀).all (unread (argViews D c.Γ args₀ ++ c.R)) = true)
    (X : List Shape) {ps ps' : List Passed} :
    SimP D c pend (fun si sw => ArgsRel D c.Γ c.In si sw args₀ ps ps')
      (ValG D c (if τ₀.mayBeView D then X ++ argsSources D c.Γ args₀ else []))
      (Eval.callAs D InPlace.memory (Stilt.eval D InPlace.memory n) false f ps)
      (Windows.call D (Windows.eval D n) fw ps' τ) := by
  refine SimP.wait (argViews D c.Γ args₀) (fun _ _ => []) (fun si sw _ hq => ?_)
    (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ _ h => by cases h)
  intro si' sw' hp hg ⟨h₁, h₂⟩
  subst h₁ h₂
  rcases hcl with ⟨rfl, hfv⟩ | ⟨hn, hn'⟩
  case inr =>
    show Outcome.Rel _ (Eval.callAs D InPlace.memory _ false f ps si')
      (Windows.call D _ fw ps' τ sw')
    rw [callAs_notCallable hn, call_notCallable hn']
    trivial
  have hd : sw'.1.env.Pairwise fun a b => a.2.Disjoint b.2 := by
    rw [hp.agree.env]; exact hp.agree.disjoint
  have hw : ∀ a ∈ ps', ∀ w, a.value? = some w → ∀ win ∈ windowsOf w,
      Watched (argViews D c.Γ args₀ ++ c.R) sw'.1.env win := fun a ha w hw' win hwin =>
    .inr (guarded_of_tracked hd (fun xv hxv w' hw'' => (hg.brought xv hxv w' hw'').2)
      (fun s hs => .inl (List.mem_append_left _ hs)) (hq.tracked a ha w hw' win hwin))
  have hrel := hq.passRel (c := { c with R := argViews D c.Γ args₀ ++ c.R })
    (by simpa only [List.append_assoc] using hu) hw
  obtain ⟨ps₁, hpt, hrel₁, hk₁, hsub⟩ := passTo_done (paramsOf D fw) hrel
  have hcomp := InPlace.compat_of_resolved hq.resolved ((pairwiseDisjoint_iff _).1 hx)
  show Outcome.Rel _ (Eval.callAs D InPlace.memory _ false fw ps si')
    ((passTo D (paramsOf D fw) ps' >>= fun args => _) sw')
  rw [bind_done_eq hpt, ← Eval.bind_pure' (Eval.callAs D InPlace.memory _ false fw ps)]
  refine SimP.bindEnv ((SimP.callValue hD ih false hfv).mono
    (fun si sw (h : si = si' ∧ sw = sw') => by obtain ⟨rfl, rfl⟩ := h; exact ⟨hrel₁, hcomp, hk₁⟩)
    fun _ _ _ _ h => h) (fun u v => ?_) si' sw' hp hg ⟨rfl, rfl⟩
  refine (SimP.result (env := sw'.1.env) (fun hv a ha w hw' win hwin => ?_) u v).mono
    (fun si₁ sw₁ ⟨hG, si₀, sw₀, ⟨_, hsw⟩, he⟩ => ⟨hG, by rw [he, hsw]⟩) fun _ _ _ _ h => h
  obtain ⟨a₀, ha₀, w₀, h₀, hm⟩ := hsub a ha w hw' win hwin
  have ht := hq.trackedSources hΓ a₀ ha₀ w₀ h₀ win hm
  simp only [hτ.2 hv, ↓reduceIte]
  exact ht.sub fun s hs => List.mem_append_right _ hs

/-- A call: its callee, its arguments while the callee's value waits, then the call, the views
its value arguments pass being read (views.across-calls). -/
theorem SimP.call (hD : DeclsChecked D) {c : Ctx}
    {pend : List (Window × Value)} (n : Nat) (hΓ : ScopeKeeps D c.Γ) (ih : RunsAll D n)
    {callee₀ callee : Expr} {args₀ args : List Arg} {τ₀ τ : Ty}
    (hi : Expr.Inst D (.call callee₀ args₀ τ₀) (.call callee args τ))
    (hr : (Expr.call callee₀ args₀ τ₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.call callee₀ args₀ τ₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.call callee₀ args₀ τ₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.call callee args τ))
      (Windows.eval D (n + 1) (.call callee args τ)) := by
  cases hi with
  | call hx hci hai hτ =>
  simp only [Expr.viewsRead, Bool.and_eq_true] at hr
  simp only [Expr.contained, Bool.and_eq_true] at hc
  obtain ⟨⟨hr₁, hr₂⟩, hr₃⟩ := hr
  show SimP D c pend _ _
    (Stilt.eval D InPlace.memory n callee >>= fun f =>
      Eval.args (Stilt.eval D InPlace.memory n) args >>= fun ps =>
        Eval.callAs D InPlace.memory (Stilt.eval D InPlace.memory n) false f ps)
    (Windows.eval D n callee >>= fun f =>
      Eval.args (Windows.eval D n) args >>= fun ps => Windows.call D (Windows.eval D n) f ps τ)
  refine SimP.bind (ih c hΓ _ _ hci c.R pend hr₁ hc.1) fun f fw => ?_
  refine (SimP.after (X := callee₀.sources D c.Γ) (Q := fun _ _ => True)
    fun si sw _ hvf _ => ?_).mono (fun _ _ h => ⟨h, trivial⟩) fun _ _ _ _ h => h
  have hcl := callLike_of_resolve hvf.1.1 hvf.1.2 hvf.2.2
  have ih₁ : ∀ e₀ e, Expr.Inst D e₀ e →
      RunsIn D { c with R := callee₀.sources D c.Γ ++ c.R } (Stilt.eval D InPlace.memory n)
        (Windows.eval D n) e₀ e :=
    fun e₀ e hi' X pend' hrx hcx => ih c hΓ e₀ e hi' X pend' hrx hcx
  refine SimP.bind ((SimP.args hai _ _ ih₁ hr₂ hc.2).mono (fun _ _ _ => trivial)
    fun _ _ _ _ h => h) fun ps ps' => ?_
  simp only [Expr.sources]
  exact SimP.callStep (c := { c with R := callee₀.sources D c.Γ ++ c.R }) hD hΓ ih hcl hτ
    hx (by simpa only [List.append_assoc] using hr₃) _

end Windows

end Stilt
