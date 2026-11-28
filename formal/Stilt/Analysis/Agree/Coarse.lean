import Stilt.Analysis.Agree.Stores

/-!
# Code analysed from no fact

The forms that the analysis reads as code keeping the facts on the bindings it doesn't write
have their parts analysed from no fact, which holds everywhere: so their release runs are their
runs from every state (`AgreeRun.eqTop`), and a step run by functions equal on those parts is
the same step (`Eval.args_congr`, `Eval.select_congr` and the others).
-/

namespace Stilt

variable {runR run : Expr → Eval Copy.State Value}

/-- A part analysed from no fact runs alike from every state. -/
theorem AgreeRun.eqTop (ih : AgreeRun runR run) {L : Bool} {d : Nat} {e : Expr}
    (h : (an L d .top e).ok = true) : runR e = run e :=
  funext fun s => (ih L d .top e (List.replicate d .unit) s h (by simp) (Facts.top_holds _)).1

theorem okExprs_all {L : Bool} {d : Nat} : ∀ {es : List Expr}, okExprs L d es = true →
    ∀ e ∈ es, (an L d .top e).ok = true
  | [], _, _, h => nomatch h
  | e :: es, h, e', he' => by
    simp only [okExprs, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h.1
    · exact okExprs_all h.2 e' he'

theorem okFields_all {L : Bool} {d : Nat} : ∀ {fs : List (Name × Expr)}, okFields L d fs = true →
    ∀ fe ∈ fs, (an L d .top fe.2).ok = true
  | [], _, _, h => nomatch h
  | (f, e) :: fs, h, fe, hfe => by
    simp only [okFields, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hfe with rfl | hfe
    · exact h.1
    · exact okFields_all h.2 fe hfe

theorem okPath_all {L : Bool} {d : Nat} : ∀ {ps : List Projection}, okPath L d ps = true →
    ∀ i, Projection.index i ∈ ps → (an L d .top i).ok = true
  | [], _, _, h => nomatch h
  | .field _ :: ps, h, i, hi => by
    simp only [okPath] at h
    rcases List.mem_cons.1 hi with h' | hi
    · cases h'
    · exact okPath_all h i hi
  | .index j :: ps, h, i, hi => by
    simp only [okPath, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hi with h' | hi
    · cases h'; exact h.1
    · exact okPath_all h.2 i hi

/-- Whether an argument's parts run alike under two functions. -/
def Arg.Alike {σ : Type} (r₁ r₂ : Expr → Eval σ Value) : Arg → Prop
  | .value e => r₁ e = r₂ e
  | .inout ⟨_, ps⟩ => ∀ i, Projection.index i ∈ ps → r₁ i = r₂ i

theorem okArgs_all (ih : AgreeRun runR run) {L : Bool} {d : Nat} : ∀ {args : List Arg},
    okArgs L d args = true → ∀ a ∈ args, a.Alike runR run
  | [], _, _, h => nomatch h
  | .value e :: args, h, a, ha => by
    simp only [okArgs, Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ih.eqTop h.1
    · exact okArgs_all ih h.2 a ha
  | .inout ⟨x, ps⟩ :: args, h, a, ha => by
    simp only [okArgs, Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact fun i hi => ih.eqTop (okPath_all h.1 i hi)
    · exact okArgs_all ih h.2 a ha

/-- Whether an arm's guard and body run alike under two functions. -/
def Arm.Alike {σ : Type} (r₁ r₂ : Expr → Eval σ Value) (a : Arm) : Prop :=
  r₁ a.body = r₂ a.body ∧ ∀ g, a.guard = some g → r₁ g = r₂ g

theorem okArms_all (ih : AgreeRun runR run) {L : Bool} {d : Nat} : ∀ {arms : List Arm},
    okArms L d arms = true → ∀ a ∈ arms, a.Alike runR run
  | [], _, _, h => nomatch h
  | ⟨p, bs, guard, body⟩ :: arms, h, a, ha => by
    simp only [okArms, Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · refine ⟨ih.eqTop h.1.2, fun g hg => ?_⟩
      simp only at hg
      subst hg
      exact ih.eqTop (by simpa [okGuard] using h.1.1)
    · exact okArms_all ih h.2 a ha

namespace Eval

variable {σ : Type} {r₁ r₂ : Expr → Eval σ Value}

theorem args_congr : ∀ {args : List Arg}, (∀ a ∈ args, a.Alike r₁ r₂) →
    Eval.args r₁ args = Eval.args r₂ args
  | [], _ => rfl
  | .value e :: args, h => by
    simp only [Eval.args]
    rw [show r₁ e = r₂ e from h _ List.mem_cons_self,
      args_congr fun a ha => h a (List.mem_cons_of_mem _ ha)]
  | .inout ⟨x, ps⟩ :: args, h => by
    simp only [Eval.args]
    rw [path_congr (h _ List.mem_cons_self), args_congr fun a ha => h a (List.mem_cons_of_mem _ ha)]

theorem guarded_congr {M : Memory σ} {bs : List Name} {g body : Expr} (hg : r₁ g = r₂ g)
    (hb : r₁ body = r₂ body) {next₁ next₂ : Eval σ Value} (hn : next₁ = next₂) :
    ∀ ways : List (List Value), Eval.guarded M r₁ bs g body next₁ ways =
      Eval.guarded M r₂ bs g body next₂ ways
  | [] => hn
  | us :: ways => by
    simp only [Eval.guarded, Eval.tryWay]
    rw [hg, hb, guarded_congr hg hb hn ways]

theorem select_congr {M : Memory σ} : ∀ {arms : List Arm}, (∀ a ∈ arms, a.Alike r₁ r₂) →
    ∀ v, Eval.select M r₁ arms v = Eval.select M r₂ arms v
  | [], _, _ => rfl
  | arm :: arms, h, v => by
    obtain ⟨hb, hg⟩ := h arm List.mem_cons_self
    have ih := select_congr (M := M) (fun a ha => h a (List.mem_cons_of_mem _ ha)) v
    simp only [Eval.select]
    split
    · rw [hb, ih]
    · rename_i g hga
      rw [guarded_congr (hg g hga) hb ih]

theorem loop_congr {M : Memory σ} {x : Name} {e b : Expr} (he : r₁ e = r₂ e) (hb : r₁ b = r₂ b) :
    Eval.loop M r₁ x e b = Eval.loop M r₂ x e b := by
  unfold Eval.loop
  rw [he, hb]

end Eval

/-- A step that keeps the state, ending with a value or a fault, from `Eval.method`. -/
theorem Eval.method_still (D : Decls) (t m : Name) (τ : Ty) (s : Copy.State) :
    (∃ v, (Eval.method D t m τ : Eval Copy.State Value) s = .done v s) ∨
      ∃ f, (Eval.method D t m τ : Eval Copy.State Value) s = Outcome.fault f s := by
  unfold Eval.method
  rcases τ.head? with _ | h
  · exact .inr ⟨.stuck, rfl⟩
  · dsimp only
    rcases D.traitImpl? t h with _ | _
    · exact .inr ⟨.stuck, rfl⟩
    · exact .inl ⟨_, rfl⟩

theorem Eval.closure_still (w : WriteBack) (caps : Name → Bool) (g : List (Name × Value) → Value)
    (s : Copy.State) :
    (∃ v, (Eval.inspect (fun s => (Copy.memoryWith w).capture s caps) >>= fun c =>
        (Pure.pure (g c) : Eval Copy.State Value)) s = .done v s) ∨
      ∃ f, (Eval.inspect (fun s => (Copy.memoryWith w).capture s caps) >>= fun c =>
        (Pure.pure (g c) : Eval Copy.State Value)) s = Outcome.fault f s := by
  simp only [Bind.bind, Eval.bind, Eval.inspect, Eval.ofExcept]
  cases (Copy.memoryWith w).capture s caps with
  | ok c => exact .inl ⟨g c, rfl⟩
  | error f => exact .inr ⟨f, by cases f <;> rfl⟩

end Stilt
