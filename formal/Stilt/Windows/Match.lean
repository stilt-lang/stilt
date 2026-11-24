import Stilt.Windows.Values
import Stilt.Windows.Control

/-!
# A `match`

The model of windows reads the scrutinee through its windows (views.functions-of-views), so
both models match the same value, which holds no window, against the same patterns, and bind
the same parts in the arm they pick (patterns.match), each binder in a scope of its own that
reads what the scrutinee reads and hides its name.
-/

namespace Stilt

namespace Windows

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

/-- An untyped binding of a value the checks accept binds it as itself. -/
theorem bindsAs_untyped {S : List Shape} {v : Value} (hv : v.Viewed D) (si : IState) (sw : WState) :
    BindsAs D c ⟨none, S, false⟩ v v si sw := by
  refine ⟨VRel.free hv.free, hv, ?_⟩
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  exact hv.free

/-- A pattern's binders bound in turn to values the checks accept, each in a scope of its own
that reads the scrutinee's sources and hides its name; the result's parameters `P` name none
of them. -/
theorem SimP.binders {S Sb : List Shape} {P : List Name} {m : Eval IState Value}
    {m' : Eval WState Value} :
    ∀ (c : Ctx) (xs : List Name) (us : List Value), xs.length = us.length →
      (∀ x ∈ xs, x ∉ P) → (∀ y ∈ P, y ∈ c.P) → (xs = [] → P = c.P) →
      (∀ u ∈ us, u.Viewed D) → (∀ s ∈ Sb, ∀ x ∈ xs, s.root ≠ x) →
      Sim D { c with Γ := c.Γ.binders xs S, R := xs.foldl hide c.R, P := P } pend Sb m m' →
      Sim D c pend Sb (Eval.withVars InPlace.memory (xs.zip us) m)
        (Eval.withVars memory (xs.zip us) m')
  | c, [], [], _, _, _, hP, _, _, hm => by
    obtain rfl := hP rfl
    exact hm
  | c, x :: xs, u :: us, hl, hxP, hPc, _, hu, hS, hm => by
    have hok : ScopeOk c x ⟨none, S, false⟩ (hide c.R x) P :=
      ⟨rfl, fun t ht hx => mem_hide.2 ⟨ht, hx⟩, fun t ht => (mem_hide.1 ht).2,
        fun h => by simp at h, hPc, hxP x List.mem_cons_self⟩
    have hrest := SimP.binders (c.scope x ⟨none, S, false⟩ (hide c.R x) P) xs us
      (by simpa using hl) (fun y hy => hxP y (List.mem_cons_of_mem _ hy)) (fun _ h => h)
      (fun _ => rfl) (fun v hv => hu v (List.mem_cons_of_mem _ hv))
      (fun s hs y hy => hS s hs y (List.mem_cons_of_mem _ hy)) hm
    exact (SimP.scope hok (fun s hs => hS s hs x List.mem_cons_self) hrest u u).mono
      (fun si sw _ => bindsAs_untyped (hu u List.mem_cons_self) si sw) fun _ _ _ _ h => h
  | _, [], _ :: _, hl, _, _, _, _, _, _ => by simp at hl
  | _, _ :: _, [], hl, _, _, _, _, _, _ => by simp at hl

/-- The first arm tried: its pattern matches, or the arms after it are. -/
theorem select_cons {σ : Type} (M : Memory σ) (run : Expr → Eval σ Value) (a : Arm)
    (arms : List Arm) (v : Value) :
    Eval.select M run (a :: arms) v = match a.pattern.matchOn v with
      | some us => if a.binders.length = us.length then
          Eval.withVars M (a.binders.zip us) (run a.body) else Eval.fail .stuck
      | none => Eval.select M run arms v := by
  cases h : a.pattern.matchOn v with
  | none => simp only [Eval.select, selectArm, h]
  | some us => simp only [Eval.select, selectArm, h]

/-- The arms of a `match` on a value the checks accept, which holds no window, the same on both
sides. -/
theorem SimP.select (n : Nat) (hΓ : ScopeKeeps D c.Γ) {S : List Shape} {v : Value}
    (hv : v.Viewed D)
    (ih : ∀ c' : Ctx, ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e →
      RunsIn D c' (Stilt.eval D InPlace.memory n) (Windows.eval D n) e₀ e) :
    ∀ {arms₀ arms : List Arm}, ArmsInst D arms₀ arms →
      armsViewsRead D c.Γ c.R S arms₀ = true → armsContained D c.Γ c.P S arms₀ = true →
      Sim D c pend (armsSources D c.Γ S arms₀)
        (Eval.select InPlace.memory (Stilt.eval D InPlace.memory n) arms v)
        (Eval.select memory (Windows.eval D n) arms v)
  | _, _, .nil, _, _ => SimP.fail .stuck
  | _, _, .cons p xs (b := b₀) (b' := b) hb has, hr, hc => by
    simp only [armsViewsRead, Bool.and_eq_true] at hr
    simp only [armsContained, Bool.and_eq_true, List.all_eq_true] at hc
    rw [select_cons, select_cons]
    dsimp only
    cases hm : p.matchOn v with
    | none =>
      exact (SimP.select n hΓ hv ih has hr.2 hc.2).mono (fun _ _ h => h) fun _ _ _ _ h =>
        ValG.sub (fun s hs => List.mem_append_right _ hs) h
    | some us =>
      by_cases hl : xs.length = us.length
      · simp only [hl, ↓reduceIte]
        let cb : Ctx :=
          { c with Γ := c.Γ.binders xs S, R := List.foldl hide c.R xs
                   P := List.filter (fun y => !xs.contains y) c.P }
        have hbody := ih cb (hΓ.binders S xs) b₀ b hb cb.R pend hr.1 hc.1.1
        refine (SimP.binders c xs us hl (fun x hx hP => ?_) (fun y hy => (List.mem_filter.1 hy).1)
          (fun h => by subst h; simp) (Pattern.matchOn_parts (Value.Viewed.passesToParts D) p hv hm)
          (fun s hs x hx he => ?_) hbody).mono (fun _ _ h => h) fun _ _ _ _ h =>
            ValG.sub (fun s hs => List.mem_append_left _ hs) h
        · simpa [hx] using (List.mem_filter.1 hP).2
        · have := hc.1.2 s hs
          rw [he] at this
          simp [hx] at this
      · simp only [hl, ↓reduceIte]
        exact SimP.fail .stuck

/-- A `match`: the scrutinee read through its windows on the windows' side, then the arm its
value picks. -/
theorem SimP.matchArms (n : Nat) (hΓ : ScopeKeeps D c.Γ) {e₀ e : Expr} {τ₀ τ : Ty}
    {arms₀ arms : List Arm} (hi : Expr.Inst D e₀ e) (has : ArmsInst D arms₀ arms)
    (ih : ∀ c' : Ctx, ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e →
      RunsIn D c' (Stilt.eval D InPlace.memory n) (Windows.eval D n) e₀ e)
    (hr : (Expr.match e₀ τ₀ arms₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.match e₀ τ₀ arms₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.match e₀ τ₀ arms₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.match e τ arms))
      (Windows.eval D (n + 1) (.match e τ arms)) := by
  simp only [Expr.viewsRead, Bool.and_eq_true] at hr
  simp only [Expr.contained, Bool.and_eq_true] at hc
  refine SimP.bind (SimP.readThrough (ih c hΓ e₀ e hi c.R pend hr.1 hc.1)) fun v w => ?_
  intro si sw hp hg hq
  obtain ⟨rfl, -, hv⟩ := hq
  exact SimP.select n hΓ hv ih has hr.2 hc.2 si sw hp hg trivial

end Windows

end Stilt
