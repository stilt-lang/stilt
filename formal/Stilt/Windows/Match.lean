import Stilt.Windows.Values
import Stilt.Windows.Control
import Stilt.Windows.Forms

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

/-- A pattern's binders bound in turn to values the checks accept around a run whose result is
the same on both sides, a guard's. -/
theorem SimP.bindersSame {α : Type} {S : List Shape} {P : List Name} {m : Eval IState α}
    {m' : Eval WState α} :
    ∀ (c : Ctx) (xs : List Name) (us : List Value), xs.length = us.length →
      (∀ x ∈ xs, x ∉ P) → (∀ y ∈ P, y ∈ c.P) → (xs = [] → P = c.P) →
      (∀ u ∈ us, u.Viewed D) →
      SimP D { c with Γ := c.Γ.binders xs S, R := xs.foldl hide c.R, P := P } pend
        (fun _ _ => True) Same m m' →
      SimP D c pend (fun _ _ => True) Same (Eval.withVars InPlace.memory (xs.zip us) m)
        (Eval.withVars memory (xs.zip us) m')
  | c, [], [], _, _, _, hP, _, hm => by
    obtain rfl := hP rfl
    exact hm
  | c, x :: xs, u :: us, hl, hxP, hPc, _, hu, hm => by
    have hok : ScopeOk c x ⟨none, S, false⟩ (hide c.R x) P :=
      ⟨rfl, fun t ht hx => mem_hide.2 ⟨ht, hx⟩, fun t ht => (mem_hide.1 ht).2,
        fun h => by simp at h, hPc, hxP x List.mem_cons_self⟩
    have hrest := SimP.bindersSame (c.scope x ⟨none, S, false⟩ (hide c.R x) P) xs us
      (by simpa using hl) (fun y hy => hxP y (List.mem_cons_of_mem _ hy)) (fun _ h => h)
      (fun _ => rfl) (fun v hv => hu v (List.mem_cons_of_mem _ hv)) hm
    exact (SimP.scopeSame hok hrest u u).mono
      (fun si sw _ => bindsAs_untyped (hu u List.mem_cons_self) si sw) fun _ _ _ _ h => h
  | _, [], _ :: _, hl, _, _, _, _, _ => by simp at hl
  | _, _ :: _, [], hl, _, _, _, _, _ => by simp at hl

section Arms

variable (n : Nat) (hΓ : ScopeKeeps D c.Γ) {S : List Shape}
  (ih : ∀ c' : Ctx, ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e →
    RunsIn D c' (Stilt.eval D InPlace.memory n) (Windows.eval D n) e₀ e)
include hΓ ih

/-- The context of an arm's guard and body: its binders bound, read and hidden. -/
private def armCtx (c : Ctx) (S : List Shape) (xs : List Name) : Ctx :=
  { c with Γ := c.Γ.binders xs S, R := List.foldl hide c.R xs
           P := List.filter (fun y => !xs.contains y) c.P }

/-- An arm's body, run with the parts of a way of its pattern bound. -/
theorem SimP.armBody {xs : List Name} {b₀ b : Expr} (hb : Expr.Inst D b₀ b) {us : List Value}
    (hl : xs.length = us.length) (hu : ∀ u ∈ us, u.Viewed D)
    (hr : b₀.viewsRead D (c.Γ.binders xs S) (xs.foldl hide c.R) = true)
    (hc₁ : b₀.contained D (c.Γ.binders xs S) (c.P.filter (!xs.contains ·)) = true)
    (hc₂ : (b₀.sources D (c.Γ.binders xs S)).all (!xs.contains ·.root) = true) :
    Sim D c pend (b₀.sources D (c.Γ.binders xs S))
      (Eval.withVars InPlace.memory (xs.zip us) (Stilt.eval D InPlace.memory n b))
      (Eval.withVars memory (xs.zip us) (Windows.eval D n b)) := by
  have hbody := ih (armCtx c S xs) (hΓ.binders S xs) b₀ b hb (armCtx c S xs).R pend hr hc₁
  refine SimP.binders c xs us hl (fun x hx hP => ?_) (fun y hy => (List.mem_filter.1 hy).1)
    (fun h => by subst h; simp) hu (fun s hs x hx he => ?_) hbody
  · simpa [hx] using (List.mem_filter.1 hP).2
  · have := List.all_eq_true.1 hc₂ s hs
    rw [he] at this
    simp [hx] at this

/-- An arm's guard with each way of its pattern, then its body or the arms after it. -/
theorem SimP.guarded {xs : List Name} {g₀ g b₀ b : Expr} (hg : Expr.Inst D g₀ g)
    (hb : Expr.Inst D b₀ b) {Sb Sr : List Shape} {next : Eval IState Value}
    {next' : Eval WState Value}
    (hrg : g₀.viewsRead D (c.Γ.binders xs S) (xs.foldl hide c.R) = true)
    (hcg : g₀.contained D (c.Γ.binders xs S) (c.P.filter (!xs.contains ·)) = true)
    (hr : b₀.viewsRead D (c.Γ.binders xs S) (xs.foldl hide c.R) = true)
    (hc₁ : b₀.contained D (c.Γ.binders xs S) (c.P.filter (!xs.contains ·)) = true)
    (hc₂ : (b₀.sources D (c.Γ.binders xs S)).all (!xs.contains ·.root) = true)
    (hSb : ∀ s ∈ b₀.sources D (c.Γ.binders xs S), s ∈ Sb) (hn : Sim D c pend Sr next next')
    (hSr : ∀ s ∈ Sr, s ∈ Sb) :
    ∀ ways : List (List Value), (∀ us ∈ ways, ∀ u ∈ us, u.Viewed D) →
      Sim D c pend Sb (Eval.guarded InPlace.memory (Stilt.eval D InPlace.memory n) xs g b next ways)
        (Eval.guarded memory (Windows.eval D n) xs g b next' ways)
  | [], _ => Sim.sub hn hSr
  | us :: ways, hw => by
    simp only [Eval.guarded]
    by_cases hl : xs.length = us.length
    · simp only [hl, ↓reduceIte]
      have hu := hw us List.mem_cons_self
      have hrest := SimP.guarded hg hb hrg hcg hr hc₁ hc₂ hSb hn hSr ways
        fun us' hu' => hw us' (List.mem_cons_of_mem _ hu')
      have hgs : SimP D (armCtx c S xs) pend (fun _ _ => True) Same
          (Stilt.eval D InPlace.memory n g >>= Eval.asBool) (Windows.eval D n g >>= Eval.asBool) :=
        SimP.bind (ih (armCtx c S xs) (hΓ.binders S xs) g₀ g hg (armCtx c S xs).R pend hrg hcg)
          fun _ _ => SimP.asBool fun _ _ h => h.1
      refine SimP.bind (SimP.bindersSame (S := S) c xs us hl (fun x hx hP => ?_)
        (fun y hy => (List.mem_filter.1 hy).1) (fun h => by subst h; simp) hu hgs)
        (SimP.branch fun k => SimP.ite k ?_ hrest)
      · simpa [hx] using (List.mem_filter.1 hP).2
      · exact Sim.sub (SimP.armBody n hΓ ih hb hl hu hr hc₁ hc₂) hSb
    · simp only [hl, ↓reduceIte]
      exact SimP.fail .stuck

end Arms

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
  | _, _, .cons p xs hg hb has, hr, hc => by
    simp only [armsViewsRead, Bool.and_eq_true] at hr
    simp only [armsContained, Bool.and_eq_true] at hc
    have hrest := (SimP.select n hΓ hv ih has hr.2 hc.2)
    simp only [Eval.select]
    cases hg with
    | none =>
      simp only
      cases hm : p.matchOn v with
      | none =>
        exact hrest.mono (fun _ _ h => h) fun _ _ _ _ h =>
          ValG.sub (fun s hs => List.mem_append_right _ hs) h
      | some us =>
        by_cases hl : xs.length = us.length
        · simp only [hl, ↓reduceIte]
          exact Sim.sub (SimP.armBody n hΓ ih hb hl
            (Pattern.matchOn_parts (Value.Viewed.passesToParts D) p hv hm) hr.1.2 hc.1.1.2 hc.1.2)
            fun s hs => List.mem_append_left _ hs
        · simp only [hl, ↓reduceIte]
          exact SimP.fail .stuck
    | some hgi =>
      simp only [guardViewsRead, guardContained] at hr hc
      exact SimP.guarded n hΓ ih hgi hb hr.1.1 hc.1.1.1 hr.1.2 hc.1.1.2 hc.1.2
        (fun s hs => List.mem_append_left _ hs) hrest (fun s hs => List.mem_append_right _ hs) _
        fun us hu => by
          obtain ⟨q, -, hq⟩ := Pattern.mem_ways hu
          exact Pattern.matchOn_parts (Value.Viewed.passesToParts D) q hv hq

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
