import Stilt.Windows.View
import Stilt.Windows.Parts

/-!
# Forms that build a value

A variable, a literal, a function or a method, and a record, variant or list literal, on the
relation of windows: both models end alike, with related values. A variable's value keeps its
windows, tracked by its binding's sources; a variant's payload keeps the windows of its
elements, tracked by theirs, as `Option<View>` holds a view (views.view-types); a record and a
list literal hold no window, as the model of windows reads their elements through their
windows, no field or element of such a type being a view (views.view-types).
-/

namespace Stilt

namespace Windows

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

/-! ## Values read from the state or written in the program -/

/-- A variable. -/
theorem SimP.var (n : Nat) (x : Name) :
    Sim D c pend ((Expr.var x).sources D c.Γ) (Stilt.eval D InPlace.memory (n + 1) (.var x))
      (Windows.eval D (n + 1) (.var x)) :=
  SimP.inspect fun _ _ hp _ _ => Pre.var hp x

/-- A variable moved from. -/
theorem SimP.move (n : Nat) (x : Name) :
    Sim D c pend ((Expr.move x).sources D c.Γ) (Stilt.eval D InPlace.memory (n + 1) (.move x))
      (Windows.eval D (n + 1) (.move x)) :=
  SimP.inspect fun _ _ hp _ _ => Pre.var hp x

/-- The same value on both sides, one that holds no window and that the checks accept. -/
theorem SimP.const {S : List Shape} (v : Value) (hf : Free v) (hv : v.Viewed D) :
    Sim D c pend S (Pure.pure v) (Pure.pure v) :=
  SimP.pure fun _ _ _ _ => ⟨VRel.free hf, fun w hw => (by rw [hf] at hw; cases hw), hv⟩

theorem SimP.int (n : Nat) (k : Int) :
    Sim D c pend ((Expr.int k).sources D c.Γ) (Stilt.eval D InPlace.memory (n + 1) (.int k))
      (Windows.eval D (n + 1) (.int k)) :=
  SimP.const _ rfl .int

theorem SimP.bool (n : Nat) (b : Bool) :
    Sim D c pend ((Expr.bool b).sources D c.Γ) (Stilt.eval D InPlace.memory (n + 1) (.bool b))
      (Windows.eval D (n + 1) (.bool b)) :=
  SimP.const _ rfl .bool

theorem SimP.unit (n : Nat) :
    Sim D c pend (Expr.unit.sources D c.Γ) (Stilt.eval D InPlace.memory (n + 1) .unit)
      (Windows.eval D (n + 1) .unit) :=
  SimP.const _ rfl .unit

/-- A function named with its type and row arguments. -/
theorem SimP.fnRef (n : Nat) (f : Name) (types : List Ty) (rows : List Row) :
    Sim D c pend ((Expr.fnRef f types rows).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.fnRef f types rows))
      (Windows.eval D (n + 1) (.fnRef f types rows)) :=
  SimP.const _ rfl .function

/-- A method of a trait at a type: the same function of its impl, or stuck. -/
theorem SimP.method (n : Nat) (trait m : Name) (τ : Ty) :
    Sim D c pend ((Expr.method trait m τ).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.method trait m τ))
      (Windows.eval D (n + 1) (.method trait m τ)) := by
  show Sim D c pend _ (Eval.method D trait m τ) (Eval.method D trait m τ)
  unfold Eval.method
  split
  · split
    · exact SimP.const _ rfl .function
    · exact SimP.fail _
  · exact SimP.fail _

/-! ## Literals of several values -/

/-- A record of fields read alike: the same record on both sides, once read through its
windows on the windows' side. -/
theorem SimP.declare {S : List Shape} (R : Name) (vs ws : List (Name × Value)) :
    SimP D c pend (FieldsG D c S vs ws) (ValG D c [])
      (Eval.declare D R vs) (Eval.declare D R ws >>= resolveE) := by
  intro si sw hp hg hq
  unfold Eval.declare
  cases hR : D.record? R with
  | none => exact CorrG.fault hp .stuck
  | some r =>
    rcases declare_rel hq R r.fields with ⟨h₁, h₂⟩ | ⟨gs, gs', h₁, h₂, h₃⟩
    · simp only [h₁, h₂]
      exact CorrG.fault hp .stuck
    · simp only [h₁, h₂]
      have hrel : VRel si.1.store sw.1.store (.record R gs') (.record R gs) :=
        ⟨mapWindows_record.2 ⟨gs, h₃.1, rfl⟩, fun win hw => (h₃.2.1 win hw).1⟩
      have hv : (Value.record R gs).Viewed D := .record h₃.2.2
      show (Outcome.done (Value.record R gs) si).Rel _
        (Eval.ofExcept (resolve sw.1.store (.record R gs')) sw)
      rw [hrel.resolve]
      exact ⟨hp, rfl, VRel.free hv.free, fun w hw => (by rw [hv.free] at hw; cases hw), hv⟩

/-- A record literal. -/
theorem SimP.record (n : Nat) (hΓ : ScopeKeeps D c.Γ) (R : Name) {τs₀ τs : List Ty}
    {fs₀ fs : List (Name × Expr)}
    (his : FieldsInst D fs₀ fs)
    (ih : ∀ c' : Ctx, ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e →
      RunsIn D c' (Stilt.eval D InPlace.memory n) (Windows.eval D n) e₀ e)
    (hr : (Expr.record R τs₀ fs₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.record R τs₀ fs₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.record R τs₀ fs₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.record R τs fs))
      (Windows.eval D (n + 1) (.record R τs fs)) :=
  SimP.bind (SimP.fields his c pend (fun _ e₀ e _ hi => ih c hΓ e₀ e hi) hr hc) fun vs ws =>
    SimP.declare R vs ws

/-- A variant: its payload's values, read alike, their windows tracked by their sources. -/
theorem SimP.variant (n : Nat) (hΓ : ScopeKeeps D c.Γ) (T C : Name) {τs₀ τs : List Ty}
    {es₀ es : List Expr}
    (his : ExprsInst D es₀ es)
    (ih : ∀ c' : Ctx, ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e →
      RunsIn D c' (Stilt.eval D InPlace.memory n) (Windows.eval D n) e₀ e)
    (hr : (Expr.variant T τs₀ C es₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.variant T τs₀ C es₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.variant T τs₀ C es₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.variant T τs C es))
      (Windows.eval D (n + 1) (.variant T τs C es)) :=
  SimP.bind (SimP.list his c pend (fun e₀ e _ hi => ih c hΓ e₀ e hi) hr hc) fun vs _ =>
    SimP.pure fun _ _ _ h => ⟨⟨mapWindows_variant.2 ⟨vs, h.1, rfl⟩,
      fun win hw => (h.2.1 win hw).1⟩, fun win hw => (h.2.1 win hw).2, .variant h.2.2⟩

/-- A list literal: its elements read alike, and the list read through its windows on the
windows' side. -/
theorem SimP.listLit (n : Nat) (hΓ : ScopeKeeps D c.Γ) (τ₀ τ : Ty) {es₀ es : List Expr}
    (his : ExprsInst D es₀ es)
    (ih : ∀ c' : Ctx, ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e →
      RunsIn D c' (Stilt.eval D InPlace.memory n) (Windows.eval D n) e₀ e)
    (hr : (Expr.list τ₀ es₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.list τ₀ es₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.list τ₀ es₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.list τ es))
      (Windows.eval D (n + 1) (.list τ es)) := by
  refine SimP.bind (SimP.list his c pend (fun e₀ e _ hi => ih c hΓ e₀ e hi) hr hc) fun vs ws => ?_
  refine SimP.inspect (f := fun _ => .ok (Value.list vs))
    (f' := fun s => resolve s.1.store (.list ws))
    fun si sw _ _ h => ?_
  have hrel : VRel si.1.store sw.1.store (.list ws) (.list vs) :=
    ⟨mapWindows_list.2 ⟨vs, h.1, rfl⟩, fun win hw => (h.2.1 win hw).1⟩
  have hv : (Value.list vs).Viewed D := .list h.2.2
  exact .inr ⟨_, _, rfl, hrel.resolve, VRel.free hv.free,
    fun w hw => (by rw [hv.free] at hw; cases hw), hv⟩

end Windows

end Stilt
