import Stilt.Panics.Keeps

/-!
# Evaluation keeps what it doesn't write

`eval_keeps`: evaluating `e` with any fuel keeps every variable that
`e.writes` doesn't name, and the length of every list that `e.resizes` doesn't
name, by induction on the fuel, case by case on the expression. A handler's clause
is a call, which writes back nothing, since its argument is a value
(handlers.no-inout-parameter).
-/

namespace Stilt

/-- Running an expression keeps the variables it doesn't write, and the lengths of
the lists it doesn't resize. -/
def KeepsRun (run : Expr → Eval Copy.State Value) : Prop :=
  ∀ e W L, e.writes ⊆ W → e.resizes ⊆ L → Eval.Keeps W L (fun _ => True) (run e)

theorem armsWrites_mem : ∀ {arms : List Arm} {arm : Arm}, arm ∈ arms →
    arm.body.writes ⊆ armsWrites arms
  | ⟨_, _, _⟩ :: _, _, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact List.subset_append_left _ _
    · exact (armsWrites_mem hm).trans (List.subset_append_right _ _)

theorem armsResizes_mem : ∀ {arms : List Arm} {arm : Arm}, arm ∈ arms →
    arm.body.resizes ⊆ armsResizes arms
  | ⟨_, _, _⟩ :: _, _, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact List.subset_append_left _ _
    · exact (armsResizes_mem hm).trans (List.subset_append_right _ _)

namespace Eval.Keeps

variable (w : WriteBack) {run : Expr → Eval Copy.State Value} {W L : List Name}

section Runs

variable (h : KeepsRun run)
include h

theorem list : ∀ es : List Expr, exprsWrites es ⊆ W → exprsResizes es ⊆ L →
    Eval.Keeps W L (fun _ => True) (Eval.list run es)
  | [], _, _ => pure trivial
  | e :: es, hw, hl => by
    simp only [exprsWrites, exprsResizes, List.append_subset] at hw hl
    exact bind (h e W L hw.1 hl.1) fun _ _ => bind (list es hw.2 hl.2) fun _ _ => pure trivial

theorem fields : ∀ fs : List (Name × Expr), fieldsWrites fs ⊆ W → fieldsResizes fs ⊆ L →
    Eval.Keeps W L (fun _ => True) (Eval.fields run fs)
  | [], _, _ => pure trivial
  | (_, e) :: fs, hw, hl => by
    simp only [fieldsWrites, fieldsResizes, List.append_subset] at hw hl
    exact bind (h e W L hw.1 hl.1) fun _ _ => bind (fields fs hw.2 hl.2) fun _ _ => pure trivial

omit h in
theorem asInt (v : Value) : Eval.Keeps W L (fun _ => True) (Eval.asInt v : Eval Copy.State Int) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem path : ∀ ps : List Projection, pathWrites ps ⊆ W → pathResizes ps ⊆ L →
    Eval.Keeps W L (fun p : Path => p = [] → ps = []) (Eval.path run ps)
  | [], _, _ => pure fun _ => rfl
  | .field _ :: ps, hw, hl => by
    simp only [pathWrites, pathResizes] at hw hl
    exact bind (path ps hw hl) fun _ _ => pure (nomatch ·)
  | .index i :: ps, hw, hl => by
    simp only [pathWrites, pathResizes, List.append_subset] at hw hl
    exact bind (bind (h i W L hw.1 hl.1) fun v _ => asInt v) fun _ _ =>
      bind (path ps hw.2 hl.2) fun _ _ => pure (nomatch ·)

theorem args : ∀ as : List Arg, argsWrites as ⊆ W → argsResizes as ⊆ L →
    Eval.Keeps W L (fun passed : List Passed => ∀ q ∈ passed, q.RootIn W L) (Eval.args run as)
  | [], _, _ => pure (by simp)
  | .value e :: as, hw, hl => by
    simp only [argsWrites, argsResizes, List.append_subset] at hw hl
    exact bind (h e W L hw.1 hl.1) fun v _ => bind (args as hw.2 hl.2) fun ps hps => pure fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · cases e <;> trivial
      · exact hps q hq
  | .inout ⟨x, ps⟩ :: as, hw, hl => by
    simp only [argsWrites, argsResizes, List.cons_subset, List.append_subset] at hw hl
    exact bind (path h ps hw.2.1 hl.2.1) fun p hp => bind (args as hw.2.2 hl.2.2) fun qs hqs =>
      pure fun q hq => by
        rcases List.mem_cons.1 hq with rfl | hq
        · exact ⟨hw.1, fun h0 => by
            have := hp h0
            subst this
            simpa using hl.1⟩
        · exact hqs q hq

theorem select {arms : List Arm} (hw : armsWrites arms ⊆ W) (hl : armsResizes arms ⊆ L) (v : Value) :
    Eval.Keeps W L (fun _ => True) (Eval.select (Copy.memoryWith w) run arms v) := by
  unfold Eval.select
  cases hsel : selectArm arms v with
  | none => exact fail _
  | some au =>
    obtain ⟨arm, us⟩ := au
    obtain ⟨hmem, -⟩ := selectArm_mem hsel
    dsimp only
    split
    · exact withVars w (h _ W L ((armsWrites_mem hmem).trans hw) ((armsResizes_mem hmem).trans hl)) _
    · exact fail _

omit h in
theorem memoryWith_write (s : Copy.State) (x : Name) (p : Path) (v : Value) :
    (Copy.memoryWith w).write s x p v = (·, s.2) <$> Copy.write s.1 x p v := rfl

omit h in
theorem update (x : Name) (p : Path) (v : Value) (hx : x ∈ W) (hl : p = [] → x ∈ L) :
    Eval.Keeps W L (fun _ => True) (Eval.update fun s => (Copy.memoryWith w).write s x p v) := by
  intro s
  unfold Eval.update
  dsimp only
  rw [memoryWith_write]
  cases hwr : Copy.write s.1 x p v with
  | ok fr => exact ⟨trivial, Frame.Keeps.write hx hl hwr⟩
  | error f => exact fault f _ _

theorem assign (x : Name) {ps : List Projection} {value : Expr}
    (hw : x :: (pathWrites ps ++ value.writes) ⊆ W)
    (hl : (if ps.isEmpty then [x] else []) ++ (pathResizes ps ++ value.resizes) ⊆ L) :
    Eval.Keeps W L (fun _ => True) (Eval.assign (Copy.memoryWith w) run x ps value) := by
  simp only [List.cons_subset, List.append_subset] at hw hl
  exact bind (path h ps hw.2.1 hl.2.1) fun p hp => bind (h value W L hw.2.2 hl.2.2) fun v _ =>
    bind (update w x p v hw.1 fun h0 => by
      have := hp h0
      subst this
      simpa using hl.1) fun _ _ => pure trivial

omit h in
theorem asList (v : Value) :
    Eval.Keeps W L (fun _ => True) (Eval.asList v : Eval Copy.State (List Value)) := by
  cases v <;> first | exact pure trivial | exact fail _

omit h in
theorem asBool (v : Value) : Eval.Keeps W L (fun _ => True) (Eval.asBool v : Eval Copy.State Bool) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem loop (x : Name) {e body : Expr} (he : e.writes ⊆ W) (hb : body.writes ⊆ W)
    (hel : e.resizes ⊆ L) (hbl : body.resizes ⊆ L) :
    Eval.Keeps W L (fun _ => True) (Eval.loop (Copy.memoryWith w) run x e body) :=
  bind (bind (h e W L he hel) fun v _ => asList v) fun vs _ =>
    bind (forEach (fun v => withVar w x v (turn (h body W L hb hbl))) vs) fun _ _ => pure trivial

end Runs

end Eval.Keeps

namespace Outcome.Keeps

variable {α : Type} {W L : List Name} {P : α → Prop}

theorem after {w : WriteBack} {s₀ : Copy.Frame} {held : Bool} {cells : List (Name × Ty × Nat)}
    {s : Copy.State} {o : Copy.State → Outcome Copy.State α}
    (ho : ∀ s', s'.1 = s.1 → (o s').Keeps W L P s₀) :
    (Outcome.after ((Copy.memoryWith w).putBack held cells) s o).Keeps W L P s₀ := by
  unfold Outcome.after
  split
  · rename_i s' h
    exact ho s' (Frames.putBack_frame _ held cells h)
  · exact Eval.Keeps.fault _ _ _

/-- A `when` keeps what its block keeps: putting values back writes no variable. -/
theorem release (w : WriteBack) (cells : List (Name × Ty × Nat)) {s₀ : Copy.Frame} :
    ∀ {o : Outcome Copy.State α}, o.Keeps W L P s₀ → (o.release (Copy.memoryWith w) cells).Keeps W L P s₀
  | .done _ _, h => after fun _ h' => ⟨h.1, h' ▸ h.2⟩
  | .raised _ _, h => after fun _ h' => show Frame.Keeps _ _ _ _ from h' ▸ h
  | .jumped _ _, h => after fun _ h' => show Frame.Keeps _ _ _ _ from h' ▸ h
  | .panicked _ _, _ => after fun _ _ => trivial
  | .performed _ _ _ _, ⟨h, hk⟩ => after fun _ h' => ⟨h' ▸ h, fun w' x => release w cells (hk w' x)⟩
  | .outOfFuel, h | .stuck, h => h

/-- Letting cells go writes no variable. -/
theorem letGo (w : WriteBack) (before : World) {s₀ : Copy.Frame} :
    ∀ {o : Outcome Copy.State α}, o.Keeps W L P s₀ → (o.letGo (Copy.memoryWith w) before).Keeps W L P s₀
  | .done _ (_, _), h | .raised _ (_, _), h | .jumped _ (_, _), h | .panicked _ (_, _), h => h
  | .performed _ _ _ _, ⟨h, hk⟩ => ⟨h, fun w' x => letGo w before (hk w' x)⟩
  | .outOfFuel, h | .stuck, h => h

end Outcome.Keeps

open Eval.Keeps in
/-- **Evaluation keeps what it doesn't write**, with any fuel. -/
theorem eval_keeps (D : Decls) (w : WriteBack) : ∀ n, KeepsRun (eval D (Copy.memoryWith w) n)
  | 0, _, _, _, _, _ => fun _ => trivial
  | n + 1, e, W, L, hw, hl => by
    have ih := eval_keeps D w n
    cases e
    case var x => exact inspect _ fun _ _ _ => trivial
    case move x => exact inspect _ fun _ _ _ => trivial
    case int k => exact pure trivial
    case bool b => exact pure trivial
    case unit => exact pure trivial
    case record R _ fs =>
      exact bind (fields ih fs hw hl) fun _ _ => by
        show Eval.Keeps W L _ (Eval.declare D R _)
        unfold Eval.declare
        split
        · split
          · exact pure trivial
          · exact fail _
        · exact fail _
    case variant T _ C es => exact bind (list ih es hw hl) fun _ _ => pure trivial
    case list τ es => exact bind (list ih es hw hl) fun _ _ => pure trivial
    case op o es => exact bind (list ih es hw hl) fun _ _ => world w _
    case view es => exact bind (list ih es hw hl) fun _ _ => ofExcept _ fun _ _ => trivial
    case field e f => exact bind (ih e W L hw hl) fun _ _ => ofExcept _ fun _ _ => trivial
    case index e i =>
      simp only [Expr.writes, Expr.resizes, List.append_subset] at hw hl
      exact bind (ih e W L hw.1 hl.1) fun _ _ =>
        bind (bind (ih i W L hw.2 hl.2) fun v _ => asInt v) fun _ _ => ofExcept _ fun _ _ => trivial
    case fnRef f types rows => exact pure trivial
    case method t m τ =>
      show Eval.Keeps W L _ (Eval.method D t m τ)
      unfold Eval.method
      split
      · split
        · exact pure trivial
        · exact fail _
      · exact fail _
    case closure ps result ρ body =>
      exact bind (inspect _ fun _ _ _ => trivial) fun _ _ => pure trivial
    case call callee as _ =>
      simp only [Expr.writes, Expr.resizes, List.append_subset] at hw hl
      exact bind (ih callee W L hw.1 hl.1) fun f _ => bind (args ih as hw.2 hl.2) fun _ hp => callAs w D _ false f hp
    case letIn x τ init body =>
      simp only [Expr.writes, Expr.resizes, List.append_subset] at hw hl
      exact bind (ih init W L hw.1 hl.1) fun v _ => withInit w x init v (ih body W L hw.2 hl.2)
    case varIn x τ init body =>
      simp only [Expr.writes, Expr.resizes, List.append_subset] at hw hl
      exact bind (ih init W L hw.1 hl.1) fun v _ => withInit w x init v (ih body W L hw.2 hl.2)
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      exact assign w ih x hw hl
    case seq a b =>
      simp only [Expr.writes, Expr.resizes, List.append_subset] at hw hl
      exact bind (ih a W L hw.1 hl.1) fun _ _ => ih b W L hw.2 hl.2
    case «if» c τ a b =>
      simp only [Expr.writes, Expr.resizes, List.append_subset] at hw hl
      exact bind (bind (ih c W L hw.1 hl.1) fun v _ => asBool v) fun v _ =>
        ite v (ih a W L hw.2.1 hl.2.1) (ih b W L hw.2.2 hl.2.2)
    case «match» e τ arms =>
      simp only [Expr.writes, Expr.resizes, List.append_subset] at hw hl
      exact bind (ih e W L hw.1 hl.1) fun v _ => select w ih hw.2 hl.2 v
    case «for» x τ e body =>
      simp only [Expr.writes, Expr.resizes, List.append_subset] at hw hl
      exact loop w ih x hw.1 hw.2 hl.1 hl.2
    case raise e => exact bind (ih e W L hw hl) fun v _ => throw v
    case «try» e => exact ih e W L hw hl
    case tryCatch e E x h τ =>
      simp only [Expr.writes, Expr.resizes, List.append_subset] at hw hl
      exact handle (ih e W L hw.1 hl.1) fun err => withVar w x err (ih h W L hw.2 hl.2)
    case «while» c body =>
      have hloop := ih (.while c body) W L hw hl
      simp only [Expr.writes, Expr.resizes, List.append_subset] at hw hl
      exact bind (bind (ih c W L hw.1 hl.1) fun v _ => asBool v) fun v _ =>
        ite v (bind (turn (ih body W L hw.2 hl.2)) fun g _ => ite g hloop (pure trivial)) (pure trivial)
    case «loop» body =>
      have hloop := ih (.loop body) W L hw hl
      exact bind (turn (ih body W L hw hl)) fun g _ => ite g hloop (pure trivial)
    case «break» => exact jump _
    case «continue» => exact jump _
    case «return» e => exact bind (ih e W L hw hl) fun v _ => jump _
    case perform op e =>
      exact bind (ih e W L hw hl) fun v _ s => ⟨.refl s.1, fun _ _ => ⟨trivial, .refl s.1⟩⟩
    case withH E c h b =>
      simp only [Expr.writes, Expr.resizes, List.append_subset] at hw hl
      exact bind (ih h W L hw.1 hl.1) fun hv _ s => Outcome.Keeps.letGo w _ <|
        Outcome.Keeps.handleWith w (fun f v s' hs' => (callAs w D _ c f (by simp [Passed.RootIn]) s').base hs')
          (ih b W L hw.2 hl.2 s)
    case held ns hs b =>
      simp only [Expr.writes, Expr.resizes, List.append_subset] at hw hl
      exact bind (list ih hs hw.1 hl.1) fun _ _ => bind (ofExcept _ fun _ _ => trivial) fun _ _ =>
        bind (bind (world w _) fun v _ => asList v) fun _ _ => by
          split
          · exact withVars w (fun s => Outcome.Keeps.release w _ (ih b W L hw.2 hl.2 s)) _
          · exact fail _

end Stilt
