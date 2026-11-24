import Stilt.Moves.Oblivious
import Stilt.Moves.Holding
import Stilt.Moves.Maps
import Stilt.Moves.Matching
import Stilt.Handling.Related

/-!
# Copy-in, copy-out runs a program as its erasure

Every expression, evaluated by copy-in, copy-out on a frame, ends as its
erasure ends on the frame erased, up to the marks of the values it makes
(`eval_erase`). So a run of a program shows what a run of its erasure shows,
once the marks in the values it shows are erased (`Program.runCopy_erase`).
The marks only differ where a closure carries its body into a value, and no
step of copy-in, copy-out looks into a body but to run it (values.passing-values).
-/

namespace Stilt

/-- Erasing a world keeps its cells of each type, as many as there were. -/
theorem World.cellsOf_erase (x : World) (u : Ty) : (x.erase.cellsOf u).length = (x.cellsOf u).length := by
  simp only [World.erase, World.cellsOf, List.filter_map]
  rw [List.length_map]
  rfl

/-- An operation's value on erased operands, in a world erased, is the erasure of its value,
in the world it leaves erased. -/
theorem Op.run_erase (o : Op) (vs : List Value) (x : World) :
    o.run (eraseValues vs) x.erase = (o.run vs x).map fun p => (p.1.erase, p.2.erase) := by
  cases o
  case world k =>
    show k.run (eraseValues vs) x.erase = (k.run vs x).map _
    have hss : ∀ ss : List String, eraseValues (ss.map .str) = ss.map .str := fun ss => by
      induction ss with
      | nil => rfl
      | cons s ss ih => simp only [List.map_cons, eraseValues, Value.erase, ih]
    cases k with
    | write err nl =>
      cases err <;> rcases vs with _ | ⟨v, _ | ⟨u, rest⟩⟩ <;> (try cases v) <;>
        simp [WorldOp.run, eraseValues, Value.erase, Except.map] <;> rfl
    | readLine =>
      rcases vs with _ | ⟨v, rest⟩ <;> simp [WorldOp.run, eraseValues, Value.erase, Except.map, hss] <;>
        exact ⟨rfl, rfl⟩
    | readAll =>
      rcases vs with _ | ⟨v, rest⟩ <;> simp [WorldOp.run, eraseValues, Value.erase, Except.map] <;>
        exact ⟨rfl, rfl⟩
    | sharedNew u =>
      rcases vs with _ | ⟨v, _ | ⟨w, rest⟩⟩ <;> simp [WorldOp.run, eraseValues, Except.map]
      refine ⟨by rw [World.cellsOf_erase]; rfl, ?_⟩
      simp [World.push, World.erase, Cell.erase]
  all_goals
    simp only [Op.run, Op.apply_erase]
    cases Op.apply _ vs <;> rfl

/-! ## Instantiation and declarations -/

section
variable (s : RowSubst)

mutual

theorem Expr.erase_substRows : ∀ e : Expr, (e.substRows s).erase = e.erase.substRows s
  | .var _ | .move _ | .int _ | .bool _ | .unit | .fnRef .. | .method .. | .break | .continue => rfl
  | .record _ fs => by simp [Expr.substRows, Expr.erase, eraseFields_substRows fs]
  | .variant _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substRows, Expr.erase, eraseExprs_substRows es]
  | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => by
    simp [Expr.substRows, Expr.erase, Expr.erase_substRows e]
  | .index a b | .seq a b | .withH _ _ a b | .while a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .tryCatch a _ _ b _ => by
    simp [Expr.substRows, Expr.erase, Expr.erase_substRows a, Expr.erase_substRows b]
  | .closure _ _ _ b => by simp [Expr.substRows, Expr.erase, Expr.erase_substRows b]
  | .call f args _ => by
    simp [Expr.substRows, Expr.erase, Expr.erase_substRows f, eraseArgs_substRows args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substRows, Expr.erase, erasePath_substRows p, Expr.erase_substRows v]
  | .if c _ a b => by
    simp [Expr.substRows, Expr.erase, Expr.erase_substRows c, Expr.erase_substRows a,
      Expr.erase_substRows b]
  | .match e _ arms => by
    simp [Expr.substRows, Expr.erase, Expr.erase_substRows e, eraseArms_substRows arms]
  | .held _ hs b => by simp [Expr.substRows, Expr.erase, eraseExprs_substRows hs, Expr.erase_substRows b]

theorem eraseExprs_substRows :
    ∀ es : List Expr, eraseExprs (substExprRows s es) = substExprRows s (eraseExprs es)
  | [] => rfl
  | e :: es => by
    simp [substExprRows, eraseExprs, Expr.erase_substRows e, eraseExprs_substRows es]

theorem eraseFields_substRows : ∀ fs : List (Name × Expr),
    eraseFields (substFieldRows s fs) = substFieldRows s (eraseFields fs)
  | [] => rfl
  | (_, e) :: fs => by
    simp [substFieldRows, eraseFields, Expr.erase_substRows e, eraseFields_substRows fs]

theorem eraseArgs_substRows :
    ∀ args : List Arg, eraseArgs (substArgRows s args) = substArgRows s (eraseArgs args)
  | [] => rfl
  | .value e :: args => by
    simp [substArgRows, eraseArgs, Expr.erase_substRows e, eraseArgs_substRows args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgRows, eraseArgs, erasePath_substRows p, eraseArgs_substRows args]

theorem erasePath_substRows :
    ∀ p : List Projection, erasePath (substPathRows s p) = substPathRows s (erasePath p)
  | [] => rfl
  | .field _ :: p => by simp [substPathRows, erasePath, erasePath_substRows p]
  | .index i :: p => by
    simp [substPathRows, erasePath, Expr.erase_substRows i, erasePath_substRows p]

theorem eraseArms_substRows :
    ∀ arms : List Arm, eraseArms (substArmRows s arms) = substArmRows s (eraseArms arms)
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by
    simp [substArmRows, eraseArms, Expr.erase_substRows b, eraseArms_substRows arms]

end

end

section
variable (s : TySubst)

mutual

theorem Expr.erase_substTys : ∀ e : Expr, (e.substTys s).erase = e.erase.substTys s
  | .var _ | .move _ | .int _ | .bool _ | .unit | .fnRef .. | .method .. | .break | .continue => rfl
  | .record _ fs => by simp [Expr.substTys, Expr.erase, eraseFields_substTys fs]
  | .variant _ _ es | .list _ es | .op _ es | .view es => by
    simp [Expr.substTys, Expr.erase, eraseExprs_substTys es]
  | .field e _ | .raise e | .perform _ e | .try e | .loop e | .return e => by
    simp [Expr.substTys, Expr.erase, Expr.erase_substTys e]
  | .index a b | .seq a b | .withH _ _ a b | .while a b | .letIn _ _ a b | .varIn _ _ a b | .for _ _ a b
  | .tryCatch a _ _ b _ => by
    simp [Expr.substTys, Expr.erase, Expr.erase_substTys a, Expr.erase_substTys b]
  | .closure _ _ _ b => by simp [Expr.substTys, Expr.erase, Expr.erase_substTys b]
  | .call f args _ => by
    simp [Expr.substTys, Expr.erase, Expr.erase_substTys f, eraseArgs_substTys args]
  | .assign ⟨_, p⟩ v => by
    simp [Expr.substTys, Expr.erase, erasePath_substTys p, Expr.erase_substTys v]
  | .if c _ a b => by
    simp [Expr.substTys, Expr.erase, Expr.erase_substTys c, Expr.erase_substTys a,
      Expr.erase_substTys b]
  | .match e _ arms => by
    simp [Expr.substTys, Expr.erase, Expr.erase_substTys e, eraseArms_substTys arms]
  | .held _ hs b => by simp [Expr.substTys, Expr.erase, eraseExprs_substTys hs, Expr.erase_substTys b]

theorem eraseExprs_substTys :
    ∀ es : List Expr, eraseExprs (substExprTys s es) = substExprTys s (eraseExprs es)
  | [] => rfl
  | e :: es => by
    simp [substExprTys, eraseExprs, Expr.erase_substTys e, eraseExprs_substTys es]

theorem eraseFields_substTys : ∀ fs : List (Name × Expr),
    eraseFields (substFieldTys s fs) = substFieldTys s (eraseFields fs)
  | [] => rfl
  | (_, e) :: fs => by
    simp [substFieldTys, eraseFields, Expr.erase_substTys e, eraseFields_substTys fs]

theorem eraseArgs_substTys :
    ∀ args : List Arg, eraseArgs (substArgTys s args) = substArgTys s (eraseArgs args)
  | [] => rfl
  | .value e :: args => by
    simp [substArgTys, eraseArgs, Expr.erase_substTys e, eraseArgs_substTys args]
  | .inout ⟨_, p⟩ :: args => by
    simp [substArgTys, eraseArgs, erasePath_substTys p, eraseArgs_substTys args]

theorem erasePath_substTys :
    ∀ p : List Projection, erasePath (substPathTys s p) = substPathTys s (erasePath p)
  | [] => rfl
  | .field _ :: p => by simp [substPathTys, erasePath, erasePath_substTys p]
  | .index i :: p => by
    simp [substPathTys, erasePath, Expr.erase_substTys i, erasePath_substTys p]

theorem eraseArms_substTys :
    ∀ arms : List Arm, eraseArms (substArmTys s arms) = substArmTys s (eraseArms arms)
  | [] => rfl
  | ⟨_, _, b⟩ :: arms => by
    simp [substArmTys, eraseArms, Expr.erase_substTys b, eraseArms_substTys arms]

end

end

/-- The declarations of a program's erasure: every function's body with its
marks read as variables (values.passing-values). -/
def Decls.erase (D : Decls) : Decls := D.mapFns FnDecl.erase

theorem Decls.fn?_erase (D : Decls) (name : Name) :
    D.erase.fn? name = (D.fn? name).map FnDecl.erase := by
  simp [Decls.fn?, Decls.erase, Decls.fns_mapFns FnDecl.erase_qualify, List.find?_map,
    Function.comp_def, FnDecl.erase]

theorem Passed.ofArg_erase (e : Expr) (v : Value) :
    Passed.ofArg e.erase v.erase = (Passed.ofArg e v).erase := by
  cases e
  case assign t _ => cases t; rfl
  all_goals rfl

theorem mapM_lookup_erase (written : List (Name × Value)) : ∀ fs : List (Name × Ty),
    fs.mapM (fun p => ((eraseBindings written).lookup p.1).map (p.1, ·)) =
      (fs.mapM fun p => (written.lookup p.1).map (p.1, ·)).map eraseBindings
  | [] => rfl
  | (f, _) :: fs => by
    rw [List.mapM_cons, List.mapM_cons, mapM_lookup_erase written fs, lookup_eraseBindings]
    cases written.lookup f <;> cases fs.mapM (fun p => (written.lookup p.1).map (p.1, ·)) <;> rfl

/-! ## The steps that evaluate subexpressions -/

namespace Eval.Erases

variable {run run' : Expr → Eval Copy.State Value}

/-- `run'` evaluates each expression's erasure as `run` evaluates the
expression, erased: what the evaluator's steps take of the evaluation of a
subexpression (values.passing-values). -/
abbrev Runs (run run' : Expr → Eval Copy.State Value) : Prop :=
  ∀ e, Erases Value.erase (run e) (run' e.erase)

theorem pure' {α : Type} {f : α → α} {a b : α} (h : b = f a) :
    Erases f (Eval.pure a) (Eval.pure b) :=
  h ▸ pure f a

theorem get (v : Value) (p : Path) :
    Erases Value.erase (Eval.ofExcept (v.get p)) (Eval.ofExcept (v.erase.get p)) := by
  rw [Value.get_erase]
  exact ofExcept _ _

theorem asInt (v : Value) : Erases id (Eval.asInt v) (Eval.asInt v.erase) := by
  cases v <;> first | exact pure id _ | exact fail id .stuck

theorem asBool (v : Value) : Erases id (Eval.asBool v) (Eval.asBool v.erase) := by
  cases v <;> first | exact pure id _ | exact fail id .stuck

theorem asList (v : Value) : Erases eraseValues (Eval.asList v) (Eval.asList v.erase) := by
  cases v <;> first | exact pure eraseValues _ | exact fail eraseValues .stuck

theorem list (h : Runs run run') :
    ∀ es, Erases eraseValues (Eval.list run es) (Eval.list run' (eraseExprs es))
  | [] => pure _ []
  | e :: es => bind (h e) fun v => bind (list h es) fun vs => pure eraseValues (v :: vs)

theorem fields (h : Runs run run') :
    ∀ fs, Erases eraseBindings (Eval.fields run fs) (Eval.fields run' (eraseFields fs))
  | [] => pure _ []
  | (f, e) :: fs => bind (h e) fun v => bind (fields h fs) fun vs =>
    pure eraseBindings ((f, v) :: vs)

theorem path (h : Runs run run') :
    ∀ ps, Erases id (Eval.path run ps) (Eval.path run' (erasePath ps))
  | [] => pure _ []
  | .field f :: ps => bind (path h ps) fun p => pure id (.field f :: p)
  | .index i :: ps =>
    bind (bind (h i) asInt) fun k => bind (path h ps) fun p => pure id (.index k :: p)

theorem args (h : Runs run run') :
    ∀ as, Erases (List.map Passed.erase) (Eval.args run as) (Eval.args run' (eraseArgs as))
  | [] => pure _ []
  | .value e :: as => bind (h e) fun v => bind (args h as) fun vs =>
    pure' (by simp [Passed.ofArg_erase])
  | .inout ⟨x, ps⟩ :: as => bind (path h ps) fun p => bind (args h as) fun vs =>
    pure (List.map Passed.erase) (.place x p :: vs)

theorem declare (D : Decls) (R : Name) (written : List (Name × Value)) :
    Erases Value.erase (Eval.declare D R written)
      (Eval.declare D.erase R (eraseBindings written)) := by
  unfold Eval.declare
  rw [show D.erase.record? R = D.record? R from rfl]
  cases D.record? R with
  | none => exact fail _ _
  | some r =>
    simp only [mapM_lookup_erase]
    cases r.fields.mapM fun p => (written.lookup p.1).map (p.1, ·) with
    | none => exact fail _ _
    | some fs => exact pure Value.erase (.record R fs)

theorem select (h : Runs run run') (arms : List Arm) (v : Value) :
    Erases Value.erase (Eval.select Copy.memory run arms v)
      (Eval.select Copy.memory run' (eraseArms arms) v.erase) := by
  simp only [Eval.select, selectArm_erase]
  cases selectArm arms v with
  | none => exact fail _ _
  | some au =>
    obtain ⟨arm, us⟩ := au
    simp only [Option.map_some, length_eraseValues, zip_eraseValues]
    split
    · exact withVars (h arm.body) _
    · exact fail _ _

theorem assign (h : Runs run run') (x : Name) (ps : List Projection) (value : Expr) :
    Erases Value.erase (Eval.assign Copy.memory run x ps value)
      (Eval.assign Copy.memory run' x (erasePath ps) value.erase) :=
  bind (path h ps) fun p => bind (h value) fun v =>
    bind (update fun s => Copy.memory_write_erase s x p v) fun _ => pure _ Value.unit

theorem loop (h : Runs run run') (x : Name) (e body : Expr) :
    Erases Value.erase (Eval.loop Copy.memory run x e body)
      (Eval.loop Copy.memory run' x e.erase body.erase) :=
  bind (bind (h e) asList) fun vs =>
    bind (forEach (fun v => withVar x v (turn (h body))) vs) fun _ =>
      pure _ Value.unit

theorem call (D : Decls) (h : Runs run run') (f : Value) (as : List Passed) :
    Erases Value.erase (Eval.call D Copy.memory run f as)
      (Eval.call D.erase Copy.memory run' f.erase (as.map Passed.erase)) := by
  cases f
  case closure captured ps r ρ body => exact invoke captured ps as (h body)
  case function name types rows =>
    simp only [Eval.call, Value.erase, Decls.fn?_erase]
    cases D.fn? name with
    | none => exact fail _ _
    | some d =>
      simp only [Option.map_some, FnDecl.erase]
      rw [← Expr.erase_substTys, ← Expr.erase_substRows]
      exact invoke [] d.params as (h _)
  all_goals exact fail _ _

/-- A function value takes control as its erasure does. -/
theorem _root_.Stilt.Value.takesControl_erase (D : Decls) (f : Value) :
    f.erase.takesControl D.erase = f.takesControl D := by
  cases f <;> simp [Value.erase, Value.takesControl, Decls.fn?_erase]
  rename_i name _ _
  cases D.fn? name <;> rfl

theorem callAs (D : Decls) (h : Runs run run') (control : Bool) (f : Value) (as : List Passed) :
    Erases Value.erase (Eval.callAs D Copy.memory run control f as)
      (Eval.callAs D.erase Copy.memory run' control f.erase (as.map Passed.erase)) := by
  unfold Eval.callAs
  rw [Value.takesControl_erase]
  split
  · exact fail _ _
  · exact call D h f as

theorem perform (op : Operation) (v : Value) :
    Erases Value.erase (Eval.perform Copy.memory op v) (Eval.perform Copy.memory op v.erase) :=
  fun _ => ⟨⟨rfl, rfl, rfl⟩, fun _ _ _ _ ⟨hw, hx⟩ => ⟨hw, by rw [hx]; rfl⟩⟩

/-- A handler's clause, erased, is the erasure's clause. -/
theorem _root_.Stilt.Value.clause?_erase (hv : Value) (n : Name) :
    hv.erase.clause? n = (hv.clause? n).map Value.erase := by
  cases hv <;> simp [Value.erase, Value.clause?, lookup_eraseBindings]

/-- A `with` handles alike what its block and the block's erasure end with,
its clauses erased (handlers.with). -/
theorem handleWith (D : Decls) (h : Runs run run') (E : Name) (c : Bool) (hv : Value)
    {m m' : Eval Copy.State Value} (hm : Erases Value.erase m m') :
    Erases Value.erase
      (Eval.handleWith Copy.memory E c hv
        (fun f v => Eval.callAs D Copy.memory run c f [.value v]) m)
      (Eval.handleWith Copy.memory E c hv.erase
        (fun f v => Eval.callAs D.erase Copy.memory run' c f [.value v]) m') := by
  intro s
  refine Outcome.Rel.handleWith (R := Outcome.erasing Value.erase) (C := fun c c' => c' = c.erase)
    (fun _ _ _ _ _ _ h => h.1) (fun n => ?_) ?_ (fun _ _ _ _ _ h => ⟨h.1, by rw [h.2]; rfl⟩)
    (fun _ _ _ _ _ h => ⟨h.2.1, by rw [h.2.2]; rfl⟩) ?_ (hm s)
  · rw [Value.clause?_erase]
    unfold ClauseRel
    cases hv.clause? n <;> trivial
  · rintro f _ op v s₁ _ _ rfl ⟨-, rfl, rfl⟩
    exact callAs D h c f [.value v] s₁
  · rintro _ s₁ _ t ⟨-, rfl⟩
    exact ⟨fun _ _ _ _ h => ⟨h.1, by rw [h.2]; rfl⟩, fun _ _ _ _ h => ⟨h.1, by rw [h.2]; rfl⟩,
      fun _ _ _ _ h => ⟨h.1, by rw [h.2]; rfl⟩, fun _ _ _ _ h => ⟨h.1, by rw [h.2]; rfl⟩,
      fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, by rw [h.2.2]; rfl⟩⟩

end Eval.Erases

/-! ## Evaluation -/

open Eval.Erases in
/-- **Copy-in, copy-out sees through marks.** Evaluating an expression's
erasure, from a state with the marks of its frame erased, ends as evaluating the expression
does, erased, with the same fuel (values.passing-values). -/
theorem eval_erase (D : Decls) : ∀ (n : Nat) (e : Expr),
    Eval.Erases Value.erase (eval D Copy.memory n e) (eval D.erase Copy.memory n e.erase)
  | 0, _ => fun _ => trivial
  | n + 1, e => by
    have ih : Runs (eval D Copy.memory n) (eval D.erase Copy.memory n) := eval_erase D n
    cases e with
    | var x | move x => exact inspect fun s => Copy.read_erase s.1 x []
    | int _ | bool _ | unit | fnRef _ _ _ => exact pure _ _
    | method t m τ =>
      show Eval.Erases Value.erase (Eval.method D t m τ) (Eval.method D.erase t m τ)
      rw [Decls.erase, Eval.method_mapFns]
      unfold Eval.method
      split
      · split
        · exact pure _ _
        · exact fail _ _
      · exact fail _ _
    | record R fs => exact bind (fields ih fs) fun w => declare D R w
    | variant T C es => exact bind (list ih es) fun vs => pure Value.erase (Value.variant T C vs)
    | list τ es => exact bind (list ih es) fun vs => pure Value.erase (Value.list vs)
    | op o es => exact bind (list ih es) fun vs => world (Op.run_erase o vs)
    | view es =>
      exact bind (list ih es) fun vs => by
        rw [Op.apply_erase]
        exact ofExcept Value.erase (Op.view.apply vs)
    | field e f => exact bind (ih e) fun v => get v [.field f]
    | index e i => exact bind (ih e) fun v => bind (bind (ih i) asInt) fun k => get v [.index k]
    | closure ps r ρ body =>
      refine bind (inspect (r := Copy.memory.capture) fun _ => rfl) fun c => ?_
      rw [captureOf_erase]
      exact pure Value.erase (Value.closure (captureOf ps body c) ps r ρ body)
    | call callee as =>
      exact bind (ih callee) fun f => bind (args ih as) fun passed => callAs D ih false f passed
    | letIn x τ init body | varIn x τ init body =>
      exact bind (ih init) fun v => withInit x init init.erase v (ih body)
    | assign p value =>
      obtain ⟨x, ps⟩ := p
      exact assign ih x ps value
    | seq a b => exact bind (ih a) fun _ => ih b
    | «if» c τ a b => exact bind (bind (ih c) asBool) fun v => ite v (ih a) (ih b)
    | «match» e τ arms => exact bind (ih e) fun v => select ih arms v
    | «for» x τ e body => exact loop ih x e body
    | raise e => exact bind (ih e) fun v => throw _ v
    | «try» e => exact ih e
    | tryCatch e E x hd τ => exact handle (ih e) fun err => withVar x err (ih hd)
    | «while» c body =>
      exact bind (bind (ih c) asBool) fun v => ite v
        (bind (turn (ih body)) fun g => ite g (ih (.while c body)) (pure _ Value.unit))
        (pure _ Value.unit)
    | «loop» body =>
      exact bind (turn (ih body)) fun g => ite g (ih (.loop body)) (pure _ Value.unit)
    | «break» => exact jump _ .brk
    | «continue» => exact jump _ .cont
    | «return» e => exact bind (ih e) fun v => jump _ (.ret v)
    | perform op e => exact bind (ih e) fun v => perform op v
    | withH E c hd b => exact bind (ih hd) fun hv => letGo (handleWith D ih E c hv (ih b))
    | held ns hs body => exact bind (list ih hs) fun vs => held (ih body) (ns.map Prod.fst) vs

/-- **Copy-in, copy-out runs a program as its erasure.** What a run of a
program shows, with the marks of the values it shows erased, is what a run of
its erasure shows, with the same fuel (values.passing-values). -/
theorem Program.runCopy_erase (p : Program) (fuel : Nat) (input : String) :
    (p.runCopy fuel input).observe.erase = (p.erase.runCopy fuel input).observe := by
  show (eval p.decls Copy.memory fuel p.main ([], World.start input)).leaveBody.observe.erase =
    (eval p.erase.decls Copy.memory fuel p.erase.main ([], World.start input)).leaveBody.observe
  exact (eval_erase p.decls fuel p.main ([], World.start input)).observe_erase

/-- A run of a program and a run of its erasure write the same output. -/
theorem Program.runCopy_output_erase (p : Program) (fuel : Nat) (input : String) :
    (p.runCopy fuel input).output = (p.erase.runCopy fuel input).output := by
  show (eval p.decls Copy.memory fuel p.main ([], World.start input)).leaveBody.output =
    (eval p.erase.decls Copy.memory fuel p.erase.main ([], World.start input)).leaveBody.output
  exact (eval_erase p.decls fuel p.main ([], World.start input)).output_erase

end Stilt
