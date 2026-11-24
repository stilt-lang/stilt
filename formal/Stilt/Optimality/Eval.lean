import Stilt.Optimality.Witness

/-!
# Evaluating the witness

What evaluating the parts of the witness gives, in any model of memory: the
literals, the variables of `main`, the reads of fields, the call and the
callee's body, whose read indexes `[0]`. `Stilt.Optimality.CopyRun` and
`Stilt.Optimality.InPlaceRun` fill in what each model does with the places.
-/

namespace Stilt.Optimality

variable {σ α β : Type}

theorem bind_done {m : Eval σ α} {f : α → Eval σ β} {s s' : σ} {a : α}
    (h : m s = .done a s') : (m >>= f) s = f a s' := by
  show Eval.bind m f s = _
  simp only [Eval.bind, Outcome.bind, h]

theorem bind_eq {m m' : Eval σ α} {f : α → Eval σ β} {s : σ} (h : m s = m' s) :
    (m >>= f) s = (m' >>= f) s := by
  show Eval.bind m f s = Eval.bind m' f s
  simp only [Eval.bind, h]

theorem mapM_eq_some {g : α → Option β} {h : α → β} :
    ∀ l : List α, (∀ x ∈ l, g x = some (h x)) → l.mapM g = some (l.map h)
  | [], _ => rfl
  | x :: l, hl => by
    rw [List.mapM_cons, hl x List.mem_cons_self,
      mapM_eq_some l fun y hy => hl y (List.mem_cons_of_mem _ hy)]
    rfl

/-! ## Values of the literals -/

section Literals

variable {F : List Name} {v : Name}

/-- Reading names of `F` from a literal's value reaches the value of the
literal with the budget less their number. -/
theorem litv_get (hv : v ∉ F) :
    ∀ {fs : List Name} {b : Nat}, (∀ f ∈ fs, f ∈ F) → fs.length ≤ b →
      (litv F v b).get (fs.map Step.field) = .ok (litv F v (b - fs.length))
  | [], _, _, _ => rfl
  | f :: fs, b, hfs, hlen => by
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by simp at hlen; omega⟩
    have hf := hfs f List.mem_cons_self
    have hne : f ≠ v := fun h => hv (h ▸ hf)
    have ih := litv_get hv (fs := fs) (b := b) (fun g hg => hfs g (List.mem_cons_of_mem _ hg))
      (by simp at hlen; omega)
    simp only [List.map_cons, litv, Value.get, lookup_cons_ne hne, lookup_map_const _ hf]
    simpa using ih

theorem litv_get_leaf (b : Nat) : (litv F v b).get [.field v] = .ok (.int 0) := by
  cases b <;> simp [litv, Value.get]

end Literals

/-! ## Evaluation in any model of memory -/

variable (D : Decls) (M : Memory σ)

theorem eval_fields_const {run : Expr → Eval σ Value} {e : Expr} {w : Value} {s : σ}
    (h : run e s = .done w s) :
    ∀ G : List Name, Eval.fields run (G.map fun f => (f, e)) s = .done (G.map fun f => (f, w)) s
  | [] => rfl
  | f :: G => by
    simp only [List.map_cons, Eval.fields]
    rw [bind_done h, bind_done (eval_fields_const h G)]
    rfl

/-- A literal evaluates to its value, in any state, with enough fuel. -/
theorem eval_lit {F : List Name} {v : Name} {K : Nat} (hD : D.records = recDecls F v K)
    (hv : v ∉ F) : ∀ {b n : Nat}, b ≤ K → b + 2 ≤ n → ∀ s,
      eval D M n (lit F v b) s = .done (litv F v b) s
  | 0, n + 1, hb, hn, s => by
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hfields : Eval.fields (eval D M (n + 1)) [(v, .int 0)] s = .done [(v, .int 0)] s := by
      simp only [Eval.fields]
      rw [bind_done (rfl : eval D M (n + 1) (.int 0) s = _)]
      rfl
    show (Eval.fields (eval D M (n + 1)) [(v, .int 0)] >>= Eval.declare D (recName 0)) s = _
    rw [bind_done hfields]
    simp only [Eval.declare, record?_recName hD hb, recDecl, recFields]
    rw [mapM_eq_some (h := fun p => (p.1, Value.int 0)) _ (by simp)]
    rfl
  | b + 1, n + 1, hb, hn, s => by
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have ih := eval_lit hD hv (b := b) (n := n + 1) (by omega) (by omega) s
    have hfields : Eval.fields (eval D M (n + 1)) ((v, .int 0) :: F.map fun f => (f, lit F v b)) s =
        .done ((v, .int 0) :: F.map fun f => (f, litv F v b)) s := by
      simp only [Eval.fields]
      rw [bind_done (rfl : eval D M (n + 1) (.int 0) s = _), bind_done (eval_fields_const ih F)]
      rfl
    show (Eval.fields (eval D M (n + 1)) ((v, .int 0) :: F.map fun f => (f, lit F v b)) >>=
      Eval.declare D (recName (b + 1))) s = _
    rw [bind_done hfields]
    simp only [Eval.declare, record?_recName hD hb, recDecl, recFields]
    rw [mapM_eq_some (h := fun p => (p.1, if p.1 = v then Value.int 0 else litv F v b)) _ ?_]
    · have hmap : ((F.map fun f => (f, recTy b)).map
          fun p => (p.1, if p.1 = v then Value.int 0 else litv F v b)) =
          F.map fun f => (f, litv F v b) := by
        simp only [List.map_map]
        refine List.map_congr_left fun f hf => ?_
        have hne : f ≠ v := fun h => hv (h ▸ hf)
        simp [hne]
      simp only [List.map_cons, hmap]
      rfl
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
        have hne : f ≠ v := fun h => hv (h ▸ hf)
        simp [lookup_cons_ne hne, lookup_map_const _ hf, hne]

/-- Binding a variable doesn't change what a run of `main`'s body shows
(expressions.scope). -/
theorem observe_withVar (x : Name) (w : Value) (m : Eval σ Value) (s : σ) :
    (Eval.withVar M x w m s).leaveBody.observe = (m (M.bind s x w)).leaveBody.observe := by
  unfold Eval.withVar Outcome.unbind
  cases m (M.bind s x w) with
  | jumped j _ => cases j <;> rfl
  | _ => rfl

theorem observe_withVars : ∀ (bs : List (Name × Value)) (m : Eval σ Value) (s : σ),
    (Eval.withVars M bs m s).leaveBody.observe =
      (m (bs.foldl (fun s xv => M.bind s xv.1 xv.2) s)).leaveBody.observe
  | [], _, _ => rfl
  | (x, w) :: bs, m, s => by
    simp only [Eval.withVars, List.foldl_cons]
    rw [observe_withVar, observe_withVars bs]

/-- The variables of `main`, each initialized with a value that doesn't
depend on the state, bind each name to it in turn (values.let-and-var). -/
theorem eval_vars {τ : Ty} {init e : Expr} {w : Value} {n₀ : Nat}
    (hinit : ∀ m, n₀ ≤ m → ∀ s, eval D M m init s = .done w s) (hmove : ∀ y, init ≠ .move y) :
    ∀ (xs : List Name) {n : Nat}, n₀ ≤ n →
      eval D M (n + xs.length) (vars τ init xs e) =
        Eval.withVars M (xs.map fun x => (x, w)) (eval D M n e)
  | [], _, _ => rfl
  | x :: xs, n, hn => by
    funext s
    rw [show n + (x :: xs).length = (n + xs.length) + 1 by simp; omega]
    show (eval D M (n + xs.length) init >>= fun u =>
      Eval.withInit M x init u (eval D M (n + xs.length) (vars τ init xs e))) s = _
    rw [bind_done (hinit _ (by omega) s), Eval.withInit_eq_withVar M x hmove,
      eval_vars hinit hmove xs hn]
    rfl

/-- Reading fields of an expression reads them from its value (types.field-access). -/
theorem eval_project {s : σ} :
    ∀ (fs : List Name) (e : Expr) (n : Nat) (w w' : Value), eval D M n e s = .done w s →
      w.get (fs.map Step.field) = .ok w' → eval D M (n + fs.length) (e.project fs) s = .done w' s
  | [], _, _, _, _, he, hw => by
    cases hw
    exact he
  | f :: fs, e, n, w, w', he, hw => by
    rw [List.map_cons, show Step.field f :: fs.map Step.field = [.field f] ++ fs.map Step.field
      from rfl, Value.get_append] at hw
    cases hf : w.get [.field f] with
    | error _ => simp [hf, Except.bind] at hw
    | ok w₁ =>
      simp only [hf, Except.bind] at hw
      have hstep : eval D M (n + 1) (.field e f) s = .done w₁ s := by
        show (eval D M n e >>= fun u => Eval.ofExcept (u.get [.field f])) s = _
        rw [bind_done he]
        simp [Eval.ofExcept, hf]
      rw [show n + (f :: fs).length = (n + 1) + fs.length by simp; omega]
      exact eval_project fs (.field e f) (n + 1) w₁ w' hstep hw

/-! ## The call and the callee's body -/

theorem eval_path_fields (run : Expr → Eval σ Value) (s : σ) :
    ∀ fs : List Name, Eval.path run (fs.map .field) s = .done (fs.map Step.field) s
  | [] => rfl
  | f :: fs => by
    simp only [List.map_cons, Eval.path]
    rw [bind_done (eval_path_fields run s fs)]
    rfl

/-- The call's arguments have no index, so evaluating them only names their
places (values.index-reads). -/
theorem eval_args_places (run : Expr → Eval σ Value) (s : σ) :
    ∀ ts : List Shape, Eval.args run (ts.map placeArg) s = .done (ts.map placePassed) s
  | [] => rfl
  | t :: ts => by
    simp only [List.map_cons, placeArg, Shape.toPlace, Eval.args]
    rw [bind_done (eval_path_fields run s t.fields), bind_done (eval_args_places run s ts)]
    rfl

theorem bindArgs_params : ∀ (ts : List Shape) (f : Nat → Name) (ty : Shape → Ty),
    bindArgs (ts.mapIdx fun i s => ⟨.inout, f i, ty s, none⟩) (ts.map placePassed) =
      some (ts.mapIdx fun i s => (f i, placePassed s))
  | [], _, _ => rfl
  | t :: ts, f, ty => by
    simp only [List.mapIdx_cons, List.map_cons]
    simp only [placePassed, bindArgs]
    rw [bindArgs_params ts (fun i => f (i + 1)) ty]
    rfl

/-- The call binds each parameter to its place. -/
theorem bindArgs_witness (ss : List Shape) :
    bindArgs (params ss) (ss.map placePassed) = some (bound ss) :=
  bindArgs_params ss _ _

theorem invoke_done {captured : List (Name × Value)} {params : List Param} {args : List Passed}
    {body : Eval σ Value} {s sc s' s'' : σ} {bound : List (Name × Passed)} {r : Value}
    (hb : bindArgs params args = some bound) (he : M.enter s captured bound = .ok sc)
    (hbody : body sc = .done r s') (hl : M.leave s s' bound = .ok s'') :
    Eval.invoke M captured params args body s = .done r s'' := by
  simp [Eval.invoke, Outcome.leaveCall, hb, he, hbody, hl]

/-- A panic in the callee's body is the call's, once the call ends as it ends
on a return (values.inout-arguments): nothing can observe an `inout` argument
after a panic, but what the program wrote before it stays written. -/
theorem invoke_panicked {captured : List (Name × Value)} {params : List Param}
    {args : List Passed} {body : Eval σ Value} {s sc s' s'' : σ} {bound : List (Name × Passed)}
    {k : PanicKind} (hb : bindArgs params args = some bound)
    (he : M.enter s captured bound = .ok sc) (hbody : body sc = .panicked k s')
    (hl : M.leave s s' bound = .ok s'') :
    Eval.invoke M captured params args body s = .panicked k s'' := by
  simp [Eval.invoke, Outcome.leaveCall, hb, he, hbody, hl]

theorem project_substRows (ρ : RowSubst) :
    ∀ (fs : List Name) (e : Expr), (e.project fs).substRows ρ = (e.substRows ρ).project fs
  | [], _ => rfl
  | f :: fs, e => by
    rw [show (e.project (f :: fs)) = (Expr.field e f).project fs from rfl, project_substRows ρ fs]
    rfl

variable (ss : List Shape) (a b : Nat) (extra : List Name)

theorem body_substRows : (body ss a b extra).substRows [] = body ss a b extra := by
  simp [body, probe, read, Expr.substRows, substExprRows, substPathRows, project_substRows,
    Ty.substRows]

/-- The call runs the callee's body on its places (values.index-reads). -/
theorem eval_theCall (hfn : D.fn? "witness" = some (callee ss a b extra)) (n : Nat) (s : σ) :
    eval D M (n + 2) (theCall ss) s =
      Eval.invoke M [] (params ss) (ss.map placePassed)
        (eval D M (n + 1) (body ss a b extra)) s := by
  show (eval D M (n + 1) (.fnRef "witness" [] []) >>= fun f =>
    Eval.args (eval D M (n + 1)) (ss.map placeArg) >>= fun passed =>
      Eval.callAs D M (eval D M (n + 1)) false f passed) s = _
  rw [bind_done (rfl : eval D M (n + 1) (.fnRef "witness" [] []) s = .done (.function "witness" [] []) s),
    bind_done (eval_args_places _ s ss)]
  have hc : (Value.function "witness" [] []).takesControl D = false := by
    simp [Value.takesControl, hfn, callee]
    rfl
  simp only [Eval.callAs, hc, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Eval.call, hfn]
  rw [show (callee ss a b extra).rowParams.zip [] = [] from rfl,
    show (callee ss a b extra).typeArgs [] = [] from rfl, Expr.substTys_nil]
  simp only [callee, body_substRows]

variable {D M ss a b extra}

/-- The read `p_a.extra.v` of the callee's body, in a state where `p_a` holds
`wa`, gives `wa`'s part below `extra` and `v` (types.field-access). -/
theorem eval_read {m : Nat} {s : σ} {wa r : Value} (hr : M.read s (nameOf 'p' a) [] = .ok wa)
    (hg : wa.get ((extra ++ [leafName ss]).map Step.field) = .ok r) :
    eval D M (m + extra.length + 2) (read ss a extra) s = .done r s := by
  rw [List.map_append, Value.get_append] at hg
  cases hd : wa.get (extra.map Step.field) with
  | error _ => simp [hd, Except.bind] at hg
  | ok wd =>
    simp only [hd, Except.bind, List.map_cons, List.map_nil] at hg
    have hvar : eval D M (m + 1) (.var (nameOf 'p' a)) s = .done wa s := by
      simp [eval, Eval.inspect, Eval.ofExcept, hr]
    have hproj := eval_project D M extra _ (m + 1) wa wd hvar hd
    show (eval D M (m + extra.length + 1) ((Expr.var (nameOf 'p' a)).project extra) >>= fun u =>
      Eval.ofExcept (u.get [.field (leafName ss)])) s = _
    rw [show m + extra.length + 1 = m + 1 + extra.length by omega, bind_done hproj]
    simp [Eval.ofExcept, hg]

/-- The callee's body, `p_b.v = 1; let r: i64 = [0][p_a.extra.v]`, in any model
of memory: the write, then the read, whose value indexes `[0]` (values.let-and-var and values.assignment-order; std.lists). -/
theorem eval_body {m : Nat} {s s' : σ} {wa : Value} {k : Int}
    (hw : M.write s (nameOf 'p' b) [.field (leafName ss)] (.int 1) = .ok s')
    (hr : M.read s' (nameOf 'p' a) [] = .ok wa)
    (hg : wa.get ((extra ++ [leafName ss]).map Step.field) = .ok (.int k)) :
    eval D M (m + extra.length + 5) (body ss a b extra) s =
      (Eval.ofExcept ((Value.list [.int 0]).get [.index k]) >>= fun w =>
        Eval.withVar M "r" w (Eval.pure .unit)) s' := by
  have hassign : eval D M (m + extra.length + 4)
      (.assign ⟨nameOf 'p' b, [.field (leafName ss)]⟩ (.int 1)) s = .done .unit s' := by
    show Eval.assign M (eval D M (m + extra.length + 3)) (nameOf 'p' b)
      [.field (leafName ss)] (.int 1) s = _
    unfold Eval.assign
    have hp : Eval.path (eval D M (m + extra.length + 3)) [.field (leafName ss)] s =
        .done [.field (leafName ss)] s := eval_path_fields _ s [leafName ss]
    rw [bind_done hp,
      bind_done (rfl : eval D M (m + extra.length + 3) (.int 1) s = .done (.int 1) s)]
    have hu : Eval.update (fun s => M.write s (nameOf 'p' b) [.field (leafName ss)] (.int 1)) s =
        .done () s' := by
      simp [Eval.update, hw]
    rw [bind_done hu]
    rfl
  have hlist : eval D M (m + extra.length + 2) (.list .i64 [.int 0]) s' =
      .done (.list [.int 0]) s' := rfl
  have hindex : eval D M (m + extra.length + 3) (probe (read ss a extra)) s' =
      Eval.ofExcept ((Value.list [.int 0]).get [.index k]) s' := by
    show (eval D M (m + extra.length + 2) (.list .i64 [.int 0]) >>= fun v =>
      (eval D M (m + extra.length + 2) (read ss a extra) >>= Eval.asInt) >>= fun k =>
        Eval.ofExcept (v.get [.index k])) s' = _
    have hk : (eval D M (m + extra.length + 2) (read ss a extra) >>= Eval.asInt) s' =
        .done k s' := (bind_done (eval_read hr hg)).trans rfl
    rw [bind_done hlist, bind_done hk]
  show (eval D M (m + extra.length + 4) _ >>= fun _ => eval D M (m + extra.length + 4) _) s = _
  rw [bind_done hassign]
  show (eval D M (m + extra.length + 3) (probe (read ss a extra)) >>= fun v =>
    Eval.withInit M "r" (probe (read ss a extra)) v (eval D M (m + extra.length + 3) .unit)) s' = _
  exact bind_eq hindex

end Stilt.Optimality
