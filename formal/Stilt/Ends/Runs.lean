import Stilt.Ends.Halts
import Stilt.Ends.Instances
import Stilt.Ends.Entry

/-!
# Runs that halt

The evaluator's steps that run expressions halt, in copy-in, copy-out, given that running
an expression free of `div` whose depth is at most `k` does, from every state whose frame
meets its roles (`HaltsRun`): lists of expressions, a record's fields, a place's indexes, a
call's arguments, a `match`, an assignment and a `for` loop, whose turns cost no fuel. Each
step keeps the variables it doesn't write, so the frame the next starts from meets the roles
too (`Roles.Inv.after`).
-/

namespace Stilt

/-- Running an expression free of `div` where `me` says, of depth at most `k`, halts from
every state whose frame meets its roles, against what `m` knows of the call, when no
variable with a role is written. -/
def HaltsRun (D : Decls) (w : WriteBack) (lim : Limited) (B : Name → Nat) (H : Name → List Nat)
    (me : Option (Name × Descent)) (m : Meas) (k : Nat) : Prop :=
  ∀ e R, e.divFree lim B H me R = true → e.depth ≤ k → R.Avoids e.writes → ∀ s : Copy.State,
    R.Inv s.1 m → Halts (fun n => eval D (Copy.memoryWith w) n e) (fun _ => True) s

theorem Expr.one_le_depth (e : Expr) : 1 ≤ e.depth := by
  cases e
  case assign t _ => obtain ⟨_, _⟩ := t; simp [Expr.depth]
  all_goals simp [Expr.depth]

namespace Eval.Ends

variable {σ : Type}

theorem asInt (v : Value) : Eval.Ends (fun _ => True) (Eval.asInt v : Eval σ Int) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem asBool (v : Value) : Eval.Ends (fun _ => True) (Eval.asBool v : Eval σ Bool) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem asList (v : Value) : Eval.Ends (fun _ => True) (Eval.asList v : Eval σ (List Value)) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem declare (D : Decls) (R : Name) (written : List (Name × Value)) :
    Eval.Ends (fun _ => True) (Eval.declare D R written : Eval σ Value) := by
  unfold Eval.declare
  split
  · split
    · exact pure trivial
    · exact fail _
  · exact fail _

end Eval.Ends

/-- Binding names in turn, in copy-in, copy-out, pushes them on the frame. -/
theorem Copy.foldl_bind (w : WriteBack) : ∀ (bs : List (Name × Value)) (s : Copy.State),
    (bs.foldl (fun s b => (Copy.memoryWith w).bind s b.1 b.2) s).1 =
      bs.foldl (fun fr b => (b.1, b.2) :: fr) s.1
  | [], _ => rfl
  | _ :: bs, _ => Copy.foldl_bind w bs _

/-- An index, then its value as an integer, keeps what the index doesn't write. -/
theorem keepsIndex (D : Decls) (w : WriteBack) (n : Nat) (i : Expr) :
    Eval.Keeps i.writes i.resizes (fun _ => True) (eval D (Copy.memoryWith w) n i >>= Eval.asInt) :=
  Eval.Keeps.bind (eval_keeps D w n i _ _ (List.Subset.refl _) (List.Subset.refl _))
    fun v _ => Eval.Keeps.asInt v

/-- A condition, then its value as a Boolean, keeps what the condition doesn't write. -/
theorem keepsBool (D : Decls) (w : WriteBack) (n : Nat) (c : Expr) :
    Eval.Keeps c.writes c.resizes (fun _ => True) (eval D (Copy.memoryWith w) n c >>= Eval.asBool) :=
  Eval.Keeps.bind (eval_keeps D w n c _ _ (List.Subset.refl _) (List.Subset.refl _))
    fun v _ => Eval.Keeps.asBool v

namespace Halts

variable {σ α : Type} {P : α → Prop}

/-- Binding names in turn halts where the code they scope halts. -/
theorem withVarsAt (M : Memory σ) {F : Nat → Eval σ α} :
    ∀ (bs : List (Name × Value)) (s : σ), Halts F P (bs.foldl (fun s b => M.bind s b.1 b.2) s) →
      Halts (fun n => Eval.withVars M bs (F n)) P s
  | [], _, h => h
  | (x, v) :: bs, _, h => withVar M x v (withVarsAt M bs _ h)

variable {D : Decls} {w : WriteBack} {lim : Limited} {B : Name → Nat} {H : Name → List Nat}
  {me : Option (Name × Descent)} {m : Meas} {k : Nat}

section Runs

variable (h : HaltsRun D w lim B H me m k)
include h

theorem list : ∀ (es : List Expr) {R : Roles}, exprsDivFree lim B H me R es = true →
    exprsDepth es ≤ k → R.Avoids (exprsWrites es) → ∀ s : Copy.State, R.Inv s.1 m →
      Halts (fun n => Eval.list (eval D (Copy.memoryWith w) n) es) (fun _ => True) s
  | [], _, _, _, _, _, _ => const (Eval.Ends.pure trivial)
  | e :: es, R, hd, hn, hA, s, hI => by
    simp only [exprsDivFree, exprsDepth, Bool.and_eq_true, Nat.max_le] at hd hn
    have hA₁ : R.Avoids e.writes := hA.mono (List.subset_append_left _ _)
    exact bind (h e R hd.1 hn.1 hA₁ s hI) fun _ s' _ hd' =>
      bind (list es hd.2 hn.2 (hA.mono (List.subset_append_right _ _)) s' (hI.afterEval hA₁ hd'))
        fun _ _ _ _ => const (Eval.Ends.pure trivial)

theorem fields : ∀ (fs : List (Name × Expr)) {R : Roles}, fieldsDivFree lim B H me R fs = true →
    fieldsDepth fs ≤ k → R.Avoids (fieldsWrites fs) → ∀ s : Copy.State, R.Inv s.1 m →
      Halts (fun n => Eval.fields (eval D (Copy.memoryWith w) n) fs) (fun _ => True) s
  | [], _, _, _, _, _, _ => const (Eval.Ends.pure trivial)
  | (_, e) :: fs, R, hd, hn, hA, s, hI => by
    simp only [fieldsDivFree, fieldsDepth, Bool.and_eq_true, Nat.max_le] at hd hn
    have hA₁ : R.Avoids e.writes := hA.mono (List.subset_append_left _ _)
    exact bind (h e R hd.1 hn.1 hA₁ s hI) fun _ s' _ hd' =>
      bind (fields fs hd.2 hn.2 (hA.mono (List.subset_append_right _ _)) s' (hI.afterEval hA₁ hd'))
        fun _ _ _ _ => const (Eval.Ends.pure trivial)

theorem path : ∀ (ps : List Projection) {R : Roles}, pathDivFree lim B H me R ps = true →
    pathDepth ps ≤ k → R.Avoids (pathWrites ps) → ∀ s : Copy.State, R.Inv s.1 m →
      Halts (fun n => Eval.path (eval D (Copy.memoryWith w) n) ps) (fun _ => True) s
  | [], _, _, _, _, _, _ => const (Eval.Ends.pure trivial)
  | .field _ :: ps, R, hd, hn, hA, s, hI => by
    simp only [pathDivFree, pathDepth] at hd hn
    exact bind (path ps hd hn hA s hI) fun _ _ _ _ => const (Eval.Ends.pure trivial)
  | .index i :: ps, R, hd, hn, hA, s, hI => by
    simp only [pathDivFree, pathDepth, Bool.and_eq_true, Nat.max_le] at hd hn
    have hA₁ : R.Avoids i.writes := hA.mono (List.subset_append_left _ _)
    exact bind (bind (h i R hd.1 hn.1 hA₁ s hI) fun v _ _ _ => const (Eval.Ends.asInt v))
      fun _ s' _ hd' => bind (path ps hd.2 hn.2 (hA.mono (List.subset_append_right _ _)) s'
        (hI.after (keepsIndex D w · i) hA₁ hd'))
        fun _ _ _ _ => const (Eval.Ends.pure trivial)

theorem args : ∀ (as : List Arg) {R : Roles}, argsDivFree lim B H me R as = true →
    argsDepth as ≤ k → R.Avoids (argsWrites as) → ∀ s : Copy.State, R.Inv s.1 m →
      Halts (fun n => Eval.args (eval D (Copy.memoryWith w) n) as) (fun _ => True) s
  | [], _, _, _, _, _, _ => const (Eval.Ends.pure trivial)
  | .value e :: as, R, hd, hn, hA, s, hI => by
    simp only [argsDivFree, argsDepth, Bool.and_eq_true, Nat.max_le] at hd hn
    have hA₁ : R.Avoids e.writes := hA.mono (List.subset_append_left _ _)
    exact bind (h e R hd.1 hn.1 hA₁ s hI) fun _ s' _ hd' =>
      bind (args as hd.2 hn.2 (hA.mono (List.subset_append_right _ _)) s' (hI.afterEval hA₁ hd'))
        fun _ _ _ _ => const (Eval.Ends.pure trivial)
  | .inout ⟨_, ps⟩ :: as, R, hd, hn, hA, s, hI => by
    simp only [argsDivFree, argsDepth, Bool.and_eq_true, Nat.max_le] at hd hn
    have hA₁ : R.Avoids (pathWrites ps) := hA.mono fun z hz =>
      List.mem_cons_of_mem _ (List.mem_append_left _ hz)
    exact bind (path h ps hd.1 hn.1 hA₁ s hI) fun _ s' _ hd' =>
      bind (args as hd.2 hn.2 (hA.mono fun z hz => List.mem_cons_of_mem _ (List.mem_append_right _ hz))
        s' (hI.after (fun n => Eval.Keeps.path (W := pathWrites ps) (L := pathResizes ps)
          (eval_keeps D w n) ps (List.Subset.refl _) (List.Subset.refl _)) hA₁ hd'))
        fun _ _ _ _ => const (Eval.Ends.pure trivial)

/-- An arm with a guard halts: its guard with each way of its pattern, then its body or what
comes next. Its binders have a role only when its pattern has no or-pattern, so that it has one
way, the one its pattern matches. -/
theorem guarded {p : Pattern} {xs : List Name} {g body : Expr} {R : Roles} {r : Role}
    (hgd : g.divFree lim B H me (R.bindAll xs (Arm.role r ⟨p, xs, some g, body⟩)) = true)
    (hgn : g.depth ≤ k)
    (hbd : body.divFree lim B H me (R.bindAll xs (Arm.role r ⟨p, xs, some g, body⟩)) = true)
    (hbn : body.depth ≤ k) (hA : R.Avoids (g.writes ++ body.writes)) {v : Value}
    (hv : r.Holds v m) {next : Nat → Eval Copy.State Value}
    (hnext : ∀ s : Copy.State, R.Inv s.1 m → Halts next (fun _ => True) s) :
    ∀ ways : List (List Value), (∀ us ∈ ways, ∀ u ∈ us,
        (Arm.role r ⟨p, xs, some g, body⟩).Holds u m) → ∀ s : Copy.State, R.Inv s.1 m →
      Halts (fun n => Eval.guarded (Copy.memoryWith w) (eval D (Copy.memoryWith w) n) xs g body
        (next n) ways) (fun _ => True) s
  | [], _, s, hI => hnext s hI
  | us :: ways, hw, s, hI => by
    simp only [Eval.guarded]
    split
    case isFalse => exact const (Eval.Ends.fail _)
    rename_i hlen
    have hAg : R.Avoids g.writes := hA.mono (List.subset_append_left _ _)
    have hguard : Halts (fun n => Eval.withVars (Copy.memoryWith w) (xs.zip us)
        (eval D (Copy.memoryWith w) n g >>= Eval.asBool)) (fun _ => True) s := by
      refine withVarsAt _ _ s (bind (h _ _ hgd hgn
        (Roles.Avoids.bindAll (fun hr x hx => Arm.role_avoids_guard (arm := ⟨p, xs, some g, body⟩)
          hr x hx) hAg) _ ?_) fun v _ _ _ => const (Eval.Ends.asBool v))
      rw [Copy.foldl_bind]
      exact hI.bindAll _ _ hlen (hw us List.mem_cons_self)
    simp only [Eval.tryWay]
    refine bind hguard fun b s' _ hd' => ?_
    have hI' : R.Inv s'.1 m := hI.after (W := g.writes) (L := g.resizes)
      (fun n => Eval.Keeps.withVars w (Eval.Keeps.bind (eval_keeps D w n g _ _
        (List.Subset.refl _) (List.Subset.refl _)) fun v _ => Eval.Keeps.asBool v) _) hAg hd'
    refine ite b ?_ (guarded hgd hgn hbd hbn hA hv hnext ways
      (fun us' hu => hw us' (List.mem_cons_of_mem _ hu)) s' hI')
    refine withVarsAt _ _ s' (h _ _ hbd hbn (Roles.Avoids.bindAll
      (Arm.role_avoids (arm := ⟨p, xs, some g, body⟩)) (hA.mono (List.subset_append_right _ _)))
      _ ?_)
    rw [Copy.foldl_bind]
    exact hI'.bindAll _ _ hlen (hw us List.mem_cons_self)

omit h in
/-- The ways of a pattern that the role of its arm reads: with a role, the pattern has no
or-pattern, so its one way is the one it matches. -/
theorem Arm.role_ways {arm : Arm} {r : Role} {v : Value} {us : List Value} {m : Meas}
    (hv : r.Holds v m) (hu : us ∈ arm.pattern.ways v) : ∀ u ∈ us, (arm.role r).Holds u m := by
  intro u hu'
  unfold Arm.role
  split
  · rename_i hw
    simp only [Bool.and_eq_true] at hw
    obtain ⟨q, hq, hqm⟩ := Pattern.mem_ways hu
    rw [Pattern.alternatives_within hw.1] at hq
    obtain rfl := List.mem_singleton.1 hq
    split
    · rename_i hs
      exact hv.step (Pattern.matchOn_lt _ hw.1 hs hqm u hu')
    · rename_i hs
      rw [Pattern.matchOn_same _ hw.1 (by simpa using hs) hqm u hu']
      exact hv
  · trivial

theorem select {R : Roles} {r : Role} {v : Value} (hv : r.Holds v m) :
    ∀ {arms : List Arm}, armsDivFree lim B H me R r arms = true → armsDepth arms ≤ k →
      R.Avoids (armsWrites arms) → ∀ (s : Copy.State), R.Inv s.1 m →
      Halts (fun n => Eval.select (Copy.memoryWith w) (eval D (Copy.memoryWith w) n) arms v)
        (fun _ => True) s
  | [], _, _, _, _, _ => const (Eval.Ends.fail _)
  | ⟨p, xs, guard, body⟩ :: arms, hd, hn, hA, s, hI => by
    simp only [armsDivFree, armsDepth, Bool.and_eq_true, Nat.max_le] at hd hn
    simp only [armsWrites] at hA
    have hrest := fun s hI => select hv hd.2 hn.2.2
      (hA.mono (List.subset_append_right _ _)) s hI
    simp only [Eval.select]
    cases guard with
    | none =>
      simp only
      cases hmatch : p.matchOn v with
      | none => exact hrest s hI
      | some us =>
        simp only
        split
        · rename_i hlen
          refine withVarsAt _ _ s (h _ _ hd.1.2 hn.2.1 ?_ _ ?_)
          · exact Roles.Avoids.bindAll (Arm.role_avoids (arm := ⟨p, xs, none, body⟩))
              (hA.mono fun z hz => List.mem_append_left _ (List.mem_append_right _ hz))
          · rw [Copy.foldl_bind]
            exact hI.bindAll _ _ hlen (Arm.role_holds (arm := ⟨p, xs, none, body⟩) hv hmatch)
        · exact const (Eval.Ends.fail _)
    | some g =>
      simp only [guardDivFree, guardDepth] at hd hn
      exact guarded h hd.1.1 hn.1 hd.1.2 hn.2.1
        (hA.mono fun z hz => by rcases List.mem_append.1 hz with hz | hz <;> simp [guardWrites, hz]) hv
        hrest _ (fun us hu => Arm.role_ways (arm := ⟨p, xs, some g, body⟩) hv hu) s hI

theorem assign (x : Name) {ps : List Projection} {R : Roles} (hd : pathDivFree lim B H me R ps = true)
    (hn : pathDepth ps ≤ k) {value : Expr} (hvd : value.divFree lim B H me R = true)
    (hvn : value.depth ≤ k) (hA : R.Avoids (pathWrites ps ++ value.writes)) (s : Copy.State)
    (hI : R.Inv s.1 m) :
    Halts (fun n => Eval.assign (Copy.memoryWith w) (eval D (Copy.memoryWith w) n) x ps value)
      (fun _ => True) s :=
  bind (path h ps hd hn (hA.mono (List.subset_append_left _ _)) s hI) fun _ s' _ hd' =>
    bind (h value R hvd hvn (hA.mono (List.subset_append_right _ _)) s'
      (hI.after (fun n => Eval.Keeps.path (W := pathWrites ps) (L := pathResizes ps)
        (eval_keeps D w n) ps (List.Subset.refl _) (List.Subset.refl _))
        (hA.mono (List.subset_append_left _ _)) hd')) fun _ _ _ _ =>
      bind (const (Eval.Ends.update _)) fun _ _ _ _ => const (Eval.Ends.pure trivial)

theorem loop (x : Name) {e body : Expr} {R : Roles} (hed : e.divFree lim B H me R = true)
    (hen : e.depth ≤ k) (hA : R.Avoids e.writes) (hbd : body.divFree lim B H me [] = true)
    (hbn : body.depth ≤ k) (s : Copy.State) (hI : R.Inv s.1 m) :
    Halts (fun n => Eval.loop (Copy.memoryWith w) (eval D (Copy.memoryWith w) n) x e body)
      (fun _ => True) s :=
  bind (bind (h e R hed hen hA s hI) fun v _ _ _ => const (Eval.Ends.asList v)) fun vs s' _ _ =>
    bind (forEach (fun v _ => withVar _ x v (turn (h body [] hbd hbn (Roles.Avoids.nil _) _
      (Roles.Inv.nil _ _)))) vs s') fun _ _ _ _ => const (Eval.Ends.pure trivial)

end Runs

end Halts

end Stilt
