import Stilt.Views.Cases

/-!
# The forms of expressions

The cases of the simulation for the forms of expressions that hold no place
and no loop: literals, fields, indexing, blocks, `if`, and the functions of a
view (views.functions-of-views). Each is stated on the step that the evaluator takes
with fuel `n + 1`, from the simulation at fuel `n`.
-/

namespace Stilt.Views

variable {D : Decls} {loops : Bool} {n : Nat}

namespace Simulates

variable {Γ : Sources} {R : List Shape} {sw sc : VState}

theorem vals (ih : Simulates D loops n) : ∀ (es : List VExpr) {sw sc : VState},
    exprsExclusive loops Γ R es = true → exprsContained Γ es = true → StateAgrees sw sc →
    InScope Γ R sw.env →
    Agree (Operand R sw) (Run.vals (veval D .window n) es sw) (Run.vals (veval D .copy n) es sc)
  | [], _, _, _, _, hst, _ => ⟨rfl, hst, Steps.refl R _⟩
  | e :: es, _, _, hex, hco, hst, hsc => by
    simp only [exprsExclusive, exprsContained, Bool.and_eq_true] at hex hco
    refine Agree.bind (ih.value hex.1 hco.1 hst hsc) fun s₁ sc₁ v v' ho₁ => ?_
    refine Agree.bind (vals ih es hex.2 hco.2 ho₁.states (hsc.after ho₁.steps))
      fun s₂ sc₂ vs vs' ho₂ => ?_
    exact ⟨by rw [ho₁.eq, ho₂.eq], ho₂.states, ho₁.steps.trans ho₂.steps fun _ h => h⟩

theorem fields (ih : Simulates D loops n) : ∀ (fs : List (Name × VExpr)) {sw sc : VState},
    fieldsExclusive loops Γ R fs = true → fieldsContained Γ fs = true → StateAgrees sw sc →
    InScope Γ R sw.env →
    Agree (Operand R sw) (Run.fields (veval D .window n) fs sw)
      (Run.fields (veval D .copy n) fs sc)
  | [], _, _, _, _, hst, _ => ⟨rfl, hst, Steps.refl R _⟩
  | (f, e) :: fs, _, _, hex, hco, hst, hsc => by
    simp only [fieldsExclusive, fieldsContained, Bool.and_eq_true] at hex hco
    refine Agree.bind (ih.value hex.1 hco.1 hst hsc) fun s₁ sc₁ v v' ho₁ => ?_
    refine Agree.bind (fields ih fs hex.2 hco.2 ho₁.states (hsc.after ho₁.steps))
      fun s₂ sc₂ vs vs' ho₂ => ?_
    exact ⟨by rw [ho₁.eq, ho₂.eq], ho₂.states, ho₁.steps.trans ho₂.steps fun _ h => h⟩

end Simulates

theorem declare_agrees {R : List Shape} {s₀ sw sc : VState} {T : Name}
    {w : List (Name × Value)} (hst : StateAgrees sw sc) (hs : Steps R s₀ sw) :
    Agree (Operand R s₀) (Eval.declare D T w sw) (Eval.declare D T w sc) := by
  unfold Eval.declare
  cases D.record? T with
  | none => exact Agree.stuck
  | some r =>
    dsimp only
    generalize List.mapM (fun x => Option.map (fun y => (x.fst, y)) (List.lookup x.fst w))
      r.fields = o
    cases o
    · exact Agree.stuck
    · exact ⟨rfl, hst, hs⟩

section Forms

variable (ih : Simulates D loops n) {Γ : Sources} {R S : List Shape} {sw sc : VState}
  (hst : StateAgrees sw sc) (hsc : InScope Γ R sw.env)
include ih hst hsc

theorem sim_record {T : Name} {fs : List (Name × VExpr)}
    (hex : fieldsExclusive loops Γ R fs = true) (hco : fieldsContained Γ fs = true) :
    Agree (Post R S sw)
      ((Run.fields (veval D .window n) fs >>= fun w => Eval.declare D T w >>= fun v =>
        pure (.val v)) sw)
      ((Run.fields (veval D .copy n) fs >>= fun w => Eval.declare D T w >>= fun v =>
        pure (.val v)) sc) :=
  Agree.bind (ih.fields fs hex hco hst hsc) fun _ _ w w' ho => by
    cases ho.eq
    exact Agree.bind (declare_agrees ho.states ho.steps) fun _ _ v v' ho' => by
      cases ho'.eq
      exact Post.val ho'.states ho'.steps

theorem sim_list {es : List VExpr} (hex : exprsExclusive loops Γ R es = true)
    (hco : exprsContained Γ es = true) :
    Agree (Post R S sw) ((Run.vals (veval D .window n) es >>= fun vs => pure (.val (.list vs))) sw)
      ((Run.vals (veval D .copy n) es >>= fun vs => pure (.val (.list vs))) sc) :=
  Agree.bind (ih.vals es hex hco hst hsc) fun _ _ vs vs' ho => by
    cases ho.eq
    exact Post.val ho.states ho.steps

theorem sim_field {e : VExpr} {f : Name} (hex : e.exclusive loops Γ R = true)
    (hco : e.contained Γ = true) :
    Agree (Post R S sw)
      ((veval D .window n e >>= Run.asVal >>= fun v => Eval.ofExcept (lift (v.get [.field f]))) sw)
      ((veval D .copy n e >>= Run.asVal >>= fun v => Eval.ofExcept (lift (v.get [.field f]))) sc) :=
  Agree.bind (ih.value hex hco hst hsc) fun _ _ v v' ho => by
    cases ho.eq
    exact Agree.ofExcept (ExceptAgree.lift _ fun _ => Post.val ho.states ho.steps)

/-- `e[i]`: the index is evaluated while the view `e` reads its sources
(views.reads-that-last). -/
theorem sim_index {e i : VExpr} (he : e.exclusive loops Γ R = true)
    (hi : i.exclusive loops Γ (e.sources Γ ++ R) = true) (hce : e.contained Γ = true)
    (hci : i.contained Γ = true) :
    Agree (Post R S sw)
      ((veval D .window n e >>= fun r => (veval D .window n i >>= Run.asInt) >>= fun k =>
        Eval.inspect fun s => r.index s.store k) sw)
      ((veval D .copy n e >>= fun r => (veval D .copy n i >>= Run.asInt) >>= fun k =>
        Eval.inspect fun s => r.index s.store k) sc) :=
  Agree.bind (ih e Γ R sw sc he hce hst hsc) fun s₁ sc₁ rw rc hp =>
    Agree.bind (ih.int hi hci hp.states ((hsc.after hp.steps).mono (mem_append_right' _)))
      fun s₂ sc₂ k k' ho => by
        cases ho.eq
        obtain ⟨x, h₁, h₂⟩ := (hp.held ho.steps).index k
        refine Agree.inspect ?_
        show ExceptAgree _ (rw.index s₂.store k) (rc.index sc₂.store k)
        rw [← ho.states.store, h₁, h₂]
        exact ExceptAgree.lift _ fun _ =>
          Post.val ho.states (hp.steps.trans ho.steps (mem_append_right' _))

theorem sim_seq {a b : VExpr} (ha : a.exclusive loops Γ R = true)
    (hb : b.exclusive loops Γ R = true) (hca : a.contained Γ = true) (hcb : b.contained Γ = true) :
    Agree (Post R (b.sources Γ) sw) ((veval D .window n a >>= fun _ => veval D .window n b) sw)
      ((veval D .copy n a >>= fun _ => veval D .copy n b) sc) :=
  Agree.bind (ih a Γ R sw sc ha hca hst hsc) fun s₁ sc₁ _ _ hp =>
    (ih b Γ R s₁ sc₁ hb hcb hp.states (hsc.after hp.steps)).mono fun _ _ _ _ hp₂ =>
      Post.after hp.steps hp₂ (fun _ h => h) (fun _ h => h)

theorem sim_if {c a b : VExpr} (hc : c.exclusive loops Γ R = true)
    (ha : a.exclusive loops Γ R = true) (hb : b.exclusive loops Γ R = true)
    (hcc : c.contained Γ = true) (hca : a.contained Γ = true) (hcb : b.contained Γ = true) :
    Agree (Post R (a.sources Γ ++ b.sources Γ) sw)
      ((veval D .window n c >>= Run.asBool >>= fun v =>
        if v then veval D .window n a else veval D .window n b) sw)
      ((veval D .copy n c >>= Run.asBool >>= fun v =>
        if v then veval D .copy n a else veval D .copy n b) sc) :=
  Agree.bind (ih.bool hc hcc hst hsc) fun s₁ sc₁ v v' ho => by
    cases ho.eq
    cases v
    · exact (ih b Γ R s₁ sc₁ hb hcb ho.states (hsc.after ho.steps)).mono fun _ _ _ _ hp =>
        Post.after ho.steps hp (fun _ h => h) fun _ h => List.mem_append_right _ h
    · exact (ih a Γ R s₁ sc₁ ha hca ho.states (hsc.after ho.steps)).mono fun _ _ _ _ hp =>
        Post.after ho.steps hp (fun _ h => h) fun _ h => List.mem_append_left _ h

/-- `let` and `var`: the rest of the block runs with the binding, which reads
its initializer's sources for its scope (views.reads-that-last), and gives a value
that reads none of the binding's storage (views.escaping). -/
theorem sim_bind {x : Name} {init body : VExpr} (hi : init.exclusive loops Γ R = true)
    (hb : body.exclusive loops ((x, init.sources Γ) :: Γ) (hide (init.sources Γ ++ R) x) = true)
    (hci : init.contained Γ = true) (hcb : body.contained ((x, init.sources Γ) :: Γ) = true)
    (hroot : (body.sources ((x, init.sources Γ) :: Γ)).all (·.root != x) = true) :
    Agree (Post R (body.sources ((x, init.sources Γ) :: Γ)) sw)
      ((veval D .window n init >>= fun r => Run.within x r (veval D .window n body)) sw)
      ((veval D .copy n init >>= fun r => Run.within x r (veval D .copy n body)) sc) :=
  Agree.bind (ih init Γ R sw sc hi hci hst hsc) fun s₁ sc₁ rw rc hp => by
    have hwin : rw.Within (init.sources Γ) s₁.env := hp.steps.env ▸ hp.within
    refine (Agree.within hp.states (hsc.after hp.steps) hp.agrees hwin
      fun sw' sc' hst' hsc' => ih body _ _ sw' sc' hb hcb hst' hsc').mono
      fun s₂ sc₂ bw bc hcl => ?_
    have hx : ∀ y ∈ body.sources ((x, init.sources Γ) :: Γ), y.root ≠ x := fun y hy => by
      simpa using List.all_eq_true.1 hroot y hy
    obtain ⟨hag, hw⟩ := hcl.value hx
    exact ⟨hcl.states, hp.steps.trans hcl.steps fun _ h => h, hag, hp.steps.env ▸ hw⟩

theorem sim_len {v : VExpr} (hex : v.exclusive loops Γ R = true) (hco : v.contained Γ = true) :
    Agree (Post R S sw)
      ((veval D .window n v >>= fun r => Eval.ofExcept r.len >>= fun k => pure (.val (.int k))) sw)
      ((veval D .copy n v >>= fun r => Eval.ofExcept r.len >>= fun k => pure (.val (.int k))) sc) :=
  Agree.bind (ih v Γ R sw sc hex hco hst hsc) fun s₁ sc₁ rw rc hp =>
    Agree.bind (Agree.ofExcept (Q := Operand R sw)
      (hp.agrees.len.mono fun _ _ _ h => ⟨h, hp.states, hp.steps⟩)) fun _ _ k k' ho => by
        cases ho.eq
        exact Post.val ho.states ho.steps

theorem sim_copy {v : VExpr} (hex : v.exclusive loops Γ R = true) (hco : v.contained Γ = true) :
    Agree (Post R S sw) ((veval D .window n v >>= fun r => Eval.inspect fun s => r.copy s.store) sw)
      ((veval D .copy n v >>= fun r => Eval.inspect fun s => r.copy s.store) sc) :=
  Agree.bind (ih v Γ R sw sc hex hco hst hsc) fun s₁ sc₁ rw rc hp => by
    obtain ⟨x, h₁, h₂⟩ := hp.agrees.copy
    refine Agree.inspect ?_
    show ExceptAgree _ (rw.copy s₁.store) (rc.copy sc₁.store)
    rw [← hp.states.store, h₁, h₂]
    exact ExceptAgree.lift _ fun _ => Post.val hp.states hp.steps

/-- `v.view(a, b)`: the offsets are evaluated while `v` reads its sources
(views.reads-that-last), and the part reads what `v` reads. -/
theorem sim_sub {v a b : VExpr} (hv : v.exclusive loops Γ R = true)
    (ha : a.exclusive loops Γ (v.sources Γ ++ R) = true)
    (hb : b.exclusive loops Γ (v.sources Γ ++ R) = true) (hcv : v.contained Γ = true)
    (hca : a.contained Γ = true) (hcb : b.contained Γ = true) :
    Agree (Post R (v.sources Γ) sw)
      ((veval D .window n v >>= fun r => (veval D .window n a >>= Run.asInt) >>= fun s =>
        (veval D .window n b >>= Run.asInt) >>= fun t => Eval.ofExcept (r.sub s t)) sw)
      ((veval D .copy n v >>= fun r => (veval D .copy n a >>= Run.asInt) >>= fun s =>
        (veval D .copy n b >>= Run.asInt) >>= fun t => Eval.ofExcept (r.sub s t)) sc) :=
  Agree.bind (ih v Γ R sw sc hv hcv hst hsc) fun s₁ sc₁ rw rc hp => by
    have hsc₁ := (hsc.after hp.steps).mono (mem_append_right' (v.sources Γ))
    refine Agree.bind (ih.int ha hca hp.states hsc₁) fun s₂ sc₂ x x' ho₂ => ?_
    refine Agree.bind (ih.int hb hcb ho₂.states (hsc₁.after ho₂.steps)) fun s₃ sc₃ y y' ho₃ => ?_
    cases ho₂.eq
    cases ho₃.eq
    have hsteps := ho₂.steps.trans ho₃.steps fun _ h => h
    exact Agree.ofExcept ((Agrees.sub (hp.held hsteps) x y).mono fun _ _ _ ⟨hag, hw⟩ =>
      ⟨ho₃.states, hp.steps.trans hsteps (mem_append_right' _), hag, hw _ _ hp.within⟩)

end Forms

end Stilt.Views
