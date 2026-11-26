import Stilt.Windows.Guards.Checks

/-!
# The guard of the views clause

`eval_guards`: when E0423 accepts `e` with the places `R` read around it
(views.change-while-viewed, `Expr.viewsRead`), evaluating `e` in place, with any fuel, from a
valid state whose regions `G` the reads `R` guard, writes only at paths disjoint from each
region of `G` and at new locations, in every outcome and in every rest of a performance.

The regions are the parts of the store that live views read. A modification that E0423
accepts is of a place whose shape overlaps none of the places read around it: an assignment
(`unread reading shape`), or a call's `inout` argument, whose place the call check leaves
unread by the views among the call's operands and the places read around it. A call writes
the caller's store only below its `inout` arguments' places (`eval_writes` of its body), and
a scope reads what the scope around it reads, except the shapes rooted at the name it binds,
which reach a new location only. So no modification reaches a region.
-/

namespace Stilt

open InPlace Eval.Guards

variable {D : Decls} {G : List Path} {run : Expr → Eval (State × World) Value}

/-- The places of a call's `inout` arguments that the call check leaves unread avoid the
regions that the reads around the call guard, and so does every part below them. -/
theorem placesAvoid_of {R R' : List Shape} {as : List Arg} {passed : List Passed}
    (hres : Sim.ArgsResolved as passed) (hu : (inoutShapes as).all (unread R') = true)
    (hR : ∀ t ∈ R, t ∈ R') : PlacesAvoid G R passed := by
  intro s hr x p r hmem hl q
  obtain ⟨ps, hp, hshape⟩ := shape_of_resolved hres hmem
  exact avoids_of_unread hr hl hp (unread_sub (List.all_eq_true.1 hu _ hshape) hR) q

/-- An assignment that E0423 accepts writes a place whose every resolution avoids the
regions. -/
theorem assign_avoids {R : List Shape} {x : Name} {ps : List Projection}
    (hu : unread R (Place.mk x ps).shape = true) :
    ∀ p : Path, p.Resolves ps → ∀ (s : State) r, Regions G R s → s.env.lookup x = some r →
      Avoids G (r.toPath ++ p) := fun p hp _ r hr hl => by
  simpa using avoids_of_unread hr hl hp hu []

theorem exprs_keep
    (ih : ∀ e Γ R, e.viewsRead D Γ R = true → Eval.Guards G R (fun _ => True) (run e))
    {Γ : ViewScope} {R : List Shape} {es : List Expr} (h : exprsViewsRead D Γ R es = true) :
    ∀ e ∈ es, Eval.Guards G R (fun _ => True) (run e) := fun e he => by
  obtain ⟨R', hR', h'⟩ := exprsViewsRead_mem h e he
  exact (ih e Γ R' h').sub hR'

/-- A call that E0423 accepts keeps the regions. -/
theorem guards_call
    (ih : ∀ e Γ R, e.viewsRead D Γ R = true → Eval.Guards G R (fun _ => True) (run e))
    (hrun : ∀ e, Eval.Guards [] [] (fun _ => True) (run e)) {Γ : ViewScope} {R : List Shape}
    {callee : Expr} {as : List Arg} {τ : Ty} (h : (Expr.call callee as τ).viewsRead D Γ R = true) :
    Eval.Guards G R (fun _ => True) (do
      let f ← run callee
      let passed ← Eval.args run as
      Eval.callAs D InPlace.memory run false f passed) := by
  simp only [Expr.viewsRead, Bool.and_eq_true] at h
  obtain ⟨⟨hc, has⟩, hu⟩ := h
  exact bind (ih callee Γ R hc) fun f _ =>
    bind (args as (keep_sub (argsViewsRead_keep ih has) (sub_append _ R))) fun _ hres =>
      callAs D hrun false f (placesAvoid_of hres hu (sub_append _ R))
where
  keep_sub {R R' : List Shape} : ∀ {as : List Arg}, ArgsKeep G R' run as →
      (∀ t ∈ R, t ∈ R') → ArgsKeep G R run as :=
    argsViewsRead_keep.keep_sub

/-- The operands of a view: its source first, then the offsets, under the source's read. -/
theorem view_keep
    (ih : ∀ e Γ R, e.viewsRead D Γ R = true → Eval.Guards G R (fun _ => True) (run e))
    {Γ : ViewScope} {R : List Shape} :
    ∀ {es : List Expr}, (Expr.view es).viewsRead D Γ R = true →
      ∀ e ∈ es, Eval.Guards G R (fun _ => True) (run e)
  | [], _, _, he => by cases he
  | e :: es, h, e', he' => by
    simp only [Expr.viewsRead, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ih _ Γ R h.1
    · exact (exprs_keep ih h.2 e' he').sub (sub_append _ R)

/-- An assignment that E0423 accepts keeps the regions. -/
theorem guards_assign
    (ih : ∀ e Γ R, e.viewsRead D Γ R = true → Eval.Guards G R (fun _ => True) (run e))
    {Γ : ViewScope} {R : List Shape} {p : Place} {value : Expr}
    (h : (Expr.assign p value).viewsRead D Γ R = true) :
    Eval.Guards G R (fun _ => True) (Eval.assign InPlace.memory run p.root p.path value) := by
  obtain ⟨x, ps⟩ := p
  simp only [Expr.viewsRead, Bool.and_eq_true] at h
  exact assign x (fun i hi => ih i Γ R (pathViewsRead_mem h.1.1.1 i hi)) (ih value Γ R h.1.1.2)
    (assign_avoids h.1.2)

/-- **The guard of the views clause.** When E0423 accepts `e` with the places `R` read
around it, evaluating `e` in place, with any fuel, from a valid state whose regions `G` the
reads `R` guard, writes only at paths disjoint from each region and at new locations, in
every outcome and every rest of a performance (views.change-while-viewed). -/
theorem eval_guards (D : Decls) (G : List Path) :
    ∀ n e Γ R, e.viewsRead D Γ R = true →
      Eval.Guards G R (fun _ => True) (eval D InPlace.memory n e)
  | 0, _, _, _, _ => outOfFuel
  | n + 1, e, Γ, R, h => by
    have ih := eval_guards D G n
    have hw := eval_writes D n
    have h0 := h
    cases e <;> try simp only [Expr.viewsRead, Bool.and_eq_true] at h
    case var x => exact inspect _ fun _ _ _ => trivial
    case move x => exact inspect _ fun _ _ _ => trivial
    case int k => exact pure trivial
    case bool b => exact pure trivial
    case unit => exact pure trivial
    case record T _ fs =>
      exact bind (fields fs fun fe hfe => by
        obtain ⟨R', hR', h'⟩ := fieldsViewsRead_mem h fe hfe
        exact (ih fe.2 Γ R' h').sub hR') fun _ _ => declare D T _
    case variant T _ C es => exact bind (list es (exprs_keep ih h)) fun _ _ => pure trivial
    case list τ es => exact bind (list es (exprs_keep ih h)) fun _ _ => pure trivial
    case op o es => exact bind (list es (exprs_keep ih h)) fun _ _ => world _
    case view es => exact bind (list es (view_keep ih h0)) fun _ _ => ofExcept _ fun _ _ => trivial
    case field e f => exact bind (ih e Γ R h) fun _ _ => ofExcept _ fun _ _ => trivial
    case index e i => exact index (ih e Γ R h.1) ((ih i Γ _ h.2).sub (sub_append _ R))
    case fnRef f types rows => exact pure trivial
    case method t m τ => exact method D t m τ
    case closure ps result ρ body =>
      exact bind (inspect _ fun _ _ _ => trivial) fun _ _ => pure trivial
    case call callee as τ => exact guards_call ih hw h0
    case letIn x τ init body =>
      exact bind (ih init Γ R h.1) fun v _ => withInit x init v (ih body _ _ h.2) (hide_sub_hide _ R x)
    case varIn x τ init body =>
      exact bind (ih init Γ R h.1) fun v _ => withInit x init v (ih body _ _ h.2) (hide_sub_hide _ R x)
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      exact guards_assign ih h0
    case seq a b => exact bind (ih a Γ R h.1) fun _ _ => ih b Γ R h.2
    case «if» c τ a b =>
      exact bind (bind (ih c Γ R h.1.1) fun _ _ => asBool) fun v _ =>
        ite v (ih a Γ R h.1.2) (ih b Γ R h.2)
    case «match» e τ arms =>
      exact bind (ih e Γ R h.1) fun v _ => select (fun arm harm =>
        (armsViewsRead_mem h.2 arm harm).elim fun Γ' h' => ih arm.body Γ' _ h') v
    case «for» x τ e body =>
      exact loop x (ih e Γ R h.1) (ih body _ _ h.2) (hide_sub_hide _ R x)
    case raise e => exact bind (ih e Γ R h) fun v _ => throw v
    case «try» e => exact ih e Γ R h
    case tryCatch e E x hd τ =>
      exact handle (ih e Γ R h.1) fun err => withVar x err (ih hd _ _ h.2) fun _ h => h
    case «while» c body => exact whileLoop (ih c Γ R h.1) (ih body Γ R h.2) (ih _ Γ R h0)
    case «loop» body => exact loopForever (ih body Γ R h) (ih _ Γ R h0)
    case «break» => exact jump _
    case «continue» => exact jump _
    case «return» e => exact bind (ih e Γ R h) fun v _ => jump _
    case perform op e => exact bind (ih e Γ R h) fun v _ => perform op v
    case withH E c hd b =>
      exact bind (ih hd Γ R h.1) fun hv _ => withHandler D hw E c hv (ih b Γ R h.2)
    case held ns hs b =>
      exact bind (list hs (exprs_keep ih h.1)) fun vs _ => held _ vs (ih b _ _ h.2)

end Stilt
