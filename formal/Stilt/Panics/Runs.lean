import Stilt.Panics.Steps
import Stilt.Panics.Tests
import Stilt.Panics.RowInstances
import Stilt.InPlace.Enter
import Stilt.Selection

/-!
# Runs without panics

The evaluator's steps that run expressions keep `Eval.PanicFree lim`, given that
running a panic-free expression does (`PanicFreeRun lim`) and keeps what it doesn't
write (`KeepsRun`): evaluating a list of expressions, each guarded by what the
ones before it don't write, a record's fields, the indexes of a place without
one, a call's arguments, a `match`, an assignment, and a `for` loop, whose
turns keep the facts about the variables its body doesn't write.
-/

namespace Stilt

/-- Running a panic-free expression, guarded by `G`, ends as panic-free code may. -/
def PanicFreeRun (lim : Limited) (run : Expr → Eval Copy.State Value) : Prop :=
  ∀ G e, e.panicFreeIn lim G = true → Eval.PanicFree lim G (Value.PanicFree lim) (run e)

variable {lim : Limited}

@[simp] theorem withoutNames_nil (G : List Known) : withoutNames G [] = G := by
  simp [withoutNames]

/-- Facts that read none of `W` don't read what a part of `W` names. -/
theorem withoutNames_sub {G : List Known} {W W' : List Name} (h : W' ⊆ W) :
    withoutNames G W ⊆ withoutNames G W' := fun f hf => by
  obtain ⟨hG, hW⟩ := mem_withoutNames.1 hf
  exact mem_withoutNames.2 ⟨hG, fun x hx hx' => hW x hx (h hx')⟩

/-- Dropping the facts that read `W` twice drops no more than once. -/
theorem withoutNames_twice (G : List Known) (W : List Name) :
    withoutNames G W ⊆ withoutNames (withoutNames G W) W := fun f hf => by
  obtain ⟨hG, hW⟩ := mem_withoutNames.1 hf
  exact mem_withoutNames.2 ⟨hf, hW⟩

theorem withoutNames_zip_fst (G : List Known) (bs : List Name) (us : List Value) :
    withoutNames G bs ⊆ withoutNames G ((bs.zip us).map Prod.fst) :=
  withoutNames_sub fun _ hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact (List.of_mem_zip hp).1

/-- A path that takes only fields evaluates nothing, and writes nothing. -/
theorem pathWrites_of_fields : ∀ {ps : List Projection},
    ps.all (fun q => q.fieldName?.isSome) = true → pathWrites ps = []
  | [], _ => rfl
  | .field _ :: ps, h => by
    simp only [List.all_cons, Projection.fieldName?, Option.isSome_some, Bool.true_and] at h
    simpa [pathWrites] using pathWrites_of_fields h
  | .index _ :: _, h => by simp [Projection.fieldName?] at h

/-- A path that takes only fields keeps every variable. -/
theorem Eval.Keeps.fieldPath {run : Expr → Eval Copy.State Value} {W L : List Name} :
    ∀ {ps : List Projection}, ps.all (fun q => q.fieldName?.isSome) = true →
      Eval.Keeps W L (fun _ => True) (Eval.path run ps)
  | [], _ => Eval.Keeps.pure trivial
  | .field _ :: ps, h => by
    simp only [List.all_cons, Projection.fieldName?, Option.isSome_some, Bool.true_and] at h
    exact Eval.Keeps.bind (fieldPath h) fun _ _ => Eval.Keeps.pure trivial
  | .index _ :: _, h => by simp [Projection.fieldName?] at h

namespace Eval.PanicFree

variable (w : WriteBack) {G : List Known}

theorem read (x : Name) :
    Eval.PanicFree lim G (Value.PanicFree lim) (Eval.inspect fun s => (Copy.memoryWith w).read s x []) :=
  inspect fun _ hs => Frame.PanicFree.read hs x (fun _ h => nomatch h)

theorem capture (keep : Name → Bool) :
    Eval.PanicFree lim G (fun c : List (Name × Value) => ∀ xv ∈ c, xv.2.PanicFree lim)
      (Eval.inspect ((Copy.memoryWith w).capture · keep)) :=
  inspect fun _ hs => CalmTo.ok fun xv hxv => hs xv (mem_of_mem_newestOf hxv)

theorem asBool {v : Value} : Eval.PanicFree lim G (fun _ => True) (Eval.asBool v) := by
  cases v <;> first | exact pure trivial | exact stuck

theorem asList {v : Value} (hv : v.PanicFree lim) :
    Eval.PanicFree lim G (fun vs : List Value => ∀ u ∈ vs, u.PanicFree lim) (Eval.asList v) := by
  cases v <;> first | exact stuck | skip
  cases hv with
  | list h => exact pure h

theorem declare (D : Decls) (R : Name) {written : List (Name × Value)}
    (hw : ∀ fv ∈ written, fv.2.PanicFree lim) :
    Eval.PanicFree lim G (Value.PanicFree lim) (Eval.declare D R written) := by
  unfold Eval.declare
  split
  · split
    · rename_i fields hfields
      refine pure (.record fun fv hfv => ?_)
      obtain ⟨⟨f, τ⟩, _, ha⟩ := InPlace.Sim.mapM_mem hfields fv hfv
      simp only [Option.map_eq_some_iff] at ha
      obtain ⟨v, hv, rfl⟩ := ha
      exact hw _ (mem_of_lookup hv)
    · exact stuck
  · exact stuck

section Runs

variable {run : Expr → Eval Copy.State Value} (h : PanicFreeRun lim run) (hk : KeepsRun run)
include h hk

theorem list : ∀ {G : List Known} (es : List Expr), exprsPanicFree lim G es = true →
    Eval.PanicFree lim G (fun vs : List Value => ∀ v ∈ vs, v.PanicFree lim) (Eval.list run es)
  | _, [], _ => pure (by simp)
  | G, e :: es, hes => by
    simp only [exprsPanicFree, Bool.and_eq_true] at hes
    exact bind (h G e hes.1) (hk e _ _ (List.Subset.refl _) (List.Subset.refl _)) fun v hv =>
      bind (list es hes.2) (Eval.Keeps.list hk es (List.Subset.refl _) (List.Subset.refl _)) fun vs hvs =>
        pure fun u hu => by
          rcases List.mem_cons.1 hu with rfl | hu
          · exact hv
          · exact hvs u hu

/-- The values of a list of expressions, one for each. -/
theorem listSized : ∀ {G : List Known} (es : List Expr), exprsPanicFree lim G es = true →
    Eval.PanicFree lim G (fun vs : List Value => (∀ v ∈ vs, v.PanicFree lim) ∧ vs.length = es.length)
      (Eval.list run es)
  | _, [], _ => pure ⟨by simp, rfl⟩
  | G, e :: es, hes => by
    simp only [exprsPanicFree, Bool.and_eq_true] at hes
    exact bind (h G e hes.1) (hk e _ _ (List.Subset.refl _) (List.Subset.refl _)) fun v hv =>
      bind (listSized es hes.2) (Eval.Keeps.list hk es (List.Subset.refl _) (List.Subset.refl _))
        fun vs hvs => pure ⟨fun u hu => by
          rcases List.mem_cons.1 hu with rfl | hu
          · exact hv
          · exact hvs.1 u hu, by simp [hvs.2]⟩

theorem fields : ∀ {G : List Known} (fs : List (Name × Expr)), fieldsPanicFree lim G fs = true →
    Eval.PanicFree lim G (fun ws : List (Name × Value) => ∀ fv ∈ ws, fv.2.PanicFree lim) (Eval.fields run fs)
  | _, [], _ => pure (by simp)
  | G, (f, e) :: fs, hfs => by
    simp only [fieldsPanicFree, Bool.and_eq_true] at hfs
    exact bind (h G e hfs.1) (hk e _ _ (List.Subset.refl _) (List.Subset.refl _)) fun v hv =>
      bind (fields fs hfs.2) (Eval.Keeps.fields hk fs (List.Subset.refl _) (List.Subset.refl _)) fun ws hws =>
        pure fun fv hfv => by
          rcases List.mem_cons.1 hfv with rfl | hfv
          · exact hv
          · exact hws fv hfv

omit h hk in
/-- The indexes of a place without one evaluate to a path along fields: no index
is evaluated. -/
theorem path : ∀ {G : List Known} (ps : List Projection), ps.all (fun q => q.fieldName?.isSome) = true →
    Eval.PanicFree lim G Path.Fields (Eval.path run ps)
  | _, [], _ => pure fun _ h => nomatch h
  | _, .field f :: ps, hps => by
    simp only [List.all_cons, Projection.fieldName?, Option.isSome_some, Bool.true_and] at hps
    exact bind (W := []) (L := []) (path ps hps) (Eval.Keeps.fieldPath hps) fun p hp => pure fun s hs => by
        rcases List.mem_cons.1 hs with rfl | hs
        · exact ⟨f, rfl⟩
        · exact hp s hs
  | _, .index _ :: _, hps => by simp [Projection.fieldName?] at hps

theorem args : ∀ {G : List Known} (as : List Arg), argsPanicFree lim G as = true →
    Eval.PanicFree lim G (fun passed : List Passed => ∀ q ∈ passed, q.PanicFree lim) (Eval.args run as)
  | _, [], _ => pure (by simp)
  | G, .value e :: as, has => by
    simp only [argsPanicFree, Bool.and_eq_true] at has
    exact bind (h G e has.1) (hk e _ _ (List.Subset.refl _) (List.Subset.refl _)) fun v hv =>
      bind (args as has.2) (Eval.Keeps.args hk as (List.Subset.refl _) (List.Subset.refl _)) fun ps hps =>
        pure fun q hq => by
          rcases List.mem_cons.1 hq with rfl | hq
          · cases e <;> exact hv
          · exact hps q hq
  | G, .inout ⟨x, projections⟩ :: as, has => by
    simp only [argsPanicFree, Place.indexFree, Bool.and_eq_true] at has
    exact bind (W := []) (L := []) (path projections has.1) (Eval.Keeps.fieldPath has.1) fun p hp =>
      bind (weaken (args as has.2) fun y hy => mem_withoutNames.2 ⟨hy, by simp⟩)
        (Eval.Keeps.args hk as (List.Subset.refl _) (List.Subset.refl _)) fun ps hps =>
        pure fun q hq => by
          rcases List.mem_cons.1 hq with rfl | hq
          · exact hp
          · exact hps q hq

/-- An arm with a guard, run with facts `H` that read nothing the guard writes: the guard
with each way, then the body or what comes next. -/
theorem guarded {bs : List Name} {g body : Expr} {H : List Known} {next : Eval Copy.State Value}
    (hH : H ⊆ withoutNames H g.writes)
    (hg : g.panicFreeIn lim (withoutNames H bs) = true)
    (hb : body.panicFreeIn lim (withoutNames H bs) = true)
    (hn : Eval.PanicFree lim H (Value.PanicFree lim) next) :
    ∀ ways : List (List Value), (∀ us ∈ ways, ∀ u ∈ us, u.PanicFree lim) →
      Eval.PanicFree lim H (Value.PanicFree lim)
        (Eval.guarded (Copy.memoryWith w) run bs g body next ways)
  | [], _ => hn
  | us :: ways, hw => by
    have hparts : ∀ xv ∈ bs.zip us, xv.2.PanicFree lim := fun xv hxv =>
      hw us List.mem_cons_self xv.2 (List.of_mem_zip hxv).2
    have hrest := guarded hH hg hb hn ways fun us' hu => hw us' (List.mem_cons_of_mem _ hu)
    simp only [Eval.guarded, Eval.tryWay]
    split
    case isFalse => exact stuck
    refine bind (W := g.writes) (L := g.resizes)
      (withVars w _ hparts (weaken (bind (h _ g hg)
        (hk g _ _ (List.Subset.refl _) (List.Subset.refl _)) fun _ _ => asBool)
        (withoutNames_zip_fst H bs us)))
      (Eval.Keeps.withVars w (Eval.Keeps.bind (hk g _ _ (List.Subset.refl _) (List.Subset.refl _))
        fun v _ => Eval.Keeps.asBool v) _)
      fun b _ => weaken (ite b ?_ hrest) hH
    exact withVars w _ hparts (weaken (h _ _ hb) (withoutNames_zip_fst H bs us))

theorem select : ∀ {G : List Known} {arms : List Arm}, armsPanicFree lim G arms = true →
    ∀ {v : Value}, v.PanicFree lim →
      Eval.PanicFree lim G (Value.PanicFree lim) (Eval.select (Copy.memoryWith w) run arms v)
  | _, [], _, _, _ => stuck
  | G, ⟨p, bs, guard, body⟩ :: arms, harms, v, hv => by
    simp only [armsPanicFree, Bool.and_eq_true] at harms
    obtain ⟨⟨hg, hb⟩, hrest⟩ := harms
    simp only [Eval.select]
    cases guard with
    | none =>
      simp only [guardWrites, withoutNames_nil] at hb hrest
      simp only
      cases hm : p.matchOn v with
      | some us =>
        simp only
        split
        case isFalse => exact stuck
        exact withVars w _ (fun xv hxv => p.matchOn_parts Value.PanicFree.passesToParts hv hm xv.2
          (List.of_mem_zip hxv).2) (weaken (h _ _ hb) (withoutNames_zip_fst G bs us))
      | none => exact select hrest hv
    | some g =>
      simp only [guardPanicFree, guardWrites] at hg hb hrest
      simp only
      refine weaken (G' := withoutNames G g.writes)
        (guarded w h hk (withoutNames_twice G g.writes) hg hb (select hrest hv) _ fun us hu => ?_)
        fun _ hf => (mem_withoutNames.1 hf).1
      obtain ⟨q, -, hq⟩ := Pattern.mem_ways hu
      exact fun u hu' => q.matchOn_parts Value.PanicFree.passesToParts hv hq u hu'

theorem assign (x : Name) {ps : List Projection} (hps : ps.all (fun q => q.fieldName?.isSome) = true)
    {value : Expr} (hv : value.panicFreeIn lim G = true) :
    Eval.PanicFree lim G (Value.PanicFree lim) (Eval.assign (Copy.memoryWith w) run x ps value) :=
  bind (W := []) (L := []) (path ps hps) (Eval.Keeps.fieldPath hps) fun _ hp =>
    bind (weaken (h G value hv) fun y hy => mem_withoutNames.2 ⟨hy, by simp⟩)
      (hk value _ _ (List.Subset.refl _) (List.Subset.refl _)) fun _ hw =>
      bind (update fun s hs => by
          rw [Eval.Keeps.memoryWith_write]
          exact CalmTo.map (Frame.PanicFree.write hs.1 x hw hp) fun _ h => ⟨h, hs.2⟩)
        (Eval.Keeps.update (L := [x]) w x _ _ (List.mem_singleton_self x) fun _ => List.mem_singleton_self x) fun _ _ => pure .unit

/-- A `for` loop, whose body may count on the facts `F` about its variable: each
holds once the frame meets those of `L vs`, for the elements `vs` that the
iterable reaches from a frame that meets `G`, that read the value of nothing the body writes and the length of
nothing it resizes. -/
theorem loop (x : Name) {e body : Expr} (F : List Known) (L : List Value → List Known)
    (he : e.panicFreeIn lim G = true)
    (hb : body.panicFreeIn lim
      (withoutNames (withoutNames (withoutNames G e.writes) body.writes) [x] ++ F) = true)
    (hafter : ∀ s v s', (run e s).Reaches v s' → ∀ vs, v = .list vs → Frame.Meets (L vs) s'.1)
    (helem : ∀ s v s', Frame.Meets G s.1 → (run e s).Reaches v s' → ∀ vs, v = .list vs → ∀ u ∈ vs, ∀ s'',
      Frame.Meets (withoutWrites (L vs) body.writes body.resizes) s'' → Frame.Meets F ((x, u) :: s'')) :
    Eval.PanicFree lim G (Value.PanicFree lim) (Eval.loop (Copy.memoryWith w) run x e body) := by
  let E : List Value → Prop := fun vs => ∀ u ∈ vs, ∀ s'',
    Frame.Meets (withoutWrites (L vs) body.writes body.resizes) s'' → Frame.Meets F ((x, u) :: s'')
  have helems : ∀ (H : List Known) v, v.PanicFree lim ∧ (∀ vs, v = .list vs → E vs) →
      Eval.PanicFree lim H (fun vs : List Value => (∀ u ∈ vs, u.PanicFree lim) ∧ E vs) (Eval.asList v) := by
    intro H v ⟨hv, hq⟩
    cases v <;> first | exact stuck | skip
    rename_i vs
    exact pure ⟨fun u hu => by cases hv with | list h => exact h u hu, hq vs rfl⟩
  have hturn : ∀ v, Eval.Keeps body.writes body.resizes (fun _ => True)
      (Eval.withVar (Copy.memoryWith w) x v (Eval.turn (run body))) := fun v =>
    Eval.Keeps.withVar w x v (Eval.Keeps.turn (hk body _ _ (List.Subset.refl _) (List.Subset.refl _)))
  have hrun := withDone (h G e he) fun s v s' hz hd vs hvs => helem s v s' hz hd vs hvs
  refine bindAfter (F := L) (bind hrun (hk e _ _ (List.Subset.refl _) (List.Subset.refl _)) fun v hv => helems _ v hv)
    (Eval.Keeps.bind (hk e _ _ (List.Subset.refl _) (List.Subset.refl _)) fun v _ => Eval.Keeps.asList v)
    (fun s vs s' hd => by
      obtain ⟨v, s₁, h₁, h₂⟩ := Eval.bind_reaches hd
      obtain ⟨rfl, rfl⟩ := Eval.asList_reaches h₂
      exact hafter s _ _ h₁ vs rfl) fun vs ⟨hvs, hE⟩ => ?_
  let T := withoutWrites (withoutNames G e.writes ++ L vs) body.writes body.resizes
  have hbody : Eval.PanicFree lim (withoutNames T [x] ++ F) (Value.PanicFree lim) (run body) :=
    weaken (h _ body hb) fun f hf => by
      simp only [List.mem_append] at hf ⊢
      rcases hf with hf | hF
      · obtain ⟨hf, hx⟩ := mem_withoutNames.1 hf
        refine .inl (mem_withoutNames.2 ⟨?_, hx⟩)
        obtain ⟨hf, hb⟩ := mem_withoutNames.1 hf
        exact withoutNames_sub_withoutWrites (body.resizes_subset)
          (mem_withoutNames.2 ⟨List.mem_append.2 (.inl hf), hb⟩)
      · exact .inr hF
  have helemT : ∀ u ∈ vs, u.PanicFree lim ∧ ∀ s'', Frame.Meets T s'' → Frame.Meets F ((x, u) :: s'') :=
    fun u hu => ⟨hvs u hu, fun s'' hT => hE u hu s'' (hT.mono fun f hf => by
      simp only [T, List.mem_append, mem_withoutWrites] at hf ⊢
      exact ⟨.inr hf.1, hf.2⟩)⟩
  have hloop := forEach (G := T) (Q := fun u => ∀ s'', Frame.Meets T s'' → Frame.Meets F ((x, u) :: s''))
    (fun _ hf => (mem_withoutWrites.1 hf).2) (fun _ hv hq => withVarFacts w hv hq (turn hbody)) hturn
    vs helemT
  exact bind (hloop.weaken fun _ hy => (mem_withoutWrites.1 hy).1) (Eval.Keeps.forEach hturn vs)
    fun _ _ => pure .unit

end Runs

end Eval.PanicFree

end Stilt
