import Stilt.Moves.Control
import Stilt.InPlace.Steps

/-!
# Evaluating parts

The combinators of `Stilt.Semantics` that evaluate subexpressions keep the
simulation, given that evaluating each subexpression keeps it (`MRun`): the
elements of a list, the fields of a record literal, the indexes of a place,
and the arm of a `match`. Each part is checked with what follows it, as
`Expr.movesOk` checks it.
-/

namespace Stilt.Moving

open InPlace

/-- Evaluating a safe expression whose marks are last uses keeps the
simulation, with the variables it mentions and those after it live. -/
def MRun (run : Expr → Eval Copy.State Value) (run' : Expr → Eval (State × World) Value) : Prop :=
  ∀ e L, e.Safe → e.movesOk L = true → MSim VOk (L.union e.mentions) L e.mentions (run e) (run' e)

variable {run : Expr → Eval Copy.State Value} {run' : Expr → Eval (State × World) Value}

namespace MSim

theorem list (h : MRun run run') : ∀ (L : Live) (es : List Expr), (∀ e ∈ es, e.Safe) →
    exprsMovesOk L es = true →
    MSim (fun vs : List Value => ∀ v ∈ vs, VOk v) (L.union (exprsMentions es)) L (exprsMentions es)
      (Eval.list run es) (Eval.list run' es)
  | _, [], _, _ => pure (by simp)
  | L, e :: es, hs, hm => by
    simp only [exprsMovesOk, Bool.and_eq_true] at hm
    simp only [exprsMentions]
    refine bind ((h e _ (hs e List.mem_cons_self) hm.1).mono (by live_sub) (Live.Sub.refl _)
      (by live_sub)) (fun v hv => bind ((list h L es (fun e' he' => hs e' (List.mem_cons_of_mem _ he'))
        hm.2).mono (by live_sub) (Live.Sub.refl _) (by live_sub)) (fun vs hvs => pure fun u hu => ?_)
        (by live_sub) (Live.Sub.refl _)) (by live_sub) (by live_sub)
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hv
    · exact hvs u hu

theorem fields (h : MRun run run') : ∀ (L : Live) (fs : List (Name × Expr)), (∀ fe ∈ fs, fe.2.Safe) →
    fieldsMovesOk L fs = true →
    MSim (fun ws : List (Name × Value) => ∀ fv ∈ ws, VOk fv.2) (L.union (fieldsMentions fs)) L
      (fieldsMentions fs) (Eval.fields run fs) (Eval.fields run' fs)
  | _, [], _, _ => pure (by simp)
  | L, (f, e) :: fs, hs, hm => by
    simp only [fieldsMovesOk, Bool.and_eq_true] at hm
    simp only [fieldsMentions]
    refine bind ((h e _ (hs (f, e) List.mem_cons_self) hm.1).mono (by live_sub) (Live.Sub.refl _)
      (by live_sub)) (fun v hv => bind ((fields h L fs (fun fe hfe => hs fe (List.mem_cons_of_mem _ hfe))
        hm.2).mono (by live_sub) (Live.Sub.refl _) (by live_sub))
        (fun ws hws => pure fun fv hfv => ?_) (by live_sub) (Live.Sub.refl _)) (by live_sub)
        (by live_sub)
    rcases List.mem_cons.1 hfv with rfl | hfv
    · exact hv
    · exact hws fv hfv

/-- Evaluating the indexes of a place gives a path that resolves it. -/
theorem path (h : MRun run run') : ∀ (L : Live) (ps : List Projection), PathSafe ps →
    pathMovesOk L ps = true →
    MSim (fun p : Path => p.Resolves ps) (L.union (pathMentions ps)) L (pathMentions ps)
      (Eval.path run ps) (Eval.path run' ps)
  | _, [], _, _ => pure trivial
  | L, .field _ :: ps, hs, hm =>
    bind (path h L ps (fun i hi => hs i (List.mem_cons_of_mem _ hi)) hm) (fun _ hp => pure ⟨rfl, hp⟩)
      (by simp only [pathMentions]; live_sub) (Live.Sub.refl _)
  | L, .index i :: ps, hs, hm => by
    simp only [pathMovesOk, Bool.and_eq_true] at hm
    simp only [pathMentions]
    exact bind (bind ((h i _ (hs i List.mem_cons_self) hm.1).mono (by live_sub) (Live.Sub.refl _)
      (by live_sub)) (fun _ _ => asInt) (by live_sub) (Live.Sub.refl _))
      (fun _ _ => bind ((path h L ps (fun j hj => hs j (List.mem_cons_of_mem _ hj)) hm.2).mono
        (by live_sub) (Live.Sub.refl _) (by live_sub)) (fun _ hp => pure hp) (by live_sub)
        (Live.Sub.refl _)) (by live_sub) (by live_sub)

/-- A record built from fields that a run may hold. -/
theorem declare (D : Decls) (R : Name) {Lb L X : Live} {written : List (Name × Value)}
    (hw : ∀ fv ∈ written, VOk fv.2) :
    MSim VOk Lb L X (Eval.declare D R written) (Eval.declare D R written) := by
  unfold Eval.declare
  split
  · split
    · rename_i fields hfields
      have hmem : ∀ fv ∈ fields, VOk fv.2 := fun fv hfv => by
        obtain ⟨⟨f, τ⟩, _, ha⟩ := InPlace.Sim.mapM_mem hfields fv hfv
        simp only [Option.map_eq_some_iff] at ha
        obtain ⟨v, hv, rfl⟩ := ha
        exact hw _ (mem_of_lookup hv)
      exact pure ⟨.record fun fv hfv => (hmem fv hfv).1, .record fun fv hfv => (hmem fv hfv).2⟩
    · exact fail _
  · exact fail _

/-- An arm's body, run with the parts of a way of its pattern bound. -/
theorem armBody (h : MRun run run') {L Lb X : Live} {bs : List Name} {body : Expr} {us : List Value}
    (hs : body.Safe) (hm : body.movesOk (L.eraseAll bs) = true) (hlen : bs.length = us.length)
    (hu : ∀ u ∈ us, VOk u) (hLb : ((L.eraseAll bs).union body.mentions).Sub (Lb.union (Live.ofList bs)))
    (hX : (body.mentions.eraseAll bs).Sub X) :
    MSim VOk Lb L X (Eval.withVars Copy.memory (bs.zip us) (run body))
      (Eval.withVars Moving.memory (bs.zip us) (run' body)) := by
  have hfst : (bs.zip us).map Prod.fst = bs := List.map_fst_zip (by omega)
  refine withVars (h _ _ hs hm) _ _ L _ (fun xv hxv => hu xv.2 (List.of_mem_zip hxv).2) ?_ ?_ ?_
  · rw [hfst]; exact hLb
  · rw [hfst]; exact Live.Sub.refl _
  · rw [hfst]; exact hX

/-- An arm with a guard: the guard with each way of its pattern, then the body or what comes
next. The guard runs with `Lg` live after it, which keeps what runs after it live, the guard
again among it. -/
theorem guarded (h : MRun run run') {L Lb Lg X : Live} {bs : List Name} {g body : Expr}
    (hgs : g.Safe) (hgm : g.movesOk Lg = true) (hbs : body.Safe)
    (hbm : body.movesOk (L.eraseAll bs) = true)
    (hLg : (Lb.eraseAll bs).Sub Lg) (hgb : (Lg.union g.mentions).Sub (Lb.union (Live.ofList bs)))
    (hgX : (g.mentions.eraseAll bs).Sub X)
    (hbb : ((L.eraseAll bs).union body.mentions).Sub (Lb.union (Live.ofList bs)))
    (hbX : (body.mentions.eraseAll bs).Sub X) (hL : L.Sub Lb)
    {next : Eval Copy.State Value} {next' : Eval (State × World) Value}
    (hn : MSim VOk Lb L X next next') :
    ∀ ways : List (List Value), (∀ us ∈ ways, ∀ u ∈ us, VOk u) →
      MSim VOk Lb L X (Eval.guarded Copy.memory run bs g body next ways)
        (Eval.guarded Moving.memory run' bs g body next' ways)
  | [], _ => hn
  | us :: ways, hw => by
    simp only [Eval.guarded]
    split
    · rename_i hlen
      have hu := hw us List.mem_cons_self
      have hfst : (bs.zip us).map Prod.fst = bs := List.map_fst_zip (by omega)
      have hrest := guarded h hgs hgm hbs hbm hLg hgb hgX hbb hbX hL hn ways
        fun us' hu' => hw us' (List.mem_cons_of_mem _ hu')
      have hgv : MSim (fun _ => True) (Lg.union g.mentions) Lg g.mentions
          (run g >>= Eval.asBool) (run' g >>= Eval.asBool) :=
        bind (h _ _ hgs hgm) (fun _ _ => asBool) (by live_sub) (Live.Sub.refl _)
      refine bind (withVars hgv (bs.zip us) Lb Lb X (fun xv hxv => hu xv.2 (List.of_mem_zip hxv).2)
          (by rw [hfst]; exact hgb) (by rw [hfst]; exact hLg) (by rw [hfst]; exact hgX))
        (fun b _ => ite b (armBody h hbs hbm hlen hu hbb hbX) hrest) (Live.Sub.refl _) hL
    · exact fail _

/-- The first arm of a `match` whose pattern matches and whose guard, if it has one, is true,
with the parts it binds bound (expressions.match, patterns.match and patterns.guards). -/
theorem select (h : MRun run run') {L : Live} :
    ∀ {arms : List Arm}, (∀ arm ∈ arms, arm.body.Safe ∧ ∀ g, arm.guard = some g → g.Safe) →
    armsMovesOk L arms = true → ∀ {v : Value}, VOk v →
    MSim VOk (L.union (armsMentions arms)) L (armsMentions arms)
      (Eval.select Copy.memory run arms v) (Eval.select Moving.memory run' arms v)
  | [], _, _, _, _ => fail _
  | ⟨p, bs, guard, b⟩ :: arms, harms, hm, v, hv => by
    simp only [armsMovesOk, Bool.and_eq_true] at hm
    obtain ⟨hbs, hgs⟩ := harms _ List.mem_cons_self
    have hrest := (select h (fun a ha => harms a (List.mem_cons_of_mem _ ha)) hm.2 hv).mono
      (Lb' := L.union (armsMentions (⟨p, bs, guard, b⟩ :: arms))) (L' := L)
      (X' := armsMentions (⟨p, bs, guard, b⟩ :: arms))
      (by simp only [armsMentions]; live_sub) (Live.Sub.refl _)
      (by simp only [armsMentions]; live_sub)
    simp only [Eval.select]
    cases guard with
    | none =>
      simp only
      cases hmatch : p.matchOn v with
      | none => exact hrest
      | some us =>
        simp only
        split
        · rename_i hlen
          exact armBody h hbs hm.1.2 hlen
            (fun u hu => ⟨p.matchOn_parts Value.Safe.passesToParts hv.1 hmatch u hu,
              p.matchOn_parts Value.Justified.passesToParts hv.2 hmatch u hu⟩)
            (by simp only [armsMentions, guardMentions]; live_sub)
            (by simp only [armsMentions, guardMentions]; live_sub)
        · exact fail _
    | some g =>
      simp only [guardMovesOk, guardMentions] at hm
      refine guarded h (hgs g rfl) hm.1.1 hbs hm.1.2 ?_ ?_ ?_ ?_ ?_ (by live_sub) hrest _
        fun us hus u hu => ?_
      all_goals try (simp only [armsMentions, guardMentions]; live_sub)
      obtain ⟨q, -, hq⟩ := Pattern.mem_ways hus
      exact ⟨q.matchOn_parts Value.Safe.passesToParts hv.1 hq u hu,
        q.matchOn_parts Value.Justified.passesToParts hv.2 hq u hu⟩

end MSim

end Stilt.Moving
