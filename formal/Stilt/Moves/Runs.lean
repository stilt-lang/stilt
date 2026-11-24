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

theorem arms_mem : ∀ {L : Live} {arms : List Arm}, armsMovesOk L arms = true → ∀ arm ∈ arms,
    arm.body.movesOk L = true ∧ arm.body.mentions.Sub (armsMentions arms)
  | _, [], _, _, h => by simp at h
  | L, ⟨C, bs, b⟩ :: arms, hm, arm, harm => by
    simp only [armsMovesOk, Bool.and_eq_true] at hm
    rcases List.mem_cons.1 harm with rfl | harm
    · exact ⟨hm.1, by simp only [armsMentions]; live_sub⟩
    · obtain ⟨h₁, h₂⟩ := arms_mem hm.2 arm harm
      exact ⟨h₁, h₂.trans (by simp only [armsMentions]; live_sub)⟩

/-- The first arm of a `match` whose pattern matches, with the parts it binds
bound (expressions.match and patterns.match). -/
theorem select (h : MRun run run') {L : Live} {arms : List Arm}
    (harms : ∀ arm ∈ arms, arm.body.Safe) (hm : armsMovesOk L arms = true) {v : Value} (hv : VOk v) :
    MSim VOk (L.union (armsMentions arms)) L (armsMentions arms)
      (Eval.select Copy.memory run arms v) (Eval.select Moving.memory run' arms v) := by
  unfold Eval.select
  cases hsel : selectArm arms v with
  | none => exact fail _
  | some au =>
    obtain ⟨arm, us⟩ := au
    obtain ⟨hmem, hmatch⟩ := selectArm_mem hsel
    dsimp only
    obtain ⟨hok, hsub⟩ := arms_mem hm arm hmem
    by_cases hlen : arm.binders.length = us.length
    · simp only [hlen, ↓reduceIte]
      exact withVars (h _ L (harms arm hmem) hok) hsub _ _
        (fun xv hxv =>
          ⟨arm.pattern.matchOn_parts Value.Safe.passesToParts hv.1 hmatch xv.2
              (List.of_mem_zip hxv).2,
            arm.pattern.matchOn_parts Value.Justified.passesToParts hv.2 hmatch xv.2
              (List.of_mem_zip hxv).2⟩)
        (Live.Sub.union ((Live.sub_union_left _ _).trans (Live.sub_union_left _ _))
          (hsub.trans ((Live.sub_union_right _ _).trans (Live.sub_union_left _ _))))
    · simp only [hlen, ↓reduceIte]
      exact fail _

end MSim

end Stilt.Moving
