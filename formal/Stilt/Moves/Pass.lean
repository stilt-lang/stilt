import Stilt.Moves.Args

/-!
# Evaluating the arguments of a call

`args` proves `ASim` for a call's arguments, evaluated from left to right
(values.left-to-right). A last use `move x` is a read that ends nothing: `x` stays
live until the call starts, and nothing after the read mentions `x`, so
nothing ends or writes it, and it still holds the value read
(`MAgrees.held`).
-/

namespace Stilt.Moving

open InPlace

variable {run : Expr → Eval Copy.State Value} {run' : Expr → Eval (State × World) Value}

theorem ASim.nil {Lb L X : Live} :
    ASim (ArgsOk []) Lb L X (Pure.pure []) (Pure.pure []) := fun _ _ _ hag _ =>
  ⟨rfl, ⟨⟨by simp [PassedOk], trivial, rfl⟩, by simp [MovedHeld]⟩, Post.refl hag⟩

theorem Post.moved {A : Live} {x : Name} {as : List Arg} {mk : List Bool} {s : State}
    {fr' : Copy.State} {s' : State × World} (hx : (argsMentions as).mem x = false)
    (h : Post (A.union (Live.ofList (movedRoots as))) (argsMentions as) mk s fr' s') :
    Post (A.union (Live.ofList (x :: movedRoots as))) ((Live.one x).union (argsMentions as))
      mk s fr' s' := by
  obtain ⟨m, hag', hk, henv, hev⟩ := h
  refine ⟨m, hag', ((hk.union_unmentioned (M := Live.one x) fun z hz => ?_).mono (by live_sub)
    (by live_sub)), henv, Evolves.of_sub (sel_mono (Live.sub_union_right _ _)) hev⟩
  simp only [Live.mem_one, Bool.eq_false_iff, ne_eq]
  rintro rfl
  rw [hx] at hz
  exact absurd hz (by simp)

/-- The arguments after a last use `move x`, which mention no `x`. -/
theorem args_move (hmv : MoveReads run run') (A : Live) (x : Name) (as : List Arg)
    (ih : ASim (ArgsOk as) (A.union (argsMentions as)) (A.union (Live.ofList (movedRoots as)))
      (argsMentions as) (Eval.args run as) (Eval.args run' as))
    (hx : (Expr.move x).movesOk (A.union (argsMentions as)) = true) :
    ASim (ArgsOk (.value (.move x) :: as)) (A.union ((Live.one x).union (argsMentions as)))
      (A.union (Live.ofList (x :: movedRoots as))) ((Live.one x).union (argsMentions as))
      (Eval.args run (.value (.move x) :: as)) (Eval.args run' (.value (.move x) :: as)) := by
  have hxa : (argsMentions as).mem x = false := by
    simp only [Expr.movesOk, Live.mem_union, Bool.not_eq_true', Bool.or_eq_false_iff] at hx
    exact hx.2
  have e₁ : Eval.args run (.value (.move x) :: as) = (run (.move x) >>= fun v =>
      Eval.args run as >>= fun vs => Pure.pure (Passed.moved x v :: vs)) := rfl
  have e₂ : Eval.args run' (.value (.move x) :: as) = (run' (.move x) >>= fun v =>
      Eval.args run' as >>= fun vs => Pure.pure (Passed.moved x v :: vs)) := rfl
  rw [e₁, e₂]
  intro ⟨fr, w⟩ ⟨s, w'⟩ mk ⟨hag, hw⟩ hinv
  dsimp only at hag hw hinv ⊢
  have hlx : LiveAt x mk (keys s) := hinv.live x (by simp)
  have hl₀ : LiveAt x mk (names fr) := hag.keys_eq ▸ hlx
  rcases hmv x with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂, MSim.bind_inspect, MSim.bind_inspect,
      show Copy.memory.read (fr, w) x [] = Copy.read fr x [] from rfl,
      show Moving.memory.read (s, w') x [] = Copy.read fr x [] from (hag.read hl₀ []).symm]
    cases hc : Copy.read fr x [] with
    | error f =>
      exact Outcome.Rel.fault (R := MCorr.relationF _ _ _ mk s)
        (fun _ => ⟨rfl, Post.refl (s := (s, w')) ⟨hag, hw⟩⟩) f
    | ok v =>
      dsimp only
      have hv := MSim.read_lookup hc
      have hvok := hag.read_ok hl₀ hc
      show ((Eval.args run as (fr, w)).bind fun a fr' =>
          (Pure.pure (Passed.moved x v :: a) : Eval Copy.State _) fr').Rel _
        ((Eval.args run' as (s, w')).bind fun a s' =>
          (Pure.pure (Passed.moved x v :: a) : Eval (State × World) _) s')
      refine Outcome.Rel.bind (ih (fr, w) (s, w') mk ⟨hag, hw⟩ (hinv.mono (by live_sub)))
        (MCorr.escapes fun _ _ hp => hp.moved hxa) ?_
      rintro a fr₁ a' s₁ ⟨rfl, ⟨hg, hheld⟩, hp⟩
      refine ⟨rfl, ⟨⟨fun q hq w hw => ?_, hg.2.1, ?_⟩, fun y w hy => ?_⟩, hp.moved hxa⟩
      · rcases List.mem_cons.1 hq with rfl | hq
        · cases hw; exact hvok
        · exact hg.1 q hq w hw
      · show x :: movedOf a = x :: movedRoots as
        rw [hg.2.2]
      · rcases List.mem_cons.1 hy with hy | hy
        · cases hy
          obtain ⟨m, hag', hk, henv, hev⟩ := hp
          exact (hag.held hlx hv hag'.1 hk hxa henv hev).1
        · exact hheld y w hy
  · rw [h₁, h₂]
    exact (trivial : MCorr _ _ _ mk s .outOfFuel .outOfFuel)

/-- Evaluating a call's arguments keeps the simulation, and passes each last
use with the value its variable still holds. -/
theorem args (h : MRun run run') (hmv : MoveReads run run') :
    ∀ (A : Live) (as : List Arg), ArgsSafe as → argsMovesOk A as = true →
      ASim (ArgsOk as) (A.union (argsMentions as)) (A.union (Live.ofList (movedRoots as)))
        (argsMentions as) (Eval.args run as) (Eval.args run' as)
  | _, [], _, _ => ASim.nil
  | A, .value e :: as, hs, hm => by
    simp only [argsMovesOk, Bool.and_eq_true] at hm
    by_cases hmove : ∃ x, e = .move x
    · obtain ⟨x, rfl⟩ := hmove
      exact args_move hmv A x as (args h hmv A as hs.tail hm.2) hm.1
    · have hne : ∀ x, e ≠ .move x := fun x hx => hmove ⟨x, hx⟩
      have hmr : movedRoots (.value e :: as) = movedRoots as := by
        simp [movedRoots, moved?_of_ne hne]
      rw [hmr]
      show ASim _ _ _ _ (run e >>= fun v => Eval.args run as >>= fun vs =>
        Pure.pure (Passed.ofArg e v :: vs)) (run' e >>= fun v => Eval.args run' as >>= fun vs =>
        Pure.pure (Passed.ofArg e v :: vs))
      simp only [ofArg_of_ne hne]
      simp only [argsMentions]
      refine ASim.bind ((h e _ (hs.1 e List.mem_cons_self) hm.1).mono (by live_sub)
        (Live.Sub.refl _) (by live_sub)) (fun v hv => ASim.cons (.value v)
          ((args h hmv A as hs.tail hm.2).mono (Live.Sub.refl _) (Live.Sub.refl _) (by live_sub)
            fun ps h => h) (fun ps hps => ⟨fun q hq w hw => ?_, hps.2.1, ?_⟩)
          (fun _ _ h => by cases h)) (by live_sub) (movedRoots_sub' A as)
      · rcases List.mem_cons.1 hq with rfl | hq
        · cases hw; exact hv
        · exact hps.1 q hq w hw
      · show movedOf ps = _
        rw [hmr, hps.2.2]
  | A, .inout ⟨x, ps⟩ :: as, hs, hm => by
    simp only [argsMovesOk, Bool.and_eq_true] at hm
    show ASim _ _ (A.union (Live.ofList (movedRoots as))) _ (Eval.path run ps >>= fun p =>
      Eval.args run as >>= fun vs => Pure.pure (Passed.place x p :: vs)) (Eval.path run' ps >>=
      fun p => Eval.args run' as >>= fun vs => Pure.pure (Passed.place x p :: vs))
    simp only [argsMentions]
    refine ASim.bind ((MSim.path h _ ps (hs.2 x ps List.mem_cons_self) hm.1).mono (by live_sub)
      (Live.Sub.refl _) (by live_sub)) (fun p hp => ASim.cons (.place x p)
        ((args h hmv A as hs.tail hm.2).mono (Live.Sub.refl _) (Live.Sub.refl _) (by live_sub)
          fun ps h => h) (fun qs hqs => ⟨fun q hq w hw => ?_, ⟨rfl, hp, hqs.2.1⟩, hqs.2.2⟩)
        (fun _ _ h => by cases h)) (by live_sub) (movedRoots_sub' A as)
    · rcases List.mem_cons.1 hq with rfl | hq
      · cases hw
      · exact hqs.1 q hq w hw

end Stilt.Moving
