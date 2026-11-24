import Stilt.Moves.Cases

/-!
# The forms of expressions

One lemma for each form of expression that the simulation treats in more than
a line: a call, `let` and `var`, indexing, assignment, `if`, the loops, `catch`
and a closure literal. Each states the simulation for the form, with the
variables it mentions and those after it live, from the simulation of its
parts (`MRun`).
-/

namespace Stilt.Moving

open InPlace

variable {run : Expr → Eval Copy.State Value} {run' : Expr → Eval (State × World) Value} {L : Live}

theorem call_case {D : Decls} (hD : DeclsOk D) (h : MRun run run') (hmv : MoveReads run run')
    {callee : Expr} {as : List Arg} {τ : Ty} {r : List Shape}
    (hex : (Expr.call callee as τ).exclusive r = true)
    (hdp : (Expr.call callee as τ).distinctParams = true)
    (hm : (Expr.call callee as τ).movesOk L = true) :
    MSim VOk (L.union (Expr.call callee as τ).mentions) L (Expr.call callee as τ).mentions
      (run callee >>= fun f => Eval.args run as >>= fun ps => Eval.callAs D Copy.memory run false f ps)
      (run' callee >>= fun f => Eval.args run' as >>= fun ps => Eval.callAs D Moving.memory run' false f ps) := by
  simp only [Expr.exclusive, Expr.distinctParams, Expr.movesOk, Bool.and_eq_true] at hex hdp hm
  simp only [Expr.mentions]
  have hIn : (Live.ofList (inoutRoots as)).Sub (argsMentions as) :=
    ⟨by simp, fun z hz => inoutRoots_sub as z ((Live.mem_ofList _ _).1 hz)⟩
  have hMv : (Live.ofList (movedRoots as)).Sub (argsMentions as) :=
    ⟨by simp, fun z hz => movedRoots_sub as z ((Live.mem_ofList _ _).1 hz)⟩
  have hA : (L.union (Live.ofList (inoutRoots as))).Sub (L.union (argsMentions as)) :=
    Live.Sub.union (Live.sub_union_left _ _) (hIn.trans (Live.sub_union_right _ _))
  refine MSim.bind ((h callee _ ⟨⟨r, hex.1.1.1⟩, hdp.1⟩ hm.1).mono (by live_sub) (Live.Sub.refl _)
    (by live_sub)) (fun f hf => MSim.bind_args ((args h hmv _ as (args_safe hex.1.1.2 hdp.2)
      hm.2).mono (Live.Sub.union hA (Live.sub_union_right _ _)) (Live.Sub.refl _) (by live_sub)
        fun _ h => h) (fun ps fr s mk hok hheld hag hinv => callAs_step hD h false hf (readyP hok hheld hag
          hinv hm.2 (compat_of_resolved hok.2.1 ((pairwiseDisjoint_iff _).1 hex.2)) (by live_sub)))
      (Live.Sub.union hA (hMv.trans (Live.sub_union_right _ _)))
      ((Live.sub_union_left _ _).trans (Live.sub_union_left _ _))) (by live_sub) (by live_sub)

theorem let_case (h : MRun run run') (hmv : MoveReads run run') {x : Name} {init body : Expr}
    (hi : init.Safe) (hb : body.Safe) (hmi : init.movesOk (L.union (body.mentions.erase x)) = true)
    (hmb : body.movesOk L = true) :
    MSim VOk (L.union ((Live.one x).union (init.mentions.union body.mentions))) L
      ((Live.one x).union (init.mentions.union body.mentions))
      (run init >>= fun v => Eval.withInit Copy.memory x init v (run body))
      (run' init >>= fun v => Eval.withInit Moving.memory x init v (run' body)) := by
  have hB : (body.mentions.erase x).Sub body.mentions := Live.erase_sub _ _
  have hLB : (L.union (body.mentions.erase x)).Sub
      (L.union ((Live.one x).union (init.mentions.union body.mentions))) :=
    Live.Sub.union (Live.sub_union_left _ _) (hB.trans (by live_sub))
  have hkeep : ∀ z, (L.union body.mentions).mem z = true → z ≠ x →
      (L.union (body.mentions.erase x)).mem z = true := fun z hz hzx => by
    simp only [Live.mem_union, Bool.or_eq_true] at hz ⊢
    exact hz.imp id fun h => Live.mem_erase_of_ne h hzx
  by_cases hmove : ∃ y, init = .move y
  · obtain ⟨y, rfl⟩ := hmove
    have hy : (L.union (body.mentions.erase x)).mem y = false := by simpa [Expr.movesOk] using hmi
    rcases hmv y with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rw [h₁, h₂]
    · refine MSim.withMove y x (h body L hb hmb) (by simp [Expr.mentions]) ?_ (by simp [Expr.mentions])
        (by live_sub) (fun z hz hzx => ⟨fun hzy => ?_, ?_⟩) ?_
      · simp only [Live.mem_union, Bool.or_eq_false_iff] at hy
        exact hy.1
      · subst hzy
        rw [hkeep z hz hzx] at hy
        cases hy
      · simp only [Live.mem_union, Bool.or_eq_true] at hz ⊢
        rcases hz with hz | hz
        · exact .inl hz
        · exact .inr (by simp [hz])
      · cases hall : (L.union body.mentions).all
        · rfl
        · have := Live.mem_of_all (L := L.union (body.mentions.erase x)) (by simpa using hall) y
          rw [hy] at this
          cases this
    · exact fun _ _ _ _ _ => trivial
  · have hne : ∀ y, init ≠ .move y := fun y hy => hmove ⟨y, hy⟩
    simp only [Eval.withInit_eq_withVar _ x hne]
    exact MSim.bind ((h init _ hi hmi).mono (Live.Sub.union hLB (by live_sub)) (Live.Sub.refl _)
      (by live_sub)) (fun v hv => MSim.withVar x hv (h body L hb hmb) hkeep
        (fun h => by simpa using h) (by live_sub)) hLB (Live.sub_union_left _ _)

theorem index_case (h : MRun run run') {e i : Expr} (he : e.Safe) (hi : i.Safe)
    (hme : e.movesOk (L.union i.mentions) = true) (hmi : i.movesOk L = true) :
    MSim VOk (L.union (e.mentions.union i.mentions)) L (e.mentions.union i.mentions)
      (run e >>= fun v => (run i >>= Eval.asInt) >>= fun k => Eval.ofExcept (v.get [.index k]))
      (run' e >>= fun v => (run' i >>= Eval.asInt) >>= fun k => Eval.ofExcept (v.get [.index k])) :=
  MSim.bind ((h e _ he hme).mono (by live_sub) (Live.Sub.refl _) (by live_sub)) (fun _ hv =>
    MSim.bind (MSim.bind ((h i L hi hmi).mono (Live.Sub.refl _) (Live.Sub.refl _) (by live_sub))
      (fun _ _ => MSim.asInt) (by live_sub) (Live.Sub.refl _)) (fun _ _ => MSim.get hv _)
      (by live_sub) (Live.Sub.refl _)) (by live_sub) (by live_sub)

theorem assign_case (h : MRun run run') {x : Name} {ps : List Projection} {v : Expr}
    (hps : PathSafe ps) (hv : v.Safe)
    (hmp : pathMovesOk ((Live.one x).union (L.union v.mentions)) ps = true)
    (hmv : v.movesOk ((Live.one x).union L) = true) :
    MSim VOk (L.union ((Live.one x).union ((pathMentions ps).union v.mentions))) L
      ((Live.one x).union ((pathMentions ps).union v.mentions))
      (Eval.assign Copy.memory run x ps v) (Eval.assign Moving.memory run' x ps v) :=
  MSim.bind ((MSim.path h _ ps hps hmp).mono (by live_sub) (Live.Sub.refl _) (by live_sub))
    (fun p _ => MSim.bind ((h v _ hv hmv).mono (by live_sub) (Live.Sub.refl _) (by live_sub))
      (fun _ hw => MSim.bind (MSim.update x p hw (by simp) (by simp))
        (fun _ _ => MSim.pure ⟨.unit, .unit⟩) (Live.Sub.refl _) (by live_sub))
      (by live_sub) (by live_sub)) (by live_sub) (by live_sub)

theorem if_case (h : MRun run run') {c a b : Expr} (hc : c.Safe) (ha : a.Safe) (hb : b.Safe)
    (hmc : c.movesOk (L.union (a.mentions.union b.mentions)) = true) (hma : a.movesOk L = true)
    (hmb : b.movesOk L = true) :
    MSim VOk (L.union (c.mentions.union (a.mentions.union b.mentions))) L
      (c.mentions.union (a.mentions.union b.mentions))
      ((run c >>= Eval.asBool) >>= fun v => if v then run a else run b)
      ((run' c >>= Eval.asBool) >>= fun v => if v then run' a else run' b) :=
  MSim.bind (MSim.bind ((h c _ hc hmc).mono (by live_sub) (Live.Sub.refl _) (by live_sub))
    (fun _ _ => MSim.asBool) (by live_sub) (Live.Sub.refl _))
    (fun v _ => MSim.ite v ((h a L ha hma).mono (by live_sub) (Live.Sub.refl _) (by live_sub))
      ((h b L hb hmb).mono (by live_sub) (Live.Sub.refl _) (by live_sub))) (by live_sub) (by live_sub)

theorem for_case (h : MRun run run') {x : Name} {e body : Expr} (he : e.Safe) (hb : body.Safe)
    (hme : e.movesOk (L.union body.mentions) = true) (hmb : body.movesOk (L.union body.mentions) = true) :
    MSim VOk (L.union ((Live.one x).union (e.mentions.union body.mentions))) L
      ((Live.one x).union (e.mentions.union body.mentions))
      (Eval.loop Copy.memory run x e body) (Eval.loop Moving.memory run' x e body) :=
  MSim.loop x ((h e _ he hme).mono (by live_sub) (Live.Sub.refl _) (by live_sub)) (h body _ hb hmb)
    (fun z hz _ => by simpa using hz) (fun h => by simpa using h) (by live_sub) (by live_sub)
    (by live_sub)

/-- A `while` evaluates its condition and runs a turn of its body until the
condition is `false` or a `break` ends it, each turn followed by the loop again
(expressions.loops and expressions.break-and-continue). -/
theorem while_case (h : MRun run run') {c body : Expr} (hs : (Expr.while c body).Safe)
    (hm : (Expr.while c body).movesOk L = true) :
    MSim VOk (L.union (c.mentions.union body.mentions)) L (c.mentions.union body.mentions)
      ((run c >>= Eval.asBool) >>= fun v => if v then
        (Eval.turn (run body) >>= fun g => if g then run (.while c body) else Pure.pure .unit)
        else Pure.pure .unit)
      ((run' c >>= Eval.asBool) >>= fun v => if v then
        (Eval.turn (run' body) >>= fun g => if g then run' (.while c body) else Pure.pure .unit)
        else Pure.pure .unit) := by
  obtain ⟨⟨r, hex⟩, hdp⟩ := hs
  have hm' := hm
  simp only [Expr.exclusive, Expr.distinctParams, Expr.movesOk, Bool.and_eq_true] at hex hdp hm'
  have hl := h (.while c body) L ⟨⟨r, by simp [Expr.exclusive, hex.1, hex.2]⟩,
    by simp [Expr.distinctParams, hdp.1, hdp.2]⟩ hm
  simp only [Expr.mentions] at hl
  exact MSim.bind (MSim.bind ((h c _ ⟨⟨r, hex.1⟩, hdp.1⟩ hm'.1).mono (by live_sub)
      (Live.Sub.refl _) (by live_sub)) (fun _ _ => MSim.asBool) (by live_sub) (Live.Sub.refl _))
    (fun v _ => MSim.ite v
      (MSim.bind (MSim.turn ((h body _ ⟨⟨r, hex.2⟩, hdp.2⟩ hm'.2).mono (by live_sub)
          (Live.Sub.refl _) (by live_sub)))
        (fun g _ => MSim.ite g (hl.mono (by live_sub) (Live.Sub.refl _) (Live.Sub.refl _))
          (MSim.pure ⟨.unit, .unit⟩)) (Live.Sub.refl _) (by live_sub))
      (MSim.pure ⟨.unit, .unit⟩)) (by live_sub) (by live_sub)

/-- A `loop` runs a turn of its body until a `break` ends it, each turn followed
by the loop again (expressions.loops). -/
theorem loop_case (h : MRun run run') {body : Expr} (hs : (Expr.loop body).Safe)
    (hm : (Expr.loop body).movesOk L = true) :
    MSim VOk (L.union body.mentions) L body.mentions
      (Eval.turn (run body) >>= fun g => if g then run (.loop body) else Pure.pure .unit)
      (Eval.turn (run' body) >>= fun g => if g then run' (.loop body) else Pure.pure .unit) := by
  obtain ⟨⟨r, hex⟩, hdp⟩ := hs
  have hm' := hm
  simp only [Expr.exclusive, Expr.distinctParams, Expr.movesOk] at hex hdp hm'
  have hl := h (.loop body) L ⟨⟨r, by simpa [Expr.exclusive] using hex⟩,
    by simpa [Expr.distinctParams] using hdp⟩ hm
  simp only [Expr.mentions] at hl
  exact MSim.bind (MSim.turn ((h body _ ⟨⟨r, hex⟩, hdp⟩ hm').mono (by live_sub)
      (Live.Sub.refl _) (Live.Sub.refl _)))
    (fun g _ => MSim.ite g (hl.mono (by live_sub) (Live.Sub.refl _) (Live.Sub.refl _))
      (MSim.pure ⟨.unit, .unit⟩)) (by live_sub) (by live_sub)

theorem catch_case (h : MRun run run') {e hd : Expr} {x : Name} (he : e.Safe) (hh : hd.Safe)
    (hme : e.movesOk (L.union hd.mentions) = true) (hmh : hd.movesOk L = true) :
    MSim VOk (L.union ((Live.one x).union (e.mentions.union hd.mentions))) L
      ((Live.one x).union (e.mentions.union hd.mentions))
      (Eval.handle (run e) fun err => Eval.withVar Copy.memory x err (run hd))
      (Eval.handle (run' e) fun err => Eval.withVar Moving.memory x err (run' hd)) :=
  MSim.handle ((h e _ he hme).mono (by live_sub) (Live.Sub.refl _) (by live_sub))
    (fun _ hv => MSim.withVar x hv (h hd L hh hmh) (fun z hz _ => hz) id (by live_sub))
    (by live_sub) (by live_sub)

theorem closure_case {ps : List Param} {result : Ty} {ρ : Row} {body : Expr}
    (hnd : (ps.map Param.name).Nodup) (hex : body.exclusive [] = true)
    (hdp : body.distinctParams = true) (hm : body.movesOk (inoutLive ps) = true) :
    MSim VOk (L.union Live.every) L Live.every
      (Eval.inspect Copy.memory.capture >>= fun c =>
        Pure.pure (Value.closure (captureOf ps body c) ps result ρ body))
      (Eval.inspect Moving.memory.capture >>= fun c =>
        Pure.pure (Value.closure (captureOf ps body c) ps result ρ body)) :=
  MSim.bind (MSim.capture (by simp)) (fun _ hc => MSim.pure
    ⟨.closure hnd hex hdp fun xv h => (hc xv (mem_of_mem_captureOf h)).1,
      .closure hm fun xv h => (hc xv (mem_of_mem_captureOf h)).2⟩)
    (by live_sub) (Live.Sub.refl _)

end Stilt.Moving
