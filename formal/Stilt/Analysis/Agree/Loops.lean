import Stilt.Analysis.Agree.Coarse

/-!
# Loops

A `while` or a `loop` whose head facts the analysis checked, facts that hold before it and that
each turn of its body keeps (`whileRes`, `loopRes`): from where they hold, its release run agrees
with the run that keeps every check, and ends where they and its condition's facts where false
hold, or a `break`'s (`agree_whileHead`, `agree_loopHead`), by induction on the fuel, each turn
running its body with less. A loop whose candidate facts fail the check is analysed from no fact,
and runs alike all the same (`while_eq`, `loop_eq`).
-/

namespace Stilt

theorem Outcome.sat_turn {P : Value → Copy.State → Prop} {B C B' C' : Copy.State → Prop} :
    ∀ {o : Outcome Copy.State Value}, o.Sat P B C →
      o.turn.Sat (fun b s => (b = true → (∃ v, P v s) ∨ C s) ∧ (b = false → B s)) B' C'
  | .done v _, h => ⟨fun _ => .inl ⟨v, h⟩, fun e => nomatch e⟩
  | .jumped .brk _, h => ⟨fun e => (nomatch e), fun _ => h⟩
  | .jumped .cont _, h => ⟨fun _ => .inr h, fun e => nomatch e⟩
  | .jumped (.ret _) _, _ => trivial
  | .performed _ _ _ _, h => fun w x => Outcome.sat_turn (h w x)
  | .raised _ _, _ | .panicked _ _, _ | .outOfFuel, _ | .stuck, _ => trivial

/-- A turn of a loop's body: it goes on where the body ends or continues, and stops at a
`break`. -/
theorem Eval.Agree.turn {P : Value → Copy.State → Prop} {B C B' C' : Copy.State → Prop}
    {m' m : Eval Copy.State Value} {s : Copy.State} (h : Eval.Agree P B C m' m s) :
    Eval.Agree (fun b s => (b = true → (∃ v, P v s) ∨ C s) ∧ (b = false → B s)) B' C'
      (Eval.turn m') (Eval.turn m) s :=
  ⟨by show (m' s).turn = (m s).turn; rw [h.1], Outcome.sat_turn h.2⟩

section

variable {D : Decls} {w : WriteBack}

local notation "M" => Copy.memoryWith w

theorem evalR_while (m : Nat) (c b : Expr) : evalR D M (m + 1) (.while c b) =
    (do if ← evalR D M m c >>= Eval.asBool then
          if ← Eval.turn (evalR D M m b) then evalR D M m (.while c b) else pure .unit
        else pure .unit) := by
  simp only [evalR]

theorem eval_while (m : Nat) (c b : Expr) : eval D M (m + 1) (.while c b) =
    (do if ← eval D M m c >>= Eval.asBool then
          if ← Eval.turn (eval D M m b) then eval D M m (.while c b) else pure .unit
        else pure .unit) := by
  simp only [eval]

theorem evalR_loop (m : Nat) (b : Expr) : evalR D M (m + 1) (.loop b) =
    (do if ← Eval.turn (evalR D M m b) then evalR D M m (.loop b) else pure .unit) := by
  simp only [evalR]

theorem eval_loop (m : Nat) (b : Expr) : eval D M (m + 1) (.loop b) =
    (do if ← Eval.turn (eval D M m b) then eval D M m (.loop b) else pure .unit) := by
  simp only [eval]

variable {n : Nat}

/-- A `while` analysed from no fact runs alike. -/
theorem while_eq (hall : ∀ k ≤ n, AgreeRun (evalR D M k) (eval D M k)) {L : Bool} {d : Nat} {c b : Expr} (hc : (an L d .top c).ok = true)
    (hb : (an L d .top b).ok = true) :
    ∀ m, m ≤ n + 1 → evalR D M m (.while c b) = eval D M m (.while c b)
  | 0, _ => rfl
  | m + 1, hm => by
    rw [evalR_while, eval_while, (hall m (by omega)).eqTop hc, (hall m (by omega)).eqTop hb,
      while_eq hall hc hb m (by omega)]

/-- A `loop` analysed from no fact runs alike. -/
theorem loop_eq (hall : ∀ k ≤ n, AgreeRun (evalR D M k) (eval D M k)) {L : Bool} {d : Nat} {b : Expr} (hb : (an L d .top b).ok = true) :
    ∀ m, m ≤ n + 1 → evalR D M m (.loop b) = eval D M m (.loop b)
  | 0, _ => rfl
  | m + 1, hm => by
    rw [evalR_loop, eval_loop, (hall m (by omega)).eqTop hb, loop_eq hall hb m (by omega)]

/-- Head facts that a turn keeps hold again at the head. -/
theorem head_again {I : Facts} {rb : Res} {st : List Value} {s : Copy.State}
    (hpres : (rb.post.noRes.join rb.cont).close.entails I = true)
    (h : (∃ v, rb.Done st v s) ∨ rb.cont.Holds (s.1.nu st .unit)) : I.Holds (s.1.nu st .unit) := by
  refine ((Facts.holds_join ?_).close rfl).entails rfl hpres
  rcases h with ⟨v, hv⟩ | h
  · exact .inl hv.1.noRes
  · exact .inr h

/-- A `while` whose head facts `I` the analysis checked (`whileRes`): from where they hold, the
release run agrees, and ends where the condition's facts where false hold, or a `break`'s. -/
theorem agree_whileHead (hall : ∀ k ≤ n, AgreeRun (evalR D M k) (eval D M k)) {L : Bool} {d : Nat} {I : Facts} {c b : Expr} {rc rb : Res}
    {st : List Value} (hd : st.length = d) (hrc : rc = an L d I c) (hrb : rb = an L d rc.tt.noRes b)
    (hc : rc.ok = true) (hb : rb.ok = true)
    (hpres : (rb.post.noRes.join rb.cont).close.entails I = true) :
    ∀ m, m ≤ n + 1 → ∀ s, I.Holds (s.1.nu st .unit) →
      Eval.Agree (fun v s => v = .unit ∧ (rc.ff.noRes.join rb.brk).Holds (s.1.nu st .unit))
        (fun s => rc.brk.Holds (s.1.nu st .unit)) (fun s => rc.cont.Holds (s.1.nu st .unit))
        (evalR D M m (.while c b)) (eval D M m (.while c b)) s
  | 0, _, _, _ => ⟨rfl, trivial⟩
  | m + 1, hm, s, hI => by
    have hA := hall m (by omega)
    subst hrc hrb
    rw [evalR_while, eval_while]
    refine (hA L d I c st s hc hd hI).asBool.bind (fun _ h => h) (fun _ h => h) fun v s₁ hv => ?_
    cases v
    · exact Eval.Agree.pure ⟨rfl, Facts.holds_join (.inl (hv.2.2 rfl).noRes)⟩
    · refine (Eval.Agree.turn (B' := fun s => (an L d I c).brk.Holds (s.1.nu st .unit))
        (C' := fun s => (an L d I c).cont.Holds (s.1.nu st .unit))
        (hA L d _ b st s₁ hb hd (hv.2.1 rfl).noRes)).bind (fun _ h => h) (fun _ h => h)
        fun u s₂ hu => ?_
      cases u
      · exact Eval.Agree.pure ⟨rfl, Facts.holds_join (.inr (hu.2 rfl))⟩
      · exact agree_whileHead hall hd rfl rfl hc hb hpres m (by omega) s₂ (head_again hpres (hu.1 rfl))

/-- A `loop` whose head facts `I` the analysis checked (`loopRes`): from where they hold, the
release run agrees, and ends where a `break`'s facts hold. -/
theorem agree_loopHead (hall : ∀ k ≤ n, AgreeRun (evalR D M k) (eval D M k)) {L : Bool} {d : Nat} {I : Facts} {b : Expr} {rb : Res} {st : List Value}
    (hd : st.length = d) (hrb : rb = an L d I b) (hb : rb.ok = true)
    (hpres : (rb.post.noRes.join rb.cont).close.entails I = true) :
    ∀ m, m ≤ n + 1 → ∀ s, I.Holds (s.1.nu st .unit) →
      Eval.Agree (fun v s => v = .unit ∧ rb.brk.Holds (s.1.nu st .unit))
        (fun s => Facts.bot.Holds (s.1.nu st .unit)) (fun s => Facts.bot.Holds (s.1.nu st .unit))
        (evalR D M m (.loop b)) (eval D M m (.loop b)) s
  | 0, _, _, _ => ⟨rfl, trivial⟩
  | m + 1, hm, s, hI => by
    have hA := hall m (by omega)
    subst hrb
    rw [evalR_loop, eval_loop]
    refine (Eval.Agree.turn (hA L d I b st s hb hd hI)).bind (fun _ h => h) (fun _ h => h)
      fun u s₂ hu => ?_
    cases u
    · exact Eval.Agree.pure ⟨rfl, hu.2 rfl⟩
    · exact agree_loopHead hall hd rfl hb hpres m (by omega) s₂ (head_again hpres (hu.1 rfl))

end

end Stilt
