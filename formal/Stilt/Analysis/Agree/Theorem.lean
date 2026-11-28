import Stilt.Analysis.Agree.Ranges

/-!
# Release builds agree

`agree`: with every fuel, the release run of an expression, where the analysis's facts hold and
every mark it analyses is proved, ends as the run that keeps every check, and meets the facts the
analysis gives it; by induction on the fuel, case by case on the expression. So a body that the
analysis proves whole runs alike in both (`evalBody_eq`), and a release build of a program shows
what the reference interpreter shows, with the same outcome (`Program.runRelease_eq`): no check
that a release build drops ever fails (facts.what-proofs-change).
-/

namespace Stilt

variable (D : Decls) (w : WriteBack)

/-- With the fuel zero, both runs are out of fuel. -/
theorem agree_zero : AgreeRun (evalR D (Copy.memoryWith w) 0) (eval D (Copy.memoryWith w) 0) :=
  fun _ _ _ _ _ _ _ _ _ => ⟨rfl, trivial⟩

/-- A body the analysis proves whole runs alike in a release build. -/
theorem evalBody_eq {n : Nat} (ih : AgreeRun (evalR D (Copy.memoryWith w) n) (eval D (Copy.memoryWith w) n)) :
    evalBody D (Copy.memoryWith w) (evalR D (Copy.memoryWith w) n) n = eval D (Copy.memoryWith w) n := by
  funext b s
  unfold evalBody
  split
  · rename_i h
    exact (ih _ 0 .top b [] s h rfl (Facts.top_holds _)).1
  · rfl

theorem an_op {L : Bool} {d : Nat} {F : Facts} {o : Op} {es : List Expr}
    (h : ¬ ∃ c, o = .not ∧ es = [c]) : an L d F (.op o es) = opRes L d o es (anOps L d F es) := by
  cases o
  case not =>
    rcases es with _ | ⟨c, _ | ⟨c', es⟩⟩
    · rfl
    · exact absurd ⟨c, rfl, rfl⟩ h
    · rfl
  all_goals rfl

theorem an_after {F : Facts} {e : Expr} {W : List Name} {ok : Bool}
    {st : List Value} {s : Copy.State} {m' m : Eval Copy.State Value} (hW : W = e.writes)
    (heq : m' s = m s) (hk : (m s).Keeps e.writes e.resizes (fun _ => True) s.1)
    (hF : F.Holds (s.1.nu st .unit)) : (Res.after F W ok).Agrees st m' m s := by
  subst hW
  exact ⟨heq, Outcome.Keeps.meets hF hk⟩

theorem whileRes_elim {P : Res → Prop} {F I : Facts} {rc rb fb : Res}
    (h1 : (F.close.entails I && (rb.post.noRes.join rb.cont).close.entails I) = true →
      P ⟨rc.ff.noRes.join rb.brk, rc.ff.noRes.join rb.brk, rc.ff.noRes.join rb.brk, rc.brk,
        rc.cont, none, none, none, rc.ok && rb.ok⟩)
    (h2 : P fb) : P (whileRes F I rc rb fb) := by
  unfold whileRes; split
  · exact h1 ‹_›
  · exact h2

theorem loopRes_elim {P : Res → Prop} {F I : Facts} {rb fb : Res}
    (h1 : (F.close.entails I && (rb.post.noRes.join rb.cont).close.entails I) = true →
      P ⟨rb.brk, rb.brk, rb.brk, .bot, .bot, none, none, none, rb.ok⟩)
    (h2 : P fb) : P (loopRes F I rb fb) := by
  unfold loopRes; split
  · exact h1 ‹_›
  · exact h2

theorem forRes_elim {P : Res → Prop} {x : Name} {G I : Facts} {re rb fb : Res}
    (h1 : (G.close.entails I && ((rb.post.noRes.join rb.cont).unbind x).close.entails I) = true →
      P ⟨I.join (rb.brk.unbind x), I.join (rb.brk.unbind x), I.join (rb.brk.unbind x), re.brk,
        re.cont, none, none, none, re.ok && rb.ok⟩)
    (h2 : P fb) : P (forRes x G I re rb fb) := by
  unfold forRes; split
  · exact h1 ‹_›
  · exact h2

section

variable {D w}

local notation "M" => Copy.memoryWith w

/-- A `for` whose head facts the analysis checked (`forRes`). -/
theorem agree_forOk {n : Nat} (ih : AgreeRun (evalR D M n) (eval D M n))
    (hk : KeepsRun (eval D M n)) (hall : ∀ k ≤ n, AgreeRun (evalR D M k) (eval D M k)) {L : Bool}
    {d : Nat} {F J I Bf : Facts} {x : Name} {τ : Ty} {e b : Expr} {lo hi : Option (Term × Int)}
    {st : List Value} {s : Copy.State} (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit))
    (hI : I = J.unbind x) (hlo : lo = forLo L d F x b e) (hhi : hi = forHi L d F x b e)
    (hBf : Bf = I.forRange x lo hi)
    (hchk : ((an L d F e).post.noRes.close.entails I &&
      (((an L d Bf b).post.noRes.join (an L d Bf b).cont).unbind x).close.entails I) = true)
    (hok : ((an L d F e).ok && (an L d Bf b).ok) = true) :
    Res.Agrees ⟨I.join ((an L d Bf b).brk.unbind x), I.join ((an L d Bf b).brk.unbind x),
        I.join ((an L d Bf b).brk.unbind x), (an L d F e).brk, (an L d F e).cont, none, none, none,
        (an L d F e).ok && (an L d Bf b).ok⟩ st
      (evalR D M (n + 1) (.for x τ e b)) (eval D M (n + 1) (.for x τ e b)) s := by
  subst hI hlo hhi hBf
  replace hchk := (Bool.and_eq_true _ _).mp hchk
  replace hok := (Bool.and_eq_true _ _).mp hok
  have hlo := forLo_steady (L := L) (d := d) (F := F) (x := x) (body := b) (e := e)
  have hhi := forHi_steady (L := L) (d := d) (F := F) (x := x) (body := b) (e := e)
  refine (agree_forHead w ih hk hd (agree_forIter (x := x) (body := b) hall hok.1 hd hF) hok.2
    hchk.1 hchk.2 (fun _ _ _ _ _ k hq => rangeQ_keeps hlo hhi k hq)
    (fun _ _ _ hv hq hI => forRange_start hlo hhi hv hq hI)).mono ?_ (fun _ h => h) (fun _ h => h)
  rintro v s' ⟨rfl, h⟩
  exact Res.done_of h (fun e => (nomatch e)) (fun e => (nomatch e))

set_option maxHeartbeats 1000000 in
/-- One more step of fuel: each form of the calculus, from what agrees with less fuel. -/
theorem agree_succ {n : Nat} (ih : AgreeRun (evalR D M n) (eval D M n))
    (ihk : ∀ k, k < n → AgreeRun (evalR D M k) (eval D M k)) :
    AgreeRun (evalR D M (n + 1)) (eval D M (n + 1)) := by
  have hk := eval_keeps D w n
  have hall : ∀ k ≤ n, AgreeRun (evalR D M k) (eval D M k) := fun k hk' =>
    (Nat.lt_or_eq_of_le hk').elim (ihk k) fun h => h ▸ ih
  have hbody := evalBody_eq D w ih
  intro L d F e st s hok hd hF
  have keeps1 : ∀ e, (eval D M (n + 1) e s).Keeps e.writes e.resizes (fun _ => True) s.1 :=
    fun e => eval_keeps D w (n + 1) e _ _ (List.Subset.refl _) (List.Subset.refl _) s
  cases e with
  | var x => exact agree_var w hF
  | move x => exact agree_move w hF
  | int k => exact agree_int hF
  | bool b => exact agree_bool hF
  | unit => exact agree_still ⟨rfl, rfl, rfl⟩ hF (.inl ⟨_, rfl⟩)
  | fnRef f ts rs => exact agree_still ⟨rfl, rfl, rfl⟩ hF (.inl ⟨_, rfl⟩)
  | method t m τ => exact agree_still ⟨rfl, rfl, rfl⟩ hF (Eval.method_still D t m τ s)
  | closure ps r ρ b => exact agree_still ⟨rfl, rfl, rfl⟩ hF (Eval.closure_still w _ _ s)
  | op o es =>
    by_cases hn : ∃ c, o = .not ∧ es = [c]
    · obtain ⟨c, rfl, rfl⟩ := hn
      exact agree_not w ih hok hd hF
    · rw [an_op hn] at hok ⊢
      exact agree_op w ih (by rwa [opRes_ok] at hok) hd hF
  | list τ es => exact agree_listLit ih hok hd hF
  | index a i => exact agree_index ih hok hd hF
  | field e f => exact agree_field ih hok hd hF
  | letIn x τ init body => exact agree_scope w ih hk hok hd hF
  | varIn x τ init body => exact agree_scope w ih hk hok hd hF
  | seq a b => exact agree_seq ih hok hd hF
  | «if» c τ a b => exact agree_if ih hok hd hF
  | «break» => exact agree_break hF
  | «continue» => exact agree_continue hF
  | «return» e => exact agree_return ih hok hd hF
  | raise e => exact agree_raise ih hok hd hF
  | assign p v =>
    obtain ⟨x, ps⟩ := p
    rcases ps with _ | ⟨p1, _ | ⟨p2, ps⟩⟩
    · exact agree_assign w ih hok hd hF
    · cases p1 with
      | index i => exact agree_store w ih hok hd hF
      | field f =>
        simp only [an, Res.after, Bool.and_eq_true] at hok
        refine an_after rfl ?_ (keeps1 _) hF
        simp only [evalR, eval, Eval.assign]
        rw [Eval.path_congr (fun i hi => ih.eqTop (okPath_all hok.1 i hi)), ih.eqTop hok.2]
    · cases p1 <;>
      · simp only [an, Res.after, Bool.and_eq_true] at hok
        refine an_after rfl ?_ (keeps1 _) hF
        simp only [evalR, eval, Eval.assign]
        rw [Eval.path_congr (fun i hi => ih.eqTop (okPath_all hok.1 i hi)), ih.eqTop hok.2]
  | record R ts fs =>
    simp only [an, Res.after] at hok
    refine an_after rfl ?_ (keeps1 _) hF
    simp only [evalR, eval]
    rw [Eval.fields_congr fun fe h => ih.eqTop (okFields_all hok fe h)]
  | variant T ts C es =>
    simp only [an, Res.after] at hok
    refine an_after rfl ?_ (keeps1 _) hF
    simp only [evalR, eval]
    rw [Eval.list_congr fun e h => ih.eqTop (okExprs_all hok e h)]
  | view es =>
    simp only [an, Res.after] at hok
    refine an_after rfl ?_ (keeps1 _) hF
    simp only [evalR, eval]
    rw [Eval.list_congr fun e h => ih.eqTop (okExprs_all hok e h)]
  | call f args τ =>
    simp only [an, Res.after, Bool.and_eq_true] at hok
    refine an_after rfl ?_ (keeps1 _) hF
    simp only [evalR, eval]
    rw [ih.eqTop hok.1, Eval.args_congr (okArgs_all ih hok.2), hbody]
  | «match» e τ arms =>
    simp only [an, Res.after, Bool.and_eq_true] at hok
    refine an_after rfl ?_ (keeps1 _) hF
    simp only [evalR, eval]
    rw [ih.eqTop hok.1]
    simp only [Eval.select_congr (okArms_all ih hok.2)]
  | «for» x τ e b =>
    revert hok
    dsimp only [an]
    refine forRes_elim (P := fun R => R.ok = true →
      R.Agrees st (evalR D M (n + 1) (.for x τ e b)) (eval D M (n + 1) (.for x τ e b)) s) ?_ ?_
    · intro hchk hok
      exact agree_forOk ih hk hall hd hF rfl rfl rfl rfl hchk hok
    · intro hok
      simp only [Res.after, Bool.and_eq_true] at hok
      refine an_after rfl ?_ (keeps1 (.for x τ e b)) hF
      simp only [evalR, eval]
      rw [Eval.loop_congr (ih.eqTop hok.1) (ih.eqTop hok.2)]
  | «while» c b =>
    revert hok
    dsimp only [an]
    refine whileRes_elim (P := fun R => R.ok = true →
      R.Agrees st (evalR D M (n + 1) (.while c b)) (eval D M (n + 1) (.while c b)) s) ?_ ?_
    · intro hchk hok
      replace hchk := (Bool.and_eq_true _ _).mp hchk
      replace hok := (Bool.and_eq_true _ _).mp hok
      refine (agree_whileHead hall hd rfl rfl hok.1 hok.2 hchk.2 (n + 1) (Nat.le_refl _) s
        ((hF.close rfl).entails rfl hchk.1)).mono ?_ (fun _ h => h) (fun _ h => h)
      rintro v s' ⟨rfl, h⟩
      exact Res.done_of h (fun e => (nomatch e)) (fun e => (nomatch e))
    · intro hok
      simp only [Res.after, Bool.and_eq_true] at hok
      exact an_after rfl (by rw [while_eq hall hok.1 hok.2 (n + 1) (Nat.le_refl _)])
        (keeps1 (.while c b)) hF
  | «loop» b =>
    revert hok
    dsimp only [an]
    refine loopRes_elim (P := fun R => R.ok = true →
      R.Agrees st (evalR D M (n + 1) (.loop b)) (eval D M (n + 1) (.loop b)) s) ?_ ?_
    · intro hchk hok
      replace hchk := (Bool.and_eq_true _ _).mp hchk
      refine (agree_loopHead hall hd rfl hok hchk.2 (n + 1) (Nat.le_refl _) s
        ((hF.close rfl).entails rfl hchk.1)).mono ?_ (fun _ h => h) (fun _ h => h)
      rintro v s' ⟨rfl, h⟩
      exact Res.done_of h (fun e => (nomatch e)) (fun e => (nomatch e))
    · intro hok
      simp only [Res.after] at hok
      exact an_after rfl (by rw [loop_eq hall hok (n + 1) (Nat.le_refl _)]) (keeps1 (.loop b)) hF
  | «try» e =>
    simp only [an, Res.after] at hok
    refine an_after (e := .try e) rfl ?_ (keeps1 _) hF
    show evalR D M n e s = eval D M n e s
    rw [ih.eqTop hok]
  | tryCatch e τ x h τ' =>
    simp only [an, Res.after, Bool.and_eq_true] at hok
    refine an_after rfl ?_ (keeps1 _) hF
    simp only [evalR, eval]
    rw [ih.eqTop hok.1, ih.eqTop hok.2]
  | perform op e =>
    simp only [an, Res.after] at hok
    refine an_after (e := .perform op e) rfl ?_ (keeps1 _) hF
    simp only [evalR, eval]
    rw [ih.eqTop hok]
  | withH E c h b =>
    simp only [an, Res.after, Bool.and_eq_true] at hok
    refine an_after rfl ?_ (keeps1 _) hF
    simp only [evalR, eval]
    rw [ih.eqTop hok.1, ih.eqTop hok.2, hbody]
  | held ns hs b =>
    simp only [an, Res.after, Bool.and_eq_true] at hok
    refine an_after rfl ?_ (keeps1 _) hF
    simp only [evalR, eval]
    rw [Eval.list_congr fun e h => ih.eqTop (okExprs_all hok.1 e h), ih.eqTop hok.2]
  | form f m =>
    cases f
    case proved ks =>
      cases n with
      | zero => exact ⟨rfl, trivial⟩
      | succ k =>
        have ihk' := ihk k (by omega)
        cases m
        case op o es =>
          simp only [an, Bool.and_eq_true] at hok
          rw [opRes_ok] at hok
          exact agree_provedOp w ihk' hok.1 hok.2 hd hF
        case index a i => exact agree_provedIndex ihk' hok hd hF
        case assign p v =>
          obtain ⟨x, ps⟩ := p
          rcases ps with _ | ⟨p1, _ | ⟨p2, ps⟩⟩
          · simp [an] at hok
          · cases p1 with
            | index i => exact agree_provedStore w ihk' hok hd hF
            | field f => simp [an] at hok
          · simp [an] at hok
        all_goals simp [an] at hok
    all_goals exact ih L d F m st s hok hd hF

end

theorem agree_le : ∀ n m, m ≤ n → AgreeRun (evalR D (Copy.memoryWith w) m) (eval D (Copy.memoryWith w) m)
  | 0, m, h => by
    obtain rfl : m = 0 := by omega
    exact agree_zero D w
  | n + 1, m, h => by
    rcases Nat.lt_or_ge m (n + 1) with hm | hm
    · exact agree_le n m (by omega)
    · obtain rfl : m = n + 1 := by omega
      exact agree_succ (agree_le n n (Nat.le_refl n)) fun k hk => agree_le n k (by omega)

/-- With every fuel, the release run agrees with the run that keeps every check, wherever the
analysis's facts hold and every mark it analyses is proved (facts.what-proofs-change). -/
theorem agree (n : Nat) : AgreeRun (evalR D (Copy.memoryWith w) n) (eval D (Copy.memoryWith w) n) :=
  agree_le D w n n (Nat.le_refl n)

/-- A release build of a program, which drops the checks of the marked operations of each body
that the analysis proves whole, runs as the reference interpreter does, to the same outcome
(facts.what-proofs-change): no check it drops ever fails. -/
theorem Program.runRelease_eq (p : Program) (fuel : Nat) (input : String) :
    p.runRelease fuel input = p.runCopy fuel input := by
  unfold Program.runRelease Program.runCopy Program.run
  split
  · rename_i h
    exact congrArg Outcome.leaveBody
      (agree p.decls .leftToRight fuel _ 0 .top p.main [] _ h rfl (Facts.top_holds _)).1
  · rfl

end Stilt
