import Stilt.Analysis.Agree.Ops

/-!
# Operands and operations

`AgreeRun runR run`: wherever the analysis's facts hold and every mark it analyses is proved,
the release run of an expression ends as the run that keeps every check, and meets the facts the
analysis gives it. From it, operands evaluated from left to right agree, each value pushed
before the next (`agree_list`), and so do an operation (`agree_op`), its marked form with the
checks of its mark dropped (`agree_provedOp`), and a list literal (`agree_listLit`).
-/

namespace Stilt

/-- Wherever the facts `F` hold, with `d` values read and not yet used, and every mark the
analysis proves, the release run `runR` agrees with `run` and meets the analysis. -/
def AgreeRun (runR run : Expr → Eval Copy.State Value) : Prop :=
  ∀ (L : Bool) (d : Nat) (F : Facts) (e : Expr) (st : List Value) (s : Copy.State),
    (an L d F e).ok = true → st.length = d → F.Holds (s.1.nu st .unit) →
    Eval.Agree ((an L d F e).Done st) (fun s => (an L d F e).brk.Holds (s.1.nu st .unit))
      (fun s => (an L d F e).cont.Holds (s.1.nu st .unit)) (runR e) (run e) s

/-- The facts after operands pushed `vs`. -/
def Ops.Done (os : Ops) (st : List Value) (n : Nat) (vs : List Value) (s : Copy.State) : Prop :=
  vs.length = n ∧ os.post.Holds (s.1.nu (st ++ vs) .unit)

theorem anOps_lins_length : ∀ (es : List Expr) (L : Bool) (d : Nat) (F : Facts),
    (anOps L d F es).lins.length = es.length
  | [], _, _, _ => rfl
  | _ :: es, L, d, F => by simp [anOps, anOps_lins_length es]

namespace Facts

variable {F : Facts} {ν : Valuation}

theorem Holds.tidy (h : F.Holds ν) (hz : ν .zero = 0) (L : Bool) : (F.tidy L).Holds ν := by
  unfold Facts.tidy
  split
  · exact (h.close hz).onlyBounds
  · exact h.close hz

theorem Holds.withinAppend {fr : Copy.Frame} {st vs : List Value} {v : Value}
    (h : F.Holds (fr.nu (st ++ vs) v)) : (F.within st.length).Holds (fr.nu st v) :=
  h.restrict fun t ht => by
    cases t <;> simp_all [Term.below, Copy.Frame.nu, List.getD_eq_getElem?_getD,
      List.getElem?_append_left]

end Facts

theorem Copy.Frame.nu_append_opnd {fr : Copy.Frame} {st vs : List Value} {v : Value} {i : Nat}
    (hi : i < vs.length) : fr.nu (st ++ vs) v (.opnd (st.length + i)) = vs[i].intOr ∧
      fr.nu (st ++ vs) v (.opndLen (st.length + i)) = vs[i].lenOr := by
  simp [Copy.Frame.nu, List.getD_eq_getElem?_getD, hi]

variable {runR run : Expr → Eval Copy.State Value}

/-- Operands evaluated from left to right agree, and meet the facts of `anOps`. -/
theorem agree_list (ih : AgreeRun runR run) : ∀ (es : List Expr) (L : Bool) (d : Nat) (F : Facts)
    (st : List Value) (s : Copy.State), (anOps L d F es).ok = true → st.length = d →
    F.Holds (s.1.nu st .unit) →
    Eval.Agree ((anOps L d F es).Done st es.length)
      (fun s => (anOps L d F es).brk.Holds (s.1.nu st .unit))
      (fun s => (anOps L d F es).cont.Holds (s.1.nu st .unit)) (Eval.list runR es) (Eval.list run es) s
  | [], _, _, _, _, _, _, _, hF => Eval.Agree.pure ⟨rfl, by simpa [anOps] using hF⟩
  | e :: es, L, d, F, st, s, hok, hd, hF => by
    simp only [anOps, Bool.and_eq_true] at hok ⊢
    simp only [Eval.list]
    refine (ih L d F e st s hok.1 hd hF).bind (fun _ h => Facts.holds_join (.inl h))
      (fun _ h => Facts.holds_join (.inl h)) fun v s₁ hv => ?_
    have hp : ((an L d F e).post.push d).Holds (s₁.1.nu (st ++ [v]) .unit) := by
      subst hd; exact hv.1.push
    refine (agree_list ih es L (d + 1) _ (st ++ [v]) s₁ hok.2 (by simp [hd]) hp).bind
      (fun _ h => Facts.holds_join (.inr (by subst hd; exact h.within)))
      (fun _ h => Facts.holds_join (.inr (by subst hd; exact h.within)))
      fun vs s₂ hvs => Eval.Agree.pure ⟨by simp [hvs.1], by simpa [List.append_assoc] using hvs.2⟩

theorem opRes_ok (L : Bool) (d : Nat) (o : Op) (es : List Expr) (os : Ops) :
    (opRes L d o es os).ok = os.ok := by
  unfold opRes; split <;> rfl

theorem opRes_brk (L : Bool) (d : Nat) (o : Op) (es : List Expr) (os : Ops) :
    (opRes L d o es os).brk = os.brk := by
  unfold opRes; split <;> rfl

theorem opRes_cont (L : Bool) (d : Nat) (o : Op) (es : List Expr) (os : Ops) :
    (opRes L d o es os).cont = os.cont := by
  unfold opRes; split <;> rfl

theorem opRes_compare {L : Bool} {d : Nat} {c : Cmp} {k : IntTy} {es : List Expr} {os : Ops}
    {a b : Option (Term × Int)} (h : os.lins = [a, b]) :
    opRes L d (.compare c k) es os =
      { post := (os.post.noRes.tidy L).within d,
        tt := ((cmpFacts c d os.lins os.post.noRes true).tidy L).within d,
        ff := ((cmpFacts c d os.lins os.post.noRes false).tidy L).within d, brk := os.brk,
        cont := os.cont, ok := os.ok } := by
  unfold opRes; rw [h]

theorem opRes_other {L : Bool} {d : Nat} {o : Op} {es : List Expr} {os : Ops}
    (h : ¬ ∃ c k a b, o = .compare c k ∧ os.lins = [a, b]) :
    opRes L d o es os =
      { post := ((opValFacts o d os.lins os.post.noRes).tidy L).within d,
        tt := ((opValFacts o d os.lins os.post.noRes).tidy L).within d,
        ff := ((opValFacts o d os.lins os.post.noRes).tidy L).within d, brk := os.brk,
        cont := os.cont, lin := linOp o es os.lins, lo := os.post.linAt d (linOf os.lins 0),
        hi := os.post.linAt (d + 1) (linOf os.lins 1), ok := os.ok } := by
  unfold opRes
  split
  · rename_i c k a b hl
    exact absurd ⟨c, k, a, b, rfl, hl⟩ h
  · rfl

/-- What an operation computes from operands that met the facts `G` meets what `opRes` says. -/
theorem opRes_done {L : Bool} {d : Nat} {o : Op} {es : List Expr} {os : Ops} {st vs : List Value}
    {fr : Copy.Frame} {wd wd' : World} {r : Value} (hd : st.length = d)
    (hG : os.post.Holds (fr.nu (st ++ vs) .unit)) (hlen : vs.length = os.lins.length)
    (hrun : o.run vs wd = .ok (r, wd')) : (opRes L d o es os).Done st r (fr, wd') := by
  have hG' : os.post.noRes.Holds (fr.nu (st ++ vs) r) := hG.noRes
  have hz : fr.nu (st ++ vs) r .zero = 0 := rfl
  have hops : ∀ i (h : i < vs.length), fr.nu (st ++ vs) r (.opnd (d + i)) = vs[i].intOr ∧
      fr.nu (st ++ vs) r (.opndLen (d + i)) = vs[i].lenOr := fun i h => by
    subst hd; exact Copy.Frame.nu_append_opnd h
  have back : ∀ H : Facts, H.Holds (fr.nu (st ++ vs) r) → ((H.tidy L).within d).Holds (fr.nu st r) :=
    fun H h => by subst hd; exact (h.tidy hz L).withinAppend
  by_cases hc : ∃ c k a b, o = .compare c k ∧ os.lins = [a, b]
  · obtain ⟨c, k, a, b, rfl, hl⟩ := hc
    rw [opRes_compare hl]
    rw [Op.run_of_ne (fun _ h => by cases h)] at hrun
    cases hap : Op.apply (.compare c k) vs with
    | error _ => rw [hap] at hrun; cases hrun
    | ok r' =>
      rw [hap] at hrun
      simp only [Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      rw [hl] at hlen
      obtain ⟨x, y, rfl⟩ := length_two hlen
      obtain ⟨a', b', rfl, rfl, hv⟩ := compare_apply hap
      have ha := (hops 0 (by simp)).1
      have hb := (hops 1 (by simp)).1
      simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ, Value.intOr] at ha hb
      refine ⟨back _ hG', fun ht => ?_, fun hf => ?_⟩
      · rw [hv] at ht
        exact back _ (cmpFacts_holds hG' hz ha hb (by simpa using ht))
      · rw [hv] at hf
        exact back _ (cmpFacts_holds hG' hz ha hb (by simpa using hf))
  · rw [opRes_other hc]
    have hH : (opValFacts o d os.lins os.post.noRes).Holds (fr.nu (st ++ vs) r) := by
      by_cases hw : ∃ k, o = .world k
      · obtain ⟨k, rfl⟩ := hw
        simpa [opValFacts] using hG'
      · rw [Op.run_of_ne (fun k h => hw ⟨k, h⟩)] at hrun
        cases hap : o.apply vs with
        | error _ => rw [hap] at hrun; cases hrun
        | ok r' =>
          rw [hap] at hrun
          simp only [Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact opValFacts_holds hG' hz hlen hap rfl rfl hops
    have := back _ hH
    exact ⟨this, fun _ => this, fun _ => this⟩

/-- A fault whose kind of panic a dropped check doesn't name is as it was. -/
theorem Eval.dropped_eq {α : Type} {ks : List PanicKind} {x : Except Fault α}
    (h : ∀ k ∈ ks, x ≠ .error (.panic k)) : Eval.dropped ks x = x := by
  cases x with
  | ok _ => rfl
  | error f =>
    cases f with
    | stuck => rfl
    | panic k =>
      simp only [Eval.dropped]
      split
      · rename_i hk; exact absurd rfl (h k hk)
      · rfl

/-- The outcome of a step on the world in copy-in, copy-out. -/
theorem Eval.world_copy (w : WriteBack) (f : World → Except Fault (Value × World)) (fr : Copy.Frame)
    (wd : World) : Eval.world (Copy.memoryWith w) f (fr, wd) =
      match f wd with
      | .ok (a, x) => .done a (fr, x)
      | .error e => Outcome.fault e (fr, wd) := by
  cases h : f wd with
  | ok p => obtain ⟨a, x⟩ := p; exact Eval.world_ok h
  | error e => exact Eval.world_error h

theorem Outcome.sat_fault {α : Type} {P : α → Copy.State → Prop} {B C : Copy.State → Prop}
    (e : Fault) (s : Copy.State) : (Outcome.fault e s : Outcome Copy.State α).Sat P B C := by
  cases e <;> trivial

/-- An operation's step on the world, once its operands met the facts of `anOps`, meets what
`opRes` says. -/
theorem opStep_sat (w : WriteBack) {L : Bool} {d : Nat} {o : Op} {es : List Expr} {os : Ops}
    {st vs : List Value} {fr : Copy.Frame} {wd : World} (hd : st.length = d)
    (hvs : os.Done st es.length vs (fr, wd)) (hlen : os.lins.length = es.length) :
    (Eval.world (Copy.memoryWith w) (o.run vs) (fr, wd)).Sat ((opRes L d o es os).Done st)
      (fun s => (opRes L d o es os).brk.Holds (s.1.nu st .unit))
      (fun s => (opRes L d o es os).cont.Holds (s.1.nu st .unit)) := by
  rw [Eval.world_copy]
  cases hrun : o.run vs wd with
  | error e => exact Outcome.sat_fault e _
  | ok p =>
    obtain ⟨r, wd'⟩ := p
    exact opRes_done hd hvs.2 (by rw [hvs.1, hlen]) hrun

/-- An operation agrees once its operands do. -/
theorem agree_op (w : WriteBack) (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts} {o : Op}
    {es : List Expr} {st : List Value} {s : Copy.State}
    (hok : (anOps L d F es).ok = true) (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    Eval.Agree ((opRes L d o es (anOps L d F es)).Done st)
      (fun s => (opRes L d o es (anOps L d F es)).brk.Holds (s.1.nu st .unit))
      (fun s => (opRes L d o es (anOps L d F es)).cont.Holds (s.1.nu st .unit))
      (Eval.list runR es >>= fun vs => Eval.world (Copy.memoryWith w) (o.run vs))
      (Eval.list run es >>= fun vs => Eval.world (Copy.memoryWith w) (o.run vs)) s :=
  (agree_list ih es L d F st s hok hd hF).bind (fun _ h => by rwa [opRes_brk])
    (fun _ h => by rwa [opRes_cont]) fun vs s₁ hvs => Eval.Agree.same (by
      obtain ⟨fr, wd⟩ := s₁
      exact opStep_sat w hd hvs (anOps_lins_length es L d F))

/-- A marked operation, the checks of its mark dropped: proved, it is the operation that keeps
them (facts.proved-divisions, facts.proved-overflow). -/
theorem agree_provedOp (w : WriteBack) (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts}
    {ks : List PanicKind} {o : Op} {es : List Expr} {st : List Value} {s : Copy.State}
    (hok : (anOps L d F es).ok = true)
    (hv : ks.all (verifyOp o d (anOps L d F es).lins (anOps L d F es).post.noRes) = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    Eval.Agree ((opRes L d o es (anOps L d F es)).Done st)
      (fun s => (opRes L d o es (anOps L d F es)).brk.Holds (s.1.nu st .unit))
      (fun s => (opRes L d o es (anOps L d F es)).cont.Holds (s.1.nu st .unit))
      (Eval.list runR es >>= fun vs => Eval.world (Copy.memoryWith w) fun x => Eval.dropped ks (o.run vs x))
      (Eval.list run es >>= fun vs => Eval.world (Copy.memoryWith w) (o.run vs)) s := by
  refine (agree_list ih es L d F st s hok hd hF).bind (fun _ h => by rwa [opRes_brk])
    (fun _ h => by rwa [opRes_cont]) fun vs s₁ hvs => ?_
  obtain ⟨fr, wd⟩ := s₁
  have heq : (fun x => Eval.dropped ks (o.run vs x)) = o.run vs := by
    funext x
    refine Eval.dropped_eq fun p hp => ?_
    have hvp := List.all_eq_true.1 hv p hp
    by_cases hw : ∃ k, o = .world k
    · obtain ⟨k, rfl⟩ := hw
      simp [verifyOp] at hvp
    · rw [Op.run_of_ne (fun k h => hw ⟨k, h⟩)]
      have hz : fr.nu (st ++ vs) .unit .zero = 0 := rfl
      have := verifyOp_sound hvp hvs.2.noRes hz (by rw [hvs.1, anOps_lins_length])
        (fun i h => by subst hd; exact (Copy.Frame.nu_append_opnd h).1)
      intro he
      cases hap : o.apply vs with
      | ok _ => rw [hap] at he; cases he
      | error f => rw [hap] at he; cases he; exact this hap
  rw [heq]
  exact Eval.Agree.same (opStep_sat w hd hvs (anOps_lins_length es L d F))

end Stilt
