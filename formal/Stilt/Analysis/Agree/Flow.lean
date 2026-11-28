import Stilt.Analysis.Agree.Straight

/-!
# Indexes, blocks, conditions and jumps

The release run agrees with the run that keeps every check, and meets the analysis, on index
reads, marked ones with their check of `bounds` dropped where the analysis proves it
(facts.proved-indexes), field reads, blocks, `if` (facts.joins) and the jumps
(facts.paths-that-leave).
-/

namespace Stilt

variable {runR run : Expr → Eval Copy.State Value}

theorem Copy.Frame.nu_push2 {fr : Copy.Frame} {st : List Value} {v u r : Value} :
    fr.nu (st ++ [v] ++ [u]) r (.opnd (st.length + 1)) = u.intOr ∧
      fr.nu (st ++ [v] ++ [u]) r (.opndLen st.length) = v.lenOr := by
  simp [Copy.Frame.nu, List.getD_eq_getElem?_getD]

/-- What an index read's value meets, from its index's facts. -/
theorem indexRes_done {d : Nat} {ra ri : Res} {st : List Value} {v u : Value} {k : Int}
    {s : Copy.State} (hd : st.length = d) (hk : ri.post.Holds (s.1.nu (st ++ [v]) (.int k))) :
    (indexRes d ra ri).Done st u s := by
  have h : (ri.post.noRes.within d).Holds (s.1.nu st u) := by subst hd; exact hk.noRes.within
  exact ⟨h, fun _ => h, fun _ => h⟩

theorem agree_indexParts (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts} {a i : Expr}
    {st : List Value} {s : Copy.State} {f' f : Value → Int → Eval Copy.State Value}
    (hok : (an L d F a).ok = true ∧ (an L (d + 1) ((an L d F a).post.push d) i).ok = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit))
    (hf : ∀ v k s₂, (an L (d + 1) ((an L d F a).post.push d) i).post.Holds
      (s₂.1.nu (st ++ [v]) (.int k)) →
      (indexRes d (an L d F a) (an L (d + 1) ((an L d F a).post.push d) i)).Agrees st (f' v k) (f v k) s₂) :
    (indexRes d (an L d F a) (an L (d + 1) ((an L d F a).post.push d) i)).Agrees st
      (do let v ← runR a; let k ← runR i >>= Eval.asInt; f' v k)
      (do let v ← run a; let k ← run i >>= Eval.asInt; f v k) s := by
  refine (ih L d F a st s hok.1 hd hF).bind (fun _ h => Facts.holds_join (.inl h))
    (fun _ h => Facts.holds_join (.inl h)) fun v s₁ hv => ?_
  have hp : ((an L d F a).post.push d).Holds (s₁.1.nu (st ++ [v]) .unit) := by
    subst hd; exact hv.1.push
  exact (ih L (d + 1) _ i (st ++ [v]) s₁ hok.2 (by simp [hd]) hp).asInt.bind
    (fun _ h => Facts.holds_join (.inr (by subst hd; exact h.within)))
    (fun _ h => Facts.holds_join (.inr (by subst hd; exact h.within)))
    fun k s₂ hk => hf v k s₂ hk.1

theorem agree_index (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts} {a i : Expr}
    {st : List Value} {s : Copy.State} (hok : (an L d F (.index a i)).ok = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.index a i)).Agrees st
      (do let v ← runR a; let k ← runR i >>= Eval.asInt; Eval.ofExcept (v.get [.index k]))
      (do let v ← run a; let k ← run i >>= Eval.asInt; Eval.ofExcept (v.get [.index k])) s := by
  simp only [an, indexRes, Bool.and_eq_true] at hok
  simp only [an]
  exact agree_indexParts ih hok hd hF fun v k s₂ hk =>
    Eval.Agree.ofExcept fun u _ => indexRes_done hd hk

/-- A marked index read, its check of `bounds` dropped: proved, it is the read that keeps it
(facts.proved-indexes, facts.analysis-order). -/
theorem agree_provedIndex (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts}
    {ks : List PanicKind} {a i : Expr} {st : List Value} {s : Copy.State}
    (hok : (an L d F (.form (.proved ks) (.index a i))).ok = true) (hd : st.length = d)
    (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.form (.proved ks) (.index a i))).Agrees st
      (do let v ← runR a; let k ← runR i >>= Eval.asInt;
          Eval.ofExcept (Eval.dropped ks (v.get [.index k])))
      (do let v ← run a; let k ← run i >>= Eval.asInt; Eval.ofExcept (v.get [.index k])) s := by
  simp only [an, indexRes, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  simp only [an]
  refine agree_indexParts ih hok.1 hd hF fun v k s₂ hk => ?_
  rw [Eval.dropped_eq]
  · exact Eval.Agree.ofExcept fun u _ => indexRes_done hd hk
  · intro p hp
    obtain ⟨rfl, hprov⟩ := hok.2 p hp
    unfold indexProved at hprov
    split at hprov
    · have hk' := (hk.push (u := .unit)).indexOk rfl (by simpa [hd] using hprov)
      obtain ⟨h1, h2⟩ := Copy.Frame.nu_push2 (fr := s₂.1) (st := st) (v := v) (u := .int k) (r := .unit)
      rw [hd] at h1 h2
      rw [h1, h2] at hk'
      exact get_index_ok (by simpa [Value.intOr] using hk')
    · cases hprov

theorem agree_field (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts} {e : Expr} {f : Name}
    {st : List Value} {s : Copy.State} (hok : (an L d F (.field e f)).ok = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.field e f)).Agrees st (do let v ← runR e; Eval.ofExcept (v.get [.field f]))
      (do let v ← run e; Eval.ofExcept (v.get [.field f])) s := by
  simp only [an] at hok ⊢
  exact (ih L d F e st s hok hd hF).bind (fun _ h => h) (fun _ h => h) fun v s₁ hv =>
    Eval.Agree.ofExcept fun u _ => ⟨hv.1.noRes, fun _ => hv.1.noRes, fun _ => hv.1.noRes⟩

theorem agree_seq (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts} {a b : Expr}
    {st : List Value} {s : Copy.State} (hok : (an L d F (.seq a b)).ok = true) (hd : st.length = d)
    (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.seq a b)).Agrees st (do let _ ← runR a; runR b) (do let _ ← run a; run b) s := by
  simp only [an, seqRes, Bool.and_eq_true] at hok ⊢
  exact (ih L d F a st s hok.1 hd hF).bind (fun _ h => Facts.holds_join (.inl h))
    (fun _ h => Facts.holds_join (.inl h)) fun v s₁ hv =>
      (ih L d _ b st s₁ hok.2 hd hv.1.noRes).mono (fun _ _ h => h)
        (fun _ h => Facts.holds_join (.inr h)) (fun _ h => Facts.holds_join (.inr h))

/-- An `if`: each branch from its condition's facts, and their join after (facts.conditions,
facts.joins). -/
theorem agree_if (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts} {c a b : Expr}
    {τ : Ty} {st : List Value} {s : Copy.State} (hok : (an L d F (.if c τ a b)).ok = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.if c τ a b)).Agrees st
      (do let v ← runR c >>= Eval.asBool; if v then runR a else runR b)
      (do let v ← run c >>= Eval.asBool; if v then run a else run b) s := by
  simp only [an, ifRes, Bool.and_eq_true] at hok ⊢
  refine (ih L d F c st s hok.1.1 hd hF).asBool.bind (fun _ h => Facts.holds_join (.inl h))
    (fun _ h => Facts.holds_join (.inl h)) fun v s₁ hv => ?_
  cases v
  · exact (ih L d _ b st s₁ hok.2 hd (hv.2.2 rfl).noRes).mono
      (fun _ _ h => ⟨Facts.holds_join (.inr h.1), fun e => Facts.holds_join (.inr (h.2.1 e)),
        fun e => Facts.holds_join (.inr (h.2.2 e))⟩)
      (fun _ h => Facts.holds_join (.inr (Facts.holds_join (.inr h))))
      (fun _ h => Facts.holds_join (.inr (Facts.holds_join (.inr h))))
  · exact (ih L d _ a st s₁ hok.1.2 hd (hv.2.1 rfl).noRes).mono
      (fun _ _ h => ⟨Facts.holds_join (.inl h.1), fun e => Facts.holds_join (.inl (h.2.1 e)),
        fun e => Facts.holds_join (.inl (h.2.2 e))⟩)
      (fun _ h => Facts.holds_join (.inr (Facts.holds_join (.inl h))))
      (fun _ h => Facts.holds_join (.inr (Facts.holds_join (.inl h))))

theorem agree_break {L : Bool} {d : Nat} {F : Facts} {st : List Value} {s : Copy.State}
    (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F .break).Agrees st (Eval.jump .brk) (Eval.jump .brk) s :=
  Eval.Agree.same (by simp only [an]; exact hF.noRes)

theorem agree_continue {L : Bool} {d : Nat} {F : Facts} {st : List Value} {s : Copy.State}
    (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F .continue).Agrees st (Eval.jump .cont) (Eval.jump .cont) s :=
  Eval.Agree.same (by simp only [an]; exact hF.noRes)

theorem agree_return (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts} {e : Expr}
    {st : List Value} {s : Copy.State} (hok : (an L d F (.return e)).ok = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.return e)).Agrees st (do let v ← runR e; Eval.jump (.ret v))
      (do let v ← run e; Eval.jump (.ret v)) s := by
  simp only [an, Res.leaves] at hok ⊢
  exact (ih L d F e st s hok hd hF).bind (fun _ h => h) (fun _ h => h) fun _ _ _ =>
    Eval.Agree.same trivial

theorem agree_raise (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts} {e : Expr}
    {st : List Value} {s : Copy.State} (hok : (an L d F (.raise e)).ok = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.raise e)).Agrees st (do let v ← runR e; Eval.throw v)
      (do let v ← run e; Eval.throw v) s := by
  simp only [an, Res.leaves] at hok ⊢
  exact (ih L d F e st s hok hd hF).bind (fun _ h => h) (fun _ h => h) fun _ _ _ =>
    Eval.Agree.same trivial

end Stilt
