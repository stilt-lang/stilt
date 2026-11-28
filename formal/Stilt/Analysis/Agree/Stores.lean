import Stilt.Analysis.Agree.Scopes

/-!
# Stores through an index, and list literals

A store `xs[i] = v` keeps its list's length and its other bindings (facts.writes-through-calls):
the index, then the value, then the store (facts.analysis-order), checked against the length
current after the value. A marked one with its check of `bounds` dropped agrees where the
analysis proves the index in range (facts.proved-indexes). A list literal's length is the number
of its elements (facts.bindings-and-assignments).
-/

namespace Stilt

variable {runR run : Expr → Eval Copy.State Value}

/-- A store in range of a list keeps every term but the value given. -/
theorem nu_store {fr : Copy.Frame} {x : Name} {u₀ u u₁ : Value} {k : Int} {st : List Value}
    {v : Value} (hl : fr.lookup x = some u₀) (hs : u₀.set [.index k] u = .ok u₁) {t : Term}
    (ht : (!t.isRes) = true) : Copy.Frame.nu (assocSet fr x u₁) st v t = fr.nu st v t := by
  have hx : (fr.lookup x).isSome = true := by simp [hl]
  have hlen : u₁.intOr = u₀.intOr ∧ u₁.lenOr = u₀.lenOr := by
    cases u₀ <;> simp only [Value.set] at hs <;> try cases hs
    rename_i vs
    split at hs
    · simp only [Functor.map, Except.map, Except.ok.injEq] at hs
      subst hs
      simp [Value.intOr, Value.lenOr]
    · cases hs
  cases t with
  | res | reslen => simp [Term.isRes] at ht
  | val y | len y =>
    by_cases hy : y = x
    · subst hy
      simp [Copy.Frame.nu, lookup_assocSet_self _ _ _ hx, hl, hlen.1, hlen.2]
    · simp [Copy.Frame.nu, lookup_assocSet_ne _ _ hy]
  | zero | opnd _ | opndLen _ => rfl

theorem Facts.Holds.noResWithin {F : Facts} {ν ν' : Valuation} {d : Nat} (h : F.Holds ν)
    (hk : ∀ t, (!t.isRes) = true → t.below d = true → ν' t = ν t) : (F.noRes.within d).Holds ν' := by
  refine ⟨fun e he => ?_, fun t ht => ?_⟩
  · simp only [Facts.within, Facts.noRes, Facts.restrict, List.mem_filter, Bool.and_eq_true] at he
    obtain ⟨⟨he, h1, h2⟩, h3, h4⟩ := he
    have := h.1 e he
    simp only [Diff.Holds] at this ⊢
    rw [hk _ h1 h3, hk _ h2 h4]; exact this
  · simp only [Facts.within, Facts.noRes, Facts.restrict, List.mem_filter] at ht
    obtain ⟨⟨ht, h1⟩, h2⟩ := ht
    rw [hk _ h1 h2]; exact h.2 t ht

/-- The step of a store, once the index and the value met their facts: `storeRes` holds. -/
theorem storeStep_sat (w : WriteBack) {d : Nat} {ri rv : Res} {x : Name} {k : Int} {u : Value}
    {st : List Value} {fr : Copy.Frame} {wd : World} (hd : st.length = d)
    (hu : rv.post.Holds (fr.nu (st ++ [.int k]) u)) :
    ((Eval.update fun s => (Copy.memoryWith w).write s x [.index k] u) >>= fun _ =>
        (Pure.pure Value.unit : Eval Copy.State Value)) (fr, wd) |>.Sat ((storeRes d ri rv).Done st)
      (fun s => (storeRes d ri rv).brk.Holds (s.1.nu st .unit))
      (fun s => (storeRes d ri rv).cont.Holds (s.1.nu st .unit)) := by
  simp only [Bind.bind, Eval.bind, Eval.update]
  cases hl : fr.lookup x with
  | none => simp [Copy.memoryWith, Frames.withWorld, Copy.frames, Copy.write, hl, Outcome.bind, Outcome.fault, Functor.map, Except.map, Outcome.Sat]
  | some u₀ =>
    cases hs : u₀.set [.index k] u with
    | error f =>
      simp only [Copy.memoryWith, Frames.withWorld, Copy.frames, Copy.write, hl, hs, Functor.map, Except.map]
      cases f <;> trivial
    | ok u₁ =>
      have hw : (Copy.memoryWith w).write (fr, wd) x [.index k] u = .ok (assocSet fr x u₁, wd) := by
        simp [Copy.memoryWith, Frames.withWorld, Copy.frames, Copy.write, hl, hs, Functor.map, Except.map]
      rw [hw]
      have h : (rv.post.noRes.within d).Holds (Copy.Frame.nu (assocSet fr x u₁) st .unit) :=
        hu.noResWithin fun t h1 h2 => by
          rw [nu_store hl hs h1, Copy.Frame.nu_noRes h1 (v := .unit) (v' := u)]
          subst hd
          exact (Copy.Frame.nu_push h2).symm
      exact ⟨h, fun _ => h, fun _ => h⟩

set_option maxHeartbeats 1000000 in
theorem agree_storeParts (w : WriteBack) (ih : AgreeRun runR run) {L : Bool} {d : Nat}
    {F : Facts} {x : Name} {i v : Expr} {st : List Value} {s : Copy.State}
    {wr' : Copy.State → Path → Value → Except Fault Copy.State}
    (hok : (an L d F i).ok = true ∧ (an L (d + 1) ((an L d F i).post.push d) v).ok = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit))
    (hwr : ∀ s k u, (an L (d + 1) ((an L d F i).post.push d) v).post.Holds
      (s.1.nu (st ++ [.int k]) u) → wr' s [.index k] u = (Copy.memoryWith w).write s x [.index k] u) :
    (storeRes d (an L d F i) (an L (d + 1) ((an L d F i).post.push d) v)).Agrees st
      (do let p ← Eval.path runR [.index i]; let u ← runR v
          Eval.update fun s => wr' s p u
          Pure.pure .unit)
      (Eval.assign (Copy.memoryWith w) run x [.index i] v) s := by
  unfold Eval.assign
  refine Eval.Agree.bind (P := fun p s' => ∃ k, p = [.index k] ∧
      (an L d F i).post.Holds (s'.1.nu st (.int k)))
    (B := fun s => (an L d F i).brk.Holds (s.1.nu st .unit))
    (C := fun s => (an L d F i).cont.Holds (s.1.nu st .unit)) ?_
    (fun _ h => Facts.holds_join (.inl h)) (fun _ h => Facts.holds_join (.inl h)) fun p s₁ hp => ?_
  · refine (ih L d F i st s hok.1 hd hF).asInt.bind (fun _ h => h) (fun _ h => h) fun k s₁ hk => ?_
    exact Eval.Agree.bind (P := fun p s' => p = [] ∧ s' = s₁) (Eval.Agree.pure ⟨rfl, rfl⟩)
      (fun _ h => h) (fun _ h => h) fun p s' hp => by
        obtain ⟨rfl, rfl⟩ := hp
        exact Eval.Agree.pure ⟨k, rfl, hk.1⟩
  · obtain ⟨k, rfl, hk⟩ := hp
    refine (ih L (d + 1) _ v (st ++ [.int k]) s₁ hok.2 (by simp [hd])
      (by subst hd; exact hk.push)).bind
      (fun _ h => Facts.holds_join (.inr (by subst hd; exact h.within)))
      (fun _ h => Facts.holds_join (.inr (by subst hd; exact h.within))) fun u s₂ hu => ?_
    have heq := hwr s₂ k u hu.1
    refine ⟨by simp only [Bind.bind, Eval.bind, Eval.update, heq], ?_⟩
    obtain ⟨fr, wd⟩ := s₂
    exact storeStep_sat w hd hu.1

theorem agree_store (w : WriteBack) (ih : AgreeRun runR run) {L : Bool} {d : Nat}
    {F : Facts} {x : Name} {i v : Expr} {st : List Value} {s : Copy.State}
    (hok : (an L d F (.assign ⟨x, [.index i]⟩ v)).ok = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.assign ⟨x, [.index i]⟩ v)).Agrees st
      (Eval.assign (Copy.memoryWith w) runR x [.index i] v)
      (Eval.assign (Copy.memoryWith w) run x [.index i] v) s := by
  simp only [an, storeRes, Bool.and_eq_true] at hok
  simp only [an]
  exact agree_storeParts w ih hok hd hF fun _ _ _ _ => rfl

/-- A marked store, its check of `bounds` dropped: proved, it is the store that keeps it
(facts.proved-indexes). -/
theorem agree_provedStore (w : WriteBack) (ih : AgreeRun runR run) {L : Bool} {d : Nat}
    {F : Facts} {ks : List PanicKind} {x : Name} {i v : Expr} {st : List Value} {s : Copy.State}
    (hok : (an L d F (.form (.proved ks) (.assign ⟨x, [.index i]⟩ v))).ok = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.form (.proved ks) (.assign ⟨x, [.index i]⟩ v))).Agrees st
      (do let p ← Eval.path runR [.index i]; let u ← runR v
          Eval.update fun s => Eval.dropped ks ((Copy.memoryWith w).write s x p u)
          Pure.pure .unit)
      (Eval.assign (Copy.memoryWith w) run x [.index i] v) s := by
  simp only [an, storeRes, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  simp only [an]
  refine agree_storeParts w ih hok.1 hd hF fun s₂ k u hu => Eval.dropped_eq fun p hp => ?_
  obtain ⟨rfl, hin⟩ := hok.2 p hp
  have hk := hu.indexOk rfl hin
  obtain ⟨fr, wd⟩ := s₂
  have h1 : fr.nu (st ++ [.int k]) u (.opnd d) = k := by
    subst hd; simpa [Value.intOr] using (Copy.Frame.nu_push_opnd (fr := fr) (st := st) (v := u)
      (u := .int k))
  rw [h1] at hk
  simp only [Copy.memoryWith, Frames.withWorld, Copy.frames, Copy.write]
  cases hl : fr.lookup x with
  | none => simp [Copy.Frame.nu, hl, Value.lenOr] at hk; omega
  | some u₀ =>
    have hne := set_index_ok (w := u) (by simpa [Copy.Frame.nu, hl] using hk)
    intro he
    cases hs : u₀.set [.index k] u with
    | ok _ => simp [hs, Functor.map, Except.map] at he
    | error f => simp [hs, Functor.map, Except.map] at he; subst he; exact hne hs

/-- A list literal: its length the number of its elements (facts.bindings-and-assignments). -/
theorem agree_listLit (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts} {τ : Ty}
    {es : List Expr} {st : List Value} {s : Copy.State} (hok : (an L d F (.list τ es)).ok = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.list τ es)).Agrees st (do let vs ← Eval.list runR es; Pure.pure (Value.list vs))
      (do let vs ← Eval.list run es; Pure.pure (Value.list vs)) s := by
  simp only [an, listRes] at hok ⊢
  refine (agree_list ih es L d F st s hok hd hF).bind (fun _ h => h) (fun _ h => h)
    fun vs s₁ hvs => Eval.Agree.pure ?_
  have h : ((((anOps L d F es).post.noRes.insert ⟨.reslen, .zero, es.length⟩).insert
      ⟨.zero, .reslen, -es.length⟩).tidy L).Holds (s₁.1.nu (st ++ vs) (.list vs)) :=
    ((hvs.2.noRes.insert (by simp [Diff.Holds, Copy.Frame.nu, Value.lenOr, hvs.1])).insert
      (by simp [Diff.Holds, Copy.Frame.nu, Value.lenOr, hvs.1])).tidy rfl L
  have h' := h.withinAppend
  rw [hd] at h'
  exact ⟨h', fun _ => h', fun _ => h'⟩

end Stilt
