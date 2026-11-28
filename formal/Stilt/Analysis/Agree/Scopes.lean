import Stilt.Analysis.Agree.Flow

/-!
# Bindings, assignments and stores

The release run agrees with the run that keeps every check, and meets the analysis, on `let`
and `var` (their binding's terms the value's, facts.bindings-and-assignments, and dropped where
the scope ends), on an assignment to a binding, and on a store through `xs[i]`, which keeps the
list's length (facts.writes-through-calls), marked ones with their check of `bounds` dropped
where the analysis proves it (facts.proved-indexes).
-/

namespace Stilt

variable {runR run : Expr → Eval Copy.State Value}

theorem bindInit_copy (w : WriteBack) (s : Copy.State) (x : Name) (init : Expr) (v : Value) :
    (Copy.memoryWith w).bindInit s x init v = ((x, v) :: s.1, s.2) := by
  cases init <;> rfl

theorem Frame.Keeps.cons_inv {W L : List Name} {x : Name} {v : Value} {fr fr' : Copy.Frame}
    (h : Frame.Keeps W L ((x, v) :: fr) fr') : ∃ u rest, fr' = (x, u) :: rest := by
  cases h with
  | cons _ _ _ => exact ⟨_, _, rfl⟩

namespace Facts

variable {G : Facts} {st : List Value}

/-- A binding of `x` to the value an expression gave: `x`'s terms are the value's
(facts.bindings-and-assignments). -/
theorem Holds.assignTo {fr : Copy.Frame} {v u : Value} {x : Name} (h : G.Holds (fr.nu st v)) :
    (G.assignTo x).Holds (Copy.Frame.nu ((x, v) :: fr) st u) := by
  unfold Facts.assignTo
  rw [holds_map]
  refine h.restrict fun t ht => ?_
  simp only [bne_iff_ne, ne_eq] at ht
  cases t with
  | res | reslen => simp [Copy.Frame.nu]
  | val y | len y =>
    have : (y == x) = false := by simpa [Term.name?] using ht
    simp [Copy.Frame.nu, List.lookup_cons, this]
  | zero | opnd _ | opndLen _ => rfl

/-- An assignment to `x` of the value an expression gave (facts.bindings-and-assignments). -/
theorem Holds.assignSet {fr : Copy.Frame} {v u : Value} {x : Name} (h : G.Holds (fr.nu st v))
    (hx : (fr.lookup x).isSome = true) :
    (G.assignTo x).Holds (Copy.Frame.nu (assocSet fr x v) st u) := by
  unfold Facts.assignTo
  rw [holds_map]
  refine h.restrict fun t ht => ?_
  simp only [bne_iff_ne, ne_eq] at ht
  cases t with
  | res | reslen => simp [Copy.Frame.nu, lookup_assocSet_self _ _ _ hx]
  | val y | len y =>
    have : y ≠ x := fun e => ht (by simp [Term.name?, e])
    simp [Copy.Frame.nu, lookup_assocSet_ne _ _ this]
  | zero | opnd _ | opndLen _ => rfl

theorem Holds.unbind {fr : Copy.Frame} {v u : Value} {x : Name}
    (h : G.Holds (Copy.Frame.nu ((x, u) :: fr) st v)) : (G.unbind x).Holds (fr.nu st v) :=
  h.restrict fun t ht => by
    simp only [bne_iff_ne, ne_eq] at ht
    exact (Copy.Frame.nu_bind ht).symm

end Facts

/-- A scope's body ends, its binding of `x` gone: what it meets, `scopeRes` says without `x`. -/
theorem Outcome.meets_unbind (w : WriteBack) {x : Name} {v : Value} {fr : Copy.Frame}
    {W L : List Name} {r b : Res} {st : List Value} :
    ∀ {o : Outcome Copy.State Value}, o.Keeps W L (fun _ => True) ((x, v) :: fr) → o.Meets b st →
      (o.unbind (Copy.memoryWith w)).Meets (scopeRes x r b) st
  | .done _ s, ⟨_, k⟩, h => by
    obtain ⟨u, rest, he⟩ := k.cons_inv
    obtain ⟨fr', wd⟩ := s
    simp only at he
    subst he
    exact ⟨h.1.unbind, fun e => (h.2.1 e).unbind, fun e => (h.2.2 e).unbind⟩
  | .jumped .brk s, k, h => by
    obtain ⟨u, rest, he⟩ := Frame.Keeps.cons_inv k
    obtain ⟨fr', wd⟩ := s
    simp only at he
    subst he
    exact Facts.holds_join (.inr h.unbind)
  | .jumped .cont s, k, h => by
    obtain ⟨u, rest, he⟩ := Frame.Keeps.cons_inv k
    obtain ⟨fr', wd⟩ := s
    simp only at he
    subst he
    exact Facts.holds_join (.inr h.unbind)
  | .jumped (.ret _) _, _, _ => trivial
  | .performed _ _ _ _, ⟨_, hk⟩, h => fun w' x' => Outcome.meets_unbind w (hk w' x') (h w' x')
  | .raised _ _, _, _ | .panicked _ _, _, _ | .outOfFuel, _, _ | .stuck, _, _ => trivial

/-- `let x = init` and the rest of its block: the binding's terms the value's, and dropped where
its scope ends (facts.bindings-and-assignments). -/
theorem agree_scope (w : WriteBack) (ih : AgreeRun runR run) (hk : KeepsRun run) {L : Bool}
    {d : Nat} {F : Facts} {x : Name} {init body : Expr} {st : List Value} {s : Copy.State}
    (hok : (scopeRes x (an L d F init) (an L d ((an L d F init).post.assignTo x) body)).ok = true)
    (hd : st.length = d) (hF : F.Holds (s.1.nu st .unit)) :
    (scopeRes x (an L d F init) (an L d ((an L d F init).post.assignTo x) body)).Agrees st
      (do let v ← runR init; Eval.withInit (Copy.memoryWith w) x init v (runR body))
      (do let v ← run init; Eval.withInit (Copy.memoryWith w) x init v (run body)) s := by
  simp only [scopeRes, Bool.and_eq_true] at hok
  refine (ih L d F init st s hok.1 hd hF).bind (fun _ h => Facts.holds_join (.inl h))
    (fun _ h => Facts.holds_join (.inl h)) fun v s₁ hv => ?_
  have hb := ih L d _ body st ((x, v) :: s₁.1, s₁.2) hok.2 hd hv.1.assignTo
  refine ⟨?_, ?_⟩
  · show (runR body _).unbind _ = (run body _).unbind _
    rw [bindInit_copy, hb.1]
  · show ((run body _).unbind _).Meets _ _
    rw [bindInit_copy]
    exact Outcome.meets_unbind w
      (hk body _ _ (List.Subset.refl _) (List.Subset.refl _) ((x, v) :: s₁.1, s₁.2)) hb.2

/-- An assignment to a binding: its terms become the value's (facts.bindings-and-assignments). -/
theorem agree_assign (w : WriteBack) (ih : AgreeRun runR run) {L : Bool} {d : Nat} {F : Facts}
    {x : Name} {v : Expr} {st : List Value} {s : Copy.State}
    (hok : (an L d F (.assign ⟨x, []⟩ v)).ok = true) (hd : st.length = d)
    (hF : F.Holds (s.1.nu st .unit)) :
    (an L d F (.assign ⟨x, []⟩ v)).Agrees st
      (Eval.assign (Copy.memoryWith w) runR x [] v) (Eval.assign (Copy.memoryWith w) run x [] v) s := by
  simp only [an] at hok ⊢
  unfold Eval.assign
  refine Eval.Agree.bind (P := fun p s' => p = [] ∧ s' = s) (Eval.Agree.pure ⟨rfl, rfl⟩)
    (fun _ h => h) (fun _ h => h) fun p s' hp => ?_
  obtain ⟨rfl, rfl⟩ := hp
  refine (ih L d F v st s' hok hd hF).bind (fun _ h => h) (fun _ h => h) fun u s₁ hu => ?_
  refine Eval.Agree.same ?_
  obtain ⟨fr, wd⟩ := s₁
  show ((Eval.update fun s => (Copy.memoryWith w).write s x [] u) >>= fun _ => Pure.pure Value.unit)
    (fr, wd) |>.Sat _ _ _
  simp only [Bind.bind, Eval.bind, Eval.update]
  cases hl : fr.lookup x with
  | none =>
    simp [Copy.memoryWith, Frames.withWorld, Copy.frames, Copy.write, hl, Outcome.bind, Outcome.fault, Functor.map, Except.map, Outcome.Sat]
  | some u₀ =>
    have hx : (fr.lookup x).isSome = true := by simp [hl]
    have hw : (Copy.memoryWith w).write (fr, wd) x [] u = .ok (assocSet fr x u, wd) := by
      simp [Copy.memoryWith, Frames.withWorld, Copy.frames, Copy.write, hl, Value.set, Functor.map, Except.map]
    rw [hw]
    have h := hu.1.assignSet (u := .unit) hx
    exact ⟨h, fun _ => h, fun _ => h⟩

end Stilt
