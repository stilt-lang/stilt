import Stilt.Views.Relation

/-!
# Steps that agree

The combinators of the monad of `Stilt.Eval` keep `Agree`: two steps that
agree, followed by two that agree from every pair of outcomes that the first
relates, agree. Each lemma reads the two runs from a window state and a copy
state.
-/

namespace Stilt.Views

variable {σ α β α' β' : Type}

namespace Agree

theorem mono {Q Q' : σ → σ → α → β → Prop} {o : Outcome σ α}
    {o' : Outcome σ β} (h : Agree Q o o') (hQ : ∀ sw sc a b, Q sw sc a b → Q' sw sc a b) :
    Agree Q' o o' :=
  Outcome.Rel.mono h
    ⟨fun a sw b sc => hQ sw sc a b, fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h,
      fun _ _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩

theorem bind {Q : σ → σ → α → β → Prop} {Q' : σ → σ → α' → β' → Prop}
    {m : Eval σ α} {m' : Eval σ β} {f : α → Eval σ α'}
    {g : β → Eval σ β'} {sw sc : σ} (h : Agree Q (m sw) (m' sc))
    (hf : ∀ sw' sc' a b, Q sw' sc' a b → Agree Q' (f a sw') (g b sc')) :
    Agree Q' ((m >>= f) sw) ((m' >>= g) sc) :=
  Outcome.Rel.bind h ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h,
    fun _ _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩
    fun a sw' b sc' hq => hf sw' sc' a b hq

theorem pure {Q : σ → σ → α → β → Prop} {a : α} {b : β} {sw sc : σ}
    (h : Q sw sc a b) :
    Agree Q ((Pure.pure a : Eval σ α) sw) ((Pure.pure b : Eval σ β) sc) :=
  h

theorem fault {Q : σ → σ → α → β → Prop} (f : Fault) {sw sc : σ} :
    Agree Q (Outcome.fault f sw) (Outcome.fault f sc) := by
  cases f <;> simp [Outcome.fault, Agree, Agree.relation, Outcome.Rel]

theorem stuck {Q : σ → σ → α → β → Prop} : Agree Q (.stuck : Outcome σ α) (.stuck : Outcome σ β) :=
  trivial

theorem fail {Q : σ → σ → α → β → Prop} (f : Fault) {sw sc : σ} :
    Agree Q (Eval.fail f sw) (Eval.fail f sc) :=
  fault f

theorem ofExcept {Q : σ → σ → α → β → Prop} {x : Except Fault α} {y : Except Fault β}
    {sw sc : σ} (h : ExceptAgree (Q sw sc) x y) :
    Agree Q (Eval.ofExcept x sw) (Eval.ofExcept y sc) := by
  cases x <;> cases y <;> simp only [ExceptAgree] at h
  · subst h
    exact fault _
  · exact h

theorem inspect {Q : σ → σ → α → β → Prop} {f : σ → Except Fault α}
    {g : σ → Except Fault β} {sw sc : σ} (h : ExceptAgree (Q sw sc) (f sw) (g sc)) :
    Agree Q (Eval.inspect f sw) (Eval.inspect g sc) :=
  ofExcept h

theorem update {Q : σ → σ → Unit → Unit → Prop} {f g : σ → Except Fault σ}
    {sw sc : σ} (h : ExceptAgree (fun s₁ s₂ => Q s₁ s₂ () ()) (f sw) (g sc)) :
    Agree Q (Eval.update f sw) (Eval.update g sc) := by
  unfold Eval.update
  revert h
  cases f sw <;> cases g sc <;> intro h <;> simp only [ExceptAgree] at h <;>
    first | (subst h; exact fault _) | exact h.elim | exact h

/-- Two loops whose steps keep an invariant keep it. -/
theorem each {I : VState → VState → Prop} {fw fc : β → Eval VState Unit}
    (h : ∀ b sw sc, I sw sc → Agree (fun sw' sc' _ _ => I sw' sc') (fw b sw) (fc b sc)) :
    ∀ (bs : List β) (sw sc : VState), I sw sc →
      Agree (fun sw' sc' _ _ => I sw' sc') (Run.each fw bs sw) (Run.each fc bs sc)
  | [], _, _, hI => hI
  | b :: bs, sw, sc, hI => bind (h b sw sc hI) fun _ _ _ _ hI' => each h bs _ _ hI'

theorem discard {Q : VState → VState → α → β → Prop} {I : VState → VState → Prop}
    {m : Eval VState α} {m' : Eval VState β} {sw sc : VState} (h : Agree Q (m sw) (m' sc))
    (hQ : ∀ sw sc a b, Q sw sc a b → I sw sc) :
    Agree (fun sw' sc' _ _ => I sw' sc') (Run.discard m sw) (Run.discard m' sc) :=
  bind h fun _ _ _ _ hq => hQ _ _ _ _ hq

end Agree

/-! ## Values -/

namespace Agrees

theorem asVal {Q : VState → VState → Value → Value → Prop} {sw sc : VState} {rw rc : RVal}
    (h : Agrees sw.store rw rc) (hQ : ∀ v, rw = .val v → Q sw sc v v) :
    Agree Q (Run.asVal rw sw) (Run.asVal rc sc) := by
  cases rw <;> cases rc <;> simp only [Agrees] at h
  · subst h
    exact hQ _ rfl
  · exact Agree.stuck

theorem asInt {Q : VState → VState → Int → Int → Prop} {sw sc : VState} {rw rc : RVal}
    (h : Agrees sw.store rw rc) (hQ : ∀ k, Q sw sc k k) :
    Agree Q (Run.asInt rw sw) (Run.asInt rc sc) := by
  cases rw <;> cases rc <;> simp only [Agrees] at h
  · subst h
    rename_i v
    cases v <;> first | exact hQ _ | exact Agree.stuck
  · exact Agree.stuck

theorem asBool {Q : VState → VState → Bool → Bool → Prop} {sw sc : VState} {rw rc : RVal}
    (h : Agrees sw.store rw rc) (hQ : ∀ b, Q sw sc b b) :
    Agree Q (Run.asBool rw sw) (Run.asBool rc sc) := by
  cases rw <;> cases rc <;> simp only [Agrees] at h
  · subst h
    rename_i v
    cases v <;> first | exact hQ _ | exact Agree.stuck
  · exact Agree.stuck

/-- A window that agrees with a copy reads within its source. -/
theorem bounds {store : Store} {ℓ : Nat} {π : Path} {a b : Int} {part : List Value}
    (h : Agrees store (.window ℓ π a b) (.copied part)) :
    ∃ vs, source store ℓ π = .ok (.list vs) ∧ bounded vs.length a b = true ∧
      part = slice vs a b := by
  simp only [Agrees, RVal.part] at h
  split at h
  · rename_i vs _
    split at h
    · cases h
      exact ⟨vs, by assumption, by assumption, rfl⟩
    · cases h
  · cases h

end Agrees

theorem slice_length {vs : List Value} {a b : Int} (h : bounded vs.length a b = true) :
    (slice vs a b).length = (b - a).toNat := by
  simp only [bounded, decide_eq_true_eq] at h
  simp only [slice, List.length_take, List.length_drop]
  omega

/-- A view that agrees with a copy has its length. -/
theorem Agrees.len {store : Store} {rw rc : RVal} (h : Agrees store rw rc) :
    ExceptAgree (· = ·) rw.len rc.len := by
  cases rw <;> cases rc <;> try exact False.elim h
  · exact rfl
  · obtain ⟨vs, -, hb, rfl⟩ := Agrees.bounds h
    show (_ : Int) - _ = ((slice vs _ _).length : Int)
    rw [slice_length hb]
    simp only [bounded, decide_eq_true_eq] at hb
    omega

/-- A view that agrees with a copy reads the same elements. -/
theorem Agrees.elem {store : Store} {rw rc : RVal} (h : Agrees store rw rc) (k : Int) :
    rw.elem store k = rc.elem store k := by
  cases rw <;> cases rc <;> try exact False.elim h
  · rfl
  · unfold RVal.elem
    rw [show (RVal.window _ _ _ _).part store = _ from h]
    rfl

/-- The results of an operation that gives a value of the core calculus. -/
theorem ExceptAgree.lift {P : RVal → RVal → Prop} (x : Except Fault Value)
    (h : ∀ v, P (.val v) (.val v)) : ExceptAgree P (lift x) (lift x) := by
  cases x
  · exact rfl
  · exact h _

/-- Indexing values or views that agree gives the same element. -/
theorem Agrees.index {store : Store} {rw rc : RVal} (h : Agrees store rw rc) (k : Int) :
    ∃ x, rw.index store k = lift x ∧ rc.index store k = lift x := by
  cases rw <;> cases rc <;> try exact False.elim h
  · cases (show _ = _ from h)
    exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, congrArg lift (Agrees.elem (rw := .window _ _ _ _) (rc := .copied _) h k).symm⟩

/-- A view that agrees with a copy copies the same part. -/
theorem Agrees.copy {store : Store} {rw rc : RVal} (h : Agrees store rw rc) :
    ∃ x, rw.copy store = lift x ∧ rc.copy store = lift x := by
  refine ⟨_, rfl, ?_⟩
  cases rw <;> cases rc <;> try exact False.elim h
  · rfl
  · show lift ((Except.ok _ : Except Fault (List Value)).map _) = _
    rw [← show (RVal.window _ _ _ _).part store = _ from h]

theorem slice_slice {vs : List Value} {a b s t : Int} (hab : bounded vs.length a b = true)
    (hst : bounded (b - a).toNat s t = true) :
    slice (slice vs a b) s t = slice vs (a + s) (a + t) := by
  simp only [bounded, decide_eq_true_eq] at hab hst
  simp only [slice, List.drop_take, List.drop_drop, List.take_take]
  congr 2 <;> omega

/-- The parts of views that agree, which a window gives by moving its
offsets (views.making-view and views.functions-of-views). -/
theorem Agrees.sub {store : Store} {rw rc : RVal} (h : Agrees store rw rc) (s t : Int) :
    ExceptAgree (fun a b => Agrees store a b ∧ ∀ S env, rw.Within S env → a.Within S env)
      (rw.sub s t) (rc.sub s t) := by
  cases rw <;> cases rc <;> try exact False.elim h
  · exact rfl
  · rename_i a b _
    obtain ⟨vs, hsrc, hb, rfl⟩ := Agrees.bounds h
    simp only [RVal.sub, slice_length hb]
    split
    · rename_i hst
      refine ⟨?_, fun _ _ hw => hw⟩
      have hb' : bounded vs.length (a + s) (a + t) = true := by
        simp only [bounded, decide_eq_true_eq] at hb hst ⊢
        omega
      simp only [Agrees, RVal.part, hsrc, hb', ite_true, slice_slice hb hst]
    · exact rfl

end Stilt.Views
