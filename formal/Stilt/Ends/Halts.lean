import Stilt.Ends.Steps

/-!
# Runs that halt

A loop whose number of turns its values decide needs more fuel the more turns
it makes, so no bound that the text gives covers every run. `Halts F P s`
says what holds instead: from the state `s`, the runs `F n`, one for each fuel
`n`, reach from some fuel on one outcome, the same with any more fuel, which
isn't running out and whose value meets `P`. The evaluator's steps keep it:
a step that takes no fuel halts when it ends (`Halts.const`), a step that runs
another at a state halts when that one does (`Halts.post`), and a step and what
follows halt when each does from where the other leaves off (`Halts.bind`).
-/

namespace Stilt

/-- From `s`, the runs `F n` reach, with every fuel from some `N` on, one outcome
`o`, which doesn't run out of fuel and whose value meets `P`. -/
def Halts {σ α : Type} (F : Nat → Eval σ α) (P : α → Prop) (s : σ) : Prop :=
  ∃ N o, Outcome.Ends P o ∧ ∀ n, N ≤ n → F n s = o

namespace Halts

variable {σ α β : Type} {P : α → Prop} {Q : β → Prop} {s : σ}

/-- A step that takes no fuel halts where it ends. -/
theorem const {m : Eval σ α} (h : Eval.Ends P m) : Halts (fun _ => m) P s :=
  ⟨0, m s, h s, fun _ _ => rfl⟩

/-- Runs that halt with one more fuel halt. -/
theorem succ {F : Nat → Eval σ α} (h : Halts (fun n => F (n + 1)) P s) : Halts F P s := by
  obtain ⟨N, o, ho, hn⟩ := h
  refine ⟨N + 1, o, ho, fun n hle => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact hn m (by omega)

/-- Runs that halt halt with one more fuel too. -/
theorem shift {F : Nat → Eval σ α} (h : Halts F P s) : Halts (fun n => F (n + 1)) P s := by
  obtain ⟨N, o, ho, hn⟩ := h
  exact ⟨N, o, ho, fun n hle => hn (n + 1) (by omega)⟩

theorem weaken {F : Nat → Eval σ α} {P' : α → Prop} (h : Halts F P s) (hP : ∀ a, P a → P' a) :
    Halts F P' s := by
  obtain ⟨N, o, ho, hn⟩ := h
  refine ⟨N, o, ?_, hn⟩
  cases o <;> simp_all [Outcome.Ends]

/-- A step that runs `F n` at a state `s'` and makes its outcome by `φ`, which keeps
outcomes that end. -/
theorem post {F : Nat → Eval σ α} {G : Nat → Eval σ β} {s' : σ} {φ : Outcome σ α → Outcome σ β}
    (h : Halts F P s') (hG : ∀ n, G n s = φ (F n s')) (hφ : ∀ o, Outcome.Ends P o → Outcome.Ends Q (φ o)) :
    Halts G Q s := by
  obtain ⟨N, o, ho, hn⟩ := h
  exact ⟨N, φ o, hφ o ho, fun n hle => by rw [hG, hn n hle]⟩

/-- A step, then what follows from the value and state it ends with. -/
theorem bind {F : Nat → Eval σ α} {G : Nat → α → Eval σ β} (hF : Halts F P s)
    (hG : ∀ a s', P a → (∃ N, ∀ n, N ≤ n → F n s = .done a s') → Halts (fun n => G n a) Q s') :
    Halts (fun n => F n >>= G n) Q s := by
  obtain ⟨N, o, ho, hn⟩ := hF
  cases o with
  | done a s' =>
    obtain ⟨N', o', ho', hn'⟩ := hG a s' ho ⟨N, hn⟩
    refine ⟨max N N', o', ho', fun n hle => ?_⟩
    show Eval.bind (F n) (G n) s = o'
    unfold Eval.bind Outcome.bind
    rw [hn n (by omega)]
    exact hn' n (by omega)
  | outOfFuel => exact absurd ho id
  | performed => exact absurd ho id
  | raised e s' =>
    refine ⟨N, .raised e s', trivial, fun n hle => ?_⟩
    show Eval.bind (F n) (G n) s = _
    unfold Eval.bind Outcome.bind; rw [hn n hle]
  | jumped j s' =>
    refine ⟨N, .jumped j s', trivial, fun n hle => ?_⟩
    show Eval.bind (F n) (G n) s = _
    unfold Eval.bind Outcome.bind; rw [hn n hle]
  | panicked k s' =>
    refine ⟨N, .panicked k s', trivial, fun n hle => ?_⟩
    show Eval.bind (F n) (G n) s = _
    unfold Eval.bind Outcome.bind; rw [hn n hle]
  | stuck =>
    refine ⟨N, .stuck, trivial, fun n hle => ?_⟩
    show Eval.bind (F n) (G n) s = _
    unfold Eval.bind Outcome.bind; rw [hn n hle]

theorem ite (b : Bool) {F G : Nat → Eval σ α} (hF : Halts F P s) (hG : Halts G P s) :
    Halts (fun n => if b then F n else G n) P s := by
  cases b
  · exact hG
  · exact hF

theorem handle {F : Nat → Eval σ α} {H : Nat → Value → Eval σ α} (hF : Halts F P s)
    (hH : ∀ e s', Halts (fun n => H n e) P s') : Halts (fun n => Eval.handle (F n) (H n)) P s := by
  obtain ⟨N, o, ho, hn⟩ := hF
  cases o with
  | raised e s' =>
    obtain ⟨N', o', ho', hn'⟩ := hH e s'
    refine ⟨max N N', o', ho', fun n hle => ?_⟩
    show Eval.handle (F n) (H n) s = o'
    unfold Eval.handle Outcome.handle
    rw [hn n (by omega)]
    exact hn' n (by omega)
  | performed => exact absurd ho id
  | _ =>
    refine ⟨N, _, ho, fun n hle => ?_⟩
    show Eval.handle (F n) (H n) s = _
    unfold Eval.handle Outcome.handle
    rw [hn n hle]

theorem turn {R : Value → Prop} {F : Nat → Eval σ Value} (h : Halts F R s) :
    Halts (fun n => Eval.turn (F n)) (fun _ => True) s := by
  refine post (φ := fun o => Eval.turn (fun _ => o) s) h (fun n => rfl) fun o ho => ?_
  cases o with
  | jumped j _ => cases j <;> trivial
  | _ => simp_all [Outcome.Ends, Eval.turn, Outcome.turn]

theorem forEach {body : Nat → Value → Eval σ Bool}
    (hb : ∀ v s, Halts (fun n => body n v) (fun _ => True) s) :
    ∀ (vs : List Value) (s : σ), Halts (fun n => Eval.forEach (body n) vs) (fun _ => True) s
  | [], _ => const (Eval.Ends.pure trivial)
  | v :: vs, s => by
    have : (fun n => Eval.forEach (body n) (v :: vs)) =
        fun n => body n v >>= fun b => if b then Eval.forEach (body n) vs else Pure.pure () := by
      funext n; rfl
    rw [this]
    refine bind (hb v s) fun b s' _ _ => ?_
    cases b
    · exact const (Eval.Ends.pure trivial)
    · exact forEach hb vs s'

section

variable (M : Memory σ)

theorem withVar (x : Name) (v : Value) {F : Nat → Eval σ α} (h : Halts F P (M.bind s x v)) :
    Halts (fun n => Eval.withVar M x v (F n)) P s :=
  post (φ := fun o => Eval.withVar M x v (fun _ => o) s) h (fun _ => rfl) fun o ho => by
    cases o <;> simp_all [Outcome.Ends, Eval.withVar, Outcome.unbind]

theorem withInit (x : Name) (init : Expr) (v : Value) {F : Nat → Eval σ α}
    (h : Halts F P (M.bindInit s x init v)) : Halts (fun n => Eval.withInit M x init v (F n)) P s :=
  post (φ := fun o => Eval.withInit M x init v (fun _ => o) s) h (fun _ => rfl) fun o ho => by
    cases o <;> simp_all [Outcome.Ends, Eval.withInit, Outcome.unbind]

theorem withVars {F : Nat → Eval σ α} (h : ∀ s, Halts F P s) :
    ∀ (bs : List (Name × Value)) (s : σ), Halts (fun n => Eval.withVars M bs (F n)) P s
  | [], s' => h s'
  | (x, v) :: bs, _ => withVar M x v (withVars h bs _)

/-- A call as code or a `with` makes it halts when the call does: a call that
can't be made is stuck. -/
theorem callAs (D : Decls) (run : Nat → Expr → Eval σ Value) (control : Bool) (f : Value)
    (passed : List Passed) {R : Value → Prop}
    (h : Halts (fun n => Eval.call D M (run n) f passed) R s) :
    Halts (fun n => Eval.callAs D M (run n) control f passed) R s := by
  unfold Eval.callAs
  split
  · exact const (Eval.Ends.fail _)
  · exact h

/-- A `with` whose block halts halts: an outcome that ends is no performance,
which the `with` passes on as it is. -/
theorem handleWith (E : Name) (c : Bool) (hv : Value) {R : Value → Prop} {F : Nat → Eval σ Value}
    {calls : Nat → Value → Value → Eval σ Value} (h : Halts F R s) :
    Halts (fun n => Eval.handleWith M E c hv (calls n) (F n)) R s := by
  obtain ⟨N, o, ho, hn⟩ := h
  refine ⟨N, o, ho, fun n hle => ?_⟩
  show (F n s).handleWith M E c hv _ = o
  rw [hn n hle]
  cases o <;> first | rfl | exact absurd ho id

/-- A `with` that lets cells go halts where its block does (shared.when). -/
theorem letGo {R : Value → Prop} {F : Nat → Eval σ Value} (h : Halts F R s) :
    Halts (fun n => Eval.letGo M (F n)) R s :=
  post h (fun _ => rfl) fun o ho => by cases o <;> first | exact ho | exact absurd ho id

/-- A `when` whose block halts from every state halts: holding its cells and putting their
values back take no fuel (shared.when). -/
theorem held {R : Value → Prop} {F : Nat → Eval σ Value} (h : ∀ s, Halts F R s)
    (names : List Name) (handles : List Value) :
    Halts (fun n => Eval.held M (F n) names handles) R s := by
  have hr : ∀ (cells : List (Name × Ty × Nat)) s,
      Halts (fun n => Eval.release M cells (F n)) R s := fun cells s =>
    post (φ := fun o => o.release M cells) (h s) (fun _ => rfl) fun o ho => by
      cases o
      case performed => exact absurd ho id
      case outOfFuel => exact absurd ho id
      case stuck => trivial
      all_goals
        simp only [Outcome.release, Outcome.after]
        split
        · exact ho
        · exact Eval.Ends.fault _ _
  refine bind (const (Eval.Ends.ofExcept _ fun _ _ => trivial)) fun cells s' _ _ => ?_
  have hl : Eval.Ends (fun _ => True) (Eval.world M (fun w =>
      (World.take cells w).map fun p => (Value.list p.1, p.2)) >>= Eval.asList) :=
    Eval.Ends.bind (Eval.Ends.world M _) fun v _ => by
      cases v <;> first | exact Eval.Ends.pure trivial | exact Eval.Ends.fail _
  refine bind (const hl) fun vs s'' _ _ => ?_
  show Halts (fun n => if names.length = vs.length then
    Eval.withVars M (names.zip vs) (Eval.release M (names.zip cells) (F n)) else Eval.fail .stuck) R s''
  split
  · exact withVars M (hr _) _ s''
  · exact const (Eval.Ends.fail _)

/-- A call whose body halts from every state halts. -/
theorem invoke (captured : List (Name × Value)) (params : List Param) (passed : List Passed)
    {F : Nat → Eval σ Value} (h : ∀ s, Halts F (fun _ => True) s) :
    Halts (fun n => Eval.invoke M captured params passed (F n)) (fun _ => True) s := by
  cases hb : bindArgs params passed with
  | none => exact ⟨0, .stuck, trivial, fun n _ => by simp [Eval.invoke, hb]⟩
  | some bound =>
    cases he : M.enter s captured bound with
    | error f => exact ⟨0, .fault f s, Eval.Ends.fault (P := fun _ => True) f s, fun n _ => by
        simp [Eval.invoke, hb, he]⟩
    | ok callee =>
      refine post (φ := fun o => Eval.invoke M captured params passed (fun _ => o) s) (h callee)
        (fun n => by simp [Eval.invoke, hb, he]) fun o ho => ?_
      simp only [Eval.invoke, hb, he]
      cases o with
      | jumped j s' =>
        cases j <;> simp only [Outcome.leaveCall] <;> (try split) <;>
          first | trivial | exact Eval.Ends.fault _ _
      | outOfFuel => exact ho
      | performed => simp [Outcome.Ends] at ho
      | _ => simp only [Outcome.leaveCall] <;> (try split) <;>
          first | trivial | exact Eval.Ends.fault _ _

end

end Halts

end Stilt
