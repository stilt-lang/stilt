import Stilt.Alloc.Values

/-!
# Steps that count no allocation

`Eval.Counts P m' m`: run from a state whose values allocate nothing when called, with any
count `c` beside it, the counting step `m'` ends as the step `m` of copy-in, copy-out does,
with `c` beside each of its states, so it counts no allocation; and `m` ends with a value that
`P` holds of, a raise or a jump whose values allocate nothing when called, each in such a
state, with a panic, out of fuel or stuck, never with a performance (`Outcome.Good`). Each
combinator of `Stilt.Semantics` keeps it.
-/

namespace Stilt

variable {D : Decls} {lim : Limited} {α β : Type}

/-- How a run of code that makes no value needing storage may end: with a value that `P` holds
of, or a raise or a jump whose values allocate nothing when called, each in a state whose values
allocate nothing when called; with a panic, out of fuel or stuck; never with a performance,
which only an allocation makes (facts.allocation). -/
def Outcome.Good (D : Decls) (lim : Limited) (P : α → Prop) : Outcome Copy.State α → Prop
  | .done a s => P a ∧ State.AllocFree D lim s
  | .raised e s => e.AllocFree D lim ∧ State.AllocFree D lim s
  | .jumped j s => j.AllocFree D lim ∧ State.AllocFree D lim s
  | .performed .. => False
  | .panicked _ _ | .outOfFuel | .stuck => True

/-- From every state whose values allocate nothing when called, with any count beside it, `m'`
ends as `m` does with the count unchanged, and `m` ends well (`Outcome.Good`). -/
def Eval.Counts (D : Decls) (lim : Limited) (P : α → Prop) (m' : Eval Count.State α)
    (m : Eval Copy.State α) : Prop :=
  ∀ (c : Nat) (s : Copy.State), State.AllocFree D lim s →
    m' (Count.lift c s) = (m s).atCount c ∧ (m s).Good D lim P

/-- A scope's end with the count beside each state. -/
theorem Outcome.unbind_atCount (c : Nat) :
    ∀ o : Outcome Copy.State α, (o.atCount c).unbind Count.memory = (o.unbind Copy.memory).atCount c
  | .done _ (_, _) | .raised _ (_, _) | .jumped _ (_, _) | .panicked _ (_, _) | .outOfFuel
  | .stuck => rfl
  | .performed op v (fr, w) k => by
    simp only [Outcome.atCount, Outcome.unbind]
    congr 1
    funext u x
    exact Outcome.unbind_atCount c (k u x)

theorem Outcome.Good.unbind {P : α → Prop} :
    ∀ {o : Outcome Copy.State α}, o.Good D lim P → (o.unbind Copy.memory).Good D lim P
  | .done _ (_, _), h | .raised _ (_, _), h | .jumped _ (_, _), h => ⟨h.1, h.2.1.tail, h.2.2⟩
  | .panicked _ (_, _), _ | .outOfFuel, _ | .stuck, _ => trivial
  | .performed .., h => h.elim

/-- An operation on the world with the count beside its state. -/
theorem Count.world_lift (f : World → Except Fault (Value × World)) (c : Nat) (s : Copy.State) :
    Eval.world Count.memory f (Count.lift c s) = (Eval.world Copy.memory f s).atCount c := by
  obtain ⟨fr, w⟩ := s
  show Eval.world Count.frames.withWorld f ((fr, c), w) = (Eval.world Copy.frames.withWorld f (fr, w)).atCount c
  cases h : f w with
  | ok p => rw [Eval.world_ok h, Eval.world_ok h]; rfl
  | error e => rw [Eval.world_error h, Eval.world_error h]; cases e <;> rfl

namespace Eval.Counts

variable {P : α → Prop} {Q : β → Prop}

theorem pure {a : α} (h : P a) : Eval.Counts D lim P (Pure.pure a) (Pure.pure a) :=
  fun _ _ hs => ⟨rfl, h, hs⟩

theorem bind {m' : Eval Count.State α} {m : Eval Copy.State α} {f' : α → Eval Count.State β}
    {f : α → Eval Copy.State β} (hm : Eval.Counts D lim P m' m)
    (hf : ∀ a, P a → Eval.Counts D lim Q (f' a) (f a)) :
    Eval.Counts D lim Q (m' >>= f') (m >>= f) := by
  intro c s hs
  obtain ⟨he, hg⟩ := hm c s hs
  show (m' (Count.lift c s)).bind (fun a s' => f' a s') =
    ((m s).bind fun a s' => f a s').atCount c ∧ ((m s).bind fun a s' => f a s').Good D lim Q
  rw [he]
  cases hms : m s with
  | done a s₁ => rw [hms] at hg; exact hf a hg.1 c s₁ hg.2
  | raised e s₁ => rw [hms] at hg; exact ⟨rfl, hg⟩
  | jumped j s₁ => rw [hms] at hg; exact ⟨rfl, hg⟩
  | panicked k s₁ => exact ⟨rfl, trivial⟩
  | performed _ _ _ _ => rw [hms] at hg; exact hg.elim
  | outOfFuel => exact ⟨rfl, trivial⟩
  | stuck => exact ⟨rfl, trivial⟩

theorem fail (f : Fault) : Eval.Counts D lim P (Eval.fail f) (Eval.fail f) := by
  intro c s _
  cases f <;> exact ⟨rfl, trivial⟩

theorem outOfFuel : Eval.Counts D lim P Eval.outOfFuel Eval.outOfFuel :=
  fun _ _ _ => ⟨rfl, trivial⟩

theorem ofExcept {x : Except Fault α} (h : ∀ a, x = .ok a → P a) :
    Eval.Counts D lim P (Eval.ofExcept x) (Eval.ofExcept x) := by
  intro c s hs
  cases x with
  | ok a => exact ⟨rfl, h a rfl, hs⟩
  | error f => cases f <;> exact ⟨rfl, trivial⟩

theorem inspect {f' : Count.State → Except Fault α} {f : Copy.State → Except Fault α}
    (hf : ∀ c s, f' (Count.lift c s) = f s)
    (h : ∀ s a, State.AllocFree D lim s → f s = .ok a → P a) :
    Eval.Counts D lim P (Eval.inspect f') (Eval.inspect f) := by
  intro c s hs
  show Eval.ofExcept (f' (Count.lift c s)) (Count.lift c s) = (Eval.ofExcept (f s) s).atCount c ∧
    (Eval.ofExcept (f s) s).Good D lim P
  rw [hf]
  exact ofExcept (fun a ha => h s a hs ha) c s hs

theorem update {f' : Count.State → Except Fault Count.State} {f : Copy.State → Except Fault Copy.State}
    (hf : ∀ c s, f' (Count.lift c s) = Count.lift c <$> f s)
    (h : ∀ s s', State.AllocFree D lim s → f s = .ok s' → State.AllocFree D lim s') :
    Eval.Counts D lim (fun _ => True) (Eval.update f') (Eval.update f) := by
  intro c s hs
  unfold Eval.update
  rw [hf]
  cases hfs : f s with
  | ok s' => exact ⟨rfl, trivial, h s s' hs hfs⟩
  | error e => cases e <;> exact ⟨rfl, trivial⟩

theorem throw {e : Value} (he : e.AllocFree D lim) :
    Eval.Counts D lim P (Eval.throw e) (Eval.throw e) := fun _ _ hs => ⟨rfl, he, hs⟩

theorem jump {j : Jump} (hj : j.AllocFree D lim) :
    Eval.Counts D lim P (Eval.jump j) (Eval.jump j) := fun _ _ hs => ⟨rfl, hj, hs⟩

theorem handle {m' : Eval Count.State α} {m : Eval Copy.State α} {h' : Value → Eval Count.State α}
    {h : Value → Eval Copy.State α} (hm : Eval.Counts D lim P m' m)
    (hh : ∀ e, e.AllocFree D lim → Eval.Counts D lim P (h' e) (h e)) :
    Eval.Counts D lim P (Eval.handle m' h') (Eval.handle m h) := by
  intro c s hs
  obtain ⟨he, hg⟩ := hm c s hs
  show (m' (Count.lift c s)).handle (fun e s' => h' e s') =
    ((m s).handle fun e s' => h e s').atCount c ∧ ((m s).handle fun e s' => h e s').Good D lim P
  rw [he]
  cases hms : m s with
  | raised e s₁ => rw [hms] at hg; exact hh e hg.1 c s₁ hg.2
  | done a s₁ => rw [hms] at hg; exact ⟨rfl, hg⟩
  | jumped j s₁ => rw [hms] at hg; exact ⟨rfl, hg⟩
  | panicked k s₁ => exact ⟨rfl, trivial⟩
  | performed _ _ _ _ => rw [hms] at hg; exact hg.elim
  | outOfFuel => exact ⟨rfl, trivial⟩
  | stuck => exact ⟨rfl, trivial⟩

theorem turn {R : Value → Prop} {m' : Eval Count.State Value} {m : Eval Copy.State Value}
    (hm : Eval.Counts D lim R m' m) :
    Eval.Counts D lim (fun _ => True) (Eval.turn m') (Eval.turn m) := by
  intro c s hs
  obtain ⟨he, hg⟩ := hm c s hs
  show (m' (Count.lift c s)).turn = (m s).turn.atCount c ∧ (m s).turn.Good D lim (fun _ => True)
  rw [he]
  cases hms : m s with
  | done a s₁ => rw [hms] at hg; exact ⟨rfl, trivial, hg.2⟩
  | raised e s₁ => rw [hms] at hg; exact ⟨rfl, hg⟩
  | jumped j s₁ =>
    rw [hms] at hg
    cases j with
    | brk => exact ⟨rfl, trivial, hg.2⟩
    | cont => exact ⟨rfl, trivial, hg.2⟩
    | ret v => exact ⟨rfl, hg⟩
  | panicked k s₁ => exact ⟨rfl, trivial⟩
  | performed _ _ _ _ => rw [hms] at hg; exact hg.elim
  | outOfFuel => exact ⟨rfl, trivial⟩
  | stuck => exact ⟨rfl, trivial⟩

theorem ite (b : Bool) {m₁' m₂' : Eval Count.State α} {m₁ m₂ : Eval Copy.State α}
    (h₁ : Eval.Counts D lim P m₁' m₁) (h₂ : Eval.Counts D lim P m₂' m₂) :
    Eval.Counts D lim P (if b then m₁' else m₂') (if b then m₁ else m₂) := by
  cases b
  · exact h₂
  · exact h₁

theorem forEach {body' : Value → Eval Count.State Bool} {body : Value → Eval Copy.State Bool}
    (hb : ∀ v, v.AllocFree D lim → Eval.Counts D lim (fun _ => True) (body' v) (body v)) :
    ∀ vs : List Value, (∀ v ∈ vs, v.AllocFree D lim) →
      Eval.Counts D lim (fun _ => True) (Eval.forEach body' vs) (Eval.forEach body vs)
  | [], _ => pure trivial
  | v :: vs, h => by
    unfold Eval.forEach
    refine bind (hb v (h v List.mem_cons_self)) fun b _ => ?_
    cases b
    · exact pure trivial
    · exact forEach hb vs fun u hu => h u (List.mem_cons_of_mem _ hu)

/-- An operation in the world, which keeps the property of every cell's value and gives a
value that allocates nothing when called, from operands that allocate nothing when called. -/
theorem run {o : Op} {vs : List Value} (hvs : ∀ v ∈ vs, v.AllocFree D lim) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.world Count.memory (o.run vs))
      (Eval.world Copy.memory (o.run vs)) := by
  intro c s hs
  refine ⟨Count.world_lift _ c s, ?_⟩
  obtain ⟨fr, w⟩ := s
  cases h : o.run vs w with
  | ok p =>
    rw [show Eval.world Copy.memory (o.run vs) (fr, w) = .done p.1 (fr, p.2) from Eval.world_ok h]
    exact ⟨Op.run_hereditary Value.AllocFree.hereditary .unit hvs h, hs.1, hs.2.run hvs h⟩
  | error e =>
    rw [show Eval.world Copy.memory (o.run vs) (fr, w) = .fault e (fr, w) from Eval.world_error h]
    cases e <;> trivial

theorem withVar {x : Name} {v : Value} {m' : Eval Count.State α} {m : Eval Copy.State α}
    (hv : v.AllocFree D lim) (hm : Eval.Counts D lim P m' m) :
    Eval.Counts D lim P (Eval.withVar Count.memory x v m') (Eval.withVar Copy.memory x v m) := by
  intro c s hs
  obtain ⟨fr, w⟩ := s
  obtain ⟨he, hg⟩ := hm c ((x, v) :: fr, w) ⟨hs.1.cons hv, hs.2⟩
  show (m' (Count.lift c ((x, v) :: fr, w))).unbind Count.memory =
    ((m ((x, v) :: fr, w)).unbind Copy.memory).atCount c ∧
      ((m ((x, v) :: fr, w)).unbind Copy.memory).Good D lim P
  rw [he, Outcome.unbind_atCount]
  exact ⟨rfl, hg.unbind⟩

theorem withInit_eq {σ : Type} (M : Memory σ) (hM : ∀ s y x v, M.bindMoved s x y v = M.bind s x v)
    (x : Name) (init : Expr) (v : Value) (m : Eval σ α) :
    Eval.withInit M x init v m = Eval.withVar M x v m := by
  funext s
  unfold Eval.withInit Eval.withVar Memory.bindInit
  cases init <;> simp [hM]

theorem withInit {x : Name} {init : Expr} {v : Value} {m' : Eval Count.State α}
    {m : Eval Copy.State α} (hv : v.AllocFree D lim) (hm : Eval.Counts D lim P m' m) :
    Eval.Counts D lim P (Eval.withInit Count.memory x init v m')
      (Eval.withInit Copy.memory x init v m) := by
  rw [withInit_eq Count.memory (fun _ _ _ _ => rfl), withInit_eq Copy.memory (fun _ _ _ _ => rfl)]
  exact withVar hv hm

theorem withVars {m' : Eval Count.State α} {m : Eval Copy.State α} (hm : Eval.Counts D lim P m' m) :
    ∀ bs : List (Name × Value), (∀ xv ∈ bs, xv.2.AllocFree D lim) →
      Eval.Counts D lim P (Eval.withVars Count.memory bs m') (Eval.withVars Copy.memory bs m)
  | [], _ => hm
  | (x, v) :: bs, h =>
    withVar (h (x, v) List.mem_cons_self) (withVars hm bs fun xv hx => h xv (List.mem_cons_of_mem _ hx))

end Eval.Counts

end Stilt
