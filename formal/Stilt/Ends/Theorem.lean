import Stilt.Ends.Start
import Stilt.Panics.Theorem
import Stilt.Soundness.Theorem

/-!
# What `without div` guarantees

**Without div** (facts.without-div): code free of `div` that names only functions
of a ranked set, free of `div` too, halts in copy-in, copy-out, whatever its order of
write-back: a call of a function of the set (`Decls.Ranked.call`), on arguments that pass, at
the parameters its body calls through, function values that halt (`Value.Halting`), a run whose
`main` is
such code (`Program.runCopyWith_halts`) and a program free of `div` whole
(`Program.DivFree.halts`), and in place when it is well typed and obeys the law
of exclusivity. A call halts by induction on its function's rank, since a body calls only
functions ranked below its own, then on its measure, since a self-call that goes down passes
a smaller one: the size of the value at the descending position, which a self-call that
descends passes a strict part of (facts.descending-self-calls), or the distance of its counter
from its bound, which a self-call that shrinks brings down (facts.shrinking-recursion); and a
body halts by induction on the depth of its
text (`eval_halts`), a closure literal's body counted in its depth, so that one given to a
non-escaping parameter halts wherever it is called: a `for` loop runs its body at its own fuel, turn after turn, and a
`while` that counts takes a turn more of fuel for each turn it makes, of which its values
allow finitely many (`Halts.whileCounts`).

**Total** (facts.without-div): a well-typed program whose `main` is free of `panic`
and `div` ends with `()`, with an error of the type its row allows, or with a
panic of the kind `overflow` or `deadlock` (`Program.total_of`, `Program.total`), as
copy-in, copy-out runs it.
-/

namespace Stilt

variable {lim : Limited}

/-- A call whose body halts from the frame the call starts it in halts. -/
theorem Halts.invokeWith {σ : Type} (M : Memory σ) (captured : List (Name × Value))
    (params : List Param) (passed : List Passed) {s : σ} {F : Nat → Eval σ Value}
    (h : ∀ bound callee, bindArgs params passed = some bound → M.enter s captured bound = .ok callee →
      Halts F (fun _ => True) callee) :
    Halts (fun n => Eval.invoke M captured params passed (F n)) (fun _ => True) s := by
  cases hb : bindArgs params passed with
  | none => exact ⟨0, .stuck, trivial, fun n _ => by simp [Eval.invoke, hb]⟩
  | some bound =>
    cases he : M.enter s captured bound with
    | error f => exact ⟨0, .fault f s, Eval.Ends.fault (P := fun _ => True) f s, fun n _ => by
        simp [Eval.invoke, hb, he]⟩
    | ok callee =>
      refine Halts.post (φ := fun o => Eval.invoke M captured params passed (fun _ => o) s)
        (h bound callee hb he) (fun n => by simp [Eval.invoke, hb, he]) fun o ho => ?_
      simp only [Eval.invoke, hb, he]
      cases o with
      | jumped j s' =>
        cases j <;> simp only [Outcome.leaveCall] <;> (try split) <;>
          first | trivial | exact Eval.Ends.fault _ _
      | outOfFuel => exact ho
      | performed => simp [Outcome.Ends] at ho
      | _ => simp only [Outcome.leaveCall] <;> (try split) <;>
          first | trivial | exact Eval.Ends.fault _ _

/-- **Without div**, for a call of a function that `lim` covers: on arguments that pass, at
the positions `H f` of the parameters its body calls through, function values that halt,
from any state, the call halts, never running out of fuel from some fuel on, and ending as no
performance. The function counts as one without `div` wherever it is named; it calls only
the functions `lim` covers, ranked below it, itself on strict parts of its descending
parameter or on a counter closer to its bound, and through no function value it is given but
those it vouches for (facts.without-div, facts.div, facts.descending-self-calls and
facts.shrinking-recursion). -/
theorem Decls.Ranked.call {D : Decls} {B : Name → Nat} {desc : Name → Descent}
    {H : Name → List Nat} (hR : D.Ranked lim B desc H) (w : WriteBack) {f : Name} {types : List Ty}
    {rows : List Row} (hf : lim.fn f = true) (passed : List Passed)
    (hp : Passed.HaltAt D w (H f) passed) (s : Copy.State) :
    Halts (fun n => Eval.call D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n)
      (.function f types rows) passed) (fun _ => True) s := by
  suffices key : ∀ r f, B f = r → lim.fn f = true → ∀ q (passed : List Passed),
      (desc f).measure passed = q → Passed.HaltAt D w (H f) passed → ∀ types rows s,
        Halts (fun n => Eval.call D (Copy.memoryWith w) (eval D (Copy.memoryWith w) n)
          (.function f types rows) passed) (fun _ => True) s from
    key _ f rfl hf _ passed rfl hp types rows s
  intro r
  induction r using Nat.strongRecOn with
  | ind r ihr =>
  intro f hBf hf q
  induction q using Nat.strongRecOn with
  | ind q ihq =>
  intro passed hq hp types rows s
  unfold Eval.call
  dsimp only
  cases hfn : D.fn? f with
  | none => exact Halts.const (Eval.Ends.fail _)
  | some d =>
    have hdd := hR f d hfn hf
    refine Halts.invokeWith _ [] d.params passed fun bound callee hb he => ?_
    obtain ⟨fr, hfr, rfl⟩ : ∃ fr, Copy.enter s.1 [] bound = .ok fr ∧ callee = (fr, s.2) := by
      change (·, s.2) <$> Copy.enter s.1 [] bound = _ at he
      cases hc : Copy.enter s.1 [] bound with
      | error e => rw [hc] at he; cases he
      | ok fr => rw [hc] at he; cases he; exact ⟨fr, rfl, rfl⟩
    have hC : CallsHalt D w lim B H (some (f, desc f))
        { (desc f).meas passed with fns := Value.Halting D w } := by
      refine ⟨fun g types' rows' passed' s' hg hp' => ?_,
        fun f' k' hme types' rows' passed' s' hlt hp' => ?_, fun f' k' hme => ?_, fun _ hu => hu⟩
      · simp only [Limited.names, Option.all_some, Bool.and_eq_true, decide_eq_true_eq] at hg
        exact ihr (B g) (hBf ▸ hg.2) g rfl hg.1 _ passed' rfl hp' types' rows' s'
      · simp only [Option.some.injEq, Prod.mk.injEq] at hme
        obtain ⟨rfl, rfl⟩ := hme
        exact ihq _ (hq ▸ hlt) passed' rfl hp' types' rows' s'
      · simp only [Option.some.injEq, Prod.mk.injEq] at hme
        obtain ⟨rfl, rfl⟩ := hme
        exact Descent.meas_fits _ _
    refine eval_halts hC _ _ _ ?_ (Nat.le_refl _) ?_ _ (enter_startRoles hb hfr hp)
    · rw [Expr.divFree_substRows, Expr.divFree_substTys]; exact hdd
    · rw [Expr.writes_substRows, Expr.writes_substTys]; exact startRoles_avoids d _ _

/-- **Without div**, for `main`: when the functions that `lim` covers are ranked and
`main`'s body is free of `div`, the run halts in copy-in, copy-out, whatever its order of
write-back, never running out of fuel from some fuel on. -/
theorem Program.runCopyWith_halts {p : Program} {B : Name → Nat} {desc : Name → Descent}
    {H : Name → List Nat} (hR : p.decls.Ranked lim B desc H)
    (hm : p.main.divFree lim B H none [] = true) (w : WriteBack) (input : String) :
    ∃ N, ∀ fuel, N ≤ fuel → p.runCopyWith w fuel input ≠ .outOfFuel := by
  have hC : CallsHalt p.decls w lim B H none { size := 0, fns := Value.Halting p.decls w } :=
    ⟨fun _ _ _ passed s hg hp => hR.call w (by simpa [Limited.names] using hg) passed hp s,
      fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ hu => hu⟩
  obtain ⟨N, o, ho, hn⟩ := eval_halts hC _ p.main [] hm (Nat.le_refl _) (Roles.Avoids.nil _)
    ([], World.start input) (Roles.Inv.nil _ _)
  refine ⟨N, fun fuel hf => ?_⟩
  have h := hn fuel hf
  dsimp only at h
  unfold Program.runCopyWith Program.run
  rw [h]
  cases o <;> simp [Outcome.leaveBody, Outcome.Ends] at ho ⊢
  rename_i j _
  cases j <;> simp

/-- **Without div** for `main`, in place: on a well-typed program that obeys the law of
exclusivity, in-place mutation shows what copy-in, copy-out does. -/
theorem Program.runInPlace_halts {p : Program} {B : Name → Nat} {desc : Name → Descent}
    {H : Name → List Nat} (hR : p.decls.Ranked lim B desc H)
    (hm : p.main.divFree lim B H none [] = true) (hwt : p.WellTyped) (hex : p.Exclusive)
    (input : String) :
    ∃ N, ∀ fuel, N ≤ fuel → (p.runInPlace fuel input).observe ≠ .outOfFuel := by
  obtain ⟨N, hN⟩ := p.runCopyWith_halts hR hm .leftToRight input
  refine ⟨N, fun fuel hf h => ?_⟩
  rw [← inPlaceAgreement_observe p fuel input hwt hex] at h
  cases ho : p.runCopy fuel input <;> rw [ho] at h <;> simp only [Outcome.observe, reduceCtorEq] at h
  exact hN fuel hf ho

/-- **Without div**, in copy-in, copy-out with any order of write-back: a program
free of `div` halts, never running out of fuel from some fuel on. -/
theorem Program.DivFree.halts {p : Program} (hp : p.DivFree) (w : WriteBack) (input : String) :
    ∃ N, ∀ fuel, N ≤ fuel → p.runCopyWith w fuel input ≠ .outOfFuel :=
  let ⟨_, _, hR, hm⟩ := hp
  p.runCopyWith_halts hR hm w input

/-- **Without div**, in place: on a well-typed program that obeys the law of
exclusivity, in-place mutation shows what copy-in, copy-out does. -/
theorem Program.DivFree.haltsInPlace {p : Program} (hp : p.DivFree) (hwt : p.WellTyped)
    (hex : p.Exclusive) (input : String) :
    ∃ N, ∀ fuel, N ≤ fuel → (p.runInPlace fuel input).observe ≠ .outOfFuel :=
  let ⟨_, _, hR, hm⟩ := hp
  p.runInPlace_halts hR hm hwt hex input

/-- **Total**, for `main`: a well-typed program whose `main` is free of `panic`, naming only
functions that a cover of panic-free functions holds, and free of `div`, naming only
ranked functions, ends with `()`, with an error of the type its row allows, or with a panic
of the kind `overflow` or `deadlock`, as the reference interpreter runs it, with every fuel
from some fuel on (facts.without-div). -/
theorem Program.total_of {p : Program} {lim lim' : Limited} {B : Name → Nat} {desc : Name → Descent}
    (hwt : p.WellTyped) (hD : p.decls.PanicCover lim) (hpm : p.main.panicFree lim = true)
    {H : Name → List Nat} (hR : p.decls.Ranked lim' B desc H)
    (hdm : p.main.divFree lim' B H none [] = true) (input : String) : ∃ N, ∀ fuel, N ≤ fuel →
      (p.runCopy fuel input).observe = .returned .unit ∨
      (∃ e E, (p.runCopy fuel input).observe = .raised e ∧ p.row.raise = some E ∧
        Value.Typed p.decls e E.sem) ∨
      (p.runCopy fuel input).observe = .panicked .overflow ∨
      (p.runCopy fuel input).observe = .panicked .deadlock := by
  obtain ⟨N, hN⟩ := p.runCopyWith_halts hR hdm .leftToRight input
  refine ⟨N, fun fuel hf => ?_⟩
  have hs := typeSoundness p fuel input hwt
  have he := hN fuel hf
  cases ho : p.runCopy fuel input with
  | done v s =>
    rw [ho] at hs
    simp only [Outcome.Sound] at hs
    exact .inl (by rw [hs]; rfl)
  | raised e s =>
    rw [ho] at hs
    obtain ⟨E, hE, ht⟩ := hs
    exact .inr (.inl ⟨e, E, rfl, hE, ht⟩)
  | jumped j s => rw [ho] at hs; exact absurd hs id
  | panicked k s =>
    rcases p.runCopyWith_panicked hD hpm .leftToRight fuel input ho with ⟨rfl, _⟩ | rfl
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr rfl))
  | performed => rw [ho] at hs; exact absurd hs id
  | outOfFuel => exact absurd ho he
  | stuck => rw [ho] at hs; exact absurd hs id

/-- **Total**: a well-typed program free of `panic` and `div` ends with `()`, with an
error of the type its row allows, or with a panic of the kind `overflow` or `deadlock`,
as the reference interpreter runs it, with every fuel from some fuel on (facts.without-div). -/
theorem Program.total {p : Program} (hwt : p.WellTyped) (hpanic : p.PanicFree) (hdiv : p.DivFree)
    (input : String) : ∃ N, ∀ fuel, N ≤ fuel →
      (p.runCopy fuel input).observe = .returned .unit ∨
      (∃ e E, (p.runCopy fuel input).observe = .raised e ∧ p.row.raise = some E ∧
        Value.Typed p.decls e E.sem) ∨
      (p.runCopy fuel input).observe = .panicked .overflow ∨
      (p.runCopy fuel input).observe = .panicked .deadlock :=
  let ⟨_, _, hR, hm⟩ := hdiv
  p.total_of hwt hpanic.cover hpanic.2 hR hm input

end Stilt
