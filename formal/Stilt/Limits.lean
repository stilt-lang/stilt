import Stilt.Ends.Theorem

/-!
# Limits of functions

A `without` clause after a function's signature, or in its module's header, limits the
function's body; the export joins the two and writes them on the function, and on `main`
(`FnDecl.limits`, `Program.limits`). The checker keeps each limit as the Reference infers
facts (facts.inferred-facts and facts.inference): a function has a fact when its own body
holds a site of it, or names a function that has it, the functions of a recursive group
solved together. A function without the fact `panic` is one of a set of functions that hold
no site of `panic` and name only functions of the set, the greatest such set being those
that the inference finds without it; so a limit is kept when some such set holds every
function the limit is on (`Program.PanicLimited`). For `div` the set is also ranked: its
functions call each other without recursion, but for self-calls that descend or shrink
(facts.descending-self-calls and facts.shrinking-recursion, `Program.DivLimited`).

What the limits promise, proved from the checks (`Program.PanicKeptBy.kept`,
`Program.DivLimited.kept`):

* a call of a function limited by `without panic`, on arguments whose closures and named
  functions are panic-free as well, wherever they were made, panics only with `overflow` or
  `deadlock`, and so does a run whose `main` is limited (effects.without-panic);
* one limited by `without panic, overflow` panics only with `deadlock`
  (effects.without-overflow). The check counts the operations that can overflow at their
  types (`Op.overflowFreeOn`), and lengths besides, which the calculus doesn't bound;
* one limited by `without overflow` alone may panic, but never with `overflow`: its code may
  index, store at an index and run operations that panic, as `lim.panics` allows;
* a call of a function limited by `without div` halts, from some fuel on, on arguments whose
  values at its non-escaping parameters are function values that halt, and so does a run whose
  `main` is limited (facts.without-div and facts.div);
* a run whose `main` is limited by both is total (`Program.total_of`).
-/

namespace Stilt

/-- A limit against `panic` kept as the Reference infers facts (facts.inferred-facts,
facts.without and effects.without-panic): some set of functions, holding every function
whose limits `limited` picks, holds no operation that adds `panic` and names only
functions of the set, and `main`'s body is such code when `limited` picks `main`'s limits.
With `overflows` false the set holds no operation that can overflow either
(effects.without-overflow), and with `panics` true it may hold the operations that add
`panic`, as `without overflow` alone allows. A function value that limited code calls adds nothing, its
closure literal's body counted where it is written and a named function where it is named
(facts.calls-through-function-values). The greatest such set is the functions that the
inference finds without the fact, solving a recursive group as a fixed point
(facts.inference). Of the facts, the model infers `panic`, `overflow` and `div`. -/
def Program.PanicKeptBy (p : Program) (limited : Limits → Bool) (overflows panics : Bool) : Prop :=
  ∃ lim : Limited, lim.overflows = overflows ∧ lim.panics = panics ∧ p.decls.PanicCover lim ∧
    (∀ d ∈ p.decls.fns, limited d.limits = true → lim.fn d.name = true) ∧
    (limited p.limits = true → p.main.panicFree lim = true)

/-- `without panic`, on each function and `main` it limits (effects.without-panic). -/
def Program.PanicLimited (p : Program) : Prop := p.PanicKeptBy (·.panic) true false

/-- `without panic, overflow`, on each function and `main` that both limit
(effects.without-overflow). -/
def Program.OverflowLimited (p : Program) : Prop :=
  p.PanicKeptBy (fun l => l.panic && l.overflow) false false

/-- `without overflow`, on each function and `main` it limits (effects.without-overflow):
their code may panic, but not with `overflow`. -/
def Program.OverflowAloneLimited (p : Program) : Prop := p.PanicKeptBy (·.overflow) false true

/-- `without div`, kept as the Reference infers facts (facts.without-div): some set of
functions, holding every function limited by `without div`, holds no site of `div` and names
only functions of the set, which call each other without recursion, but for self-calls that
descend (facts.descending-self-calls) or shrink (facts.shrinking-recursion), and `main`'s body
is such code when `main` is limited. A function's body may call through its non-escaping
parameters at the positions `H` gives, which adds no `div`: each call of the function passes
there an argument whose sites are counted where it is written (facts.div). -/
def Program.DivLimited (p : Program) : Prop :=
  ∃ (lim : Limited) (B : Name → Nat) (desc : Name → Descent) (H : Name → List Nat),
    p.decls.Ranked lim B desc H ∧
    (∀ name d, p.decls.fn? name = some d → ∀ k ∈ H name, ∃ q, d.params[k]? = some q ∧
      q.implicit.isSome = true) ∧
    (∀ d ∈ p.decls.fns, d.limits.div = true → lim.fn d.name = true) ∧
    (p.limits.div = true → p.main.divFree lim B H none [] = true)

/-- What a limit against `panic` promises (effects.without-panic and
effects.without-overflow): the functions whose limits `limited` picks are among a set of
functions such that a call of any of them, from a state and on arguments whose values hold
closures panic-free under the set and name only its functions, ends as panic-free code may
(`Outcome.PanicFree`): it panics only with `deadlock`, or with `overflow` when `overflows`
allows it, and so does the rest of every performance it makes. A run whose `main`'s limits
`limited` picks panics only so, as the reference interpreter runs it and in place. -/
def Program.PanicsKeptBy (p : Program) (limited : Limits → Bool) (overflows panics : Bool)
    (fuel : Nat) (input : String) : Prop :=
  (∃ lim : Limited, lim.overflows = overflows ∧ lim.panics = panics ∧
    (∀ name d, p.decls.fn? name = some d → limited d.limits = true → lim.fn name = true) ∧
    ∀ (n : Nat) (name : Name) (types : List Ty) (rows : List Row) (passed : List Passed)
      (s : Copy.State), lim.fn name = true → (∀ q ∈ passed, q.PanicFree lim) →
      State.PanicFree lim s → Outcome.PanicFree lim (Value.PanicFree lim)
        (Eval.call p.decls Copy.memory (eval p.decls Copy.memory n) (.function name types rows)
          passed s)) ∧
  (limited p.limits = true →
    (∀ k s, p.runCopy fuel input = .panicked k s → (k = .overflow ∧ overflows = true) ∨
      k = .deadlock ∨ (k ≠ .overflow ∧ panics = true)) ∧
    ∀ k, (p.runInPlace fuel input).observe = .panicked k → (k = .overflow ∧ overflows = true) ∨
      k = .deadlock ∨ (k ≠ .overflow ∧ panics = true))

/-- What `without div` promises (facts.without-div): the functions limited by it are among a
set of functions a call of any of which, from any state, on arguments that pass, at its
non-escaping parameters, function values that halt on any arguments (`Value.Halting`), halts:
from some fuel on, it ends the same way, not out of fuel and not as a performance (`Halts`).
A call through a non-escaping parameter adds no `div` of the callee's: its sites are the
argument's, counted where it is written (facts.div). A run whose `main` is limited never runs
out of fuel from some fuel on, as the reference interpreter runs it and in place. With
`Program.PanicsKeptBy` and type soundness, a run whose `main` is limited by
`without panic, div` is total (`Program.total_of`). -/
def Program.HaltsKept (p : Program) (input : String) : Prop :=
  (∃ lim : Limited, (∀ name d, p.decls.fn? name = some d → d.limits.div = true →
      lim.fn name = true) ∧
    ∀ (name : Name) (types : List Ty) (rows : List Row) (passed : List Passed) (s : Copy.State),
      lim.fn name = true →
      (∀ d, p.decls.fn? name = some d → ∀ (k : Nat) (q : Param), d.params[k]? = some q →
        q.implicit.isSome = true → ∃ (a : Passed) (u : Value), passed[k]? = some a ∧ (a = .value u ∨ ∃ z, a = .moved z u) ∧
          u.Halting p.decls .leftToRight) →
      Halts (fun n => Eval.call p.decls Copy.memory (eval p.decls Copy.memory n)
        (.function name types rows) passed) (fun _ => True) s) ∧
  (p.limits.div = true →
    (∃ N, ∀ fuel, N ≤ fuel → p.runCopy fuel input ≠ .outOfFuel) ∧
    ∃ N, ∀ fuel, N ≤ fuel → (p.runInPlace fuel input).observe ≠ .outOfFuel)

/-- A function the declarations find under a name is one of their functions, of that name. -/
theorem Decls.fn?_spec {D : Decls} {name : Name} {d : FnDecl} (h : D.fn? name = some d) :
    d ∈ D.fns ∧ d.name = name :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The checks of a limit against `panic` keep its promises. -/
theorem Program.PanicKeptBy.kept {p : Program} {limited : Limits → Bool} {overflows panics : Bool}
    (h : p.PanicKeptBy limited overflows panics) (hwt : p.WellTyped) (hex : p.Exclusive)
    (fuel : Nat) (input : String) : p.PanicsKeptBy limited overflows panics fuel input := by
  obtain ⟨lim, rfl, rfl, hD, hfns, hmain⟩ := h
  refine ⟨⟨lim, rfl, rfl, fun name d hd hl => ?_, fun n name _ _ _ s hf hp hs =>
    hD.call .leftToRight n hf hp s hs (Frame.Meets.nil _)⟩, fun hl => ?_⟩
  · obtain ⟨hmem, rfl⟩ := Decls.fn?_spec hd
    exact hfns d hmem hl
  · exact ⟨fun _ _ h => p.runCopyWith_panicked hD (hmain hl) .leftToRight fuel input h,
      fun _ h => p.runInPlace_panicked hD (hmain hl) hwt hex fuel input h⟩

/-- The checks of `without div` keep its promises. -/
theorem Program.DivLimited.kept {p : Program} (h : p.DivLimited) (hwt : p.WellTyped)
    (hex : p.Exclusive) (input : String) : p.HaltsKept input := by
  obtain ⟨lim, B, desc, H, hR, hH, hfns, hmain⟩ := h
  refine ⟨⟨lim, fun name d hd hl => ?_, fun name _ _ passed s hf hp => ?_⟩, fun hl =>
    ⟨p.runCopyWith_halts hR (hmain hl) .leftToRight input,
      p.runInPlace_halts hR (hmain hl) hwt hex input⟩⟩
  · obtain ⟨hmem, rfl⟩ := Decls.fn?_spec hd
    exact hfns d hmem hl
  · cases hd : p.decls.fn? name with
    | none =>
      unfold Eval.call
      simp only [hd]
      exact Halts.const (Eval.Ends.fail _)
    | some d =>
      refine hR.call .leftToRight hf passed (fun k hk => ?_) s
      obtain ⟨q, hq, hi⟩ := hH name d hd k hk
      exact hp d hd k q hq hi

end Stilt
