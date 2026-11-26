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
functions call each other without recursion (`Program.DivLimited`).

What the limits promise, proved from the checks (`Program.PanicLimited.kept`,
`Program.DivLimited.kept`):

* a call of a function limited by `without panic`, on arguments whose closures and named
  functions are panic-free as well, wherever they were made, panics only with `overflow` or
  `deadlock`, and so does a run whose `main` is limited (effects.without-panic);
* a call of a function limited by `without div` halts, from some fuel on, on any arguments,
  and so does a run whose `main` is limited (facts.without-div);
* a run whose `main` is limited by both is total (`Program.total_of`).
-/

namespace Stilt

/-- `without panic`, kept as the Reference infers facts (facts.inferred-facts, facts.without
and effects.without-panic): some set of functions, holding every function limited by
`without panic`, holds no operation that adds `panic` and names only functions of the set,
and `main`'s body is such code when `main` is limited. A function value that limited code
calls adds nothing, its closure literal's body counted where it is written and a named
function where it is named (facts.calls-through-function-values). Of the facts, the model
infers `panic`, `overflow` and `div`. -/
def Program.PanicLimited (p : Program) : Prop :=
  ∃ lim : Limited, p.decls.PanicCover lim ∧
    (∀ d ∈ p.decls.fns, d.limits.panic = true → lim.fn d.name = true) ∧
    (p.limits.panic = true → p.main.panicFree lim = true)

/-- `without div`, kept as the Reference infers facts (facts.without-div): some set of
functions, holding every function limited by `without div`, holds no site of `div` and names
only functions of the set, which call each other without recursion, and `main`'s body is
such code when `main` is limited. -/
def Program.DivLimited (p : Program) : Prop :=
  ∃ (lim : Limited) (B : Name → Nat), p.decls.Ranked lim B ∧
    (∀ d ∈ p.decls.fns, d.limits.div = true → lim.fn d.name = true) ∧
    (p.limits.div = true → p.main.divFree lim = true)

/-- What `without panic` promises (effects.without-panic): the functions limited by it are
among a set of functions such that a call of any of them, from a state and on arguments
whose values hold closures panic-free under the set and name only its functions, ends as
panic-free code may (`Outcome.PanicFree`): it panics only with `overflow` or `deadlock`, and
so does the rest of every performance it makes. A run whose `main` is limited panics only
so, as the reference interpreter runs it and in place. -/
def Program.PanicsKept (p : Program) (fuel : Nat) (input : String) : Prop :=
  (∃ lim : Limited, (∀ name d, p.decls.fn? name = some d → d.limits.panic = true →
      lim.fn name = true) ∧
    ∀ (n : Nat) (name : Name) (types : List Ty) (rows : List Row) (passed : List Passed)
      (s : Copy.State), lim.fn name = true → (∀ q ∈ passed, q.PanicFree lim) →
      State.PanicFree lim s → Outcome.PanicFree lim (Value.PanicFree lim)
        (Eval.call p.decls Copy.memory (eval p.decls Copy.memory n) (.function name types rows)
          passed s)) ∧
  (p.limits.panic = true →
    (∀ k s, p.runCopy fuel input = .panicked k s → k = .overflow ∨ k = .deadlock) ∧
    ∀ k, (p.runInPlace fuel input).observe = .panicked k → k = .overflow ∨ k = .deadlock)

/-- What `without div` promises (facts.without-div): the functions limited by it are among a
set of functions a call of any of which, on any arguments and from any state, halts: from
some fuel on, it ends the same way, not out of fuel and not as a performance (`Halts`). A
run whose `main` is limited never runs out of fuel from some fuel on, as the reference
interpreter runs it and in place. -/
def Program.HaltsKept (p : Program) (input : String) : Prop :=
  (∃ lim : Limited, (∀ name d, p.decls.fn? name = some d → d.limits.div = true →
      lim.fn name = true) ∧
    ∀ (name : Name) (types : List Ty) (rows : List Row) (passed : List Passed) (s : Copy.State),
      lim.fn name = true →
      Halts (fun n => Eval.call p.decls Copy.memory (eval p.decls Copy.memory n)
        (.function name types rows) passed) (fun _ => True) s) ∧
  (p.limits.div = true →
    (∃ N, ∀ fuel, N ≤ fuel → p.runCopy fuel input ≠ .outOfFuel) ∧
    ∃ N, ∀ fuel, N ≤ fuel → (p.runInPlace fuel input).observe ≠ .outOfFuel)

/-- A function the declarations find under a name is one of their functions, of that name. -/
theorem Decls.fn?_spec {D : Decls} {name : Name} {d : FnDecl} (h : D.fn? name = some d) :
    d ∈ D.fns ∧ d.name = name :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The checks of `without panic` keep its promises. -/
theorem Program.PanicLimited.kept {p : Program} (h : p.PanicLimited) (hwt : p.WellTyped)
    (hex : p.Exclusive) (fuel : Nat) (input : String) : p.PanicsKept fuel input := by
  obtain ⟨lim, hD, hfns, hmain⟩ := h
  refine ⟨⟨lim, fun name d hd hl => ?_, fun n name _ _ _ s hf hp hs =>
    hD.call .leftToRight n hf hp s hs (Frame.Meets.nil _)⟩, fun hl => ?_⟩
  · obtain ⟨hmem, rfl⟩ := Decls.fn?_spec hd
    exact hfns d hmem hl
  · exact ⟨fun _ _ h => p.runCopyWith_panicked hD (hmain hl) .leftToRight fuel input h,
      fun _ h => p.runInPlace_panicked hD (hmain hl) hwt hex fuel input h⟩

/-- The checks of `without div` keep its promises. -/
theorem Program.DivLimited.kept {p : Program} (h : p.DivLimited) (hwt : p.WellTyped)
    (hex : p.Exclusive) (input : String) : p.HaltsKept input := by
  obtain ⟨lim, B, hR, hfns, hmain⟩ := h
  refine ⟨⟨lim, fun name d hd hl => ?_, fun _ _ _ passed s hf => hR.call .leftToRight hf passed s⟩, fun hl =>
    ⟨p.runCopyWith_halts hR (hmain hl) .leftToRight input,
      p.runInPlace_halts hR (hmain hl) hwt hex input⟩⟩
  obtain ⟨hmem, rfl⟩ := Decls.fn?_spec hd
  exact hfns d hmem hl

end Stilt
