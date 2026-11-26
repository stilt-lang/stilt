import Stilt.Counterexamples.Paired

/-!
# A non-escaping parameter that escapes

A program that shows what the no-escape rule of effects.no-escape is for.

A non-escaping parameter passes its argument's effects through to the caller:
its row holds an implicit row variable that the function's own row holds too,
so each call performs them. That accounts for every effect of the argument
only while it runs during the call. `keep` returns its parameter instead, and
`main` calls it after `keep` has returned, outside every row that holds the
caller's raise:

```stilt
fn keep(g: fn()) -> fn() { g }

fn main() {
  let h: fn() = try keep(|| raise true) catch _ because "keep raises nothing" => || ()
  h()
}
```

effects.no-escape makes a row that lacks a parameter's implicit variable no
error where the variable meets it, since only a use that breaks the no-escape
rule can bring the variable there. Here `g` meets `fn()`, the result type of
`keep`, whose row lacks `g'`. So the checker accepts the program once the
no-escape rule is gone, and its run raises a `bool` out of a `main` that
raises nothing. The no-escape rule rejects it, at the return of `g` (E0508).
Typing that checks every row rejects `keep`'s body as well: the row of `g`
holds `g'`, which `fn()` lacks.
-/

namespace Stilt.Counterexamples

/-! ## The program -/

/-- The row `/ g'`, where `g'` is the implicit row variable of `g`. -/
abbrev gRow : Row := ⟨false, none, ["g'"], [], none⟩

/-- `fn keep(g: fn()) -> fn() { g }`, with `g` non-escaping, so that `keep`'s
own row is `{g'}`. -/
def keep : FnDecl :=
  ⟨"keep", [], ["g'"], [⟨.let, "g", .fn [] .unit gRow, some "g'"⟩], .fn [] .unit Row.pure, gRow,
    .var "g", {}⟩

/-- `try keep(|| raise true) catch _ => || ()`, which instantiates `g'` with
`raise<bool>`. -/
def keepRaisingBool : Expr :=
  .tryCatch
    (.call (.fnRef "keep" [] [raisesBool])
      [.value (.closure [] .unit raisesBool (.raise (.bool true)))] (.fn [] .unit Row.pure))
    .bool "x" (.closure [] .unit Row.pure .unit) (.fn [] .unit Row.pure)

/-- `let h: fn() = try keep(|| raise true) catch _ => || (); h()`, in a `main`
whose row is pure. -/
def escaped : Program :=
  ⟨⟨[], [], [keep], [], [], [], []⟩,
    .letIn "h" (.fn [] .unit Row.pure) keepRaisingBool (.call (.var "h") [] .unit),
    Row.pure, {}⟩

/-! ## The checker needs the no-escape rule -/

/-- The checker accepts `keep`'s body: `g` has type `fn() / g'`, and the
result type's row lacks `g'` where `g` meets it. -/
private theorem keep_lenient {D : Decls} : keep.Lenient D keep.scope :=
  ⟨.fn [] .unit gRow, .var rfl,
    .inr ⟨by decide, [], .unit, gRow, rfl, .fn ⟨fun h => h, fun _ h => h,
      fun _ h => by simp [Row.without, FnDecl.implicits, keep] at h, (fun _ h => nomatch h),
      (fun _ h => nomatch h)⟩⟩⟩

/-- `main` checks: the call of `keep` raises `bool` through `g'`, which the
`catch` handles, and `h` is a pure function. -/
private theorem escaped_main :
    HasType escaped.decls .closed [] ⟨Row.pure, false, false, .unit, false, false⟩ escaped.main .unit := by
  have hcallee : HasType escaped.decls .closed [] ⟨Row.pure.withRaise .bool, true, true, .unit, false, false⟩
      (.fnRef "keep" [] [raisesBool]) (keep.type.substRows (keep.rowParams.zip [raisesBool])) :=
    .fnRef (types := []) rfl rfl (instantiable_of_check (by decide)) (by decide) (wellFormed_of_check (by decide))
      (passesOn_of_check (by decide)) .nil
  have htype : keep.type.substRows (keep.rowParams.zip [raisesBool]) =
      .fn [(.let, .fn [] .unit raisesBool)] (.fn [] .unit Row.pure) raisesBool := rfl
  rw [htype] at hcallee
  exact .letIn (wellFormed_of_check (by decide))
    (.tryCatch (wellFormed_of_check (by decide)) (wellFormed_of_check (by decide))
      (.call hcallee
        (.value (by decide) (.closure .nil rfl (wellFormed_of_check (by decide))
          (.raise rfl .bool (.refl _)) (.never _)) (.refl _) .nil)
        ⟨⟨fun h => h, fun _ h => h, fun _ h => h, (fun _ h => nomatch h), (fun _ h => nomatch h)⟩,
          fun _ => rfl, fun _ _ h => (nomatch h), rfl⟩)
      (.refl _)
      (.closure .nil rfl (wellFormed_of_check (by decide)) .unit (.refl _)) (.refl _))
    (.refl _)
    (.call (.var rfl) .nil ⟨.refl _, fun h => (nomatch h), fun h => (nomatch h), rfl⟩)

/-- The checker without the no-escape rule accepts `escaped`. -/
theorem escaped_lenient : escaped.LenientIn FnDecl.scope where
  decls := declsWellFormed (by decide) (by decide) (by simp [escaped]) ⟨rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Decls.receivers_of_nil rfl (by decide))
  fns := by
    intro d hd
    simp only [escaped, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    exact keep_lenient
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  main := ⟨.unit, escaped_main, .refl _⟩

/-- The run calls the closure that `keep` returned, which raises the `bool`
out of `main`. -/
theorem escaped_raises : escaped.runCopy 16 = .raised (.bool true) ([], {}) := rfl

/-- So type soundness fails for the checker without the no-escape rule. -/
theorem typeSoundnessWithoutNoEscape_false : ¬TypeSoundnessWithoutNoEscape := by
  intro h
  have hsound := h escaped 16 escaped_lenient
  rw [escaped_raises] at hsound
  obtain ⟨E, hE, _⟩ := hsound
  exact nomatch hE

/-! ## The no-escape rule rejects it, and so does typing that checks every row -/

/-- `keep` returns its non-escaping parameter (E0508). -/
theorem escaped_escapes : ¬escaped.NoEscape :=
  fun h => absurd (h keep (by simp [escaped])) (by unfold FnDecl.NoEscape; decide)

/-- The model rejects `escaped`, at the no-escape rule. -/
theorem escaped_not_wellTyped : ¬escaped.WellTyped :=
  fun h => escaped_escapes h.noEscape

/-- Typing that checks every row rejects `keep`'s body: `g`'s row holds `g'`,
which the result type's row lacks. -/
theorem keep_not_typed {D : Decls} : ¬keep.WellTyped D keep.scope := by
  rintro ⟨σ, hbody, hfit⟩
  cases hbody with
  | var hl =>
    obtain rfl : Ty.fn [] .unit gRow = σ :=
      congrArg Binding.type (Option.some.inj (Eq.trans rfl hl))
    have := (Fits.fn_iff.1 hfit).2.2.vars "g'" (by simp)
    exact nomatch this

end Stilt.Counterexamples
