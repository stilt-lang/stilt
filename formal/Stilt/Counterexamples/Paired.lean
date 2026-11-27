import Stilt.Theorems
import Stilt.Counterexamples.Checks

/-!
# Row variables paired with an error type

Programs that show what effects.paired-row-variables is for. They write row variables on `escaping`
parameters, which effects.no-escape as it was written had for every parameter of
function type, and the accepted one uses the implicit variable of a
non-escaping parameter.

The first two show that effects.no-escape, as it was written before effects.paired-row-variables, is
unsound. It let a `catch` operand call a function whose row holds a row
variable, provided the row also holds a `raise` label: "A row that also holds
`raise<E>` is fine: the variable can then add only that error type". That
holds of a row that a function's signature writes, because every call checks
that its instantiation leaves the row one `raise` label (effects.one-error-type). It
fails for a row that a body forms, which no caller checks. A body forms one in
two ways, and each program uses one:

* `annotated` grows the row of `escaping g: fn() / e` with an annotation, as
  effects.function-values allows: `let h: fn() / {raise<Box>, e} = g`;
* `generic` calls `apply<r>(escaping k: fn() / {raise<Box>, r}) / {raise<Box>,
  r}` with `r` instantiated by `e`.

In both, `f(|| raise true)` instantiates `e` with `raise<bool>`, and the
`bool` reaches arms written for `Box`:

```stilt
type Box = { v: i64 }

fn f<e>(escaping g: fn() / e) -> i64 / e {
  try {
    let h: fn() / {raise<Box>, e} = g
    h()
    0
  } catch x because "only a Box can reach here" => x.v
}

fn main() / io {
  let n = try f(|| raise true) catch _ because "the error is a bool" => 0
  print("{n}")
}
```

The calculus has no `print`, so `main` here declares `raise<bool>` instead of
catching it, and leaves `n` unused. effects.no-escape as it was written accepts both
programs, and both runs reach `x.v` with `x` a `bool`. effects.paired-row-variables rejects both,
and accepts `paired`, the guide's `or_zero`, whose signature pairs its
parameter's implicit variable with the caught type. `main` returns `()`
(program.main), so `paired` shows the value it computes by raising it.
-/

namespace Stilt.Counterexamples

/-! ## The programs -/

/-- `type Box = { v: i64 }`. -/
def box : RecordDecl := ⟨"Box", [("v", .i64)], []⟩

/-- The row `/ e`. -/
abbrev eRow : Row := ⟨false, none, ["e"], [], none⟩

/-- The row `/ {raise<Box>, e}`. -/
abbrev boxE : Row := ⟨false, some (.record "Box" []), ["e"], [], none⟩

/-- The row `/ {raise<Box>, r}`. -/
abbrev boxR : Row := ⟨false, some (.record "Box" []), ["r"], [], none⟩

/-- The row `/ raise<bool>`. -/
abbrev raisesBool : Row := ⟨false, some .bool, [], [], none⟩

/-- `try operand catch x => x.v`, where the operand raises `Box`. -/
def catchBox (operand : Expr) : Expr :=
  .tryCatch operand (.record "Box" []) "x" (.field (.var "x") "v") .i64

/-- `try { let h: fn() / {raise<Box>, e} = g; h(); 0 } catch x => x.v`. -/
def annotatedBody : Expr :=
  catchBox (.letIn "h" (.fn [] .unit boxE) (.var "g") (.seq (.call (.var "h") [] .unit) (.int 0)))

/-- `fn f<e>(escaping g: fn() / e) -> i64 / e { try { let h: fn() /
{raise<Box>, e} = g; h(); 0 } catch x => x.v }`. -/
def annotatedF : FnDecl :=
  ⟨"f", [], ["e"], [⟨.let, "g", .fn [] .unit eRow, none⟩], .i64, eRow, annotatedBody, {}⟩

/-- `fn apply<r>(escaping k: fn() / {raise<Box>, r}) / {raise<Box>, r} { try
k() }`. -/
def apply : FnDecl :=
  ⟨"apply", [], ["r"], [⟨.let, "k", .fn [] .unit boxR, none⟩], .unit, boxR,
    .try (.call (.var "k") [] .unit), {}⟩

/-- `fn f<e>(escaping g: fn() / e) -> i64 / e { try { apply<e>(g); 0 } catch x
=> x.v }`. -/
def genericF : FnDecl :=
  ⟨"f", [], ["e"], [⟨.let, "g", .fn [] .unit eRow, none⟩], .i64, eRow,
    catchBox (.seq (.call (.fnRef "apply" [] [eRow]) [.value (.var "g")] .unit) (.int 0)), {}⟩

/-- `let n: i64 = try f<raise<bool>>(|| raise true)`, in a `main` whose row is
`raise<bool>`. -/
def callRaisingBool (f : Name) : Expr :=
  .letIn "n" .i64
    (.try (.call (.fnRef f [] [raisesBool])
      [.value (.closure [] .unit raisesBool (.raise (.bool true)))] .i64))
    .unit

/-- The program whose row is formed by an annotation. -/
def annotated : Program :=
  ⟨⟨[box], [], [annotatedF], [], [], [], [], []⟩, callRaisingBool "f", raisesBool, {}⟩

/-- The program whose row is formed by an instantiation. -/
def generic : Program :=
  ⟨⟨[box], [], [apply, genericF], [], [], [], [], []⟩, callRaisingBool "f", raisesBool, {}⟩

/-! ## effects.no-escape as it was written is unsound -/

/-- `callRaisingBool f` checks, whatever `f`'s body, if `f` has one row
variable, and instantiating it with `raise<bool>` makes `f`'s type
`fn(fn() / raise<bool>) -> i64 / raise<bool>`. -/
theorem callRaisingBool_typed {D : Decls} {f : Name} {d : FnDecl}
    (hd : D.fn? f = some d) (hlen : d.rowParams.length = 1)
    (hinst : d.type.InstantiableBy (d.rowParams.zip [raisesBool]))
    (htype : d.type.substRows (d.rowParams.zip [raisesBool]) =
      .fn [(.let, .fn [] .unit raisesBool)] .i64 raisesBool) (htp : d.typeParams = []) :
    HasType D .closed [] ⟨raisesBool, false, false, .unit, false, false⟩ (callRaisingBool f) .unit := by
  have hcallee : HasType D .closed [] ⟨raisesBool, true, false, .unit, false, false⟩ (.fnRef f [] [raisesBool])
      ((d.type.substTys (d.typeArgs [])).substRows (d.rowParams.zip [raisesBool])) :=
    .fnRef hd (by simp [hlen]) hinst (fun _ h => by simp only [List.mem_singleton] at h; subst h; rfl)
      (by
        simp only [FnDecl.typeArgs, List.zip_nil_right, Ty.substTys_nil]
        rw [htype]
        exact wellFormed_of_check (by decide))
      (passesOn_of_check (by decide)) (by rw [htp]; exact .nil)
  simp only [FnDecl.typeArgs, List.zip_nil_right, Ty.substTys_nil] at hcallee
  rw [htype] at hcallee
  exact .letIn (wellFormed_of_check (by decide))
    (.try (.call hcallee
      (.value (by decide) (.closure .nil rfl (wellFormed_of_check (by decide))
        (.raise rfl .bool (.refl _)) (.never _)) (.refl _) .nil)
      ⟨.refl _, fun _ => rfl, fun h => (nomatch h), rfl⟩))
    (.refl _) .unit

theorem annotated_wellTypedAsRecorded : annotated.WellTypedAsRecorded where
  decls := declsWellFormed (by decide) (by decide) (by unfold Ty.Closed; decide) ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Decls.receivers_of_nil rfl (by decide))
  fns := by
    intro d hd
    apply FnDecl.WellTyped.lenient
    simp only [annotated, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    refine ⟨.i64, .tryCatch (wellFormed_of_check (by decide)) (wellFormed_of_check (by decide))
      (.letIn (wellFormed_of_check (by decide)) (.var rfl)
        (.fn ⟨id, fun _ h => (nomatch h), fun _ => id, fun _ h => (nomatch h), fun _ h => (nomatch h)⟩)
        (.seq
          (.call (.var rfl) .nil ⟨.refl _, fun _ => rfl, fun _ _ _ => ⟨_, rfl, trivial⟩, rfl⟩)
          (.refl _) (.int (by decide))))
      (.refl _) (.field (.var rfl) rfl rfl rfl) (.refl _), .refl _⟩
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  main := ⟨.unit,
    callRaisingBool_typed (d := annotatedF) rfl rfl (instantiable_of_check (by decide)) rfl rfl,
    .refl _⟩
  noEscape := noEscape_of_check (by decide)

theorem generic_wellTypedAsRecorded : generic.WellTypedAsRecorded where
  decls := declsWellFormed (by decide) (by decide) (by unfold Ty.Closed; decide) ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Decls.receivers_of_nil rfl (by decide))
  fns := by
    intro d hd
    apply FnDecl.WellTyped.lenient
    simp only [generic, Decls.fns_mk, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact ⟨.unit, .try (.call (.var rfl) .nil ⟨.refl _, fun _ => rfl, fun h => (nomatch h), rfl⟩),
        .refl _⟩
    · have hcallee : HasType generic.decls genericF.recordedScope
          (Ctx.params [] genericF.params) ⟨eRow.withRaise (.record "Box" []), true, true, .i64, false, false⟩
          (.fnRef "apply" [] [eRow]) (apply.type.substRows (apply.rowParams.zip [eRow])) :=
        .fnRef (types := []) rfl rfl (instantiable_of_check (by decide)) (by decide) (wellFormed_of_check (by decide))
          (fun _ _ _ _ _ _ _ => trivial) .nil
      exact ⟨.i64, .tryCatch (wellFormed_of_check (by decide)) (wellFormed_of_check (by decide))
        (.seq (.call hcallee
            (.value (by decide) (.var rfl) (.fn ⟨id, fun _ h => (nomatch h), fun _ => id, fun _ h => (nomatch h), fun _ h => (nomatch h)⟩) .nil)
            ⟨.refl _, fun _ => rfl, fun _ _ _ => ⟨_, rfl, trivial⟩, rfl⟩)
          (.refl _) (.int (by decide)))
        (.refl _) (.field (.var rfl) rfl rfl rfl) (.refl _), .refl _⟩
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  main := ⟨.unit,
    callRaisingBool_typed (d := genericF) rfl rfl (instantiable_of_check (by decide)) rfl rfl,
    .refl _⟩
  noEscape := noEscape_of_check (by decide)

/-- `annotated` reaches `x.v` with `x` the `bool` that `g` raised, and gets
stuck. -/
theorem annotated_stuck : annotated.runCopy 16 = .stuck := rfl

/-- So does `generic`. -/
theorem generic_stuck : generic.runCopy 16 = .stuck := rfl

/-- Type soundness fails for effects.no-escape as it was written. -/
theorem typeSoundnessAsRecorded_false : ¬TypeSoundnessAsRecorded := by
  intro h
  have hsound := h annotated 16 annotated_wellTypedAsRecorded
  rw [annotated_stuck] at hsound
  exact hsound

/-! ## effects.paired-row-variables rejects both programs -/

/-- effects.catch-around-row-variables rejects the call `h()`: its row `{raise<Box>, e}` ends in
`e`, which `f`'s signature pairs with no error type. -/
theorem annotated_not_wellTypedWithoutPassing : ¬annotated.WellTypedWithoutPassing := by
  intro h
  obtain ⟨_, hfns, _, _⟩ := h.toLenientIn.typedIn h.noEscape
  obtain ⟨σ, hbody, _⟩ := hfns annotatedF (by simp [annotated])
  cases hbody with
  | tryCatch _ _ hop _ _ _ =>
    cases hop with
    | letIn _ _ _ hrest =>
      cases hrest with
      | seq hcall _ _ =>
        cases hcall with
        | call hcallee _ hallowed =>
          cases hcallee with
          | var hlook =>
            have hτ : Ty.fn [] .unit boxE = _ :=
              congrArg Binding.type (Option.some.inj (Eq.trans rfl hlook))
            injection hτ with _ _ hσ
            subst hσ
            obtain ⟨E, _, hpair⟩ := hallowed.paired rfl "e" (by simp)
            exact pairs_nothing (d := annotatedF) (by decide) "e" E hpair

/-- effects.catch-around-row-variables rejects the call `apply<e>(g)`: its row as instantiated,
`{raise<Box>, e}`, ends in `e`, which `f`'s signature pairs with no error
type. -/
theorem generic_not_wellTypedWithoutPassing : ¬generic.WellTypedWithoutPassing := by
  intro h
  obtain ⟨_, hfns, _, _⟩ := h.toLenientIn.typedIn h.noEscape
  obtain ⟨σ, hbody, _⟩ := hfns genericF (by simp [generic])
  cases hbody with
  | tryCatch _ _ hop _ _ _ =>
    cases hop with
    | seq hcall _ _ =>
      cases hcall with
      | call hcallee _ hallowed =>
        obtain ⟨d, hd, htype, _⟩ := fnRef_inv hcallee
        obtain rfl : apply = d := Option.some.inj (Eq.trans rfl hd)
        have hinst : apply.type.substRows (apply.rowParams.zip [eRow]) =
            .fn [(.let, .fn [] .unit boxE)] .unit boxE := rfl
        rw [hinst] at htype
        injection htype with _ _ hσ
        subst hσ
        obtain ⟨E, _, hpair⟩ := hallowed.paired rfl "e" (by simp)
        exact pairs_nothing (d := genericF) (by decide) "e" E hpair

/-- The model rejects `annotated`, as effects.paired-row-variables does. -/
theorem annotated_not_wellTyped : ¬annotated.WellTyped :=
  fun h => annotated_not_wellTypedWithoutPassing h.withoutPassing

/-- The model rejects `generic`, as effects.paired-row-variables does. -/
theorem generic_not_wellTyped : ¬generic.WellTyped :=
  fun h => generic_not_wellTypedWithoutPassing h.withoutPassing

/-! ## effects.paired-row-variables accepts a pairing in the signature -/

/-- The row `/ {raise<Box>, f'}`, where `f'` is the implicit row variable of a
non-escaping parameter `f`, which no program writes (effects.non-escaping-parameters). -/
abbrev boxF : Row := ⟨false, some (.record "Box" []), ["f'"], [], none⟩

/-- `fn or_zero(f: fn() -> i64 / raise<Box>) -> i64 { try f() catch x => x.v }`,
the guide's `or_zero` with `Box` for `E`. Its parameter is non-escaping, so its
row is `{raise<Box>, f'}` and the function's own row is `{f'}`. -/
def orZero : FnDecl :=
  ⟨"or_zero", [], ["f'"], [⟨.let, "f", .fn [] .i64 boxF, some "f'"⟩], .i64, ⟨false, none, ["f'"], [], none⟩,
    catchBox (.call (.var "f") [] .i64), {}⟩

/-- The row `/ raise<Box>`. -/
abbrev raisesBox : Row := ⟨false, some (.record "Box" []), [], [], none⟩

/-- `raise Box { v: 7 }`. -/
def raiseBox : Expr := .raise (.record "Box" [] [("v", .int 7)])

/-- The row `/ raise<i64>`. -/
abbrev raisesI64 : Row := ⟨false, some .i64, [], [], none⟩

/-- `raise or_zero(|| raise Box { v: 7 })`, in a `main` whose row is
`raise<i64>`. The call instantiates `f'` with the argument's effects beyond
`raise<Box>`: none. -/
def paired : Program :=
  ⟨⟨[box], [], [orZero], [], [], [], [], []⟩,
    .raise (.call (.fnRef "or_zero" [] [Row.pure]) [.value (.closure [] .i64 raisesBox raiseBox)] .i64),
    raisesI64, {}⟩

/-- The model accepts `paired`: the signature of `or_zero` pairs `f'` with
`Box`, the type its `catch` handles, in `f`'s row (effects.paired-row-variables and effects.catch-around-row-variables). -/
theorem paired_wellTyped : paired.WellTyped where
  decls := declsWellFormed (by decide) (by decide) (by unfold Ty.Closed; decide) ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Decls.receivers_of_nil rfl (by decide))
  fns := by
    intro d hd
    apply FnDecl.WellTyped.lenient
    simp only [paired, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    exact ⟨.i64, .tryCatch (wellFormed_of_check (by decide)) (wellFormed_of_check (by decide))
      (.call (.var rfl) .nil ⟨.refl _, fun _ => rfl, fun _ _ hv => ⟨.record "Box" [], rfl,
        ⟨boxF, by simp [paramRows, Ty.rows, Row.rows, Param.sig, orZero], hv, rfl⟩⟩, rfl⟩)
      (.refl _) (.field (.var rfl) rfl rfl rfl) (.refl _), .refl _⟩
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  main := by
    have hcallee : HasType paired.decls .closed [] ⟨raisesI64, false, false, .unit, false, false⟩
        (.fnRef "or_zero" [] [Row.pure]) (orZero.type.substRows (orZero.rowParams.zip [Row.pure])) :=
      .fnRef (types := []) rfl rfl (instantiable_of_check (by decide)) (by decide) (wellFormed_of_check (by decide))
        (passesOn_of_check (by decide)) .nil
    exact ⟨.never, .raise rfl (.call hcallee
      (.value (by decide) (.closure .nil rfl (wellFormed_of_check (by decide))
        (.raise rfl (.record rfl rfl (fun _ h => nomatch h) (.refl _) (.cons rfl (.int (by decide)) (.refl _) .nil)) (.refl _)) (.never _))
        (.refl _) .nil)
      ⟨Row.pure_within _, fun h => (nomatch h), fun h => (nomatch h), rfl⟩) (.refl _), .never _⟩
  noEscape := noEscape_of_check (by decide)

/-- `or_zero` catches the `Box` and returns its field, which `main` raises, in
both models of memory. -/
theorem paired_runs :
    (paired.runCopy 16).observe = .raised (.int 7) ∧
      (paired.runInPlace 16).observe = .raised (.int 7) :=
  ⟨rfl, rfl⟩

end Stilt.Counterexamples
