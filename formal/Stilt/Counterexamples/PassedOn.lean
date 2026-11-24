import Stilt.Counterexamples.Paired

/-!
# Row variables passed on

Programs that show what effects.passing-to-paired-variables is for.

The first, `passedOn`, shows that effects.paired-row-variables is unsound without effects.passing-to-paired-variables. Its
`f` pairs `e` with `Box` in `k`'s type, so effects.paired-row-variables lets it catch `Box` from a
call through `e`. A generic caller then gives `e` its own unpaired `r`, and
the row `{raise<Box>, r}` keeps one `raise` label, so effects.one-error-type accepts
it, while `main` instantiates `r` with `raise<bool>`:

```stilt
fn f<e>(escaping g: fn() / e, escaping k: fn() / {raise<Box>, e}) -> i64 / e {
  try {
    let h: fn() / {raise<Box>, e} = g
    h()
    0
  } catch x because "only a Box can reach here" => x.v
}

fn caller<r>(escaping g: fn() / r) -> i64 / r { f(g, || ()) }

fn main() / io {
  let n = try caller(|| raise true) catch _ because "the error is a bool" => 0
  print("{n}")
}
```

effects.paired-row-variables accepts it, and the run reaches `x.v` with `x` a `bool`. The model,
which states effects.passing-to-paired-variables, rejects the use `f<r>`, and accepts
`passedOnPaired`, where `caller`'s signature pairs `r` with `Box`. `main`
returns `()` (program.main), so `passedOnPaired` shows the value it computes
by raising it.
-/

namespace Stilt.Counterexamples

/-! ## effects.paired-row-variables without effects.passing-to-paired-variables is unsound -/

/-- The row `/ r`. -/
abbrev rRow : Row := ⟨false, none, ["r"], [], none⟩

/-- `fn f<e>(escaping g: fn() / e, escaping k: fn() / {raise<Box>, e}) -> i64 /
e { try { let h: fn() / {raise<Box>, e} = g; h(); 0 } catch x => x.v }`:
`annotatedF` with a parameter whose type pairs `e` with `Box`. -/
def pairedF : FnDecl :=
  ⟨"f", [], ["e"], [⟨.let, "g", .fn [] .unit eRow, none⟩, ⟨.let, "k", .fn [] .unit boxE, none⟩],
    .i64, eRow, annotatedBody⟩

/-- `fn caller<r>(escaping g: fn() / r) -> i64 / r { f<r>(g, || ()) }`. -/
def unpairedCaller : FnDecl :=
  ⟨"caller", [], ["r"], [⟨.let, "g", .fn [] .unit rRow, none⟩], .i64, rRow,
    .call (.fnRef "f" [] [rRow]) [.value (.var "g"), .value (.closure [] .unit Row.pure .unit)] .i64⟩

/-- The program in which `caller` passes its unpaired `r` on to `f`'s paired
`e`. -/
def passedOn : Program :=
  ⟨⟨[box], [], [pairedF, unpairedCaller], [], [], [], []⟩, callRaisingBool "caller", raisesBool⟩

/-- `f`'s signature pairs `e` with `Box`, in `k`'s type. -/
private theorem pairedF_pairs : pairedF.pairs "e" (.record "Box") :=
  ⟨boxE, by simp [paramRows, Ty.rows, Row.rows, Param.sig, pairedF], by simp, rfl⟩

/-- `f`'s body checks: the call `h()` in the `catch` operand ends in `e`, which
the signature pairs with `Box` (effects.catch-around-row-variables). -/
private theorem pairedF_wellTyped {D : Decls} (hbox : D.record? "Box" = some box) :
    pairedF.WellTyped D pairedF.scope :=
  ⟨.i64, .tryCatch (wellFormed_of_check (by decide)) (wellFormed_of_check (by decide))
    (.letIn (wellFormed_of_check (by decide)) (.var rfl)
      (.fn ⟨id, fun _ h => (nomatch h), fun _ => id, fun _ h => (nomatch h), fun _ h => (nomatch h)⟩)
      (.seq (.call (.var rfl) .nil ⟨.refl _, fun _ => rfl, fun _ _ hv =>
          ⟨.record "Box", rfl, by simp at hv; exact hv ▸ pairedF_pairs⟩, rfl⟩)
        (.refl _) (.int (by decide))))
    (.refl _) (.field (.var rfl) hbox rfl) (.refl _), .refl _⟩

/-- effects.paired-row-variables accepts `passedOn`: instantiating `e` with `r` leaves every row of
`f`'s type one `raise` label (effects.one-error-type), and `f` pairs `e` with `Box`. -/
theorem passedOn_wellTypedWithoutPassing : passedOn.WellTypedWithoutPassing where
  decls := declsWellFormed (by decide) (by decide) (by unfold Ty.Closed; decide) ⟨rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Decls.receivers_of_nil rfl (by decide))
  fns := by
    intro d hd
    apply FnDecl.WellTyped.lenient
    simp only [passedOn, Decls.fns_mk, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact (pairedF_wellTyped rfl).of_le pairedF.scope_le_withoutPassingScope
    · have hcallee : HasType passedOn.decls unpairedCaller.withoutPassingScope
          (Ctx.params [] unpairedCaller.params) ⟨rRow, false, false, unpairedCaller.result, false, false⟩
          (.fnRef "f" [] [rRow])
          (pairedF.type.substRows (pairedF.rowParams.zip [rRow])) :=
        .fnRef (types := []) rfl rfl (instantiable_of_check (by decide)) (by decide) (wellFormed_of_check (by decide))
          (fun _ _ _ _ _ _ _ => trivial) .nil
      exact ⟨.i64, .call hcallee
        (.value (by decide) (.var rfl) (.refl _)
          (.value (by decide) (.closure .nil rfl (wellFormed_of_check (by decide)) .unit (.refl _))
            (.fn (Row.pure_within _)) .nil))
        ⟨.refl _, fun h => (nomatch h), fun h => (nomatch h), rfl⟩, .refl _⟩
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  main := ⟨.unit,
    callRaisingBool_typed (d := unpairedCaller) rfl rfl (instantiable_of_check (by decide)) rfl rfl,
    .refl _⟩
  noEscape := noEscape_of_check (by decide)

/-- `passedOn` reaches `x.v` with `x` the `bool` that `g` raised, and gets
stuck. -/
theorem passedOn_stuck : passedOn.runCopy 16 = .stuck := rfl

/-- Type soundness fails for effects.paired-row-variables without effects.passing-to-paired-variables. -/
theorem typeSoundnessWithoutPassing_false : ¬TypeSoundnessWithoutPassing := by
  intro h
  have hsound := h passedOn 16 passedOn_wellTypedWithoutPassing
  rw [passedOn_stuck] at hsound
  exact hsound

/-! ## effects.passing-to-paired-variables rejects it, and accepts the pairing passed on -/

/-- effects.passing-to-paired-variables rejects the use `f<r>`: `f` pairs `e` with `Box`, the use
gives `e` the row `/ r`, and `caller`'s signature pairs `r` with nothing. -/
theorem passedOn_not_wellTyped : ¬passedOn.WellTyped := by
  intro h
  obtain ⟨_, hfns, _, _⟩ := h.typedIn
  obtain ⟨σ, hbody, _⟩ := hfns unpairedCaller (by simp [passedOn])
  cases hbody with
  | call hcallee _ _ =>
    obtain ⟨d, hd, _, hpass⟩ := fnRef_inv hcallee
    obtain rfl : pairedF = d := Option.some.inj (Eq.trans rfl hd)
    exact pairs_nothing (d := unpairedCaller) (by decide) "r" (.record "Box")
      (hpass "e" (.record "Box") rRow "r" pairedF_pairs rfl (by simp))

/-- `fn caller<r>(escaping g: fn() / {raise<Box>, r}) -> i64 / {raise<Box>, r}
{ try f<{raise<Box>, r}>(g, || ()) }`: `caller` pairs `r` with `Box`, in `g`'s
type. -/
def pairedCaller : FnDecl :=
  ⟨"caller", [], ["r"], [⟨.let, "g", .fn [] .unit boxR, none⟩], .i64, boxR,
    .try (.call (.fnRef "f" [] [boxR])
      [.value (.var "g"), .value (.closure [] .unit Row.pure .unit)] .i64)⟩

/-- `let n = try caller<{}>(|| raise Box { v: 7 }) catch _ => 0; raise n`, in a
`main` whose row is `raise<i64>`. The `catch` returns 0 only if a `Box`
escapes `caller`. -/
def passedOnPaired : Program :=
  ⟨⟨[box], [], [pairedF, pairedCaller], [], [], [], []⟩,
    .letIn "n" .i64
      (.tryCatch
        (.call (.fnRef "caller" [] [Row.pure]) [.value (.closure [] .unit raisesBox raiseBox)] .i64)
        (.record "Box") "x" (.int 0) .i64)
      (.raise (.var "n")),
    raisesI64⟩

/-- Instantiating `e` with `{raise<Box>, r}` leaves every row of `f`'s type
one `raise` label: `k`'s row `{raise<Box>, e}` becomes `{raise<Box>, r}`
(effects.one-error-type). -/
private theorem pairedF_instantiable :
    pairedF.type.InstantiableBy (pairedF.rowParams.zip [boxR]) := by
  intro ρ hρ
  have hrows : pairedF.type.rows = [eRow, boxE, eRow] := rfl
  rw [hrows] at hρ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
  have hl : (pairedF.rowParams.zip [boxR]).lookup "e" = some boxR := rfl
  refine ⟨fun E hE F hF => ?_, fun v hv σ hσ => ?_⟩
  · rcases hρ with rfl | rfl | rfl <;> simp_all [Row.labels, Ty.substRows]
  · rcases hρ with rfl | rfl | rfl <;> simp_all <;> subst_vars <;> rfl

/-- The use `f<{raise<Box>, r}>` passes `r` on with its pairing: `f` pairs only
`e`, with `Box`, and `caller` pairs `r` with `Box` (effects.passing-to-paired-variables). -/
private theorem pairedCaller_passesOn :
    PassesOnPairs pairedCaller.scope pairedF (pairedF.rowParams.zip [boxR]) := by
  rintro v E ρ r ⟨ρ', hρ', hv, hE⟩ hl hr
  have hrows : paramRows (pairedF.params.map Param.sig) ++ [pairedF.row] = [eRow, boxE, eRow] :=
    rfl
  rw [hrows] at hρ'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ'
  rcases hρ' with rfl | rfl | rfl
  · exact nomatch hE
  · simp only [List.mem_singleton] at hv
    subst hv
    obtain rfl := Option.some.inj hE
    obtain rfl : boxR = ρ := Option.some.inj hl
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨boxR, by simp [paramRows, Ty.rows, Row.rows, Param.sig, pairedCaller], by simp, rfl⟩
  · exact nomatch hE

/-- The model accepts `passedOnPaired`. -/
theorem passedOnPaired_wellTyped : passedOnPaired.WellTyped where
  decls := declsWellFormed (by decide) (by decide) (by unfold Ty.Closed; decide) ⟨rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Decls.receivers_of_nil rfl (by decide))
  fns := by
    intro d hd
    apply FnDecl.WellTyped.lenient
    simp only [passedOnPaired, Decls.fns_mk, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact pairedF_wellTyped rfl
    · have hcallee : HasType passedOnPaired.decls pairedCaller.scope
          (Ctx.params [] pairedCaller.params) ⟨boxR, true, false, pairedCaller.result, false, false⟩
          (.fnRef "f" [] [boxR])
          (pairedF.type.substRows (pairedF.rowParams.zip [boxR])) :=
        .fnRef (types := []) rfl rfl pairedF_instantiable (by decide) (wellFormed_of_check (by decide)) pairedCaller_passesOn .nil
      exact ⟨.i64, .try (.call hcallee
        (.value (by decide) (.var rfl) (.refl _)
          (.value (by decide) (.closure .nil rfl (wellFormed_of_check (by decide)) .unit (.refl _))
            (.fn (Row.pure_within _)) .nil))
        ⟨.refl _, fun _ => rfl, fun h => (nomatch h), rfl⟩), .refl _⟩
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  noEscape := noEscape_of_check (by decide)
  main := by
    have hcallee : HasType passedOnPaired.decls .closed [] ⟨raisesBox, true, true, .unit, false, false⟩
        (.fnRef "caller" [] [Row.pure])
        (pairedCaller.type.substRows (pairedCaller.rowParams.zip [Row.pure])) :=
      .fnRef (types := []) rfl rfl (instantiable_of_check (by decide)) (by decide) (wellFormed_of_check (by decide))
        (passesOn_of_check (by decide)) .nil
    exact ⟨.never, .letIn (wellFormed_of_check (by decide))
      (.tryCatch (wellFormed_of_check (by decide)) (wellFormed_of_check (by decide))
        (.call hcallee
          (.value (by decide) (.closure .nil rfl (wellFormed_of_check (by decide))
            (.raise rfl (.record rfl (.refl _) (.cons rfl (.int (by decide)) (.refl _) .nil)) (.refl _))
            (.never _)) (.refl _) .nil)
          ⟨.refl _, fun _ => rfl, fun _ _ hv => (nomatch hv), rfl⟩)
        (.refl _) (.int (by decide)) (.refl _))
      (.refl _) (.raise rfl (.var rfl) (.refl _)), .never _⟩

/-- `f` catches the `Box` that `g` raised, through `caller`, and returns its
field, which `main` raises, in both models of memory. -/
theorem passedOnPaired_runs :
    (passedOnPaired.runCopy 16).observe = .raised (.int 7) ∧
      (passedOnPaired.runInPlace 16).observe = .raised (.int 7) :=
  ⟨rfl, rfl⟩

end Stilt.Counterexamples
