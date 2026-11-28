import Stilt.Optimality.Typing
import Stilt.Optimality.CopyRun
import Stilt.Optimality.InPlaceRun
import Stilt.Optimality.IndexFree
import Stilt.Counterexamples.Checks
import Stilt.Receivers

/-!
# Optimality of the call rule

The call rule of modes.overlapping-inout rejects a call whose `inout` arguments overlap, or whose
`inout` argument overlaps its `inout self` receiver, the first place a method
call modifies (E0402). It is sound (`pairwiseDisjoint_sound`), and no sound
call rule accepts more: a call rule that accepts a list of shapes with an
overlapping pair accepts the witness of `Stilt.Optimality.Witness`, a
well-typed program which panics in place and not under copy-in, copy-out. So
modes.overlapping-inout is the greatest sound call rule, and a call rule is sound exactly when
it accepts nothing that modes.overlapping-inout rejects. A method call is a call, so a sound
call rule compares its receiver with its `inout` arguments too.

The witness's runs differ inside the callee, before any place is written back,
so the bound holds whatever the order in which copy-out writes back, not only
the order of write-back of values.inout-argument-order, and not only its's. Its places hold no index, so the bound holds for rules asked
to be sound only on programs whose places hold none.

The comparison is among rules that see shapes, which modes.overlap makes of places
by removing their indexes. A rule that saw the values of indexes could accept
`swap(inout xs[0], inout xs[1])`, which modes.overlapping-inout rejects.
-/

namespace Stilt

open Optimality

/-- A list of shapes that modes.overlapping-inout rejects has two positions whose shapes
overlap, the shallower one first (modes.overlapping-inout). -/
theorem Optimality.overlap_of_not_pairwiseDisjoint {ss : List Shape}
    (h : pairwiseDisjoint ss = false) : ∃ a b extra, Overlap ss a b extra := by
  have hnot : ¬ss.Pairwise fun s t => s.overlaps t = false := by
    rw [← pairwiseDisjoint_iff, h]
    simp
  rw [List.pairwise_iff_getElem] at hnot
  simp only [Classical.not_forall, Bool.not_eq_false] at hnot
  obtain ⟨i, j, hi, hj, hij, hov⟩ := hnot
  simp only [Shape.overlaps, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    List.isPrefixOf_iff_prefix] at hov
  obtain ⟨hroot, hpre | hpre⟩ := hov
  · obtain ⟨extra, hextra⟩ := hpre
    exact ⟨i, j, extra, hi, hj, by omega, hroot, hextra⟩
  · obtain ⟨extra, hextra⟩ := hpre
    exact ⟨j, i, extra, hj, hi, by omega, hroot.symm, hextra⟩

/-- The witness's runs differ, whatever the order of write-back: under
copy-in, copy-out the callee's body returns, and in place it panics, with no
write-back (values.inout-arguments and values.inout-argument-order). -/
theorem Optimality.witness_disagrees (w : WriteBack) {ss : List Shape} {a b : Nat}
    {extra : List Name} (h : Overlap ss a b extra) :
    ((witness ss a b extra).runCopyWith w (depth ss + extra.length + 6 + ss.length)).observe ≠
      ((witness ss a b extra).runInPlace (depth ss + extra.length + 6 + ss.length)).observe := by
  rw [copy_runWith w h, inPlace_run h]
  exact nofun

/-- **No call rule sound under any order of write-back accepts more than
the rule of modes.overlapping-inout's.** Whatever the order in which copy-out writes the `inout` arguments
back, a call rule sound under it accepts only lists of `inout` shapes that
modes.overlapping-inout accepts. -/
theorem callRule_le_pairwiseDisjoint_anyOrder (w : WriteBack) (rule : CallRule) (h : rule.SoundWith w)
    (ss : List Shape) (hs : rule ss = true) : pairwiseDisjoint ss = true := by
  cases hp : pairwiseDisjoint ss with
  | true => rfl
  | false =>
    obtain ⟨a, b, extra, ho⟩ := overlap_of_not_pairwiseDisjoint hp
    exact absurd (h _ (witness_wellTyped ss a b extra ho) (witness_exclusiveWith rule hs) _)
      (witness_disagrees w ho)

/-- **No sound call rule accepts more than the rule of modes.overlapping-inout's.** A call rule that is
sound accepts only lists of `inout` shapes that modes.overlapping-inout accepts: no two of
them overlap. -/
theorem callRule_le_pairwiseDisjoint (rule : CallRule) (h : rule.Sound) (ss : List Shape)
    (hs : rule ss = true) : pairwiseDisjoint ss = true :=
  callRule_le_pairwiseDisjoint_anyOrder .leftToRight rule h ss hs

/-- **No call rule sound on programs without indexes accepts more than
the rule of modes.overlapping-inout's.** A call rule asked to be sound only on programs whose places hold
no index still accepts only lists of `inout` shapes that modes.overlapping-inout accepts. -/
theorem callRule_le_pairwiseDisjoint_indexFree (rule : CallRule) (h : rule.SoundIndexFree)
    (ss : List Shape) (hs : rule ss = true) : pairwiseDisjoint ss = true := by
  cases hp : pairwiseDisjoint ss with
  | true => rfl
  | false =>
    obtain ⟨a, b, extra, ho⟩ := overlap_of_not_pairwiseDisjoint hp
    exact absurd (h _ (witness_wellTyped ss a b extra ho) (witness_indexFree ss a b extra)
      (witness_exclusiveWith rule hs) _) (witness_disagrees .leftToRight ho)

/-- **The call rule of modes.overlapping-inout is the greatest sound call rule.** It is sound,
and every sound call rule accepts only what modes.overlapping-inout accepts. -/
theorem pairwiseDisjoint_greatest :
    CallRule.Sound pairwiseDisjoint ∧
      ∀ rule : CallRule, rule.Sound → ∀ ss, rule ss = true → pairwiseDisjoint ss = true :=
  ⟨pairwiseDisjoint_sound, callRule_le_pairwiseDisjoint⟩

/-- **The sound call rules are exactly those below the rule of modes.overlapping-inout's.** A call rule is
sound exactly when it accepts nothing that modes.overlapping-inout rejects. -/
theorem callRule_sound_iff (rule : CallRule) :
    rule.Sound ↔ ∀ ss, rule ss = true → pairwiseDisjoint ss = true :=
  ⟨callRule_le_pairwiseDisjoint rule, fun hle => pairwiseDisjoint_sound.of_le hle⟩

/-- A call rule sound under some order of write-back is sound under the order of values.inout-argument-order's's. -/
theorem CallRule.SoundWith.sound {w : WriteBack} {rule : CallRule} (h : rule.SoundWith w) :
    rule.Sound :=
  pairwiseDisjoint_sound.of_le (callRule_le_pairwiseDisjoint_anyOrder w rule h)

/-- Asking a call rule to be sound only on programs whose places hold no index
asks no less than asking it to be sound. -/
theorem CallRule.soundIndexFree_iff (rule : CallRule) : rule.SoundIndexFree ↔ rule.Sound :=
  ⟨fun h => pairwiseDisjoint_sound.of_le (callRule_le_pairwiseDisjoint_indexFree rule h),
    CallRule.Sound.indexFree⟩

/-- **A sound call rule compares the receiver.** The `inout` shapes of a
method call whose receiver is taken `inout self` start with the receiver's
(`inoutShapes_inoutReceiver`). A sound call rule rejects them when the receiver
overlaps one of the `inout` arguments, as modes.overlapping-inout does (modes.overlapping-inout). -/
theorem callRule_receiver (rule : CallRule) (h : rule.Sound) (s : Shape) (ss : List Shape)
    (hs : rule (s :: ss) = true) : ∀ t ∈ ss, s.overlaps t = false :=
  ((pairwiseDisjoint_cons_iff s ss).1 (callRule_le_pairwiseDisjoint rule h _ hs)).1

/-! ## A rule that saw indexes -/

namespace Optimality

open Counterexamples (declsWellFormed wellFormed_of_check instantiable_of_check
  passesOn_of_check noEscape_of_check)

/-- `fn alias(inout x: i64, inout y: i64) { x = 1; let r: i64 = [0][y] }`: the
witness's body for two places of type `i64`. It panics when `y` sees the write
to `x` (effects.panic-kinds; std.lists), and returns `()`. -/
def indexedCallee : FnDecl :=
  ⟨"alias", [], [], [⟨.inout, "x", .i64, none⟩, ⟨.inout, "y", .i64, none⟩], .unit, Row.pure,
    .seq (.assign ⟨"x", []⟩ (.int 1)) (.letIn "r" .i64 (probe (.var "y")) .unit), {}⟩

/-- `var xs = [0, 0]; alias(inout xs[0], inout xs[1])`. modes.overlap
removes the indexes, so the two places have the shape `xs`, and modes.overlapping-inout rejects
the call. -/
def indexed : Program :=
  ⟨⟨[], [], [indexedCallee], [], [], [], [], []⟩,
    .varIn "xs" (.list .i64) (.list .i64 [.int 0, .int 0])
      (.call (.fnRef "alias" [] [])
        [.inout ⟨"xs", [.index (.int 0)]⟩, .inout ⟨"xs", [.index (.int 1)]⟩] .unit),
    Row.pure, {}, {}⟩

theorem indexed_wellTyped : indexed.WellTyped where
  decls := declsWellFormed (by decide) (by decide) (by simp [indexed]) ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Decls.receivers_of_nil rfl (by decide))
  fns := by
    intro d hd
    apply FnDecl.WellTyped.lenient
    simp only [indexed, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    exact ⟨.unit, .seq (.assign (.mk rfl .nil) (.int (by decide)) (.refl _)) (.refl _)
      (probe_hasType (.var rfl)), .refl _⟩
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  noEscape := noEscape_of_check (by decide)
  main := by
    have hcallee :
        HasType indexed.decls .closed [("xs", ⟨.list .i64, true⟩)]
        ⟨Row.pure, false, false, .unit, false, false⟩
        (.fnRef "alias" [] []) (indexedCallee.type.substRows (indexedCallee.rowParams.zip [])) :=
      .fnRef (types := []) rfl rfl (instantiable_of_check (by decide)) (by decide) (wellFormed_of_check (by decide))
        (passesOn_of_check (by decide)) .nil
    have hplace : ∀ k : Int, IntTy.i64.Contains k →
        PlaceFits indexed.decls .closed [("xs", ⟨.list .i64, true⟩)]
        ⟨Row.pure, false, false, .unit, false, false⟩ ⟨"xs", [.index (.int k)]⟩ .i64 :=
      fun _ hk => .mk rfl (.index (.int hk) (.refl _) .nil)
    exact ⟨.unit, .varIn (wellFormed_of_check (by decide))
      (.list (wellFormed_of_check (by decide))
        (.cons (.int (by decide)) (.refl _) (.cons (.int (by decide)) (.refl _) .nil)))
      (.refl _)
      (.call hcallee (.inout (hplace 0 (by decide)) (.inout (hplace 1 (by decide)) .nil))
        ⟨.refl _, fun h => (nomatch h), fun h => (nomatch h), rfl⟩), .refl _⟩

/-- modes.overlapping-inout rejects the call. -/
theorem indexed_not_exclusive : ¬indexed.Exclusive := by
  rintro ⟨_, h⟩
  exact absurd h (by decide)

/-- Its places hold indexes, so `callRule_le_pairwiseDisjoint_indexFree` asks nothing of
a call rule on it. -/
theorem indexed_not_indexFree : ¬indexed.IndexFree := by
  rintro ⟨_, h⟩
  exact absurd h (by decide)

/-- Yet the places are disjoint: `y` doesn't see the write to `x`, and both
models return `()`, where the witness panics in place. A rule that saw the
values of indexes could accept this call; `callRule_le_pairwiseDisjoint` is about rules
that see shapes. -/
theorem indexed_runs :
    (indexed.runCopy 16).observe = .returned .unit ∧
      (indexed.runInPlace 16).observe = .returned .unit :=
  ⟨rfl, rfl⟩

end Optimality

end Stilt
