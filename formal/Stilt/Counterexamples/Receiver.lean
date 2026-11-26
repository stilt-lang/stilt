import Stilt.Receivers
import Stilt.Optimality.Rule
import Stilt.Counterexamples.Checks

/-!
# An `inout` argument that overlaps an `inout self` receiver

A program that shows that modes.overlapping-inout needs its receiver clause: a
well-typed method call whose `inout` argument overlaps its `inout self`
receiver, `a.f(inout a.b)`, tells copy-in, copy-out from in-place mutation.
Its arguments other than the receiver don't overlap one another, and it has no
loop, so the receiver clause is the only part of modes.overlapping-inout that rejects it. A call
rule that never compares a call's first `inout` shape, the receiver of a
method call, with the others is therefore unsound.
-/

namespace Stilt.Counterexamples

/-- `type A = { b: i64 }`. -/
def aType : RecordDecl := ⟨"A", [("b", .i64)], []⟩

/-- `fn f(inout self, inout b: i64) -> i64 { b = 1; self.b }`. -/
def peek : FnDecl :=
  ⟨"f", [], [], [⟨.inout, selfName, .record "A" [], none⟩, ⟨.inout, "b", .i64, none⟩], .i64,
    Row.pure, .seq (.assign ⟨"b", []⟩ (.int 1)) (.field (.var selfName) "b"), {}⟩

/-- `impl A { fn f(inout self, inout b: i64) -> i64 { … } }` (traits.impl-blocks). -/
def aImpl : ImplDecl := ⟨"A", [peek]⟩

/-- `var a = A { b: 0 }; raise a.f(inout a.b)`, in a `main` whose row is
`raise<i64>`. modes.overlapping-inout rejects the call. -/
def receiverAliased : Program :=
  ⟨⟨[aType], [], [], [aImpl], [], [], []⟩,
    .varIn "a" (.record "A" []) (.record "A" [] [("b", .int 0)])
      (.raise (Expr.methodCall "A" "f" [] (.inout ⟨"a", []⟩) [.inout ⟨"a", [.field "b"]⟩] .i64)),
    ⟨false, some .i64, [], [], none⟩, {}⟩

theorem receiverAliased_receivers : receiverAliased.decls.Receivers where
  types := by decide
  functions := by decide
  later := by decide
  first := by
    intro i hi d hd p hp _
    simp only [receiverAliased, aImpl, List.mem_singleton] at hi
    subst hi
    simp only [List.mem_singleton] at hd
    subst hd
    simp only [peek, List.take, List.mem_singleton] at hp
    subst hp
    rfl

theorem receiverAliased_wellTyped : receiverAliased.WellTyped where
  decls := declsWellFormed (by decide) (by decide) (by unfold Ty.Closed; decide) ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide) receiverAliased_receivers
  fns := by
    intro d hd
    apply FnDecl.WellTyped.lenient
    simp only [receiverAliased, Decls.fns, ImplDecl.members, aImpl, List.flatMap_cons,
      List.flatMap_nil, List.map_cons, List.map_nil, List.nil_append, List.append_nil,
      List.mem_singleton] at hd
    subst hd
    exact ⟨.i64, .seq (.assign (.mk rfl .nil) (.int (by decide)) (.refl _)) (.refl _)
      (.field (.var rfl) rfl rfl rfl), .refl _⟩
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  main := by
    have hcallee :
        HasType receiverAliased.decls .closed [("a", ⟨.record "A" [], true⟩)]
          ⟨receiverAliased.row, false, false, .unit, false, false⟩ (.fnRef (qualify "A" "f") [] [])
          ((peek.qualify "A").type.substRows ((peek.qualify "A").rowParams.zip [])) :=
      .fnRef (types := []) rfl rfl (instantiable_of_check (by decide)) (by decide) (wellFormed_of_check (by decide))
        (passesOn_of_check (by decide)) .nil
    exact ⟨.never, .varIn (wellFormed_of_check (by decide))
      (.record rfl rfl (fun _ h => nomatch h) (List.Perm.refl _) (.cons rfl (.int (by decide)) (.refl _) .nil)) (.refl _)
      (.raise rfl (.call hcallee
        (.inout (.mk rfl .nil) (.inout (.mk rfl (.field rfl rfl rfl .nil)) .nil))
        ⟨Row.pure_within _, fun h => (nomatch h), fun h => (nomatch h), rfl⟩) (.refl _)), .never _⟩
  noEscape := noEscape_of_check (by decide)

/-- The law of exclusivity rejects the call. -/
theorem receiverAliased_not_exclusive : ¬receiverAliased.Exclusive := by
  rintro ⟨_, h⟩
  exact absurd h (by decide)

/-- A call rule that compares every two `inout` arguments of a call but never
its first `inout` shape with the others: modes.overlapping-inout without its receiver
clause, at a method call. -/
def withoutReceiver : CallRule := fun ss => pairwiseDisjoint ss.tail

/-- Only the receiver clause rejects the call: under the rule without it, the
program obeys the law. -/
theorem receiverAliased_exclusiveWithout : receiverAliased.ExclusiveWith withoutReceiver :=
  ⟨by decide, by decide⟩

/-- Copy-in, copy-out gives `self` the value `a` had when the call started, so
`self.b` reads 0 after `b = 1`, and `main` raises 0. In place, `self.b` and
`b` are both `a.b`, so `main` raises 1. -/
theorem receiverAliased_runs :
    (receiverAliased.runCopy 16).observe = .raised (.int 0) ∧
      (receiverAliased.runInPlace 16).observe = .raised (.int 1) :=
  ⟨rfl, rfl⟩

/-- **modes.overlapping-inout needs its receiver clause.** A call rule that never compares the
receiver of a method call with its `inout` arguments is unsound: a well-typed
program that obeys it tells the two models apart. -/
theorem receiver_clause_needed : ¬withoutReceiver.Sound := by
  intro h
  have hagree := h receiverAliased receiverAliased_wellTyped receiverAliased_exclusiveWithout 16
  rw [receiverAliased_runs.1, receiverAliased_runs.2] at hagree
  exact nomatch hagree

end Stilt.Counterexamples
