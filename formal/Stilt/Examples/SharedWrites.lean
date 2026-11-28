import Stilt.Accepted
import Stilt.Sharing.Eval
import Stilt.Counterexamples.Checks

/-!
# Shared writes that sharing copies first

Programs of the core calculus in which a copy of a binding into another shares its storage
(`Program.runSharing`) and a later write to one of them would reach storage that another binding
reads after it. Each is well typed and obeys the law of exclusivity, so each is a program the
checker accepts; the inference of modes.shared-writes calls the write `shared`, so sharing
copies first, and shows what copies show:

* `writtenBack`: a `var` whose value is a copy of an `inout` parameter is written, and the
  parameter is named nowhere after the write; its caller reads the parameter's final value
  when the call returns (values.inout-arguments), so the parameter is read when the body ends;
* `selfPart`: a `var` is assigned a part of its own value, which a copy made before the
  assignment holds too, and is then written; the assignment's value holds a part of the
  binding, so the copy still counts.

`main` returns `()` (program.main), so each raises what it reads.
-/

namespace Stilt.Examples.SharedWrites

open Stilt.Counterexamples

private def listTy : Ty := .list .i64

private def ints (ns : List Int) : Expr := .list .i64 (ns.map .int)

/-! ## A copy of an `inout` parameter written -/

/-- `fn grow(inout a: List<i64>) { var b = a; b[0] = 1 }`. -/
def grow : FnDecl :=
  ⟨"grow", [], [], [⟨.inout, "a", listTy, none⟩], .unit, Row.pure,
    .varIn "b" listTy (.var "a") (.assign ⟨"b", [.index (.int 0)]⟩ (.int 1)), {}⟩

/-- `var xs = [0]; grow(inout xs); raise xs[0]`, in a `main` whose row is `raise<i64>`. -/
def writtenBack : Program :=
  ⟨⟨[], [], [grow], [], [], [], [], []⟩,
    .varIn "xs" listTy (ints [0])
      (.seq (.call (.fnRef "grow" [] []) [.inout ⟨"xs", []⟩] .unit)
        (.raise (.index (.var "xs") (.int 0)))),
    ⟨false, some .i64, [], [], none⟩, {}, {}⟩

theorem writtenBack_wellTyped : writtenBack.WellTyped where
  decls := declsWellFormed (by decide) (by decide) (by simp [writtenBack]) ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Decls.receivers_of_nil rfl (by decide))
  fns := by
    intro d hd
    apply FnDecl.WellTyped.lenient
    simp only [writtenBack, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    exact ⟨.unit, .varIn (wellFormed_of_check (by decide)) (.var rfl) (.refl _)
      (.assign (.mk rfl (.index (.int (by decide)) (.refl _) .nil)) (.int (by decide)) (.refl _)),
      .refl _⟩
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  main := by
    have hcallee :
        HasType writtenBack.decls .closed [("xs", ⟨listTy, true⟩)]
          ⟨writtenBack.row, false, false, .unit, false, false⟩
        (.fnRef "grow" [] []) (grow.type.substRows (grow.rowParams.zip [])) :=
      .fnRef (types := []) rfl rfl (instantiable_of_check (by decide)) (by decide)
        (wellFormed_of_check (by decide)) (passesOn_of_check (by decide)) .nil
    exact ⟨.never, .varIn (wellFormed_of_check (by decide))
      (.list (wellFormed_of_check (by decide)) (.cons (.int (by decide)) (.refl _) .nil))
      (.refl _)
      (.seq (.call hcallee (.inout (.mk rfl .nil) .nil)
        ⟨Row.pure_within _, fun h => (nomatch h), fun h => (nomatch h), rfl⟩) (.refl _)
        (.raise rfl (.index (.var rfl) (.int (by decide)) (.refl _)) (.refl _))), .never _⟩
  noEscape := noEscape_of_check (by decide)

theorem writtenBack_exclusive : writtenBack.Exclusive := by
  refine ⟨fun d hd => ?_, by decide⟩
  simp only [writtenBack, Decls.fns_mk, List.mem_singleton] at hd
  subst hd
  decide

/-- The walk of `a` finds `b` shared (modes.shared-writes): `a` is read when the body ends. -/
theorem grow_shared : writtenBack.modeEnv.bodyShared grow.params grow.body = ["b"] := by
  decide

/-- Both raise 0, what `xs` holds after `grow` gives it back: sharing copies `b` before the
write. -/
theorem writtenBack_runs :
    (writtenBack.runCopy 20).observe = .raised (.int 0) ∧
      (writtenBack.runSharing 20).observe = .raised (.int 0) :=
  ⟨rfl, rfl⟩

/-! ## A binding assigned a part of its own value -/

private def treeTy : Ty := .record "Tree" []

/-- `type Tree = { items: List<i64>, kids: List<Tree> }`. -/
def treeDecl : RecordDecl := ⟨"Tree", [("items", listTy), ("kids", .list treeTy)], []⟩

/-- `Tree { items: [i], kids }`. -/
private def tree (i : Int) (kids : List Expr) : Expr :=
  .record "Tree" [] [("items", ints [i]), ("kids", .list treeTy kids)]

/-- The rest of `selfPart` after `z` is bound: `x = x.kids[0]; x.items[0] = 9;
raise z.kids[0].items[0]`. -/
def descend : Expr :=
  .seq (.assign ⟨"x", []⟩ (.index (.field (.var "x") "kids") (.int 0)))
    (.seq (.assign ⟨"x", [.field "items", .index (.int 0)]⟩ (.int 9))
      (.raise (.index (.field (.index (.field (.var "z") "kids") (.int 0)) "items") (.int 0))))

/-- `var x = Tree { items: [1], kids: [Tree { items: [2], kids: [] }] }; let z = x;
x = x.kids[0]; x.items[0] = 9; raise z.kids[0].items[0]`, in a `main` whose row is
`raise<i64>`. -/
def selfPart : Program :=
  ⟨⟨[treeDecl], [], [], [], [], [], [], []⟩,
    .varIn "x" treeTy (tree 1 [tree 2 []]) (.letIn "z" treeTy (.var "x") descend),
    ⟨false, some .i64, [], [], none⟩, {}, {}⟩

theorem selfPart_wellTyped : selfPart.WellTyped where
  decls := declsWellFormed (by decide) (by decide) (by unfold Ty.Closed; decide)
    ⟨rfl, rfl, rfl, rfl⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
    (Decls.receivers_of_nil rfl (by decide))
  fns := fun _ h => nomatch h
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  main := by
    have hint : ∀ {Γ : Ctx} {fx : Effects} (n : Int), IntTy.i64.Contains n →
        HasType selfPart.decls .closed Γ fx (.int n) .i64 := fun _ h => .int h
    have htree : ∀ {Γ : Ctx} {fx : Effects} (i : Int) (kids : List Expr),
        IntTy.i64.Contains i →
        ExprsFit selfPart.decls .closed Γ fx kids (List.replicate kids.length treeTy) →
        HasType selfPart.decls .closed Γ fx (tree i kids) treeTy := fun i kids hi hk =>
      .record rfl rfl (fun _ h => nomatch h) (.refl _) (.cons rfl (.list (wellFormed_of_check (by decide))
        (.cons (hint i hi) (.refl _) .nil)) (.refl _)
        (.cons rfl (.list (wellFormed_of_check (by decide)) hk) (.refl _) .nil))
    exact ⟨.never, .varIn (wellFormed_of_check (by decide))
      (htree 1 _ (by decide) (.cons (htree 2 [] (by decide) .nil) (.refl _) .nil)) (.refl _)
      (.letIn (wellFormed_of_check (by decide)) (.var rfl) (.refl _)
        (.seq (.assign (.mk rfl .nil) (.index (.field (.var rfl) rfl rfl rfl) (hint _ (by decide))
            (.refl _)) (.refl _)) (.refl _)
          (.seq (.assign (.mk rfl (.field rfl rfl rfl (.index (hint _ (by decide)) (.refl _) .nil)))
              (hint _ (by decide)) (.refl _)) (.refl _)
            (.raise rfl (.index (.field (.index (.field (.var rfl) rfl rfl rfl) (hint _ (by decide))
              (.refl _)) rfl rfl rfl) (hint _ (by decide)) (.refl _)) (.refl _))))), .never _⟩
  noEscape := noEscape_of_check (by decide)

theorem selfPart_exclusive : selfPart.Exclusive :=
  ⟨fun _ h => (nomatch h), by decide⟩

/-- The inference calls `x` shared (modes.shared-writes): the value assigned to its whole holds a
part of it, so the copy `z` holds still counts. -/
theorem selfPart_shared : selfPart.modeEnv.bodyShared [] selfPart.main = ["x"] := by
  decide

/-- Both raise 2, the element `z` copied: sharing copies `x` before the write. -/
theorem selfPart_runs :
    (selfPart.runCopy 20).observe = .raised (.int 2) ∧
      (selfPart.runSharing 20).observe = .raised (.int 2) :=
  ⟨rfl, rfl⟩

end Stilt.Examples.SharedWrites
