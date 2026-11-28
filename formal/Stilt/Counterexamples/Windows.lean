import Stilt.Exclusivity
import Stilt.ViewReads
import Stilt.ViewContained
import Stilt.Windows.Eval
import Stilt.Counterexamples.Checks

/-!
# Windows that read a change or freed storage

Programs of the core calculus that tell copies from windows (`Program.runWindows`), as
`Stilt.Counterexamples.Aliasing` tells copies from in-place mutation. Each is well typed and
obeys the law of exclusivity, and breaks one of the two rules that keep a view's window reading
what a copy of its part holds:

* `viewChanged` changes a source while a view of it lives, which views.change-while-viewed
  rejects (E0423): the window reads the change, and the copy doesn't;
* `viewEscaped` returns a view of a local, which views.escaping rejects (E0422): the window
  reads storage that the local's scope freed, which is stuck.

`main` returns `()` (program.main), so each raises what it reads through its view.
-/

namespace Stilt.Counterexamples

private def listTy : Ty := .list .i64

private def ints (ns : List Int) : Expr := .list .i64 (ns.map .int)

/-! ## A source changed while a view reads it -/

/-- `var xs = [1, 2, 3]; let v = View.of(xs, 0, 3); xs[0] = 9; raise v.copy()[0]`, in a `main`
whose row is `raise<i64>`. views.change-while-viewed rejects the assignment. -/
def viewChanged : Program :=
  ⟨⟨[], [], [], [], [], [], [], []⟩,
    .varIn "xs" listTy (ints [1, 2, 3])
      (.letIn "v" (.view listTy) (.view [.var "xs", .int 0, .int 3])
        (.seq (.assign ⟨"xs", [.index (.int 0)]⟩ (.int 9))
          (.raise (.index (.op .copy [.var "v"]) (.int 0))))),
    ⟨false, some .i64, [], [], none⟩, {}, {}⟩

theorem viewChanged_wellTyped : viewChanged.WellTyped where
  decls := declsWellFormed (by decide) (by decide) (by simp [viewChanged]) ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Decls.receivers_of_nil rfl (by decide))
  fns := fun _ h => nomatch h
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  main := by
    have hint : ∀ {Γ : Ctx} {fx : Effects} (n : Int), IntTy.i64.Contains n →
        HasType viewChanged.decls .closed Γ fx (.int n) .i64 := fun _ h => .int h
    refine ⟨.never, .varIn (wellFormed_of_check (by decide))
      (.list (wellFormed_of_check (by decide))
        (.cons (hint _ (by decide)) (.refl _) (.cons (hint _ (by decide)) (.refl _)
          (.cons (hint _ (by decide)) (.refl _) .nil)))) (.refl _)
      (.letIn (wellFormed_of_check (by decide))
        (.view (.viewOf rfl) (.cons (.var rfl) (.refl _) (.cons (hint _ (by decide)) (.refl _)
          (.cons (hint _ (by decide)) (.refl _) .nil)))) (.refl _)
        (.seq (.assign (.mk rfl (.index (hint _ (by decide)) (.refl _) .nil)) (hint _ (by decide))
          (.refl _)) (.refl _)
          (.raise rfl (.index (.op .copy (.cons (.var rfl) (.refl _) .nil) (Op.keysIn_of_nil rfl) (Op.boundsIn_of_nil rfl) (Op.noIo rfl))
            (hint _ (by decide)) (.refl _)) (.refl _)))), .never _⟩
  noEscape := noEscape_of_check (by decide)

theorem viewChanged_exclusive : viewChanged.Exclusive :=
  ⟨fun _ h => (nomatch h), by decide⟩

theorem viewChanged_contained : viewChanged.ViewsContained :=
  ⟨fun _ h => (nomatch h), by decide⟩

/-- views.change-while-viewed rejects the assignment to `xs` while `v` lives (E0423). -/
theorem viewChanged_not_read : ¬viewChanged.ViewsRead := by
  rintro ⟨_, h⟩
  exact absurd h (by decide)

/-- The copy raises the element it copied, 1; the window reads the change, 9. -/
theorem viewChanged_runs :
    (viewChanged.runCopy 20).observe = .raised (.int 1) ∧
      (viewChanged.runWindows 20).observe = .raised (.int 9) :=
  ⟨rfl, rfl⟩

/-- Windows need views.change-while-viewed: without it, a well-typed program that obeys the
law of exclusivity and whose views stay in their sources' scopes tells copies from windows. -/
theorem viewsRead_needed :
    ¬∀ (p : Program) (fuel : Nat), p.WellTyped → p.Exclusive → p.ViewsContained →
      (p.runCopy fuel).observe = (p.runWindows fuel).observe := by
  intro h
  have hagree := h viewChanged 20 viewChanged_wellTyped viewChanged_exclusive
    viewChanged_contained
  rw [viewChanged_runs.1, viewChanged_runs.2] at hagree
  exact nomatch hagree

/-! ## A view of a local returned -/

/-- `fn f() -> View<List<i64>> { var ys = [1, 2]; View.of(ys, 0, 1) }`. -/
def escaping : FnDecl :=
  ⟨"f", [], [], [], .view listTy, Row.pure,
    .varIn "ys" listTy (ints [1, 2]) (.view [.var "ys", .int 0, .int 1]), {}⟩

/-- `raise f().copy()`, in a `main` whose row is `raise<List<i64>>`. views.escaping rejects
`f`'s result, which views its local `ys`. -/
def viewEscaped : Program :=
  ⟨⟨[], [], [escaping], [], [], [], [], []⟩,
    .raise (.op .copy [.call (.fnRef "f" [] []) [] (.view listTy)]),
    ⟨false, some listTy, [], [], none⟩, {}, {}⟩

theorem viewEscaped_wellTyped : viewEscaped.WellTyped where
  decls := declsWellFormed (by decide) (by decide) (by simp [viewEscaped]) ⟨rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (Decls.receivers_of_nil rfl (by decide))
  fns := by
    intro d hd
    apply FnDecl.WellTyped.lenient
    simp only [viewEscaped, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    have hint : ∀ {Γ : Ctx} {fx : Effects} (n : Int), IntTy.i64.Contains n →
        HasType viewEscaped.decls escaping.scope Γ fx (.int n) .i64 := fun _ h => .int h
    exact ⟨.view listTy, .varIn (wellFormed_of_check (by decide))
      (.list (wellFormed_of_check (by decide))
        (.cons (hint _ (by decide)) (.refl _) (.cons (hint _ (by decide)) (.refl _) .nil)))
      (.refl _)
      (.view (.viewOf rfl) (.cons (.var rfl) (.refl _) (.cons (hint _ (by decide)) (.refl _)
        (.cons (hint _ (by decide)) (.refl _) .nil)))), .refl _⟩
  closed := by unfold Ty.Closed; decide
  unhandled := ⟨rfl, rfl⟩
  main := by
    have hcallee :
        HasType viewEscaped.decls .closed []
          ⟨viewEscaped.row, false, false, .unit, false, false⟩
        (.fnRef "f" [] []) (escaping.type.substRows (escaping.rowParams.zip [])) :=
      .fnRef (types := []) rfl rfl (instantiable_of_check (by decide)) (by decide)
        (wellFormed_of_check (by decide)) (passesOn_of_check (by decide)) .nil
    exact ⟨.never, .raise rfl (.op .copy (.cons (.call hcallee .nil
      ⟨Row.pure_within _, fun h => (nomatch h), fun h => (nomatch h), rfl⟩) (.refl _) .nil)
      (Op.keysIn_of_nil rfl) (Op.boundsIn_of_nil rfl) (Op.noIo rfl)) (.refl _), .never _⟩
  noEscape := noEscape_of_check (by decide)

theorem viewEscaped_exclusive : viewEscaped.Exclusive := by
  refine ⟨fun d hd => ?_, by decide⟩
  simp only [viewEscaped, Decls.fns_mk, List.mem_singleton] at hd
  subst hd
  decide

theorem viewEscaped_read : viewEscaped.ViewsRead := by
  refine ⟨fun d hd => ?_, by decide⟩
  simp only [viewEscaped, Decls.fns_mk, List.mem_singleton] at hd
  subst hd
  decide

/-- views.escaping rejects `f`'s result, which views its local `ys` (E0422). -/
theorem viewEscaped_not_contained : ¬viewEscaped.ViewsContained := by
  rintro ⟨h, _⟩
  exact absurd (h escaping (by simp [viewEscaped])).2 (by decide)

/-- The copy raises the part it copied; the window reads `ys` after `f`'s scope freed it, which
is stuck. -/
theorem viewEscaped_runs :
    (viewEscaped.runCopy 20).observe = .raised (.list [.int 1]) ∧
      (viewEscaped.runWindows 20).observe = .stuck :=
  ⟨rfl, rfl⟩

/-- Windows need views.escaping: without it, a well-typed program that obeys the law of
exclusivity and changes no source while a view reads it tells copies from windows. -/
theorem viewsContained_needed :
    ¬∀ (p : Program) (fuel : Nat), p.WellTyped → p.Exclusive → p.ViewsRead →
      (p.runCopy fuel).observe = (p.runWindows fuel).observe := by
  intro h
  have hagree := h viewEscaped 20 viewEscaped_wellTyped viewEscaped_exclusive viewEscaped_read
  rw [viewEscaped_runs.1, viewEscaped_runs.2] at hagree
  exact nomatch hagree

end Stilt.Counterexamples
