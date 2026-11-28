import Stilt.Sharing.Eval

/-!
# Shared writes along the paths execution takes

Programs of the core calculus in which a copy of a binding shares its storage
(`Program.runSharing`) and a later write to one of them would reach storage that another binding
reads after it, where only the paths execution takes, not the order of the source, show the
copy still held. The inference of modes.shared-writes calls each such write `shared`, so sharing
copies first, and shows what copies show:

* `poppedSource`: two bindings hold copies of a third, whose scope ends before one of them is
  written and the other read;
* `breakSkips`: a `break` skips the assignment that would replace a copy before a write;
* `loopCarries`: a turn of a loop writes a binding that holds a copy given by the turn before;
* `caughtCopy`: a copy of a `catch`'s binder is written while the binder is read after;
* `shadowed`: a program that binds a name twice, in which every binding is shared.

`main` returns `()` (program.main), so each raises what it reads.
-/

namespace Stilt.Examples.SharedWritesFlow

private def listTy : Ty := .list .i64

private def ints (ns : List Int) : Expr := .list .i64 (ns.map .int)

/-- `x[0] = v`. -/
private def setFirst (x : Name) (v : Int) : Expr := .assign ⟨x, [.index (.int 0)]⟩ (.int v)

/-- `raise x[0]`. -/
private def raiseFirst (x : Name) : Expr := .raise (.index (.var x) (.int 0))

/-- A `main` whose row is `raise<i64>`. -/
private def program (main : Expr) : Program :=
  ⟨⟨[], [], [], [], [], [], [], []⟩, main, ⟨false, some .i64, [], [], none⟩, {}, {}⟩

/-- `var w = [1]; var z = [0]; if true { var u = [5]; w = u; z = u }; z[0] = 9; raise w[0]`. -/
def poppedSource : Program := program <|
  .varIn "w" listTy (ints [1]) <| .varIn "z" listTy (ints [0]) <|
    .seq (.if (.bool true) .unit (.varIn "u" listTy (ints [5])
        (.seq (.assign ⟨"w", []⟩ (.var "u")) (.assign ⟨"z", []⟩ (.var "u")))) .unit)
      (.seq (setFirst "z" 9) (raiseFirst "w"))

/-- The walk of `u` goes on after its scope ends, where `w` is read after `z` is written. -/
theorem poppedSource_shared : poppedSource.sharedNames = ["z"] := by decide +kernel

theorem poppedSource_runs :
    (poppedSource.runCopy 20).observe = .raised (.int 5) ∧
      (poppedSource.runSharing 20).observe = .raised (.int 5) :=
  ⟨rfl, rfl⟩

/-- `var x = [5]; var w = [1]; loop { if true { w = x; break }; w = [1] }; w[0] = 9;
raise x[0]`. -/
def breakSkips : Program := program <|
  .varIn "x" listTy (ints [5]) <| .varIn "w" listTy (ints [1]) <|
    .seq (.loop (.seq (.if (.bool true) .unit (.seq (.assign ⟨"w", []⟩ (.var "x")) .break) .unit)
        (.assign ⟨"w", []⟩ (ints [1]))))
      (.seq (setFirst "w" 9) (raiseFirst "x"))

/-- What the walk knows at the `break` joins what it knows after the loop. -/
theorem breakSkips_shared : breakSkips.sharedNames = ["w"] := by decide +kernel

theorem breakSkips_runs :
    (breakSkips.runCopy 20).observe = .raised (.int 5) ∧
      (breakSkips.runSharing 20).observe = .raised (.int 5) :=
  ⟨rfl, rfl⟩

/-- `var x = [5]; var w = [1]; var y = [2]; var c = false;
loop { w[0] = 9; if c { raise y[0] }; w = x; y = x; c = true }`. -/
def loopCarries : Program := program <|
  .varIn "x" listTy (ints [5]) <| .varIn "w" listTy (ints [1]) <|
    .varIn "y" listTy (ints [2]) <| .varIn "c" .bool (.bool false) <|
      .loop (.seq (setFirst "w" 9) (.seq (.if (.var "c") .unit (raiseFirst "y") .unit)
        (.seq (.assign ⟨"w", []⟩ (.var "x")) (.seq (.assign ⟨"y", []⟩ (.var "x"))
          (.assign ⟨"c", []⟩ (.bool true))))))

/-- Whether an observation raises the integer `n`: a check the kernel evaluates by
`decide +kernel`, where `rfl` would have the elaborator unfold a whole run, which took 20 s and
14 GB. -/
private def raisesInt (n : Int) : Observation → Bool
  | .raised (.int m) => m == n
  | _ => false

private theorem of_raisesInt {o : Observation} {n : Int} (h : raisesInt n o = true) :
    o = .raised (.int n) := by
  cases o with
  | raised e => cases e <;> simp_all [raisesInt]
  | _ => simp [raisesInt] at h

/-- At the head of the loop, `w` and `y` hold the copies the turn before gave them. -/
theorem loopCarries_shared : loopCarries.sharedNames = ["w", "w"] := by decide +kernel

theorem loopCarries_runs :
    (loopCarries.runCopy 12).observe = .raised (.int 5) ∧
      (loopCarries.runSharing 12).observe = .raised (.int 5) := by
  refine ⟨rfl, ?_⟩
  unfold Program.runSharing
  rw [Program.isShared_of_nodup _ (by decide +kernel), loopCarries_shared]
  exact of_raisesInt (by decide +kernel)

/-- `try { raise [1, 2] } catch e => { var z = e; z[0] = 9; raise e[0] }`, the body raising a
`List<i64>`. -/
def caughtCopy : Program := program <|
  .tryCatch (.raise (ints [1, 2])) listTy "e"
    (.varIn "z" listTy (.var "e") (.seq (setFirst "z" 9) (raiseFirst "e"))) .never

/-- The walk of the `catch`'s binder finds `z` shared. -/
theorem caughtCopy_shared : caughtCopy.sharedNames = ["z"] := by decide +kernel

theorem caughtCopy_runs :
    (caughtCopy.runCopy 20).observe = .raised (.int 1) ∧
      (caughtCopy.runSharing 20).observe = .raised (.int 1) :=
  ⟨rfl, rfl⟩

/-- `var u = [1]; var w = u; { let w = 5; var z = u; z[0] = 9 }; raise w[0]`. -/
def shadowed : Program := program <|
  .varIn "u" listTy (ints [1]) <| .varIn "w" listTy (.var "u") <|
    .seq (.letIn "w" .i64 (.int 5) (.varIn "z" listTy (.var "u") (setFirst "z" 9)))
      (raiseFirst "w")

/-- It binds `w` twice, so every binding is shared. -/
theorem shadowed_shared : shadowed.sharedNames = ["u", "w", "w", "z"] := by decide +kernel

theorem shadowed_runs :
    (shadowed.runCopy 20).observe = .raised (.int 1) ∧
      (shadowed.runSharing 20).observe = .raised (.int 1) :=
  ⟨rfl, rfl⟩

end Stilt.Examples.SharedWritesFlow
