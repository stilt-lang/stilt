/-!
# Calls that a handler ends

handlers.call-that-handler-ends: a call that a handler ends, by never resuming, ends as a raise
ends it, and each `inout` argument holds what the callee wrote before the
performance. The model is a callee whose body is a list of steps on its
`inout` parameters, each a place of a store: a write, or a performance, which
the handler resumes or ends the call at. The compiler writes the places
themselves; the reference interpreter copies them in when the call starts and writes them back
when it ends, however it ends. `ended_agree` proves that both leave the same
store, whether the handler resumes or ends the call, and `unwritten_differ`
that leaving the write-back out when the handler ends the call, as the reference interpreter
once did, leaves another one.
-/

namespace Stilt.Interactions.Ended

/-- A store, from places to values. -/
abbrev Store := Nat → Int

/-- `s` with the place `p` holding `v`. -/
def Store.set (s : Store) (p : Nat) (v : Int) : Store :=
  fun q => if q = p then v else s q

/-- A step of the callee's body: adding `d` to the place `p`, one of its
`inout` parameters, or performing an operation. -/
inductive Step where
  | add (p : Nat) (d : Int)
  | perform

/-- Runs the steps on a store: a performance goes on when the handler resumes
it, and ends the call when it doesn't. -/
def run (resumes : Bool) : List Step → Store → Store
  | [], s => s
  | .add p d :: rest, s => run resumes rest (s.set p (s p + d))
  | .perform :: rest, s => if resumes then run resumes rest s else s

/-- The body writes only the places in `ps`, its parameters. -/
def Writes (ps : List Nat) : List Step → Prop
  | [] => True
  | .add p _ :: rest => p ∈ ps ∧ Writes ps rest
  | .perform :: rest => Writes ps rest

/-- Writing the places `ps` of the frame `f` back into `s`, from left to
right. -/
def writeBack : List Nat → Store → Store → Store
  | [], _, s => s
  | p :: ps, f, s => writeBack ps f (s.set p (f p))

/-- In place: the call writes the store itself. -/
def inPlace (resumes : Bool) (body : List Step) (s : Store) : Store :=
  run resumes body s

/-- Copy-in, copy-out: the call runs on a copy, written back however it ends
(values.inout-arguments and values.inout-argument-order; handlers.call-that-handler-ends). -/
def copied (ps : List Nat) (resumes : Bool) (body : List Step) (s : Store) :
    Store :=
  writeBack ps (run resumes body s) s

theorem writeBack_apply (ps : List Nat) (f : Store) :
    ∀ (s : Store) (q : Nat), writeBack ps f s q = if q ∈ ps then f q else s q := by
  induction ps with
  | nil => intro s q; simp [writeBack]
  | cons p ps ih =>
    intro s q
    simp only [writeBack, ih, Store.set, List.mem_cons]
    by_cases hq : q ∈ ps
    · simp [hq]
    · by_cases hp : q = p
      · subst hp; simp
      · simp [hq, hp]

/-- A place that the body doesn't write keeps its value. -/
theorem run_outside (ps : List Nat) (resumes : Bool) :
    ∀ (body : List Step) (s : Store) (q : Nat), Writes ps body → q ∉ ps →
      run resumes body s q = s q := by
  intro body
  induction body with
  | nil => intro s q _ _; rfl
  | cons step rest ih =>
    intro s q hw hq
    cases step with
    | add p d =>
      simp only [Writes] at hw
      simp only [run]
      rw [ih _ q hw.2 hq]
      have hne : q ≠ p := fun h => hq (h ▸ hw.1)
      simp [Store.set, hne]
    | perform =>
      simp only [Writes] at hw
      simp only [run]
      cases resumes
      · rfl
      · exact ih s q hw hq

/-- handlers.call-that-handler-ends: copy-in, copy-out with the write-back on every end leaves
the store that writing in place leaves, whether the handler resumes the call or
ends it. -/
theorem ended_agree (ps : List Nat) (resumes : Bool) (body : List Step)
    (s : Store) (h : Writes ps body) :
    copied ps resumes body s = inPlace resumes body s := by
  funext q
  simp only [copied, inPlace]
  rw [writeBack_apply]
  by_cases hq : q ∈ ps
  · simp [hq]
  · simp [hq, run_outside ps resumes body s q h hq]

/-- Without the write-back when the handler ends the call, the store keeps
what it held before the call: `bump` of handlers.call-that-handler-ends writes 1 to its place, which
writing in place keeps and the unwritten copy loses. -/
theorem unwritten_differ :
    inPlace false [.add 0 1, .perform] (fun _ => 0) 0 ≠ (fun _ => (0 : Int)) 0 := by
  simp [inPlace, run, Store.set]

end Stilt.Interactions.Ended
