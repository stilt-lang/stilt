import Stilt.Modes.Solved

/-!
# Rounds kept in a table

`Decls.consumed` and `Decls.onceParams` are rounds over the call graph, each a function of the
previous one. Read as functions, a round asks the previous one again at each question, so an
answer costs as many walks of bodies as there are paths through the rounds. Kept in a table of
the program's parameters, each round asks each of the previous round's answers once
(`ParamSet.rounds`), and gives the same answers, since a round holds only the program's
parameters (`ParamSet.rounds_eq`). `Program.modeEnvTabled` is the program's mode environment
with its rounds kept so, and it is `Program.modeEnv` (`Program.modeEnvTabled_eq`).
-/

namespace Stilt

/-- The answers of a set of parameters for the parameters `S`, in a table. -/
def ParamSet.table (S : List (Name × Nat)) (A : ParamSet) : List ((Name × Nat) × Bool) :=
  S.map fun gn => (gn, A gn.1 gn.2)

/-- The set of parameters a table holds: none outside it. -/
def ParamSet.ofTable (t : List ((Name × Nat) × Bool)) : ParamSet := fun g n =>
  (t.lookup (g, n)).getD false

theorem ParamSet.ofTable_table (S : List (Name × Nat)) (A : ParamSet) (g : Name) (n : Nat) :
    ofTable (table S A) g n = if (g, n) ∈ S then A g n else false := by
  unfold ofTable table
  induction S with
  | nil => rfl
  | cons gn S ih =>
    simp only [List.map_cons, List.lookup_cons, List.mem_cons]
    by_cases h : (g, n) = gn
    · subst h
      simp
    · have : ((g, n) == gn) = false := by simpa using h
      simp only [this, ih, h, false_or]

/-- The tables of the rounds of `step` from `A` for the parameters `S`, each read by the next:
the table of the round `k + 1`. A table is data, so each round's answers are found once. -/
def ParamSet.rounds (step : ParamSet → ParamSet) (S : List (Name × Nat)) (A : ParamSet) :
    Nat → List ((Name × Nat) × Bool)
  | 0 => table S (step A)
  | k + 1 => table S (step (ofTable (rounds step S A k)))

/-- Rounds that hold only the parameters `S` give the same answers kept in tables. -/
theorem ParamSet.rounds_eq {step : ParamSet → ParamSet} {S : List (Name × Nat)}
    (supp : ∀ A g n, step A g n = true → (g, n) ∈ S) (A : ParamSet) :
    ∀ k, ofTable (rounds step S A k) = Nat.repeat step (k + 1) A := by
  have kept : ∀ B, ofTable (table S (step B)) = step B := by
    intro B
    funext g n
    rw [ofTable_table]
    split
    · rfl
    · rename_i h
      cases hs : step B g n
      · rfl
      · exact absurd (supp _ g n hs) h
  intro k
  induction k with
  | zero => exact kept A
  | succ k ih => rw [rounds, ih, kept]; rfl

/-- Consumption, its rounds kept in a table. -/
def Decls.consumedTabled (D : Decls) : Consumed :=
  ParamSet.ofTable (ParamSet.rounds D.consumeStep D.slotList (fun _ _ => false) D.slots)

theorem Decls.consumedTabled_eq (D : Decls) : D.consumedTabled = D.consumed :=
  ParamSet.rounds_eq D.consumeStep_supp _ _

/-- The `once` parameters, their rounds kept in a table. -/
def Decls.onceParamsTabled (D : Decls) : OnceParams :=
  ParamSet.ofTable (ParamSet.rounds D.onceStep D.slotList (fun _ _ => true) D.slots)

theorem Decls.onceParamsTabled_eq (D : Decls) : D.onceParamsTabled = D.onceParams :=
  ParamSet.rounds_eq D.onceStep_supp _ _

/-- The program's mode environment, its rounds kept in tables, each found once: the tables are
data, which the environment's sets of parameters read. -/
def Program.modeEnvTabled (p : Program) : ModeEnv :=
  let consumed := ParamSet.rounds p.decls.consumeStep p.decls.slotList (fun _ _ => false)
    p.decls.slots
  let once := ParamSet.rounds p.decls.onceStep p.decls.slotList (fun _ _ => true) p.decls.slots
  ⟨p.decls, ParamSet.ofTable consumed, ParamSet.ofTable once⟩

theorem Program.modeEnvTabled_eq (p : Program) : p.modeEnvTabled = p.modeEnv := by
  simp only [Program.modeEnvTabled, Program.modeEnv]
  rw [← Decls.consumedTabled_eq, ← Decls.onceParamsTabled_eq]
  rfl

end Stilt
