import Stilt.Soundness.Types
import Stilt.Typing
import Stilt.Ops

/-!
# Reading types at run time

How `Ty.close` reads the relations of `Stilt.Rows`: a row that fits within
another raises no more error types, `Fits` gives a run-time type that fits,
a closed type reads the same under every environment, and instantiating a
type's row variables, then reading it, is reading it under the composed
environment, up to equivalence. The last holds because a use leaves every row
of the signature one `raise` label (effects.one-error-type): the label that
instantiation keeps is the one that every variable brings.
-/

namespace Stilt

/-- The environment of a body that a use instantiates with `s`, from the
environment of the use: each variable stands for what the row the use gives it
raises (effects.inference). -/
def RowSubst.compose (s : RowSubst) (η : REnv) : REnv :=
  fun v => (s.lookup v).elim (η v) (Row.close η)

theorem Row.close_eq (η : REnv) (ρ : Row) :
    ρ.close η = (ρ.raise.map (Ty.close η)).toList ++ ρ.vars.flatMap η ++
      Row.labelsOf ρ.effects ρ.resume ++ Row.ioLabel ρ.io := by
  obtain ⟨_, raise, _⟩ := ρ
  cases raise <;> simp [Row.close]

/-- What a run-time row holds: its own error type, what its variables stand
for, and the labels of its effects, its `resume` and its `io`. -/
theorem Row.mem_close {η : REnv} {ρ : Row} {x : STy} :
    x ∈ ρ.close η ↔ (∃ E, ρ.raise = some E ∧ x = E.close η) ∨ (∃ v ∈ ρ.vars, x ∈ η v) ∨
      (∃ E ∈ ρ.effects, x = .effect E) ∨ (∃ p, ρ.resume = some p ∧ x = .resume p.1 p.2) ∨
      (ρ.io = true ∧ x = .io) := by
  rw [Row.close_eq]
  rcases ρ with ⟨io, raise, _, _, resume⟩
  cases raise <;> cases resume <;> cases io <;> simp [Row.labelsOf, Row.ioLabel, eq_comm]

/-- A row that fits within another raises no error type the other lacks, and
holds no label the other lacks. -/
theorem Row.Within.close {a b : Row} (h : a.Within b) (η : REnv) :
    ∀ x ∈ a.close η, x ∈ b.close η := by
  intro x hx
  rcases Row.mem_close.1 hx with ⟨E, hE, rfl⟩ | ⟨v, hv, hx⟩ | ⟨E, hE, rfl⟩ | ⟨p, hp, rfl⟩ |
    ⟨hio, rfl⟩
  · exact Row.mem_close.2 (.inl ⟨E, h.raise E hE, rfl⟩)
  · exact Row.mem_close.2 (.inr (.inl ⟨v, h.vars v hv, hx⟩))
  · exact Row.mem_close.2 (.inr (.inr (.inl ⟨E, h.effects E hE, rfl⟩)))
  · exact Row.mem_close.2 (.inr (.inr (.inr (.inl ⟨p, h.resume _ hp, rfl⟩))))
  · exact Row.mem_close.2 (.inr (.inr (.inr (.inr ⟨h.io hio, rfl⟩))))

/-- A type read under an environment is no label. -/
theorem Ty.close_not_label (η : REnv) : ∀ τ : Ty, ¬ (τ.close η).IsLabel
  | .view τ => by simpa [Ty.close] using Ty.close_not_label η τ
  | .int _ | .float _ | .bool | .str | .unit | .never | .record _ _ | .variant _ _ | .list _
  | .tuple _ | .map _ _ | .set _ | .shared _ | .param _ | .fn _ _ _ => by simp [Ty.close, STy.IsLabel]

/-- A row and the row of a `catch` operand built from it hold the same labels. -/
theorem Row.labels_withRaise {η : REnv} {ρ : Row} {E : Ty} :
    ∀ x ∈ (ρ.withRaise E).close η, x.IsLabel → x ∈ ρ.close η := by
  intro x hx hl
  rcases Row.mem_close.1 hx with ⟨_, _, rfl⟩ | h
  · exact absurd hl (Ty.close_not_label η _)
  · exact Row.mem_close.2 (.inr h)

/-- A `catch` operand raises the caught type, and what the row's variables
stand for. -/
theorem Row.close_withRaise (η : REnv) (ρ : Row) (E : Ty) :
    (ρ.withRaise E).close η =
      E.close η :: (ρ.vars.flatMap η ++ Row.labelsOf ρ.effects ρ.resume ++ Row.ioLabel ρ.io) :=
  rfl

/-- `Fits` gives a run-time type that fits. -/
theorem Fits.close {σ τ : Ty} (h : Fits σ τ) (η : REnv) : (σ.close η).Fits (τ.close η) := by
  cases h with
  | refl => exact .refl _
  | never => exact .never _
  | fn h => exact .of_covers (Covers.of_subset (h.close η))

/-! ## Closed types -/

mutual

theorem Ty.close_closed (η η' : REnv) :
    ∀ τ : Ty, (∀ ρ ∈ τ.rows, ρ.vars = []) → τ.close η = τ.close η'
  | .int _, _ | .float _, _ | .bool, _ | .str, _ | .unit, _ | .never, _ | .param _, _ => rfl
  | .record _ τs, h | .variant _ τs, h => by
    simp [Ty.close, closeTys_closed η η' τs (by simpa [Ty.rows] using h)]
  | .list τ, h => by simp [Ty.close, Ty.close_closed η η' τ (by simpa [Ty.rows] using h)]
  | .tuple τs, h => by
    simp [Ty.close, closeTys_closed η η' τs (by simpa [Ty.rows] using h)]
  | .map κ τ, h => by
    simp only [Ty.rows, List.mem_append] at h
    simp [Ty.close, Ty.close_closed η η' κ fun σ hσ => h σ (.inl hσ),
      Ty.close_closed η η' τ fun σ hσ => h σ (.inr hσ)]
  | .set τ, h => by simp [Ty.close, Ty.close_closed η η' τ (by simpa [Ty.rows] using h)]
  | .view τ, h => by simp [Ty.close, Ty.close_closed η η' τ (by simpa [Ty.rows] using h)]
  | .shared τ, h => by simp [Ty.close, Ty.close_closed η η' τ (by simpa [Ty.rows] using h)]
  | .fn ps r ρ, h => by
    simp only [Ty.rows, List.mem_append] at h
    simp [Ty.close, closeParams_closed η η' ps fun σ hσ => h σ (.inl (.inl hσ)),
      Ty.close_closed η η' r fun σ hσ => h σ (.inl (.inr hσ)),
      Row.close_closed η η' ρ fun σ hσ => h σ (.inr hσ)]

theorem closeTys_closed (η η' : REnv) :
    ∀ τs : List Ty, (∀ ρ ∈ tysRows τs, ρ.vars = []) → closeTys η τs = closeTys η' τs
  | [], _ => rfl
  | τ :: τs, h => by
    simp only [tysRows, List.mem_append] at h
    simp [closeTys, Ty.close_closed η η' τ fun σ hσ => h σ (.inl hσ),
      closeTys_closed η η' τs fun σ hσ => h σ (.inr hσ)]

theorem closeParams_closed (η η' : REnv) :
    ∀ ps : List (Mode × Ty), (∀ ρ ∈ paramRows ps, ρ.vars = []) →
      closeParams η ps = closeParams η' ps
  | [], _ => rfl
  | (_, τ) :: ps, h => by
    simp only [paramRows, List.mem_append] at h
    simp [closeParams, Ty.close_closed η η' τ fun σ hσ => h σ (.inl hσ),
      closeParams_closed η η' ps fun σ hσ => h σ (.inr hσ)]

theorem Row.close_closed (η η' : REnv) :
    ∀ ρ : Row, (∀ σ ∈ ρ.rows, σ.vars = []) → ρ.close η = ρ.close η'
  | ⟨io, some E, vs, es, r⟩, h => by
    have hvs : vs = [] := h ⟨io, some E, vs, es, r⟩ (by simp [Row.rows])
    subst hvs
    simp [Row.close, Ty.close_closed η η' E fun σ hσ => h σ (by simp [Row.rows, hσ])]
  | ⟨io, none, vs, es, r⟩, h => by
    have hvs : vs = [] := h ⟨io, none, vs, es, r⟩ (by simp [Row.rows])
    subst hvs
    rfl

end

theorem closeTys_eq_map (η : REnv) : ∀ τs : List Ty, closeTys η τs = τs.map (Ty.close η)
  | [] => rfl
  | τ :: τs => by simp [closeTys, closeTys_eq_map η τs]

/-- The element a position names, read under an environment. -/
theorem closeTys_lookup (η : REnv) {τs : List Ty} {f : Name} {τ : Ty}
    (h : (positions τs).lookup f = some τ) :
    (positions (closeTys η τs)).lookup f = some (τ.close η) := by
  rw [closeTys_eq_map, positions, lookup_positionsFrom_map, ← positions, h]
  rfl

/-- A closed type reads as itself under every environment. -/
theorem Ty.Closed.close {τ : Ty} (h : τ.Closed) (η : REnv) : τ.close η = τ.sem :=
  Ty.close_closed η _ τ h

end Stilt
