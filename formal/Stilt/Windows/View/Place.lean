import Stilt.Windows.View.Narrow
import Stilt.Windows.Handling.Escapes

/-!
# The place a view names

A view's source that is a place with no index (`fieldPath`) is a variable followed by fields:
an instance of a generic body has the same one (`inst_eq_of_place`), and both models evaluate
it, once they have the fuel, by reading the state alone, the in-place model the part of the
variable's place at its fields (`eval_place`; views.making-view).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-! ## Places that take no index -/

theorem fieldPath_append_field (f : Name) :
    ∀ ps : List Projection, fieldPath (ps ++ [.field f]) = (fieldPath ps).map (· ++ [.field f])
  | [] => rfl
  | .field g :: ps => by
    simp only [List.cons_append, fieldPath, fieldPath_append_field f ps]
    cases fieldPath ps <;> rfl
  | .index _ :: _ => rfl

theorem fieldPath_append_index (i : Expr) :
    ∀ ps : List Projection, fieldPath (ps ++ [.index i]) = none
  | [] => rfl
  | .field g :: ps => by
    simp only [List.cons_append, fieldPath, fieldPath_append_index i ps]
    rfl
  | .index _ :: _ => rfl

/-- A place that takes no index has the fields of its path. -/
theorem fieldNames_of_fieldPath :
    ∀ {ps : List Projection} {path : Path}, fieldPath ps = some path →
      path.fieldNames = ps.filterMap Projection.fieldName?
  | [], _, h => by cases h; rfl
  | .field g :: ps, path, h => by
    simp only [fieldPath] at h
    cases hp : fieldPath ps with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      cases h
      simp [Path.fieldNames, Projection.fieldName?, fieldNames_of_fieldPath hp]
  | .index _ :: _, _, h => by cases h

/-- The forms of a place. -/
theorem place_cases {e : Expr} {x : Name} {ps : List Projection} (h : e.place? = some ⟨x, ps⟩) :
    (ps = [] ∧ (e = .var x ∨ e = .move x)) ∨
      (∃ e' f ps', e = .field e' f ∧ e'.place? = some ⟨x, ps'⟩ ∧ ps = ps' ++ [.field f]) ∨
      ∃ e' i ps', e = .index e' i ∧ e'.place? = some ⟨x, ps'⟩ ∧ ps = ps' ++ [.index i] := by
  cases e <;> simp only [Expr.place?, Option.some.injEq, Place.mk.injEq, reduceCtorEq,
    Option.map_eq_some_iff] at h
  · obtain ⟨rfl, rfl⟩ := h; exact .inl ⟨rfl, .inl rfl⟩
  · obtain ⟨rfl, rfl⟩ := h; exact .inl ⟨rfl, .inr rfl⟩
  · obtain ⟨⟨y, qs⟩, hq, h⟩ := h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr (.inl ⟨_, _, _, rfl, hq, rfl⟩)
  · obtain ⟨⟨y, qs⟩, hq, h⟩ := h
    obtain ⟨rfl, rfl⟩ := h
    exact .inr (.inr ⟨_, _, _, rfl, hq, rfl⟩)

/-- A place with no index after one more field. -/
theorem fieldPath_field {ps : List Projection} {f : Name} {path : Path}
    (h : fieldPath (ps ++ [.field f]) = some path) :
    ∃ path', fieldPath ps = some path' ∧ path = path' ++ [.field f] := by
  rw [fieldPath_append_field] at h
  cases hp : fieldPath ps with
  | none => rw [hp] at h; cases h
  | some p => rw [hp] at h; cases h; exact ⟨p, rfl, rfl⟩

/-- An instance of a place that takes no index is the place itself. -/
theorem inst_eq_of_place {x : Name} : ∀ (k : Nat) {e₀ e : Expr} {ps : List Projection}
    {path : Path}, ps.length = k → Expr.Inst D e₀ e → e.place? = some ⟨x, ps⟩ →
      fieldPath ps = some path → e₀ = e
  | k, e₀, e, ps, path, hk, hi, hp, hf => by
    rcases place_cases hp with ⟨-, rfl | rfl⟩ | ⟨e', f, ps', rfl, hp', rfl⟩ |
      ⟨e', i, ps', rfl, -, rfl⟩
    · cases hi; rfl
    · cases hi; rfl
    · cases hi with
      | field _ hi =>
        obtain ⟨path', hf', -⟩ := fieldPath_field hf
        cases k with
        | zero => simp at hk
        | succ k => rw [inst_eq_of_place k (by simpa using hk) hi hp' hf']
    · rw [fieldPath_append_index] at hf; cases hf

/-- A generic place that takes no index is its instance. -/
theorem inst_eq_of_place₀ {x : Name} : ∀ (k : Nat) {e₀ e : Expr} {ps : List Projection}
    {path : Path}, ps.length = k → Expr.Inst D e₀ e → e₀.place? = some ⟨x, ps⟩ →
      fieldPath ps = some path → e₀ = e
  | k, e₀, e, ps, path, hk, hi, hp, hf => by
    rcases place_cases hp with ⟨-, rfl | rfl⟩ | ⟨e', f, ps', rfl, hp', rfl⟩ |
      ⟨e', i, ps', rfl, -, rfl⟩
    · cases hi; rfl
    · cases hi; rfl
    · cases hi with
      | field _ hi =>
        obtain ⟨path', hf', -⟩ := fieldPath_field hf
        cases k with
        | zero => simp at hk
        | succ k => rw [inst_eq_of_place₀ k (by simpa using hk) hi hp' hf']
    · rw [fieldPath_append_index] at hf; cases hf

/-! ## Evaluating a place that takes no index -/

/-- A field after a read of the state, read in turn. -/
theorem inspect_field {σ : Type} (F : σ → Except Fault Value) (f : Name) :
    (Eval.inspect F >>= fun v => Eval.ofExcept (v.get [.field f])) =
      Eval.inspect fun s => F s >>= (·.get [.field f]) := by
  funext s
  show (Eval.ofExcept (F s) s).bind _ = Eval.ofExcept (F s >>= (·.get [.field f])) s
  cases F s with
  | error e => cases e <;> rfl
  | ok _ => rfl

/-- A field after a read of the state through its windows, read in turn. -/
theorem inspect_resolve_field (G : WState → Except Fault Value) (f : Name) :
    (Eval.inspect G >>= resolveE >>= fun v => Eval.ofExcept (v.get [.field f])) =
      Eval.inspect fun s => G s >>= resolve s.1.store >>= (·.get [.field f]) := by
  funext s
  show ((Eval.ofExcept (G s) s).bind fun v s' => resolveE v s').bind _ =
    Eval.ofExcept (G s >>= resolve s.1.store >>= (·.get [.field f])) s
  cases G s with
  | error e => cases e <;> rfl
  | ok a =>
    show (Eval.ofExcept (resolve s.1.store a) s).bind _ =
      Eval.ofExcept (resolve s.1.store a >>= (·.get [.field f])) s
    cases resolve s.1.store a with
    | error e => cases e <;> rfl
    | ok b => rfl

/-- Both models evaluate a place that takes no index by reading the state alone, once they
have the fuel: in place, the part of the variable's place at its fields; through windows, the
variable's value as it is, or a value that holds no window when it takes a field. -/
theorem eval_place {x : Name} : ∀ (n : Nat) {e : Expr} {ps : List Projection} {path : Path},
    e.place? = some ⟨x, ps⟩ → fieldPath ps = some path →
    (Stilt.eval D InPlace.memory n e = Eval.outOfFuel ∧ Windows.eval D n e = Eval.outOfFuel) ∨
      (Stilt.eval D InPlace.memory n e =
          Eval.inspect (fun s => InPlace.read s.1 x [] >>= (·.get path)) ∧
        ∃ g, Windows.eval D n e = Eval.inspect g ∧ (ps = [] → g = fun s => readWindows s.1 x []) ∧
          (ps ≠ [] → ∀ s v, g s = .ok v → Free v))
  | 0, _, _, _, _, _ => .inl ⟨rfl, rfl⟩
  | n + 1, e, ps, path, hp, hf => by
    rcases place_cases hp with ⟨rfl, rfl | rfl⟩ | ⟨e', f, ps', rfl, hp', rfl⟩ |
      ⟨e', i, ps', rfl, -, rfl⟩
    · cases hf
      refine .inr ⟨?_, _, rfl, fun _ => rfl, fun h => absurd rfl h⟩
      funext s
      show Eval.ofExcept (InPlace.read s.1 x []) s =
        Eval.ofExcept (InPlace.read s.1 x [] >>= (·.get [])) s
      cases InPlace.read s.1 x [] <;> rfl
    · cases hf
      refine .inr ⟨?_, _, rfl, fun _ => rfl, fun h => absurd rfl h⟩
      funext s
      show Eval.ofExcept (InPlace.read s.1 x []) s =
        Eval.ofExcept (InPlace.read s.1 x [] >>= (·.get [])) s
      cases InPlace.read s.1 x [] <;> rfl
    · obtain ⟨path', hf', rfl⟩ := fieldPath_field hf
      rcases eval_place n hp' hf' with ⟨h₁, h₂⟩ | ⟨h₁, g, h₂, -, -⟩
      · refine .inl ⟨?_, ?_⟩
        · show Stilt.eval D InPlace.memory n e' >>= _ = _
          rw [h₁]; rfl
        · show Windows.eval D n e' >>= resolveE >>= _ = _
          rw [h₂]; rfl
      · refine .inr ⟨?_, fun s => g s >>= resolve s.1.store >>= (·.get [.field f]), ?_,
          fun h => absurd h (by simp), fun _ s v hv => ?_⟩
        · show Stilt.eval D InPlace.memory n e' >>= _ = _
          rw [h₁, inspect_field]
          congr 1
          funext s
          cases InPlace.read s.1 x [] with
          | error _ => rfl
          | ok u =>
            show (u.get path').bind _ = u.get _
            rw [Value.get_append]
        · show Windows.eval D n e' >>= resolveE >>= _ = _
          rw [h₂, inspect_resolve_field]
        · simp only at hv
          cases ha : g s with
          | error _ => rw [ha] at hv; cases hv
          | ok a =>
            rw [ha] at hv
            change (resolve s.1.store a >>= (·.get [.field f])) = .ok v at hv
            cases hb : resolve s.1.store a with
            | error _ => rw [hb] at hv; cases hv
            | ok b => rw [hb] at hv; exact free_get b _ (free_of_resolve hb) hv
    · rw [fieldPath_append_index] at hf; cases hf

end Windows

end Stilt
