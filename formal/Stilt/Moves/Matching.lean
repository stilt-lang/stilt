import Stilt.Moves.Observed

/-!
# Matching erased values

A pattern reads no closure's body, so it matches a value's erasure as it
matches the value, and binds the erasures of the parts it binds; a `match`
over erased arms selects the erasure of the arm it selects.
-/

namespace Stilt

theorem eraseValues_append : ∀ (vs ws : List Value),
    eraseValues (vs ++ ws) = eraseValues vs ++ eraseValues ws
  | [], _ => rfl
  | v :: vs, ws => by simp [eraseValues, eraseValues_append vs ws]

theorem map_snd_eraseBindings : ∀ l : List (Name × Value),
    (eraseBindings l).map Prod.snd = eraseValues (l.map Prod.snd)
  | [] => rfl
  | (_, _) :: l => by simp [eraseBindings, eraseValues, map_snd_eraseBindings l]

/-- Two optional parts joined, erased, are the erased parts joined. -/
private theorem join_erase (a b : Option (List Value)) :
    (match a.map eraseValues, b.map eraseValues with
      | some us, some us' => some (us ++ us')
      | _, _ => none) =
    (match a, b with
      | some us, some us' => some (us ++ us')
      | _, _ => none).map eraseValues := by
  cases a <;> cases b <;> simp [eraseValues_append]

mutual

theorem Pattern.matchOn_erase : ∀ (p : Pattern) (v : Value),
    p.matchOn v.erase = (p.matchOn v).map eraseValues
  | .wild, _ => rfl
  | .bind _, _ => rfl
  | .int _, v | .bool _, v | .str _, v | .unit, v => by
    cases v <;> simp only [Pattern.matchOn, Value.erase] <;> (try split) <;> rfl
  | .tuple ps, v => by
    cases v <;> simp only [Pattern.matchOn, Value.erase, Option.map_none]
    rw [map_snd_eraseBindings, matchOnAll_erase]
  | .record _ fps, v => by
    cases v <;> simp only [Pattern.matchOn, Value.erase, Option.map_none]
    exact matchOnFields_erase fps _
  | .variant _ C ps, v => by
    cases v <;> simp only [Pattern.matchOn, Value.erase, Option.map_none]
    split
    · exact matchOnAll_erase ps _
    · rfl
  | .or p q, v => by
    simp only [Pattern.matchOn, Pattern.matchOn_erase p v]
    cases p.matchOn v with
    | some us => rfl
    | none => exact Pattern.matchOn_erase q v
  | .list ps r, v => by
    cases v <;> simp only [Pattern.matchOn, Value.erase, Option.map_none]
    exact matchOnList_erase ps r _
  | .const _ p, v => by
    simp only [Pattern.matchOn, Pattern.matchOn_erase p v]
    cases p.matchOn v <;> rfl

theorem matchOnList_erase : ∀ (ps : List Pattern) (r : ListRest) (vs : List Value),
    matchOnList ps r (eraseValues vs) = (matchOnList ps r vs).map eraseValues
  | [], .exact, [] | [], .exact, _ :: _ | [], .any, _ | _ :: _, _, [] => rfl
  | [], .bind _, vs => by simp [matchOnList, eraseValues, Value.erase]
  | p :: ps, r, v :: vs => by
    simp only [eraseValues, matchOnList, Pattern.matchOn_erase p v, matchOnList_erase ps r vs]
    exact join_erase _ _

theorem matchOnAll_erase : ∀ (ps : List Pattern) (vs : List Value),
    matchOnAll ps (eraseValues vs) = (matchOnAll ps vs).map eraseValues
  | [], [] => rfl
  | [], _ :: _ | _ :: _, [] => rfl
  | p :: ps, v :: vs => by
    simp only [eraseValues, matchOnAll, Pattern.matchOn_erase p v, matchOnAll_erase ps vs]
    exact join_erase _ _

theorem matchOnFields_erase : ∀ (fps : List (Name × Pattern)) (fields : List (Name × Value)),
    matchOnFields fps (eraseBindings fields) = (matchOnFields fps fields).map eraseValues
  | [], _ => rfl
  | (f, p) :: fps, fields => by
    simp only [matchOnFields, lookup_eraseBindings]
    cases fields.lookup f with
    | none => rfl
    | some v =>
      simp only [Option.map_some, Pattern.matchOn_erase p v, matchOnFields_erase fps fields]
      exact join_erase _ _

end

theorem eraseArms_eq_map : ∀ arms : List Arm,
    eraseArms arms = arms.map fun a => ⟨a.pattern, a.binders, eraseGuard a.guard, a.body.erase⟩
  | [] => rfl
  | ⟨_, _, _, _⟩ :: arms => by simp [eraseArms, eraseArms_eq_map arms]

/-- The ways a pattern matches an erased value are the erasures of the ways it matches the
value. -/
theorem Pattern.ways_erase (p : Pattern) (v : Value) :
    p.ways v.erase = (p.ways v).map eraseValues := by
  simp only [Pattern.ways]
  induction p.alternatives with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.filterMap_cons, Pattern.matchOn_erase q v]
    cases q.matchOn v <;> simp [ih]

end Stilt
