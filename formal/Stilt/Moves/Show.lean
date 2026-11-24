import Stilt.Moves.Observed
import Stilt.Show

/-!
# Showing sees through marks

A value's text is its erased copy's (values.passing-values): erasing changes
only the bodies of closures, which no text shows.
-/

namespace Stilt

theorem eraseBindings_length : ∀ fields : List (Name × Value),
    (eraseBindings fields).length = fields.length
  | [] => rfl
  | _ :: fields => by simp [eraseBindings, eraseBindings_length fields]

mutual

theorem Value.shown_erase (b : Bool) : ∀ v : Value, v.erase.shown b = v.shown b
  | .int _ | .float _ | .str _ | .bool _ | .unit => rfl
  | .record R fields => by
    have hl := eraseBindings_length fields
    have he : (eraseBindings fields).isEmpty = fields.isEmpty := by
      cases fields <;> rfl
    simp only [Value.erase, Value.shown, hl, he, shownFields_erase, shownEntries_erase,
      shownElements_erase, shownNamed_erase]
  | .variant _ _ [] => rfl
  | .variant _ _ (v :: vs) => by
    have h := shownValues_erase (v :: vs)
    simp only [eraseValues] at h
    simp only [Value.erase, eraseValues, Value.shown, h]
  | .list vs => by simp only [Value.erase, Value.shown, shownValues_erase vs]
  | .closure .. | .function .. | .handle .. | .window .. => rfl

theorem shownValues_erase : ∀ vs : List Value, shownValues (eraseValues vs) = shownValues vs
  | [] => rfl
  | v :: vs => by simp only [eraseValues, shownValues, Value.shown_erase true v, shownValues_erase vs]

theorem shownFields_erase : ∀ fields : List (Name × Value),
    shownFields (eraseBindings fields) = shownFields fields
  | [] => rfl
  | (_, v) :: fields => by
    simp only [eraseBindings, shownFields, Value.shown_erase true v, shownFields_erase fields]

theorem shownNamed_erase : ∀ fields : List (Name × Value),
    shownNamed (eraseBindings fields) = shownNamed fields
  | [] => rfl
  | (_, v) :: fields => by
    simp only [eraseBindings, shownNamed, Value.shown_erase true v, shownNamed_erase fields]

theorem shownPairs_erase : ∀ es : List Value, shownPairs (eraseValues es) = shownPairs es
  | [] => rfl
  | .list [k, v] :: es => by
    simp only [eraseValues, Value.erase, shownPairs, Value.shown_erase true k,
      Value.shown_erase true v, shownPairs_erase es]
  | .list [] :: es | .list [_] :: es | .list (_ :: _ :: _ :: _) :: es
  | .int _ :: es | .float _ :: es | .str _ :: es | .bool _ :: es | .unit :: es
  | .record .. :: es | .variant .. :: es | .closure .. :: es | .function .. :: es | .handle .. :: es
  | .window .. :: es => by
    simp only [eraseValues, Value.erase, shownPairs, shownPairs_erase es]

theorem shownEntries_erase : ∀ fields : List (Name × Value),
    shownEntries (eraseBindings fields) = shownEntries fields
  | [] => rfl
  | (_, .list es) :: _ => by simp only [eraseBindings, Value.erase, shownEntries, shownPairs_erase es]
  | (_, .int _) :: fields | (_, .float _) :: fields | (_, .str _) :: fields
  | (_, .bool _) :: fields | (_, .unit) :: fields | (_, .record ..) :: fields
  | (_, .variant ..) :: fields | (_, .closure ..) :: fields | (_, .function ..) :: fields
  | (_, .handle ..) :: fields | (_, .window ..) :: fields => by
    simp only [eraseBindings, Value.erase, shownEntries, shownEntries_erase fields]

theorem shownElements_erase : ∀ fields : List (Name × Value),
    shownElements (eraseBindings fields) = shownElements fields
  | [] => rfl
  | (_, .list ks) :: _ => by
    simp only [eraseBindings, Value.erase, shownElements, shownValues_erase ks]
  | (_, .int _) :: fields | (_, .float _) :: fields | (_, .str _) :: fields
  | (_, .bool _) :: fields | (_, .unit) :: fields | (_, .record ..) :: fields
  | (_, .variant ..) :: fields | (_, .closure ..) :: fields | (_, .function ..) :: fields
  | (_, .handle ..) :: fields | (_, .window ..) :: fields => by
    simp only [eraseBindings, Value.erase, shownElements, shownElements_erase fields]

end

end Stilt
