import Stilt.Moves.Show
import Stilt.Structural

/-!
# Structural comparisons see through marks

Two values compare as their erased copies do (values.passing-values): erasing
changes only the bodies of closures, which no comparison reads.
-/

namespace Stilt

theorem eraseValues_eq_map : ∀ vs : List Value, eraseValues vs = vs.map Value.erase
  | [] => rfl
  | v :: vs => by simp [eraseValues, eraseValues_eq_map vs]

mutual

theorem Value.keyEq_erase : ∀ (a b : Value), a.erase.keyEq b.erase = a.keyEq b
  | .record R fs, .record S gs => by
    simp only [Value.erase, Value.keyEq, fieldsKeyEq_erase fs gs]
  | .variant T C vs, .variant U D ws => by
    simp only [Value.erase, Value.keyEq, payloadKeyEq_erase vs ws]
  | .list vs, .list ws => by
    simp only [Value.erase, Value.keyEq, payloadKeyEq_erase vs ws]
  | .list _, .int _ | .list _, .float _ | .list _, .str _ | .list _, .bool _
  | .list _, .unit | .list _, .record .. | .list _, .variant ..
  | .list _, .closure .. | .list _, .function .. | .list _, .handle .. | .list _, .window .. => rfl
  | .record _ _, .int _ | .record _ _, .float _ | .record _ _, .str _ | .record _ _, .bool _
  | .record _ _, .unit | .record _ _, .variant .. | .record _ _, .list _
  | .record _ _, .closure .. | .record _ _, .function .. | .record _ _, .handle ..
  | .record _ _, .window .. => rfl
  | .variant .., .int _ | .variant .., .float _ | .variant .., .str _ | .variant .., .bool _
  | .variant .., .unit | .variant .., .record .. | .variant .., .list _
  | .variant .., .closure .. | .variant .., .function .. | .variant .., .handle ..
  | .variant .., .window .. => rfl
  | .int _, b | .float _, b | .str _, b | .bool _, b | .unit, b
  | .closure .., b | .function .., b | .handle .., b | .window .., b => by cases b <;> rfl

theorem fieldsKeyEq_erase : ∀ (fs gs : List (Name × Value)),
    Value.keyEq.fieldsKeyEq (eraseBindings fs) (eraseBindings gs) = Value.keyEq.fieldsKeyEq fs gs
  | [], [] | [], _ :: _ | _ :: _, [] => rfl
  | (_, a) :: fs, (_, b) :: gs => by
    simp only [eraseBindings, Value.keyEq.fieldsKeyEq, Value.keyEq_erase a b, fieldsKeyEq_erase fs gs]

theorem payloadKeyEq_erase : ∀ (vs ws : List Value),
    Value.keyEq.payloadKeyEq (eraseValues vs) (eraseValues ws) = Value.keyEq.payloadKeyEq vs ws
  | [], [] | [], _ :: _ | _ :: _, [] => rfl
  | a :: vs, b :: ws => by
    simp only [eraseValues, Value.keyEq.payloadKeyEq, Value.keyEq_erase a b, payloadKeyEq_erase vs ws]

end

theorem Keys.has_erase (k : Value) (ks : List Value) :
    Keys.has k.erase (ks.map Value.erase) = Keys.has k ks := by
  simp [Keys.has, Function.comp_def, Value.keyEq_erase]

theorem SetRelation.test_erase (r : SetRelation) (a b : List Value) :
    r.test (a.map Value.erase) (b.map Value.erase) = r.test a b := by
  cases r <;> simp [SetRelation.test, Function.comp_def, Keys.has_erase]

theorem Value.entryAt_erase (k : Value) : ∀ es : List Value,
    Value.entryAt k.erase (eraseValues es) = (Value.entryAt k es).map Value.erase
  | [] => rfl
  | .list [k', w] :: es => by
    simp only [eraseValues, Value.erase, Value.entryAt, Value.keyEq_erase]
    split
    · rfl
    · exact Value.entryAt_erase k es
  | .list [] :: es | .list [_] :: es | .list (_ :: _ :: _ :: _) :: es
  | .int _ :: es | .float _ :: es | .str _ :: es | .bool _ :: es | .unit :: es
  | .record .. :: es | .variant .. :: es | .closure .. :: es | .function .. :: es | .handle .. :: es
  | .window .. :: es => by
    simp only [eraseValues, Value.erase, Value.entryAt, Value.entryAt_erase k es]

theorem sameSets_erase (fs gs : List (Name × Value)) :
    sameSets (eraseBindings fs) (eraseBindings gs) = sameSets fs gs := by
  rcases fs with _ | ⟨⟨_, v⟩, fs⟩
  · rfl
  rcases gs with _ | ⟨⟨_, w⟩, gs⟩ <;> cases v <;> (try cases w) <;>
    simp only [eraseBindings, Value.erase, sameSets, eraseValues_eq_map, SetRelation.test_erase]

mutual

theorem Value.same_erase : ∀ v w : Value, v.erase.same w.erase = v.same w
  | .record R fs, w => by
    cases w <;> first | rfl |
      simp only [Value.erase, Value.same, sameFields_erase fs, sameMaps_erase fs, sameSets_erase]
  | .variant _ _ vs, w => by
    cases w <;> first | rfl | simp only [Value.erase, Value.same, sameValues_erase vs]
  | .list vs, w => by
    cases w <;> first | rfl | simp only [Value.erase, Value.same, sameValues_erase vs]
  | .int _, w | .float _, w | .bool _, w | .str _, w | .unit, w | .closure .., w
  | .function .., w | .handle .., w | .window .., w => by cases w <;> rfl

theorem sameValues_erase : ∀ vs ws : List Value,
    sameValues (eraseValues vs) (eraseValues ws) = sameValues vs ws
  | [], ws => by cases ws <;> rfl
  | _ :: _, [] => rfl
  | v :: vs, w :: ws => by
    simp only [eraseValues, sameValues, Value.same_erase v w, sameValues_erase vs ws]

theorem sameFields_erase : ∀ fs gs : List (Name × Value),
    sameFields (eraseBindings fs) (eraseBindings gs) = sameFields fs gs
  | [], gs => by cases gs <;> rfl
  | _ :: _, [] => rfl
  | (_, v) :: fs, (_, w) :: gs => by
    simp only [eraseBindings, sameFields, Value.same_erase v w, sameFields_erase fs gs]

theorem sameMaps_erase : ∀ fs gs : List (Name × Value),
    sameMaps (eraseBindings fs) (eraseBindings gs) = sameMaps fs gs
  | [], _ => rfl
  | (_, .list es) :: _, gs => by
    rcases gs with _ | ⟨⟨_, w⟩, gs⟩
    · rfl
    · cases w <;> simp only [eraseBindings, Value.erase, sameMaps, length_eraseValues,
        sameEntries_erase es]
  | (_, .int _) :: _, _ | (_, .float _) :: _, _ | (_, .str _) :: _, _ | (_, .bool _) :: _, _
  | (_, .unit) :: _, _ | (_, .record ..) :: _, _ | (_, .variant ..) :: _, _
  | (_, .closure ..) :: _, _ | (_, .function ..) :: _, _ | (_, .handle ..) :: _, _
  | (_, .window ..) :: _, _ => rfl

theorem sameEntries_erase : ∀ es bs : List Value,
    sameEntries (eraseValues es) (eraseValues bs) = sameEntries es bs
  | [], _ => rfl
  | .list [k, v] :: es, bs => by
    simp only [eraseValues, Value.erase, sameEntries, Value.entryAt_erase k bs]
    cases Value.entryAt k bs <;> simp only [Option.map, Value.same_erase v, sameEntries_erase es bs]
  | .list [] :: es, _ | .list [_] :: es, _ | .list (_ :: _ :: _ :: _) :: es, _
  | .int _ :: es, _ | .float _ :: es, _ | .str _ :: es, _ | .bool _ :: es, _ | .unit :: es, _
  | .record .. :: es, _ | .variant .. :: es, _ | .closure .. :: es, _ | .function .. :: es, _
  | .handle .. :: es, _ | .window .. :: es, _ => rfl

end

variable (orders : CtorOrders)

mutual

theorem Value.order_erase : ∀ v w : Value, v.erase.order orders w.erase = v.order orders w
  | .record _ fs, w => by
    cases w <;> first | rfl | simp only [Value.erase, Value.order, orderFields_erase fs]
  | .variant _ _ vs, w => by
    cases w <;> first | rfl | simp only [Value.erase, Value.order, orderValues_erase vs]
  | .list vs, w => by
    cases w <;> first | rfl | simp only [Value.erase, Value.order, orderValues_erase vs]
  | .int _, w | .float _, w | .bool _, w | .str _, w | .unit, w | .closure .., w
  | .function .., w | .handle .., w | .window .., w => by cases w <;> rfl

theorem orderValues_erase : ∀ vs ws : List Value,
    orderValues orders (eraseValues vs) (eraseValues ws) = orderValues orders vs ws
  | [], ws => by cases ws <;> rfl
  | _ :: _, [] => rfl
  | v :: vs, w :: ws => by
    simp only [eraseValues, orderValues, Value.order_erase v w, orderValues_erase vs ws]

theorem orderFields_erase : ∀ fs gs : List (Name × Value),
    orderFields orders (eraseBindings fs) (eraseBindings gs) = orderFields orders fs gs
  | [], gs => by cases gs <;> rfl
  | _ :: _, [] => rfl
  | (_, v) :: fs, (_, w) :: gs => by
    simp only [eraseBindings, orderFields, Value.order_erase v w, orderFields_erase fs gs]

end

theorem Cmp.values_erase (c : Cmp) (v w : Value) :
    c.values orders v.erase w.erase = c.values orders v w := by
  cases c <;> simp only [Cmp.values, Value.same_erase, Value.order_erase]

end Stilt
