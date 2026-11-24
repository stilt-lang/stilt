import Stilt.Moves.Show
import Stilt.Structural

/-!
# Structural comparisons see through marks

Two values compare as their erased copies do (values.passing-values): erasing
changes only the bodies of closures, which no comparison reads.
-/

namespace Stilt

mutual

theorem Value.same_erase : ∀ v w : Value, v.erase.same w.erase = v.same w
  | .record _ fs, w => by
    cases w <;> first | rfl | simp only [Value.erase, Value.same, sameFields_erase fs]
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
