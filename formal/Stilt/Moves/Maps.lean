import Stilt.Moves.Observed
import Stilt.Moves.Show
import Stilt.Moves.Structural

/-!
# Erasing the marks of maps and sets

The functions of maps and sets see through marks: a key equals another as its
erasure equals the other's, since keys are numbers, Booleans, strings and
`()`, and every other part of a map or a set is carried as it is. So every
operation, applied to erased operands, gives its value erased.
-/

namespace Stilt

/-- An entry with its marks erased. -/
def eraseEntry (e : Value × Value) : Value × Value := (e.1.erase, e.2.erase)


theorem Value.erase_tuple (vs : List Value) : (Value.tuple vs).erase = .tuple (eraseValues vs) := by
  simp only [Value.tuple, Value.erase, positions, eraseBindings_positionsFrom]

theorem Value.erase_mapOf (es : List (Value × Value)) (d : Option Value) :
    (Value.mapOf es d).erase = .mapOf (es.map eraseEntry) (d.map Value.erase) := by
  cases d <;> simp [Value.mapOf, Value.erase, eraseBindings, eraseValues_eq_map, Value.entry,
    eraseEntry]

theorem Value.erase_setOf (ks : List Value) :
    (Value.setOf ks).erase = .setOf (ks.map Value.erase) := by
  simp [Value.setOf, Value.erase, eraseBindings, eraseValues_eq_map]

/-! ## Reading erased maps and sets -/

theorem Value.list?_erase (v : Value) : v.erase.list? = v.list?.map eraseValues := by
  cases v <;> rfl

theorem Value.int?_erase (v : Value) : v.erase.int? = v.int? := by
  cases v <;> rfl

theorem eraseValues_rangeValues (a b : Int) (inclusive : Bool) :
    eraseValues (rangeValues a b inclusive) = rangeValues a b inclusive := by
  simp [rangeValues, eraseValues_eq_map, Value.erase]

theorem Value.entry?_erase (v : Value) : v.erase.entry? = v.entry?.map eraseEntry := by
  cases v with
  | list vs => rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> rfl
  | _ => rfl

theorem Value.listField?_erase (v : Value) (f : Name) :
    v.erase.listField? f = (v.listField? f).map eraseValues := by
  cases v with
  | record R fields =>
    simp only [Value.erase, Value.listField?, lookup_eraseBindings]
    cases fields.lookup f <;> simp [Value.list?_erase]
  | _ => rfl

theorem mapM_entry?_erase : ∀ vs : List Value,
    (vs.map Value.erase).mapM Value.entry? = (vs.mapM Value.entry?).map (List.map eraseEntry)
  | [] => rfl
  | v :: vs => by
    simp only [List.map_cons, List.mapM_cons, Value.entry?_erase, mapM_entry?_erase vs]
    cases v.entry? <;> cases vs.mapM Value.entry? <;> rfl

theorem Value.map?_erase (v : Value) :
    v.erase.map? = v.map?.map fun (es, d) => (es.map eraseEntry, d.map Value.erase) := by
  unfold Value.map?
  rw [Value.listField?_erase, Value.listField?_erase]
  cases v.listField? entriesField <;> cases v.listField? defaultField <;> try rfl
  rename_i us ds
  simp only [Option.map_some, eraseValues_eq_map, List.head?_map, mapM_entry?_erase]
  cases us.mapM Value.entry? <;> rfl

theorem Value.set?_erase (v : Value) : v.erase.set? = v.set?.map eraseValues :=
  Value.listField?_erase v elementsField

theorem onMap_erase (m : Value) {f g : List (Value × Value) → Option Value → Except Fault Value}
    (h : ∀ es d, f (es.map eraseEntry) (d.map Value.erase) = (g es d).map Value.erase) :
    onMap m.erase f = (onMap m g).map Value.erase := by
  unfold onMap
  rw [Value.map?_erase]
  cases m.map? with
  | none => rfl
  | some p => exact h p.1 p.2

theorem onSet_erase (s : Value) {f g : List Value → Except Fault Value}
    (h : ∀ ks, f (ks.map Value.erase) = (g ks).map Value.erase) :
    onSet s.erase f = (onSet s g).map Value.erase := by
  unfold onSet
  rw [Value.set?_erase]
  cases s.set? with
  | none => rfl
  | some ks => simpa [eraseValues_eq_map] using h ks

theorem onList_erase (l : Value) {f g : List Value → Except Fault Value}
    (h : ∀ vs, f (vs.map Value.erase) = (g vs).map Value.erase) :
    onList l.erase f = (onList l g).map Value.erase := by
  unfold onList
  rw [Value.list?_erase]
  cases l.list? with
  | none => rfl
  | some vs => simpa [eraseValues_eq_map] using h vs

/-! ## Finding erased keys -/

section

variable (k v : Value) (es : List (Value × Value)) (ks : List Value)

theorem Entries.has_erase : Entries.has k.erase (es.map eraseEntry) = Entries.has k es := by
  simp [Entries.has, List.any_map, Function.comp_def, eraseEntry, Value.keyEq_erase]

theorem Entries.find_erase :
    Entries.find k.erase (es.map eraseEntry) = (Entries.find k es).map Value.erase := by
  simp only [Entries.find, List.find?_map, Function.comp_def, eraseEntry, Value.keyEq_erase]
  cases es.find? (fun e => k.keyEq e.1) <;> rfl

theorem Entries.insert_erase :
    Entries.insert k.erase v.erase (es.map eraseEntry) = (Entries.insert k v es).map eraseEntry := by
  unfold Entries.insert
  rw [Entries.has_erase]
  split
  · simp only [List.map_map, Function.comp_def]
    congr 1
    funext e
    simp only [eraseEntry, Value.keyEq_erase]
    split <;> rfl
  · simp [eraseEntry]

theorem Entries.remove_erase :
    Entries.remove k.erase (es.map eraseEntry) = (Entries.remove k es).map eraseEntry := by
  simp [Entries.remove, List.filter_map, Function.comp_def, eraseEntry, Value.keyEq_erase]

theorem Entries.index_erase (d : Option Value) :
    Entries.index k.erase (es.map eraseEntry) (d.map Value.erase) =
      (Entries.index k es d).map Value.erase := by
  unfold Entries.index
  rw [Entries.find_erase]
  cases Entries.find k es <;> cases d <;> rfl

theorem Keys.insert_erase :
    Keys.insert k.erase (ks.map Value.erase) = (Keys.insert k ks).map Value.erase := by
  unfold Keys.insert
  rw [Keys.has_erase]
  split <;> simp

theorem Keys.remove_erase :
    Keys.remove k.erase (ks.map Value.erase) = (Keys.remove k ks).map Value.erase := by
  simp [Keys.remove, List.filter_map, Function.comp_def, Value.keyEq_erase]

end

theorem Keys.insertAll_erase : ∀ ks xs : List Value,
    Keys.insertAll (ks.map Value.erase) (xs.map Value.erase) =
      (Keys.insertAll ks xs).map Value.erase
  | _, [] => rfl
  | ks, x :: xs => by
    rw [List.map_cons, Keys.insertAll, Keys.insertAll, Keys.insert_erase, Keys.insertAll_erase]

theorem SetCombine.run_erase (c : SetCombine) (a b : List Value) :
    c.run (a.map Value.erase) (b.map Value.erase) = (c.run a b).map Value.erase := by
  cases c <;> simp [SetCombine.run, List.filter_map, Function.comp_def, Keys.has_erase]

theorem Keys.insertAll_nil_erase (xs : List Value) :
    Keys.insertAll [] (xs.map Value.erase) = (Keys.insertAll [] xs).map Value.erase :=
  Keys.insertAll_erase [] xs

/-! ## Operations -/

@[simp] theorem Except.map_ok_erase (v : Value) :
    (Except.ok v : Except Fault Value).map Value.erase = .ok v.erase := rfl

@[simp] theorem Except.map_int_erase (x : Except Fault Int) :
    (Value.int <$> x).map Value.erase = Value.int <$> x := by
  cases x <;> rfl

theorem Entries.equal_erase (a b : List (Value × Value)) :
    Entries.equal (a.map eraseEntry) (b.map eraseEntry) = Entries.equal a b := by
  simp only [Entries.equal, List.length_map, List.all_map, Function.comp_def]
  congr 1
  apply List.all_congr rfl
  intro e
  have := Entries.find_erase (k := e.1) (es := b)
  simp only [eraseEntry] at this ⊢
  rw [this]
  cases Entries.find e.1 b <;> simp [Value.keyEq_erase]

theorem MapOp.apply_erase (o : MapOp) (vs : List Value) :
    o.apply (eraseValues vs) = (o.apply vs).map Value.erase := by
  rcases vs with _ | ⟨m, _ | ⟨k, _ | ⟨v, _ | ⟨w, rest⟩⟩⟩⟩ <;> cases o <;>
    simp only [eraseValues, MapOp.apply] <;> first
    | rfl
    | (apply onMap_erase
       intro es d
       simp [Entries.has_erase, Entries.find_erase, Entries.insert_erase, Entries.remove_erase,
         Entries.index_erase, Value.erase_mapOf, Value.erase_tuple, Value.erase,
         eraseValues_eq_map, eraseEntry, Option.getD_map, Value.keyEq_erase]
       try (split <;> simp_all [Except.map, Value.erase_mapOf]))
    | simp [Value.erase_mapOf]
    | (apply onMap_erase
       intro es d
       apply onMap_erase
       intro es' d'
       simp [Entries.equal_erase, Value.erase])

theorem SetOp.apply_erase (o : SetOp) (vs : List Value) :
    o.apply (eraseValues vs) = (o.apply vs).map Value.erase := by
  rcases vs with _ | ⟨s, _ | ⟨t, _ | ⟨u, rest⟩⟩⟩ <;> cases o <;>
    simp only [eraseValues, SetOp.apply] <;> first
    | rfl
    | (apply onSet_erase
       intro a
       first
       | (apply onSet_erase
          intro b
          simp [SetCombine.run_erase, SetRelation.test_erase, Value.erase_setOf, Value.erase])
       | simp [Keys.has_erase, Keys.insert_erase, Keys.remove_erase, Value.erase_setOf,
           Value.erase, eraseValues_eq_map])
    | (apply onList_erase
       intro xs
       simp [Keys.insertAll_nil_erase, Value.erase_setOf])
    | simp [Value.erase_setOf]

theorem strsOf_erase : ∀ vs : List Value, strsOf (vs.map Value.erase) = strsOf vs
  | [] => rfl
  | v :: vs => by cases v <;> simp [strsOf, Value.erase, strsOf_erase vs]

theorem ListOp.join_erase (vs : List Value) :
    ListOp.join.apply (eraseValues vs) = (ListOp.join.apply vs).map Value.erase := by
  match vs with
  | [.str sep, l] =>
    simp only [eraseValues, Value.erase, ListOp.apply]
    apply onList_erase
    intro xs
    rw [strsOf_erase]
    split <;> rfl
  | [] => rfl
  | [v] => cases v <;> rfl
  | a :: b :: c :: rest => cases a <;> rfl
  | [.int _, _] | [.float _, _] | [.bool _, _] | [.unit, _] | [.record .., _]
  | [.variant .., _] | [.list _, _] | [.closure .., _] | [.function .., _] | [.handle .., _]
  | [.window .., _] => rfl

/-- `slice`, `insert` and `removeAt` read the integers among their operands,
which erasing leaves as they are, and move the other values. -/
theorem ListOp.slice_erase (vs : List Value) :
    ListOp.slice.apply (eraseValues vs) = (ListOp.slice.apply vs).map Value.erase := by
  rcases vs with _ | ⟨l, _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩⟩
  case cons.cons.cons.nil =>
    cases a <;> cases b <;> try rfl
    simp only [eraseValues, Value.erase, ListOp.apply]
    apply onList_erase
    intro xs
    simp only [List.length_map]
    split <;> simp [Except.map, Value.erase, eraseValues_eq_map, List.map_take, List.map_drop]
  all_goals first | rfl | (cases a <;> rfl) | (cases a <;> cases b <;> rfl)

theorem ListOp.insert_erase (vs : List Value) :
    ListOp.insert.apply (eraseValues vs) = (ListOp.insert.apply vs).map Value.erase := by
  rcases vs with _ | ⟨l, _ | ⟨a, _ | ⟨x, _ | ⟨c, rest⟩⟩⟩⟩
  case cons.cons.cons.nil =>
    cases a <;> try rfl
    simp only [eraseValues, Value.erase, ListOp.apply]
    apply onList_erase
    intro xs
    simp only [List.length_map]
    split <;> simp [Except.map, Value.erase, eraseValues_eq_map, List.map_take, List.map_drop]
  all_goals first | rfl | (cases a <;> rfl)

theorem ListOp.removeAt_erase (vs : List Value) :
    ListOp.removeAt.apply (eraseValues vs) = (ListOp.removeAt.apply vs).map Value.erase := by
  rcases vs with _ | ⟨l, _ | ⟨a, _ | ⟨c, rest⟩⟩⟩
  case cons.cons.nil =>
    cases a <;> try rfl
    simp only [eraseValues, Value.erase, ListOp.apply]
    apply onList_erase
    intro xs
    simp only [List.length_map]
    split <;> simp [Except.map, Value.erase, eraseValues_eq_map, List.map_take, List.map_drop]
  all_goals first | rfl | (cases a <;> rfl)

/-- A list of strings is its own erasure. -/
theorem strings_erase (ss : List String) : (strings ss).erase = strings ss := by
  simp only [strings, Value.erase, eraseValues_eq_map, List.map_map]
  rfl

theorem ints_erase (ns : List Nat) : (ints ns).erase = ints ns := by
  simp only [ints, Value.erase, eraseValues_eq_map, List.map_map]
  rfl

/-- The functions that split a string read only strings, which erasing leaves
as they are. -/
theorem ListOp.splitting_erase (o : ListOp)
    (ho : o = .chars ∨ o = .split ∨ o = .lines ∨ o = .splitWhitespace ∨ o = .bytes ∨
      o = .codePoints ∨ o = .nextLine) (vs : List Value) :
    o.apply (eraseValues vs) = (o.apply vs).map Value.erase := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (cases a <;> first | rfl | (cases b <;> first | rfl |
        simp [eraseValues, Value.erase, ListOp.apply, Except.map, strings_erase]))
    | (cases a <;> first | rfl | simp [eraseValues, Value.erase, ListOp.apply, Except.map,
        strings_erase, ints_erase])

theorem intsOf_erase : ∀ vs : List Value, intsOf (vs.map Value.erase) = intsOf vs
  | [] => rfl
  | v :: vs => by cases v <;> simp [intsOf, Value.erase, intsOf_erase vs]

/-- Decoding bytes reads only integers and gives strings. -/
theorem ListOp.fromUtf8_erase (lossy : Bool) (vs : List Value) :
    (ListOp.fromUtf8 lossy).apply (eraseValues vs) =
      ((ListOp.fromUtf8 lossy).apply vs).map Value.erase := by
  match vs with
  | [l] =>
    simp only [eraseValues, ListOp.apply]
    apply onList_erase
    intro xs
    rw [intsOf_erase]
    split <;> try rfl
    split <;> simp [Except.map, Value.erase, strings_erase]
  | [] => rfl
  | _ :: _ :: _ => rfl

theorem ListOp.fromCodePoint_erase (vs : List Value) :
    ListOp.fromCodePoint.apply (eraseValues vs) = (ListOp.fromCodePoint.apply vs).map Value.erase := by
  match vs with
  | [a] => cases a <;> simp [eraseValues, Value.erase, ListOp.apply, Except.map, strings_erase]
  | [] => rfl
  | a :: _ :: _ => cases a <;> rfl

/-- `checked` and `narrow` read and give only integers. -/
theorem ListOp.fitting_erase (o : ListOp)
    (ho : (∃ c lo hi, o = .checked c lo hi) ∨ ∃ lo hi, o = .narrow lo hi) (vs : List Value) :
    o.apply (eraseValues vs) = (o.apply vs).map Value.erase := by
  rcases ho with ⟨c, lo, hi, rfl⟩ | ⟨lo, hi, rfl⟩ <;>
    rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> try rfl
  all_goals first
    | (cases a <;> try rfl) <;> (cases b <;> try rfl) <;>
        simp only [eraseValues, Value.erase, ListOp.apply, Except.map, fitting] <;>
        split <;> rfl
    | (cases a <;> try rfl) <;> simp only [eraseValues, Value.erase, ListOp.apply, Except.map,
        fitting] <;> split <;> rfl

/-- `find` reads only strings and gives integers, which erasing leaves as they are. -/
theorem ListOp.find_erase (last : Bool) (vs : List Value) :
    (ListOp.find last).apply (eraseValues vs) = ((ListOp.find last).apply vs).map Value.erase := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> try rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> try rfl
    simp only [eraseValues, Value.erase, ListOp.apply]
    rcases Str.find last _ _ with _ | n
    · rfl
    · simp only []
      rcases IntTy.i64.check (n : Int) with _ | m <;> rfl
  · cases a <;> cases b <;> rfl

theorem ListOp.apply_erase (o : ListOp) (vs : List Value) :
    o.apply (eraseValues vs) = (o.apply vs).map Value.erase := by
  cases o
  case join => exact ListOp.join_erase vs
  case chars => exact ListOp.splitting_erase _ (.inl rfl) vs
  case split => exact ListOp.splitting_erase _ (.inr (.inl rfl)) vs
  case lines => exact ListOp.splitting_erase _ (.inr (.inr (.inl rfl))) vs
  case splitWhitespace => exact ListOp.splitting_erase _ (.inr (.inr (.inr (.inl rfl)))) vs
  case bytes => exact ListOp.splitting_erase _ (.inr (.inr (.inr (.inr (.inl rfl))))) vs
  case codePoints => exact ListOp.splitting_erase _ (.inr (.inr (.inr (.inr (.inr (.inl rfl)))))) vs
  case nextLine => exact ListOp.splitting_erase _ (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))) vs
  case slice => exact ListOp.slice_erase vs
  case insert => exact ListOp.insert_erase vs
  case removeAt => exact ListOp.removeAt_erase vs
  case find last => exact ListOp.find_erase last vs
  case fromUtf8 lossy => exact ListOp.fromUtf8_erase lossy vs
  case fromCodePoint => exact ListOp.fromCodePoint_erase vs
  case checked o lo hi => exact ListOp.fitting_erase _ (.inl ⟨o, lo, hi, rfl⟩) vs
  case narrow lo hi => exact ListOp.fitting_erase _ (.inr ⟨lo, hi, rfl⟩) vs
  case truncate lo hi =>
    rcases vs with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · rfl
    · cases a <;> try rfl
      simp only [eraseValues, Value.erase, ListOp.apply, Except.map, truncating, fitting]
      split <;> (try split) <;> rfl
    · cases a <;> rfl
  all_goals rcases vs with _ | ⟨l, _ | ⟨x, _ | ⟨y, rest⟩⟩⟩ <;>
    simp only [eraseValues, ListOp.apply] <;> first
    | rfl
    | (apply onList_erase
       intro xs
       simp [Value.erase, eraseValues_eq_map])
    | (simp only [Value.int?_erase]
       split <;> simp [Except.map, Value.erase, eraseValues_rangeValues])

/-- Sorting by keys sees through marks: the structural order of erased keys is
theirs (traits.structural-calls). -/
theorem sortByKeys_erase (orders : CtorOrders) (d : Bool) (ks xs : List Value) :
    sortByKeys orders d (ks.map Value.erase) (xs.map Value.erase) =
      (sortByKeys orders d ks xs).map Value.erase := by
  unfold sortByKeys
  rw [List.zip_map, List.map_map, ← List.map_mergeSort (r := fun a b => keyBefore orders d a.1 b.1)]
  · simp only [List.map_map]
    rfl
  · intro a _ b _
    simp [keyBefore, Value.order_erase]

theorem sortedByKey_erase (d : Bool) (orders : CtorOrders) (vs : List Value) :
    (Op.sortedByKey d orders).apply (eraseValues vs) =
      ((Op.sortedByKey d orders).apply vs).map Value.erase := by
  rcases vs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  case cons.cons.nil =>
    cases a <;> cases b <;> try rfl
    simp only [eraseValues, Value.erase, Op.apply, eraseValues_eq_map, Except.map,
      sortByKeys_erase]
  all_goals first | rfl | (cases a <;> rfl) | (cases a <;> cases b <;> rfl)

/-- An operation sees through marks: applied to erased operands, it gives its
value erased. -/
theorem Op.apply_erase (o : Op) (vs : List Value) :
    o.apply (eraseValues vs) = (o.apply vs).map Value.erase := by
  rcases o.cases_scalar with rfl | rfl | ⟨c, orders, rfl⟩ | rfl | ⟨d, orders, rfl⟩ | ⟨k, rfl⟩ |
    ⟨l, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩ | (rfl | rfl) | ho
  · simp only [Op.apply, Except.map, Value.erase_tuple]
  · rcases vs with _ | ⟨v, _ | ⟨w, rest⟩⟩ <;>
      simp [eraseValues, Op.apply, Except.map, Value.erase, Value.shown_erase]
  · rcases vs with _ | ⟨v, _ | ⟨w, _ | ⟨u, rest⟩⟩⟩ <;>
      simp [eraseValues, Op.apply, Except.map, Value.erase, Cmp.values_erase]
  · rcases vs with _ | ⟨v, _ | ⟨w, _ | ⟨u, rest⟩⟩⟩ <;>
      simp [eraseValues, Op.apply, Except.map, Value.erase, Value.same_erase]
  · exact sortedByKey_erase d orders vs
  · rfl
  · exact ListOp.apply_erase l vs
  · exact MapOp.apply_erase m vs
  · exact SetOp.apply_erase m vs
  all_goals try (rcases vs with _ | ⟨v, _ | ⟨w, rest⟩⟩ <;> simp [eraseValues, Op.apply, Except.map]; done)
  · rcases vs with _ | ⟨v, _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · have hl := ListOp.apply_erase .slice [v, a, b]
      cases v
      case str s =>
        show Op.slice.applyScalars (eraseValues [.str s, a, b]) =
          (Op.slice.applyScalars [.str s, a, b]).map Value.erase
        simp only [Op.applyScalars, mapM_scalar?_erase]
        split
        · cases Op.compute _ _ <;> simp [Functor.map, Except.map, Scalar.erase_value]
        · rfl
      all_goals exact hl
    · rfl
  · simp only [Op.apply_of_scalar ho, Op.applyScalars, mapM_scalar?_erase]
    split
    · cases o.compute _ <;> simp [Functor.map, Except.map, Scalar.erase_value]
    · rfl

end Stilt
