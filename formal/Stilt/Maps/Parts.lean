import Stilt.Maps

/-!
# The parts of maps and sets

What a function of maps or sets gives is made of its operands and their parts:
the keys, values and default of a map, and the elements of a set or a list,
in new maps, sets, lists and tuples. So a property of values that holds of
numbers, Booleans and strings and passes through records and lists, as being
safe and being justified do, holds of what it gives (`Value.Hereditary`). The
lemmas about entries and elements serve the soundness proof too, which gives
those parts their types.
-/

namespace Stilt

/-! ## Reading what a map or a set holds -/

theorem mapM_entry? : ∀ es : List (Value × Value), (es.map Value.entry).mapM Value.entry? = some es
  | [] => rfl
  | e :: es => by simp [Value.entry, Value.entry?, mapM_entry? es]

@[simp] theorem Value.map?_mapOf (es : List (Value × Value)) (d : Option Value) :
    (Value.mapOf es d).map? = some (es, d) := by
  have h : (defaultField == entriesField) = false := by decide
  cases d <;> simp only [Value.map?, Value.mapOf, Value.listField?, Value.list?, List.lookup_cons, h,
    beq_self_eq_true, Option.bind_some, mapM_entry?, Option.map_some, List.head?, Option.toList] <;> rfl

@[simp] theorem Value.set?_setOf (ks : List Value) : (Value.setOf ks).set? = some ks := by
  simp [Value.set?, Value.setOf, Value.listField?, Value.list?]

@[simp] theorem onMap_mapOf (es : List (Value × Value)) (d : Option Value)
    (f : List (Value × Value) → Option Value → Except Fault Value) :
    onMap (.mapOf es d) f = f es d := by
  simp [onMap]

@[simp] theorem onSet_setOf (ks : List Value) (f : List Value → Except Fault Value) :
    onSet (.setOf ks) f = f ks := by
  simp [onSet]

@[simp] theorem onList_list (vs : List Value) (f : List Value → Except Fault Value) :
    onList (.list vs) f = f vs := rfl

theorem onMap_ok {m w : Value} {f : List (Value × Value) → Option Value → Except Fault Value}
    (h : onMap m f = .ok w) : ∃ es d, m.map? = some (es, d) ∧ f es d = .ok w := by
  unfold onMap at h
  split at h
  · exact ⟨_, _, ‹_›, h⟩
  · cases h

theorem onSet_ok {s w : Value} {f : List Value → Except Fault Value} (h : onSet s f = .ok w) :
    ∃ ks, s.set? = some ks ∧ f ks = .ok w := by
  unfold onSet at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

theorem onList_ok {l w : Value} {f : List Value → Except Fault Value} (h : onList l f = .ok w) :
    ∃ vs, l.list? = some vs ∧ f vs = .ok w := by
  unfold onList at h
  split at h
  · exact ⟨_, ‹_›, h⟩
  · cases h

theorem Value.list?_eq_some {v : Value} {vs : List Value} (h : v.list? = some vs) : v = .list vs := by
  cases v <;> simp_all [Value.list?]

theorem Value.entry?_eq_some {v : Value} {e : Value × Value} (h : v.entry? = some e) :
    v = .entry e := by
  unfold Value.entry? at h
  split at h
  · cases h
    rfl
  · cases h

theorem mem_of_mapM_entry? : ∀ {us : List Value} {es : List (Value × Value)},
    us.mapM Value.entry? = some es → ∀ e ∈ es, Value.entry e ∈ us
  | [], es, h => by simp at h; subst h; simp
  | u :: us, es, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨e, he, es', hes', rfl⟩ := h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · rw [← Value.entry?_eq_some he]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_mapM_entry? hes' e' he')

/-- A record's field that holds a list, as `listField?` reads it. -/
theorem Value.listField?_eq_some {v : Value} {f : Name} {vs : List Value}
    (h : v.listField? f = some vs) : ∃ R fields, v = .record R fields ∧ (f, .list vs) ∈ fields := by
  cases v with
  | record R fields =>
    simp only [Value.listField?, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, hl⟩ := h
    exact ⟨R, fields, rfl, Value.list?_eq_some hl ▸ mem_of_lookup hx⟩
  | _ => simp [Value.listField?] at h

/-- What `map?` reads: entries, from a field that holds a list of them, and a
default, the head of another. -/
theorem Value.map?_eq_some {v : Value} {es : List (Value × Value)} {d : Option Value}
    (h : v.map? = some (es, d)) : ∃ us ds, v.listField? entriesField = some us ∧
      us.mapM Value.entry? = some es ∧ v.listField? defaultField = some ds ∧ d = ds.head? := by
  unfold Value.map? at h
  split at h
  · rename_i us ds hus hds
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨es', hes, rfl, rfl⟩ := h
    exact ⟨us, ds, hus, hes, hds, rfl⟩
  · cases h

/-! ## Entries and elements -/

section

variable {Q : Value → Prop}

theorem Entries.mem_find {k v : Value} {es : List (Value × Value)}
    (h : Entries.find k es = some v) : ∃ e ∈ es, e.2 = v := by
  unfold Entries.find at h
  cases hf : es.find? (fun e => k.keyEq e.1) with
  | none => rw [hf] at h; cases h
  | some e => rw [hf] at h; cases h; exact ⟨e, List.mem_of_find?_eq_some hf, rfl⟩

/-- `m[k]` gives a value of the map or its default. -/
theorem Entries.index_ok {k w : Value} {es : List (Value × Value)} {d : Option Value}
    (h : Entries.index k es d = .ok w) : (∃ e ∈ es, e.2 = w) ∨ d = some w := by
  unfold Entries.index at h
  split at h
  · cases h
    exact .inl (Entries.mem_find ‹_›)
  · cases h
    exact .inr rfl
  · cases h

/-- `m.get_or(k, d)` gives a value of the map or `d`. -/
theorem Entries.getD_find (k v : Value) (es : List (Value × Value)) :
    (∃ e ∈ es, e.2 = (Entries.find k es).getD v) ∨ (Entries.find k es).getD v = v := by
  cases hf : Entries.find k es with
  | none => exact .inr rfl
  | some x => exact .inl (Entries.mem_find hf)

theorem Entries.insert_keys {k v : Value} {es : List (Value × Value)} (hk : Q k)
    (h : ∀ e ∈ es, Q e.1) : ∀ e ∈ Entries.insert k v es, Q e.1 := by
  unfold Entries.insert
  split
  · intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    split
    · exact h e' he'
    · exact h e' he'
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact h e he
    · rw [List.mem_singleton] at he
      subst he
      exact hk

theorem Entries.insert_values {k v : Value} {es : List (Value × Value)} (hv : Q v)
    (h : ∀ e ∈ es, Q e.2) : ∀ e ∈ Entries.insert k v es, Q e.2 := by
  unfold Entries.insert
  split
  · intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    split
    · exact hv
    · exact h e' he'
  · intro e he
    rcases List.mem_append.1 he with he | he
    · exact h e he
    · rw [List.mem_singleton] at he
      subst he
      exact hv

theorem Entries.mem_remove {k : Value} {es : List (Value × Value)} {e : Value × Value}
    (h : e ∈ Entries.remove k es) : e ∈ es :=
  (List.mem_filter.1 h).1

theorem Keys.insert_all {x : Value} {ks : List Value} (hx : Q x) (h : ∀ k ∈ ks, Q k) :
    ∀ k ∈ Keys.insert x ks, Q k := by
  unfold Keys.insert
  split
  · exact h
  · intro k hk
    rcases List.mem_append.1 hk with hk | hk
    · exact h k hk
    · rw [List.mem_singleton] at hk
      exact hk ▸ hx

theorem Keys.mem_remove {x k : Value} {ks : List Value} (h : k ∈ Keys.remove x ks) : k ∈ ks :=
  (List.mem_filter.1 h).1

theorem Keys.insertAll_all : ∀ {ks xs : List Value}, (∀ k ∈ ks, Q k) → (∀ x ∈ xs, Q x) →
    ∀ k ∈ Keys.insertAll ks xs, Q k
  | _, [], h, _ => h
  | _, x :: _, h, hxs => by
    rw [Keys.insertAll]
    exact Keys.insertAll_all (Keys.insert_all (hxs x List.mem_cons_self) h)
      fun y hy => hxs y (List.mem_cons_of_mem _ hy)

theorem SetCombine.run_all (c : SetCombine) {a b : List Value} (ha : ∀ k ∈ a, Q k)
    (hb : ∀ k ∈ b, Q k) : ∀ k ∈ c.run a b, Q k := by
  intro k hk
  cases c <;> simp only [SetCombine.run, List.mem_append, List.mem_filter] at hk
  · rcases hk with hk | ⟨hk, -⟩
    · exact ha k hk
    · exact hb k hk
  · exact ha k hk.1
  · exact ha k hk.1
  · rcases hk with ⟨hk, -⟩ | ⟨hk, -⟩
    · exact ha k hk
    · exact hb k hk

end

/-! ## Hereditary properties -/

/-- A property of values that holds of every number, Boolean, string and handle,
and of a record or a list exactly when it holds of its parts. -/
structure Value.Hereditary (P : Value → Prop) : Prop where
  int : ∀ n, P (.int n)
  float : ∀ x, P (.float x)
  bool : ∀ b, P (.bool b)
  str : ∀ s, P (.str s)
  record : ∀ R fields, P (.record R fields) ↔ ∀ fv ∈ fields, P fv.2
  list : ∀ vs, P (.list vs) ↔ ∀ v ∈ vs, P v
  handle : ∀ u i, P (.handle u i)

namespace Value.Hereditary

variable {P : Value → Prop} (hP : Value.Hereditary P)
include hP

theorem tuple {vs : List Value} (h : ∀ v ∈ vs, P v) : P (.tuple vs) :=
  (hP.record _ _).2 fun _ hfv => h _ (mem_positionsFrom hfv)

theorem mapOf {es : List (Value × Value)} {d : Option Value} (hk : ∀ e ∈ es, P e.1)
    (hv : ∀ e ∈ es, P e.2) (hd : ∀ x, d = some x → P x) : P (.mapOf es d) := by
  refine (hP.record _ _).2 fun fv hfv => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfv
  rcases hfv with rfl | rfl
  · refine (hP.list _).2 fun u hu => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hu
    refine (hP.list _).2 fun x hx => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hk e he
    · exact hv e he
  · refine (hP.list _).2 fun x hx => hd x ?_
    cases d <;> simp_all

theorem setOf {ks : List Value} (h : ∀ k ∈ ks, P k) : P (.setOf ks) := by
  refine (hP.record _ _).2 fun fv hfv => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfv
  subst hfv
  exact (hP.list _).2 h

theorem listField? {v : Value} {f : Name} {vs : List Value} (hv : P v)
    (h : v.listField? f = some vs) : ∀ u ∈ vs, P u := by
  obtain ⟨R, fields, rfl, hf⟩ := Value.listField?_eq_some h
  exact (hP.list _).1 ((hP.record _ _).1 hv _ hf)

/-- The parts of a map. -/
theorem map? {v : Value} {es : List (Value × Value)} {d : Option Value} (hv : P v)
    (h : v.map? = some (es, d)) :
    (∀ e ∈ es, P e.1) ∧ (∀ e ∈ es, P e.2) ∧ ∀ x, d = some x → P x := by
  obtain ⟨us, ds, hus, hes, hds, rfl⟩ := Value.map?_eq_some h
  have hu := hP.listField? hv hus
  have he : ∀ e ∈ es, P e.1 ∧ P e.2 := fun e he => by
    have := (hP.list _).1 (hu _ (mem_of_mapM_entry? hes e he))
    exact ⟨this _ List.mem_cons_self, this _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  refine ⟨fun e h => (he e h).1, fun e h => (he e h).2, fun x hx => ?_⟩
  exact hP.listField? hv hds x (List.mem_of_mem_head? hx)

theorem checked {x : Except Fault Int} {w : Value} (h : (Value.int <$> x) = .ok w) : P w := by
  cases x with
  | error => cases h
  | ok n => cases h; exact hP.int n

/-- What `f` gives from a map's parts has a hereditary property when they have it. -/
theorem onMap {m w : Value} {f : List (Value × Value) → Option Value → Except Fault Value}
    (hm : P m) (h : onMap m f = .ok w)
    (hf : ∀ es d, (∀ e ∈ es, P e.1) → (∀ e ∈ es, P e.2) → (∀ x, d = some x → P x) →
      f es d = .ok w → P w) : P w :=
  let ⟨_, _, hmap, h⟩ := onMap_ok h
  let ⟨hk, hv, hd⟩ := hP.map? hm hmap
  hf _ _ hk hv hd h

/-- What `f` gives from a set's elements has a hereditary property when they have it. -/
theorem onSet {s w : Value} {f : List Value → Except Fault Value} (hs : P s)
    (h : onSet s f = .ok w) (hf : ∀ ks, (∀ k ∈ ks, P k) → f ks = .ok w → P w) : P w :=
  let ⟨_, hset, h⟩ := onSet_ok h
  hf _ (hP.listField? hs hset) h

/-- What a function of maps gives has a hereditary property when its operands
have it. -/
theorem mapOp {o : MapOp} {vs : List Value} (hvs : ∀ v ∈ vs, P v) {w : Value}
    (h : o.apply vs = .ok w) : P w := by
  unfold MapOp.apply at h
  split at h
  next => cases h; exact hP.mapOf (by simp) (by simp) (by simp)
  next d =>
    cases h
    exact hP.mapOf (by simp) (by simp) fun x hx => by cases hx; exact hvs d (by simp)
  next m => exact hP.onMap (hvs m (by simp)) h fun _ _ _ _ _ h => hP.checked h
  next m => exact hP.onMap (hvs m (by simp)) h fun _ _ _ _ _ h => by cases h; exact hP.bool _
  next m k => exact hP.onMap (hvs m (by simp)) h fun _ _ _ _ _ h => by cases h; exact hP.bool _
  next m k =>
    exact hP.onMap (hvs m (by simp)) h fun _ _ _ hv hd h =>
      (Entries.index_ok h).elim (fun ⟨e, he, hw⟩ => hw ▸ hv e he) (hd _)
  next m k v =>
    refine hP.onMap (hvs m (by simp)) h fun es _ _ hv _ h => ?_
    cases h
    rcases Entries.getD_find k v es with ⟨e, he, hw⟩ | hw
    · exact hw ▸ hv e he
    · rw [hw]
      exact hvs v (by simp)
  next m k v =>
    refine hP.onMap (hvs m (by simp)) h fun _ _ hk hv hd h => ?_
    cases h
    exact hP.mapOf (Entries.insert_keys (hvs k (by simp)) hk)
      (Entries.insert_values (hvs v (by simp)) hv) hd
  next m k =>
    refine hP.onMap (hvs m (by simp)) h fun _ _ hk hv hd h => ?_
    cases h
    exact hP.mapOf (fun e he => hk e (Entries.mem_remove he))
      (fun e he => hv e (Entries.mem_remove he)) hd
  next m =>
    refine hP.onMap (hvs m (by simp)) h fun _ _ hk _ _ h => ?_
    cases h
    refine (hP.list _).2 fun u hu => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hu
    exact hk e he
  next m =>
    refine hP.onMap (hvs m (by simp)) h fun _ _ _ hv _ h => ?_
    cases h
    refine (hP.list _).2 fun u hu => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hu
    exact hv e he
  next m =>
    refine hP.onMap (hvs m (by simp)) h fun _ _ hk hv _ h => ?_
    cases h
    refine (hP.list _).2 fun u hu => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hu
    exact hP.tuple (by simp [hk e he, hv e he])
  next m n =>
    refine hP.onMap (hvs m (by simp)) h fun _ _ _ _ _ h => ?_
    refine hP.onMap (hvs n (by simp)) h fun _ _ _ _ _ h => ?_
    cases h; exact hP.bool _
  next => cases h

theorem fitting (lo hi n : Int) : P (fitting lo hi n) := by
  unfold Stilt.fitting
  split <;> exact (hP.list _).2 (by simp [hP.int])

theorem ints (ns : List Nat) : P (ints ns) :=
  (hP.list _).2 fun v hv => by
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hv
    exact hP.int _

theorem strings (ss : List String) : P (strings ss) :=
  (hP.list _).2 fun v hv => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hv
    exact hP.str s

/-- What a function of lists gives has a hereditary property when its operands
have it. -/
theorem listOp {o : ListOp} {vs : List Value} (hvs : ∀ v ∈ vs, P v) {w : Value}
    (h : o.apply vs = .ok w) : P w := by
  unfold ListOp.apply at h
  split at h
  next l =>
    obtain ⟨xs, -, h⟩ := onList_ok h
    exact hP.checked h
  next l =>
    obtain ⟨xs, -, h⟩ := onList_ok h
    cases h; exact hP.bool _
  next l x =>
    obtain ⟨xs, hl, h⟩ := onList_ok h
    cases h
    have hxs := (hP.list xs).1 (Value.list?_eq_some hl ▸ hvs l (by simp))
    refine (hP.list _).2 fun v hv => ?_
    rcases List.mem_append.1 hv with hv | hv
    · exact hxs v hv
    · rw [List.mem_singleton.1 hv]; exact hvs x (by simp)
  next =>
    split at h
    · cases h
      refine (hP.list _).2 fun v hv => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
      exact hP.int _
    · cases h
  next l a b =>
    obtain ⟨xs, hl, h⟩ := onList_ok h
    have hxs := (hP.list xs).1 (Value.list?_eq_some hl ▸ hvs l (by simp))
    split at h
    · cases h
      exact (hP.list _).2 fun v hv => hxs v (List.mem_of_mem_drop (List.mem_of_mem_take hv))
    · cases h
  next l i x =>
    obtain ⟨xs, hl, h⟩ := onList_ok h
    have hxs := (hP.list xs).1 (Value.list?_eq_some hl ▸ hvs l (by simp))
    split at h
    · cases h
      refine (hP.list _).2 fun v hv => ?_
      rcases List.mem_append.1 hv with hv | hv
      · exact hxs v (List.mem_of_mem_take hv)
      · rcases List.mem_cons.1 hv with rfl | hv
        · exact hvs _ (by simp)
        · exact hxs v (List.mem_of_mem_drop hv)
    · cases h
  next l i =>
    obtain ⟨xs, hl, h⟩ := onList_ok h
    have hxs := (hP.list xs).1 (Value.list?_eq_some hl ▸ hvs l (by simp))
    split at h
    · cases h
      refine (hP.list _).2 fun v hv => ?_
      rcases List.mem_append.1 hv with hv | hv
      · exact hxs v (List.mem_of_mem_take hv)
      · exact hxs v (List.mem_of_mem_drop hv)
    · cases h
  next => cases h; exact hP.strings _
  next => cases h; exact hP.ints _
  next => cases h; exact hP.ints _
  next => cases h; exact hP.strings _
  next l =>
    obtain ⟨xs, -, h⟩ := onList_ok h
    split at h
    · cases h
      split
      · exact hP.str _
      · exact hP.strings _
    · cases h
  next => cases h; exact hP.strings _
  next => cases h; exact hP.fitting _ _ _
  next => cases h; exact hP.fitting _ _ _
  next =>
    cases h
    unfold truncating
    split
    · exact hP.fitting _ _ _
    · exact (hP.list _).2 (by simp)
  next =>
    split at h
    · cases h; exact (hP.list _).2 (by simp)
    · cases hc : IntTy.i64.check _ <;> rw [hc] at h <;> cases h
      exact (hP.list _).2 (by simp [hP.int])
  next => cases h; exact hP.strings _
  next => cases h; exact hP.strings _
  next => cases h; exact hP.strings _
  next =>
    obtain ⟨xs, -, h⟩ := onList_ok h
    split at h
    · cases h; exact hP.str _
    · cases h
  next => cases h

theorem setOp {o : SetOp} {vs : List Value} (hvs : ∀ v ∈ vs, P v) {w : Value}
    (h : o.apply vs = .ok w) : P w := by
  unfold SetOp.apply at h
  split at h
  next => cases h; exact hP.setOf (by simp)
  next l =>
    obtain ⟨xs, hl, h⟩ := onList_ok h
    cases h
    have hxs := (hP.list xs).1 (Value.list?_eq_some hl ▸ hvs l (by simp))
    exact hP.setOf (Keys.insertAll_all (by simp) hxs)
  next s => exact hP.onSet (hvs s (by simp)) h fun _ _ h => hP.checked h
  next s => exact hP.onSet (hvs s (by simp)) h fun _ _ h => by cases h; exact hP.bool _
  next s x => exact hP.onSet (hvs s (by simp)) h fun _ _ h => by cases h; exact hP.bool _
  next s x =>
    refine hP.onSet (hvs s (by simp)) h fun _ hk h => ?_
    cases h
    exact hP.setOf (Keys.insert_all (hvs x (by simp)) hk)
  next s x =>
    refine hP.onSet (hvs s (by simp)) h fun _ hk h => ?_
    cases h
    exact hP.setOf fun k hk' => hk k (Keys.mem_remove hk')
  next s => exact hP.onSet (hvs s (by simp)) h fun _ hk h => by cases h; exact (hP.list _).2 hk
  next c s t =>
    refine hP.onSet (hvs s (by simp)) h fun _ ha h => ?_
    refine hP.onSet (hvs t (by simp)) h fun _ hb h => ?_
    cases h
    exact hP.setOf (c.run_all ha hb)
  next r s t =>
    refine hP.onSet (hvs s (by simp)) h fun _ _ h => ?_
    refine hP.onSet (hvs t (by simp)) h fun _ _ h => ?_
    cases h
    exact hP.bool _
  next => cases h

end Value.Hereditary

end Stilt
