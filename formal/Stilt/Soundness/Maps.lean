import Stilt.Soundness.Lists

/-!
# Maps and sets

What a built-in operation ends with, and the soundness of the functions of
maps and sets. A function of maps or sets applied to operands of its
signature's types gives a value of the type it gives, or panics, as `m[k]`
does with `missing-key` for a missing key when the map has no default
(std.maps); it is never stuck. Each keeps a map's keys at its key type and its
values and default at its value type.
-/

namespace Stilt

section

variable {D : Decls} {η : REnv}

theorem ValuesAt.nil_inv {vs : List Value} (h : ValuesAt D η vs []) : vs = [] := by
  cases h
  rfl

theorem ValuesAt.one_inv {vs : List Value} {τ : Ty} (h : ValuesAt D η vs [τ]) :
    ∃ v, vs = [v] ∧ Value.Typed D v (τ.close η) := by
  cases h with
  | cons hv hvs => cases hvs; exact ⟨_, rfl, hv⟩

theorem ValuesAt.two_inv {vs : List Value} {τ τ' : Ty} (h : ValuesAt D η vs [τ, τ']) :
    ∃ v v', vs = [v, v'] ∧ Value.Typed D v (τ.close η) ∧ Value.Typed D v' (τ'.close η) := by
  cases h with
  | cons hv hvs => cases hvs with
    | cons hv' hvs' => cases hvs'; exact ⟨_, _, rfl, hv, hv'⟩

theorem ValuesAt.three_inv {vs : List Value} {τ τ' τ'' : Ty} (h : ValuesAt D η vs [τ, τ', τ'']) :
    ∃ v v' v'', vs = [v, v', v''] ∧ Value.Typed D v (τ.close η) ∧
      Value.Typed D v' (τ'.close η) ∧ Value.Typed D v'' (τ''.close η) := by
  cases h with
  | cons hv hvs =>
    obtain ⟨v', v'', rfl, hv', hv''⟩ := hvs.two_inv
    exact ⟨_, _, _, rfl, hv, hv', hv''⟩

/-- What a sound operation ends with: a value of its type, or a panic. -/
def Applied (D : Decls) (x : Except Fault Value) (σ : STy) : Prop :=
  (∃ v, x = .ok v ∧ Value.Typed D v σ) ∨ ∃ k, x = .error (.panic k)

/-- An integer of the type, or a panic. -/
def IntOk (k : IntTy) (x : Except Fault Int) : Prop :=
  (∃ n, x = .ok n ∧ k.Contains n) ∨ ∃ p, x = .error (.panic p)

theorem IntOk.check (k : IntTy) (n : Int) : IntOk k (k.check n) := by
  unfold IntTy.check
  split
  · exact .inl ⟨_, rfl, ‹_›⟩
  · exact .inr ⟨_, rfl⟩

/-- A length is an `i64`, or a panic (numbers.lengths-are-i64). -/
theorem Applied.length (n : Nat) : Applied D (Value.int <$> IntTy.i64.check n) STy.i64 := by
  rcases IntOk.check .i64 n with ⟨m, h, hm⟩ | ⟨p, h⟩
  · exact .inl ⟨.int m, by rw [h]; rfl, .int hm⟩
  · exact .inr ⟨p, by rw [h]; rfl⟩

/-- `m[k]` gives a value of the map or its default, or panics. -/
theorem Applied.index (k : Value) {es : List (Value × Value)} {d : Option Value} {σ : STy}
    (hv : ∀ e ∈ es, Value.Typed D e.2 σ) (hd : ∀ u, d = some u → Value.Typed D u σ) :
    Applied D (Entries.index k es d) σ := by
  unfold Entries.index
  cases hf : Entries.find k es with
  | some v =>
    obtain ⟨e, he, rfl⟩ := Entries.mem_find hf
    exact .inl ⟨_, rfl, hv e he⟩
  | none =>
    cases d with
    | some u => exact .inl ⟨_, rfl, hd u rfl⟩
    | none => exact .inr ⟨_, rfl⟩

theorem Value.Typed.getD_find {k v : Value} {es : List (Value × Value)} {σ : STy}
    (hvs : ∀ e ∈ es, Value.Typed D e.2 σ) (hv : Value.Typed D v σ) :
    Value.Typed D ((Entries.find k es).getD v) σ := by
  cases hf : Entries.find k es with
  | some x =>
    obtain ⟨e, he, rfl⟩ := Entries.mem_find hf
    exact hvs e he
  | none => exact hv

/-! ## The functions of maps -/

/-- The operand of a function of maps that takes the map alone. -/
theorem ValuesAt.map_inv {vs : List Value} {κ τ : Ty} (h : ValuesAt D η vs [.map κ τ]) :
    ∃ es d, vs = [.mapOf es d] ∧ (∀ e ∈ es, Value.Typed D e.1 (κ.close η)) ∧
      (∀ e ∈ es, Value.Typed D e.2 (τ.close η)) := by
  obtain ⟨m, rfl, hm⟩ := h.one_inv
  obtain ⟨es, d, rfl, hk, hv, -⟩ := hm.map_inv
  exact ⟨es, d, rfl, hk, hv⟩

/-! ## The functions of lists -/

/-- A list of strings is a `List<str>`. -/
theorem Value.Typed.strings (ss : List String) : Value.Typed D (strings ss) (.list .str) :=
  .list fun v hv => by
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hv
    exact .str

/-- A list of strings holds only strings. -/
theorem strsOf_typed : ∀ {xs : List Value}, (∀ v ∈ xs, Value.Typed D v .str) →
    ∃ ts, strsOf xs = some ts
  | [], _ => ⟨[], rfl⟩
  | v :: vs, h => by
    obtain ⟨s, rfl⟩ := (h v List.mem_cons_self).str_inv
    obtain ⟨ts, hts⟩ := strsOf_typed fun u hu => h u (List.mem_cons_of_mem _ hu)
    exact ⟨s :: ts, by simp [strsOf, hts]⟩

/-- An integer within a type's bounds, as a list of none or one, is a list of that
type. -/
theorem Value.Typed.fitting (k : IntTy) (n : Int) :
    Value.Typed D (Stilt.fitting k.min k.max n) (.list (.int k)) := by
  unfold Stilt.fitting
  split
  · exact .list fun v hv => by rw [List.mem_singleton.1 hv]; exact .int (by assumption)
  · exact .list (by simp)

/-- A list of integers of a type holds only integers. -/
theorem intsOf_typed {k : IntTy} : ∀ {xs : List Value}, (∀ v ∈ xs, Value.Typed D v (.int k)) →
    ∃ ns, intsOf xs = some ns
  | [], _ => ⟨[], rfl⟩
  | v :: vs, h => by
    obtain ⟨n, rfl, -⟩ := (h v List.mem_cons_self).int_inv
    obtain ⟨ns, hns⟩ := intsOf_typed fun u hu => h u (List.mem_cons_of_mem _ hu)
    exact ⟨n :: ns, by simp [intsOf, hns]⟩

theorem ListOp.Sig.apply {o : ListOp} {vs : List Value} {τs : List Ty} {τ : Ty} (h : o.Sig τs τ)
    (hvs : ValuesAt D η vs τs) : Applied D (o.apply vs) (τ.close η) := by
  cases h with
  | len =>
    obtain ⟨l, rfl, hl⟩ := hvs.one_inv
    obtain ⟨xs, rfl, -⟩ := hl.list_inv
    exact Applied.length xs.length
  | isEmpty =>
    obtain ⟨l, rfl, hl⟩ := hvs.one_inv
    obtain ⟨xs, rfl, -⟩ := hl.list_inv
    exact .inl ⟨_, rfl, .bool⟩
  | push =>
    obtain ⟨l, x, rfl, hl, hx⟩ := hvs.two_inv
    obtain ⟨xs, rfl, hxs⟩ := hl.list_inv
    refine .inl ⟨_, rfl, .list fun v hv => ?_⟩
    rcases List.mem_append.1 hv with hv | hv
    · exact hxs v hv
    · rw [List.mem_singleton.1 hv]; exact hx
  | range =>
    obtain ⟨u, w, rfl, hu, hw⟩ := hvs.two_inv
    obtain ⟨a, rfl, ha₁, ha₂⟩ := hu.int_inv
    obtain ⟨b, rfl, hb₁, hb₂⟩ := hw.int_inv
    refine .inl ⟨_, rfl, .list fun v hv => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    have hi := List.mem_range.1 hi
    refine .int ⟨by omega, ?_⟩
    split at hi <;> omega
  | fromUtf8 =>
    obtain ⟨l, rfl, hl⟩ := hvs.one_inv
    obtain ⟨xs, rfl, hxs⟩ := hl.list_inv
    obtain ⟨ns, hns⟩ := intsOf_typed hxs
    simp only [ListOp.apply, onList, Value.list?, hns]
    exact .inl ⟨_, rfl, Value.Typed.strings _⟩
  | fromUtf8Lossy =>
    obtain ⟨l, rfl, hl⟩ := hvs.one_inv
    obtain ⟨xs, rfl, hxs⟩ := hl.list_inv
    obtain ⟨ns, hns⟩ := intsOf_typed hxs
    simp only [ListOp.apply, onList, Value.list?, hns]
    exact .inl ⟨_, rfl, .str⟩
  | checked =>
    obtain ⟨u, w, rfl, hu, hw⟩ := hvs.two_inv
    obtain ⟨a, rfl, -⟩ := hu.int_inv
    obtain ⟨b, rfl, -⟩ := hw.int_inv
    exact .inl ⟨_, rfl, Value.Typed.fitting _ _⟩
  | narrow =>
    obtain ⟨u, rfl, hu⟩ := hvs.one_inv
    obtain ⟨n, rfl, -⟩ := hu.int_inv
    exact .inl ⟨_, rfl, Value.Typed.fitting _ _⟩
  | truncate =>
    obtain ⟨u, rfl, hu⟩ := hvs.one_inv
    obtain ⟨x, rfl, -⟩ := hu.float_inv
    refine .inl ⟨_, rfl, ?_⟩
    unfold truncating
    split
    · exact Value.Typed.fitting _ _
    · exact .list (by simp)
  | fromCodePoint =>
    obtain ⟨u, rfl, hu⟩ := hvs.one_inv
    obtain ⟨p, rfl, -⟩ := hu.int_inv
    exact .inl ⟨_, rfl, Value.Typed.strings _⟩
  | find =>
    obtain ⟨u, w, rfl, hu, hw⟩ := hvs.two_inv
    obtain ⟨s, rfl⟩ := hu.str_inv
    obtain ⟨t, rfl⟩ := hw.str_inv
    simp only [ListOp.apply]
    rcases Str.find _ s t with _ | n
    · exact .inl ⟨_, rfl, .list (by simp)⟩
    · simp only []
      rcases IntOk.check .i64 n with ⟨m, h, hm⟩ | ⟨p, h⟩
      · rw [h]
        exact .inl ⟨_, rfl, .list fun v hv => by rw [List.mem_singleton.1 hv]; exact .int hm⟩
      · rw [h]
        exact .inr ⟨p, rfl⟩
  | chars | nextLine =>
    obtain ⟨u, rfl, hu⟩ := hvs.one_inv
    obtain ⟨s, rfl⟩ := hu.str_inv
    exact .inl ⟨_, rfl, Value.Typed.strings _⟩
  | bytes =>
    obtain ⟨u, rfl, hu⟩ := hvs.one_inv
    obtain ⟨s, rfl⟩ := hu.str_inv
    refine .inl ⟨_, rfl, .list fun v hv => ?_⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hv
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 hn
    have := b.toNat_lt
    exact .int ⟨by simp [IntTy.min, IntTy.signed], by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩
  | codePoints =>
    obtain ⟨u, rfl, hu⟩ := hvs.one_inv
    obtain ⟨s, rfl⟩ := hu.str_inv
    refine .inl ⟨_, rfl, .list fun v hv => ?_⟩
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hv
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hn
    have := c.val.toNat_lt
    have h : c.toNat = c.val.toNat := rfl
    rw [h]
    exact .int ⟨by simp [IntTy.min, IntTy.signed], by simp [IntTy.max, IntTy.signed, IntTy.bits]; omega⟩
  | split =>
    obtain ⟨u, w, rfl, hu, hw⟩ := hvs.two_inv
    obtain ⟨s, rfl⟩ := hu.str_inv
    obtain ⟨t, rfl⟩ := hw.str_inv
    exact .inl ⟨_, rfl, Value.Typed.strings _⟩
  | lines =>
    obtain ⟨u, rfl, hu⟩ := hvs.one_inv
    obtain ⟨s, rfl⟩ := hu.str_inv
    exact .inl ⟨_, rfl, Value.Typed.strings _⟩
  | splitWhitespace =>
    obtain ⟨u, rfl, hu⟩ := hvs.one_inv
    obtain ⟨s, rfl⟩ := hu.str_inv
    exact .inl ⟨_, rfl, Value.Typed.strings _⟩
  | slice =>
    obtain ⟨l, u, w, rfl, hl, hu, hw⟩ := hvs.three_inv
    obtain ⟨xs, rfl, hxs⟩ := hl.list_inv
    obtain ⟨a, rfl, -⟩ := hu.int_inv
    obtain ⟨b, rfl, -⟩ := hw.int_inv
    simp only [ListOp.apply, onList, Value.list?]
    split
    · exact .inl ⟨_, rfl, .list fun v hv =>
        hxs v (List.mem_of_mem_drop (List.mem_of_mem_take hv))⟩
    · exact .inr ⟨_, rfl⟩
  | insert =>
    obtain ⟨l, u, x, rfl, hl, hu, hx⟩ := hvs.three_inv
    obtain ⟨xs, rfl, hxs⟩ := hl.list_inv
    obtain ⟨i, rfl, -⟩ := hu.int_inv
    simp only [ListOp.apply, onList, Value.list?]
    split
    · refine .inl ⟨_, rfl, .list fun v hv => ?_⟩
      rcases List.mem_append.1 hv with hv | hv
      · exact hxs v (List.mem_of_mem_take hv)
      · rcases List.mem_cons.1 hv with rfl | hv
        · exact hx
        · exact hxs v (List.mem_of_mem_drop hv)
    · exact .inr ⟨_, rfl⟩
  | removeAt =>
    obtain ⟨l, u, rfl, hl, hu⟩ := hvs.two_inv
    obtain ⟨xs, rfl, hxs⟩ := hl.list_inv
    obtain ⟨i, rfl, -⟩ := hu.int_inv
    simp only [ListOp.apply, onList, Value.list?]
    split
    · refine .inl ⟨_, rfl, .list fun v hv => ?_⟩
      rcases List.mem_append.1 hv with hv | hv
      · exact hxs v (List.mem_of_mem_take hv)
      · exact hxs v (List.mem_of_mem_drop hv)
    · exact .inr ⟨_, rfl⟩
  | join =>
    obtain ⟨s, l, rfl, hs, hl⟩ := hvs.two_inv
    obtain ⟨sep, rfl⟩ := hs.str_inv
    obtain ⟨xs, rfl, hxs⟩ := hl.list_inv
    obtain ⟨ts, hts⟩ := strsOf_typed hxs
    simp only [ListOp.apply, onList, Value.list?, hts]
    exact .inl ⟨_, rfl, .str⟩

theorem MapOp.Sig.apply {o : MapOp} {vs : List Value} {τs : List Ty} {τ : Ty} (h : o.Sig τs τ)
    (hvs : ValuesAt D η vs τs) : Applied D (o.apply vs) (τ.close η) := by
  cases h with
  | new => rw [hvs.nil_inv]; exact .inl ⟨_, rfl, .map (by simp) (by simp) (by simp)⟩
  | withDefault =>
    obtain ⟨d, rfl, hd⟩ := hvs.one_inv
    exact .inl ⟨_, rfl, .map (by simp) (by simp) fun v hv => by cases hv; exact hd⟩
  | len =>
    obtain ⟨es, d, rfl, -⟩ := hvs.map_inv
    simp only [MapOp.apply, onMap_mapOf]
    exact Applied.length es.length
  | isEmpty =>
    obtain ⟨es, d, rfl, -⟩ := hvs.map_inv
    simp only [MapOp.apply, onMap_mapOf]
    exact .inl ⟨_, rfl, .bool⟩
  | contains =>
    obtain ⟨m, k, rfl, hm, -⟩ := hvs.two_inv
    obtain ⟨es, d, rfl, -⟩ := hm.map_inv
    simp only [MapOp.apply, onMap_mapOf]
    exact .inl ⟨_, rfl, .bool⟩
  | index =>
    obtain ⟨m, k, rfl, hm, -⟩ := hvs.two_inv
    obtain ⟨es, d, rfl, -, hv, hd⟩ := hm.map_inv
    simp only [MapOp.apply, onMap_mapOf]
    exact Applied.index k hv hd
  | getOr =>
    obtain ⟨m, k, v, rfl, hm, -, hv⟩ := hvs.three_inv
    obtain ⟨es, d, rfl, -, hvs, -⟩ := hm.map_inv
    simp only [MapOp.apply, onMap_mapOf]
    exact .inl ⟨_, rfl, Value.Typed.getD_find hvs hv⟩
  | insert =>
    obtain ⟨m, k, v, rfl, hm, hk, hv⟩ := hvs.three_inv
    obtain ⟨es, d, rfl, hks, hvs, hd⟩ := hm.map_inv
    simp only [MapOp.apply, onMap_mapOf]
    exact .inl ⟨_, rfl, .map (Entries.insert_keys (Q := (Value.Typed D · _)) hk hks)
      (Entries.insert_values (Q := (Value.Typed D · _)) hv hvs) hd⟩
  | remove =>
    obtain ⟨m, k, rfl, hm, -⟩ := hvs.two_inv
    obtain ⟨es, d, rfl, hks, hvs, hd⟩ := hm.map_inv
    simp only [MapOp.apply, onMap_mapOf]
    exact .inl ⟨_, rfl, .map (fun e he => hks e (Entries.mem_remove he))
      (fun e he => hvs e (Entries.mem_remove he)) hd⟩
  | keys =>
    obtain ⟨es, d, rfl, hks, -⟩ := hvs.map_inv
    simp only [MapOp.apply, onMap_mapOf]
    refine .inl ⟨_, rfl, .list fun u hu => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hu
    exact hks e he
  | values =>
    obtain ⟨es, d, rfl, -, hvs⟩ := hvs.map_inv
    simp only [MapOp.apply, onMap_mapOf]
    refine .inl ⟨_, rfl, .list fun u hu => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hu
    exact hvs e he
  | entries =>
    obtain ⟨es, d, rfl, hks, hvs⟩ := hvs.map_inv
    simp only [MapOp.apply, onMap_mapOf]
    refine .inl ⟨_, rfl, .list fun u hu => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hu
    exact .tuple (.cons (hks e he) (.cons (hvs e he) .nil))
  | equal =>
    obtain ⟨m, n, rfl, hm, hn⟩ := hvs.two_inv
    obtain ⟨es, d, rfl, -⟩ := hm.map_inv
    obtain ⟨es', d', rfl, -⟩ := hn.map_inv
    simp only [MapOp.apply, onMap_mapOf]
    exact .inl ⟨_, rfl, .bool⟩

/-! ## The functions of sets -/

theorem SetOp.Sig.apply {o : SetOp} {vs : List Value} {τs : List Ty} {τ : Ty} (h : o.Sig τs τ)
    (hvs : ValuesAt D η vs τs) : Applied D (o.apply vs) (τ.close η) := by
  cases h with
  | new => rw [hvs.nil_inv]; exact .inl ⟨_, rfl, .set (by simp)⟩
  | fromList =>
    obtain ⟨l, rfl, hl⟩ := hvs.one_inv
    obtain ⟨xs, rfl, hxs⟩ := hl.list_inv
    simp only [SetOp.apply, onList_list]
    exact .inl ⟨_, rfl, .set (Keys.insertAll_all (by simp) hxs)⟩
  | len =>
    obtain ⟨s, rfl, hs⟩ := hvs.one_inv
    obtain ⟨ks, rfl, -⟩ := hs.set_inv
    simp only [SetOp.apply, onSet_setOf]
    exact Applied.length ks.length
  | isEmpty =>
    obtain ⟨s, rfl, hs⟩ := hvs.one_inv
    obtain ⟨ks, rfl, -⟩ := hs.set_inv
    simp only [SetOp.apply, onSet_setOf]
    exact .inl ⟨_, rfl, .bool⟩
  | contains =>
    obtain ⟨s, x, rfl, hs, -⟩ := hvs.two_inv
    obtain ⟨ks, rfl, -⟩ := hs.set_inv
    simp only [SetOp.apply, onSet_setOf]
    exact .inl ⟨_, rfl, .bool⟩
  | insert =>
    obtain ⟨s, x, rfl, hs, hx⟩ := hvs.two_inv
    obtain ⟨ks, rfl, hks⟩ := hs.set_inv
    simp only [SetOp.apply, onSet_setOf]
    exact .inl ⟨_, rfl, .set (Keys.insert_all hx hks)⟩
  | remove =>
    obtain ⟨s, x, rfl, hs, -⟩ := hvs.two_inv
    obtain ⟨ks, rfl, hks⟩ := hs.set_inv
    simp only [SetOp.apply, onSet_setOf]
    exact .inl ⟨_, rfl, .set fun k hk => hks k (Keys.mem_remove hk)⟩
  | toList =>
    obtain ⟨s, rfl, hs⟩ := hvs.one_inv
    obtain ⟨ks, rfl, hks⟩ := hs.set_inv
    simp only [SetOp.apply, onSet_setOf]
    exact .inl ⟨_, rfl, .list hks⟩
  | combine =>
    obtain ⟨s, t, rfl, hs, ht⟩ := hvs.two_inv
    obtain ⟨a, rfl, ha⟩ := hs.set_inv
    obtain ⟨b, rfl, hb⟩ := ht.set_inv
    simp only [SetOp.apply, onSet_setOf]
    exact .inl ⟨_, rfl, .set (SetCombine.run_all _ ha hb)⟩
  | relate =>
    obtain ⟨s, t, rfl, hs, ht⟩ := hvs.two_inv
    obtain ⟨a, rfl, -⟩ := hs.set_inv
    obtain ⟨b, rfl, -⟩ := ht.set_inv
    simp only [SetOp.apply, onSet_setOf]
    exact .inl ⟨_, rfl, .bool⟩

end

end Stilt
