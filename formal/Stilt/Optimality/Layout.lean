import Stilt.Optimality.Rule

/-!
# The witness's record types

The record types that the witness of `Stilt.Optimality.Witness` gives its
variables, and the literals that build their values.

Records are nominal (declarations.records), and a record literal gives every
field (expressions.struct-literal-fields), so a value is a finite tree and a record type can't
contain itself. The witness types a place of any field path of depth up to
`K` with one record type per budget `b ≤ K`: the type with budget `b` has a
field `v` of type `i64`, and, when `b > 0`, a field of the type with budget
`b - 1` for each name of a list `F`. A variable of the type with budget `K`
has every place whose fields are names of `F`, up to depth `K`, and each of
them has a field `v`.
-/

namespace Stilt.Optimality

/-! ## Names -/

/-- A name made of `n + 1` copies of `c`. Different counts give different
names, so the witness can name as many records and parameters as it needs. -/
def nameOf (c : Char) (n : Nat) : Name := String.ofList (List.replicate (n + 1) c)

theorem length_nameOf (c : Char) (n : Nat) : (nameOf c n).length = n + 1 := by
  simp [nameOf, String.length_ofList]

theorem nameOf_inj {c : Char} {m n : Nat} (h : nameOf c m = nameOf c n) : m = n := by
  have := congrArg String.length h
  simpa [length_nameOf] using this

/-- A name made of one letter, repeated, is not `self` unless the letter is
`s`. -/
theorem nameOf_ne_selfName {c : Char} (hc : c ≠ 's') (n : Nat) : nameOf c n ≠ selfName := by
  intro h
  have := congrArg String.toList h
  simp [nameOf, selfName, List.replicate_succ] at this
  exact hc this.1

/-- The length of the longest name of a list. -/
def maxLength : List Name → Nat
  | [] => 0
  | f :: fs => max f.length (maxLength fs)

theorem length_le_maxLength {f : Name} :
    ∀ {fs : List Name}, f ∈ fs → f.length ≤ maxLength fs
  | g :: fs, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (length_le_maxLength h) (Nat.le_max_right _ _)

/-- A name that is none of `fs`, since it is longer than each. -/
def freshName (fs : List Name) : Name := nameOf 'v' (maxLength fs)

theorem freshName_not_mem (fs : List Name) : freshName fs ∉ fs := fun h => by
  have := length_le_maxLength h
  simp only [freshName, length_nameOf] at this
  omega

/-- The names of a list, each once. -/
def distinct : List Name → List Name
  | [] => []
  | x :: xs => if x ∈ distinct xs then distinct xs else x :: distinct xs

theorem mem_distinct {x : Name} : ∀ {xs : List Name}, x ∈ distinct xs ↔ x ∈ xs
  | [] => by simp [distinct]
  | y :: xs => by
    unfold distinct
    split
    · rename_i hy
      rw [mem_distinct, List.mem_cons]
      exact ⟨.inr, fun h => h.elim (fun h => h ▸ mem_distinct.1 hy) id⟩
    · rw [List.mem_cons, mem_distinct, List.mem_cons]

theorem nodup_distinct : ∀ xs : List Name, (distinct xs).Nodup
  | [] => .nil
  | y :: xs => by
    unfold distinct
    split
    · exact nodup_distinct xs
    · rename_i hy
      exact List.nodup_cons.2 ⟨hy, nodup_distinct xs⟩

/-! ## Association lists -/

theorem lookup_map_const {β : Type} (x : β) {f : Name} :
    ∀ {F : List Name}, f ∈ F → (F.map fun g => (g, x)).lookup f = some x
  | g :: F, h => by
    by_cases hf : f = g
    · subst hf
      simp
    · rw [List.map_cons, lookup_cons_ne hf]
      exact lookup_map_const x (List.mem_of_ne_of_mem hf h)

/-- A key whose entries all hold `b` finds `b`. -/
theorem lookup_of_unique {β : Type} {k : Name} {b : β} :
    ∀ {l : List (Name × β)}, (k, b) ∈ l → (∀ b', (k, b') ∈ l → b' = b) →
      l.lookup k = some b
  | (k', b'') :: l, h, hu => by
    by_cases hk : k = k'
    · subst hk
      simp [hu b'' List.mem_cons_self]
    · rw [lookup_cons_ne hk]
      rcases List.mem_cons.1 h with h | h
      · cases h
        exact absurd rfl hk
      · exact lookup_of_unique h fun b' hb' => hu b' (List.mem_cons_of_mem _ hb')

/-- A key of a list whose entries all hold `b` finds `b`. -/
theorem lookup_of_all {β : Type} {k : Name} {b : β} :
    ∀ {l : List (Name × β)}, (∀ e ∈ l, e.2 = b) → k ∈ l.map Prod.fst →
      l.lookup k = some b
  | (k', b') :: l, hall, hk => by
    by_cases h : k = k'
    · subst h
      simpa using hall (k, b') List.mem_cons_self
    · rw [lookup_cons_ne h]
      refine lookup_of_all (fun e he => hall e (List.mem_cons_of_mem _ he)) ?_
      simpa [h] using hk

theorem map_fst_assocSet {β : Type} (k : Name) (b : β) :
    ∀ l : List (Name × β), (assocSet l k b).map Prod.fst = l.map Prod.fst
  | [] => rfl
  | (k', b') :: l => by
    by_cases h : k = k' <;> simp [assocSet, h, map_fst_assocSet k b l]

theorem lookup_of_mem_keys {β : Type} {k : Name} :
    ∀ {l : List (Name × β)}, k ∈ l.map Prod.fst → ∃ b, l.lookup k = some b
  | (k', b') :: l, h => by
    by_cases hk : k = k'
    · subst hk
      exact ⟨b', by simp⟩
    · rw [lookup_cons_ne hk]
      exact lookup_of_mem_keys (by simpa [hk] using h)

/-! ## Record types by budget -/

/-- The name of the record type with budget `b` (declarations.records). -/
def recName (b : Nat) : Name := nameOf 'T' b

/-- The record type with budget `b` (declarations.records). -/
def recTy (b : Nat) : Ty := .record (recName b) []

section

variable (F : List Name) (v : Name)

/-- The fields of the record type with budget `b`: `v`, an `i64`, then, when
`b > 0`, a field of the type with budget `b - 1` for each name of `F`. -/
def recFields : Nat → List (Name × Ty)
  | 0 => [(v, .i64)]
  | b + 1 => (v, .i64) :: F.map fun f => (f, recTy b)

/-- The declaration of the record type with budget `b` (declarations.records). -/
def recDecl (b : Nat) : RecordDecl := ⟨recName b, recFields F v b, []⟩

/-- The declarations of the record types with budgets `K` down to `0`, with
distinct names (declarations.records and declarations.unique-names). -/
def recDecls : Nat → List RecordDecl
  | 0 => [recDecl F v 0]
  | b + 1 => recDecl F v (b + 1) :: recDecls b

/-- A literal of the record type with budget `b`, whose `i64` fields are all
`0` (expressions.struct-literal-fields). -/
def lit : Nat → Expr
  | 0 => .record (recName 0) [] [(v, .int 0)]
  | b + 1 => .record (recName (b + 1)) [] ((v, .int 0) :: F.map fun f => (f, lit b))

/-- The value of `lit F v b`, its fields in the order they are declared
(values.left-to-right). -/
def litv : Nat → Value
  | 0 => .record (recName 0) [(v, .int 0)]
  | b + 1 => .record (recName (b + 1)) ((v, .int 0) :: F.map fun f => (f, litv b))

end

variable {F : List Name} {v : Name}

theorem mem_recDecls {r : RecordDecl} :
    ∀ {K : Nat}, r ∈ recDecls F v K → ∃ b, b ≤ K ∧ r = recDecl F v b
  | 0, h => ⟨0, Nat.le_refl _, by simpa [recDecls] using h⟩
  | K + 1, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨K + 1, Nat.le_refl _, rfl⟩
    · obtain ⟨b, hb, rfl⟩ := mem_recDecls h
      exact ⟨b, Nat.le_succ_of_le hb, rfl⟩

theorem find_recDecls {b : Nat} :
    ∀ {K : Nat}, b ≤ K → (recDecls F v K).find? (·.name == recName b) = some (recDecl F v b)
  | 0, hb => by
    obtain rfl : b = 0 := Nat.le_zero.1 hb
    simp [recDecls, recDecl]
  | K + 1, hb => by
    by_cases h : b = K + 1
    · subst h
      simp [recDecls, recDecl]
    · have hne : (recName (K + 1) == recName b) = false := by
        simpa [recName] using fun he => h (nameOf_inj he).symm
      simp only [recDecls, List.find?_cons, recDecl, hne]
      exact find_recDecls (by omega)

theorem nodup_recNames : ∀ K : Nat, ((recDecls F v K).map (·.name)).Nodup
  | 0 => by simp [recDecls]
  | K + 1 => by
    refine List.nodup_cons.2 ⟨fun h => ?_, nodup_recNames K⟩
    obtain ⟨r, hr, he⟩ := List.mem_map.1 h
    obtain ⟨b, hb, rfl⟩ := mem_recDecls hr
    have := nameOf_inj he
    omega

theorem nodup_recFields (hv : v ∉ F) (hF : F.Nodup) :
    ∀ b : Nat, ((recFields F v b).map Prod.fst).Nodup
  | 0 => by simp [recFields]
  | b + 1 => by
    simp only [recFields, List.map_cons, List.map_map]
    have hmap : List.map (Prod.fst ∘ fun f => (f, recTy b)) F = F := by
      simp [Function.comp_def]
    rw [hmap]
    exact List.nodup_cons.2 ⟨hv, hF⟩

theorem lookup_recFields_leaf (b : Nat) : (recFields F v b).lookup v = some .i64 := by
  cases b <;> simp [recFields]

theorem lookup_recFields_field (hv : v ∉ F) {f : Name} (hf : f ∈ F) (b : Nat) :
    (recFields F v (b + 1)).lookup f = some (recTy b) := by
  have hne : f ≠ v := fun h => hv (h ▸ hf)
  rw [recFields, lookup_cons_ne hne]
  exact lookup_map_const _ hf

theorem closed_recFields : ∀ (b : Nat), ∀ f ∈ recFields F v b, f.2.Closed
  | 0, f, h => by
    simp only [recFields, List.mem_singleton] at h
    subst h
    intro ρ hρ
    simp [Ty.rows] at hρ
  | b + 1, f, h => by
    rcases List.mem_cons.1 h with rfl | h
    · intro ρ hρ
      simp [Ty.rows] at hρ
    · obtain ⟨g, -, rfl⟩ := List.mem_map.1 h
      intro ρ hρ
      simp [recTy, Ty.rows, tysRows] at hρ

end Stilt.Optimality
