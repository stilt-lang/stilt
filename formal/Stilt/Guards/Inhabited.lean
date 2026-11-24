import Stilt.Guards.Covers

/-!
# What completeness rests on

A value of every type, and the facts about or-patterns and constants that
`Stilt.Guards.Complete` uses:
that a pattern that matches has an alternative that matches, and that taking
rows apart keeps them without constants; and each constructor's rows, which
keep every row that matches a value the constructor builds (`SpecFull`).
-/

namespace Stilt.Guards

/-! ## Values of types -/

mutual

/-- A value of a type. -/
def Ty.witness : Ty → Val
  | .int => .int 0
  | .bool => .bool true
  | .unit => .unit
  | .tuple ts => .tuple (Ty.witnesses ts)
  | .list _ => .list []
  | .option _ => .none

/-- A value of each type. -/
def Ty.witnesses : List Ty → List Val
  | [] => []
  | t :: ts => t.witness :: Ty.witnesses ts

end

mutual

/-- Every type has a value. -/
theorem Ty.witness_ty : ∀ τ : Ty, ValTy τ.witness τ
  | .int => .int
  | .bool => .bool
  | .unit => .unit
  | .tuple ts => .tuple (Ty.witnesses_ty ts)
  | .list _ => .list fun _ h => nomatch h
  | .option _ => .none

theorem Ty.witnesses_ty : ∀ ts : List Ty, ValsTy (Ty.witnesses ts) ts
  | [] => .nil
  | t :: ts => .cons (Ty.witness_ty t) (Ty.witnesses_ty ts)

end

/-- Values of types put after others are values of the first types, then of the
others. -/
theorem ValsTy.split : ∀ {ts us : List Ty} {vs : List Val}, ValsTy vs (ts ++ us) →
    ∃ ws xs, vs = ws ++ xs ∧ ValsTy ws ts ∧ ValsTy xs us
  | [], _, vs, h => ⟨[], vs, rfl, .nil, h⟩
  | _ :: _, _, _ :: _, .cons hv hvs => by
    obtain ⟨ws, xs, rfl, hw, hx⟩ := ValsTy.split hvs
    exact ⟨_ :: ws, xs, rfl, .cons hv hw, hx⟩

/-! ## Patterns, alternatives and constants -/

/-- Whether a pattern is not an or-pattern, as every alternative is. -/
def Pat.noOr : Pat → Bool
  | .or _ _ => false
  | _ => true

theorem Matches.or_iff {p q : Pat} {v : Val} : Matches (.or p q) v ↔ Matches p v ∨ Matches q v := by
  simp only [Matches, Pat.ways, ne_eq, List.append_eq_nil_iff]
  constructor
  · intro h
    by_cases hp : p.ways v = []
    · exact .inr fun hq => h ⟨hp, hq⟩
    · exact .inl hp
  · rintro (h | h) ⟨hp, hq⟩
    · exact h hp
    · exact h hq

/-- A pattern that matches has an alternative that matches. -/
theorem Pat.alts_complete : ∀ {p : Pat} {v : Val}, Matches p v → ∃ q ∈ p.alts, Matches q v
  | .or p₁ p₂, v, h => by
    rcases Matches.or_iff.1 h with h | h
    · obtain ⟨q, hq, hm⟩ := Pat.alts_complete h
      exact ⟨q, by simp [Pat.alts, hq], hm⟩
    · obtain ⟨q, hq, hm⟩ := Pat.alts_complete h
      exact ⟨q, by simp [Pat.alts, hq], hm⟩
  | .wild, _, h | .bind _, _, h | .int _, _, h | .bool _, _, h | .unit, _, h | .const _ _, _, h
  | .tuple _, _, h | .none, _, h | .some _, _, h | .list _, _, h | .prefix _ _, _, h =>
    ⟨_, by simp [Pat.alts], h⟩

theorem Pat.alts_noOr : ∀ {p q : Pat}, q ∈ p.alts → q.noOr = true
  | .or p₁ p₂, q, h => by
    simp only [Pat.alts, List.mem_append] at h
    rcases h with h | h
    · exact Pat.alts_noOr h
    · exact Pat.alts_noOr h
  | .wild, _, h | .bind _, _, h | .int _, _, h | .bool _, _, h | .unit, _, h | .const _ _, _, h
  | .tuple _, _, h | .none, _, h | .some _, _, h | .list _, _, h | .prefix _ _, _, h => by
    simp only [Pat.alts, List.mem_singleton] at h
    subst h
    rfl

theorem Pat.alts_constFree : ∀ {p q : Pat}, p.hasConst = false → q ∈ p.alts → q.hasConst = false
  | .or p₁ p₂, q, hc, h => by
    simp only [Pat.hasConst, Bool.or_eq_false_iff] at hc
    simp only [Pat.alts, List.mem_append] at h
    rcases h with h | h
    · exact Pat.alts_constFree hc.1 h
    · exact Pat.alts_constFree hc.2 h
  | .wild, _, hc, h | .bind _, _, hc, h | .int _, _, hc, h | .bool _, _, hc, h | .unit, _, hc, h
  | .const _ _, _, hc, h | .tuple _, _, hc, h | .none, _, hc, h | .some _, _, hc, h
  | .list _, _, hc, h | .prefix _ _, _, hc, h => by
    simp only [Pat.alts, List.mem_singleton] at h
    exact h ▸ hc

theorem Pat.anyConst_false : ∀ {ps : List Pat}, Pat.anyConst ps = false → ∀ p ∈ ps, p.hasConst = false
  | [], _, _, h => nomatch h
  | q :: ps, hc, p, h => by
    simp only [Pat.anyConst, Bool.or_eq_false_iff] at hc
    rcases List.mem_cons.1 h with rfl | h
    · exact hc.1
    · exact Pat.anyConst_false hc.2 p h

/-- Rows none of whose patterns holds a constant. -/
def ConstFree (rows : Rows) : Prop := ∀ r ∈ rows, ∀ p ∈ r, p.hasConst = false

theorem wilds_constFree (n : Nat) : ∀ p ∈ wilds n, p.hasConst = false := by
  intro p h
  simp only [wilds, List.mem_replicate] at h
  rw [h.2]
  rfl

theorem expand_constFree {rows : Rows} (h : ConstFree rows) : ConstFree (expand rows) := by
  intro r hr p hp
  obtain ⟨r', hr', hrow⟩ := List.mem_flatMap.1 hr
  match r', hrow with
  | q :: rest, hrow =>
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hrow
    rcases List.mem_cons.1 hp with rfl | hp
    · exact Pat.alts_constFree (h _ hr' q List.mem_cons_self) hq'
    · exact h _ hr' p (List.mem_cons_of_mem _ hp)
  | [], hrow =>
    simp only [List.mem_singleton] at hrow
    subst hrow
    nomatch hp

/-- A constructor whose rows take a pattern without constants apart into
patterns without constants. -/
def KeepsConstFree (f : Pat → Option (List Pat)) : Prop :=
  ∀ p ps, f p = some ps → p.hasConst = false → ∀ q ∈ ps, q.hasConst = false

theorem spec_constFree {f : Pat → Option (List Pat)} (hf : KeepsConstFree f) {rows : Rows}
    (h : ConstFree rows) : ConstFree (spec f rows) := by
  intro r hr q hq
  obtain ⟨r', hr', hrow⟩ := List.mem_filterMap.1 hr
  match r', hrow with
  | p :: rest, hrow =>
    simp only [Option.map_eq_some_iff] at hrow
    obtain ⟨ps, hps, rfl⟩ := hrow
    rcases List.mem_append.1 hq with hq | hq
    · exact hf p ps hps (h _ hr' p List.mem_cons_self) q hq
    · exact h _ hr' q (List.mem_cons_of_mem _ hq)

/-! ## Each constructor's rows keep the rows that match -/

/-- `f` keeps each pattern that matches the value `v` that it takes apart into
the parts `ws`, as patterns that match the parts: the converse of `SpecOk`. -/
def SpecFull (f : Pat → Option (List Pat)) (v : Val) (ws : List Val) : Prop :=
  ∀ p, p.noOr = true → p.hasConst = false → Matches p v → ∃ ps, f p = some ps ∧ RowMatches ps ws

theorem rowMatches_append_of : ∀ {ps qs : List Pat} {ws vs : List Val},
    RowMatches ps ws → RowMatches qs vs → RowMatches (ps ++ qs) (ws ++ vs)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, h, h' => by
    rw [rowMatches_cons] at h
    rw [List.cons_append, List.cons_append, rowMatches_cons]
    exact ⟨h.1, rowMatches_append_of h.2 h'⟩
  | [], _, _ :: _, _, h, _ | _ :: _, _, [], _, h, _ => absurd (rowMatches_length h) (by simp)

theorem boolC_full (b : Bool) : SpecFull (boolC b) (.bool b) [] := by
  intro p _ _ hm
  cases p with
  | bool c =>
    have : c = b := by cases b <;> cases c <;> simp_all [Matches, Pat.ways]
    exact ⟨[], by simp [boolC, this], rowMatches_nil⟩
  | wild | bind _ => exact ⟨[], rfl, rowMatches_nil⟩
  | or _ _ => contradiction
  | const _ _ => simp_all [Pat.hasConst]
  | _ => simp [Matches, Pat.ways] at hm

theorem unitC_full : SpecFull unitC .unit [] := by
  intro p _ _ hm
  cases p with
  | unit => exact ⟨[], rfl, rowMatches_nil⟩
  | wild | bind _ => exact ⟨[], rfl, rowMatches_nil⟩
  | or _ _ => contradiction
  | const _ _ => simp_all [Pat.hasConst]
  | _ => simp [Matches, Pat.ways] at hm

theorem noneC_full : SpecFull noneC .none [] := by
  intro p _ _ hm
  cases p with
  | none => exact ⟨[], rfl, rowMatches_nil⟩
  | wild | bind _ => exact ⟨[], rfl, rowMatches_nil⟩
  | or _ _ => contradiction
  | const _ _ => simp_all [Pat.hasConst]
  | _ => simp [Matches, Pat.ways] at hm

theorem someC_full (u : Val) : SpecFull someC (.some u) [u] := by
  intro p _ _ hm
  cases p with
  | some q => exact ⟨[q], rfl, rowMatches_cons.2 ⟨hm, rowMatches_nil⟩⟩
  | wild | bind _ =>
    exact ⟨[.wild], rfl, rowMatches_cons.2 ⟨Pat.isWild_matches rfl u, rowMatches_nil⟩⟩
  | or _ _ => contradiction
  | const _ _ => simp_all [Pat.hasConst]
  | _ => simp [Matches, Pat.ways] at hm

theorem tupleC_full (ws : List Val) : SpecFull (tupleC ws.length) (.tuple ws) ws := by
  intro p _ _ hm
  cases p with
  | tuple ps =>
    have hl : ps.length = ws.length := rowMatches_length hm
    exact ⟨ps, by simp [tupleC, hl], hm⟩
  | wild | bind _ => exact ⟨wilds ws.length, rfl, rowMatches_wilds ws⟩
  | or _ _ => contradiction
  | const _ _ => simp_all [Pat.hasConst]
  | _ => simp [Matches, Pat.ways] at hm

theorem keeps_anyC : KeepsConstFree anyC := by
  intro p ps h _ q hq
  unfold anyC at h
  split at h <;> cases h
  nomatch hq

theorem keeps_boolC (b : Bool) : KeepsConstFree (boolC b) := by
  intro p ps h hc q hq
  cases p
  case bool c =>
    simp only [boolC] at h
    split at h <;> cases h
    nomatch hq
  all_goals exact keeps_anyC _ _ h hc q hq

theorem keeps_unitC : KeepsConstFree unitC := by
  intro p ps h hc q hq
  cases p
  case unit => cases h; nomatch hq
  all_goals exact keeps_anyC _ _ h hc q hq

theorem keeps_noneC : KeepsConstFree noneC := by
  intro p ps h hc q hq
  cases p
  case none => cases h; nomatch hq
  all_goals exact keeps_anyC _ _ h hc q hq

theorem keeps_someC : KeepsConstFree someC := by
  intro p ps h hc q hq
  cases p
  case some r =>
    cases h
    simp only [List.mem_singleton] at hq
    exact hq ▸ hc
  all_goals
    simp only [someC] at h
    split at h <;> cases h
    simp only [List.mem_singleton] at hq
    exact hq ▸ rfl

theorem keeps_tupleC (k : Nat) : KeepsConstFree (tupleC k) := by
  intro p ps h hc q hq
  cases p
  case tuple rs =>
    simp only [tupleC] at h
    split at h <;> cases h
    exact Pat.anyConst_false hc q hq
  all_goals
    simp only [tupleC] at h
    split at h <;> cases h
    exact wilds_constFree k q hq

end Stilt.Guards
