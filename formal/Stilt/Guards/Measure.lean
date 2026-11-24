import Stilt.Guards.Inhabited

/-!
# A measure of the check's work

What bounds the fuel that the check needs on every column, lists included: the
cost of a column, which a column of wildcards puts at 1 and which otherwise
exceeds the costs of the columns that each of its constructors' rows give, the
longest list pattern bounding a list column's lengths.
-/

namespace Stilt.Guards

/-- The first pattern of each row. -/
def heads (rows : Rows) : List Pat := rows.filterMap List.head?

/-- Each row after its first pattern. -/
def tails (rows : Rows) : Rows :=
  rows.filterMap fun
    | _ :: r => some r
    | [] => none

/-- A column as rows of one pattern each. -/
def single (P : List Pat) : Rows := P.map ([·])

/-- Whether every alternative of a column is a wildcard. -/
def allWild (P : List Pat) : Bool := (P.flatMap Pat.alts).all Pat.isWild

mutual

/-- The cost of a column of type `τ` whose patterns are `P`. -/
def cost : Ty → List Pat → Nat
  | .int, P | .bool, P | .unit, P => if allWild P then 1 else 2
  | .option t, P =>
    if allWild P then 1 else 2 + cost t (heads (spec someC (expand (single P))))
  | .tuple ts, P =>
    if allWild P then 1 else 2 + costs ts (spec (tupleC ts.length) (expand (single P)))
  | .list t, P =>
    if allWild P then 1 else
      let R := expand (single P)
      let L := longest R
      2 + (List.range (L + 1)).foldr
          (fun k acc => max acc (spread t k (spec (lenC k) R))) 0
        + spread t (L + 1) (spec (longC (L + 1)) R) + 1

/-- The costs of the columns of rows, of types `ts`. -/
def costs : List Ty → Rows → Nat
  | [], _ => 0
  | t :: ts, R => cost t (heads R) + costs ts (tails R)

/-- The costs of the first `k` columns of rows, each of type `t`. -/
def spread (t : Ty) : Nat → Rows → Nat
  | 0, _ => 0
  | k + 1, R => cost t (heads R) + spread t k (tails R)

end

/-- The rows after their first `k` patterns. -/
def drops : Nat → Rows → Rows
  | 0, R => R
  | k + 1, R => drops k (tails R)

/-- Column `i` of rows. -/
def col (i : Nat) (R : Rows) : List Pat := heads (drops i R)

/-- Every member of the first is one of the second. -/
def Sub {α : Type} (a b : List α) : Prop := ∀ x ∈ a, x ∈ b

theorem Sub.refl {α : Type} (a : List α) : Sub a a := fun _ h => h

theorem mem_heads {R : Rows} {p : Pat} : p ∈ heads R ↔ ∃ r, p :: r ∈ R := by
  simp only [heads, List.mem_filterMap]
  constructor
  · rintro ⟨r, hr, he⟩
    match r, he with
    | q :: rest, he =>
      simp only [List.head?_cons, Option.some.injEq] at he
      exact ⟨rest, he ▸ hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨p :: r, hr, rfl⟩

theorem mem_tails {R : Rows} {r : List Pat} : r ∈ tails R ↔ ∃ p, p :: r ∈ R := by
  simp only [tails, List.mem_filterMap]
  constructor
  · rintro ⟨r', hr, he⟩
    match r', he with
    | q :: rest, he =>
      simp only [Option.some.injEq] at he
      exact ⟨q, he ▸ hr⟩
  · rintro ⟨p, hr⟩
    exact ⟨p :: r, hr, rfl⟩

theorem mem_drops : ∀ {k : Nat} {R : Rows} {r : List Pat},
    r ∈ drops k R ↔ ∃ ps : List Pat, ps.length = k ∧ ps ++ r ∈ R
  | 0, R, r => by simp [drops]
  | k + 1, R, r => by
    simp only [drops, mem_drops, mem_tails]
    constructor
    · rintro ⟨ps, hl, p, hp⟩
      exact ⟨p :: ps, by simp [hl], hp⟩
    · rintro ⟨ps, hl, hp⟩
      match ps, hl with
      | p :: ps, hl => exact ⟨ps, by simpa using hl, p, hp⟩

theorem heads_sub {R R' : Rows} (h : Sub R' R) : Sub (heads R') (heads R) := by
  intro p hp
  obtain ⟨r, hr⟩ := mem_heads.1 hp
  exact mem_heads.2 ⟨r, h _ hr⟩

theorem tails_sub {R R' : Rows} (h : Sub R' R) : Sub (tails R') (tails R) := by
  intro r hr
  obtain ⟨p, hp⟩ := mem_tails.1 hr
  exact mem_tails.2 ⟨p, h _ hp⟩

theorem drops_sub : ∀ (k : Nat) {R R' : Rows}, Sub R' R → Sub (drops k R') (drops k R)
  | 0, _, _, h => h
  | k + 1, _, _, h => drops_sub k (tails_sub h)

theorem col_sub (i : Nat) {R R' : Rows} (h : Sub R' R) : Sub (col i R') (col i R) :=
  heads_sub (drops_sub i h)

theorem drops_tails : ∀ (k : Nat) (R : Rows), drops k (tails R) = drops (k + 1) R
  | _, _ => rfl

theorem heads_append (a b : Rows) : heads (a ++ b) = heads a ++ heads b := by
  simp [heads, List.filterMap_append]

theorem heads_alts (p : Pat) (rest : List Pat) :
    heads (p.alts.map (· :: rest)) = p.alts := by
  simp only [heads, List.filterMap_map]
  induction p.alts with
  | nil => rfl
  | cons q qs ih => simp only [List.filterMap_cons, Function.comp, List.head?_cons]; rw [ih]

/-- The first patterns of the expanded rows are the alternatives of the first
patterns of the rows. -/
theorem heads_expand : ∀ rows : Rows, heads (expand rows) = (heads rows).flatMap Pat.alts
  | [] => rfl
  | [] :: rows => by
    have ih := heads_expand rows
    have e : expand ([] :: rows) = [[]] ++ expand rows := rfl
    rw [e, heads_append, ih]
    rfl
  | (p :: rest) :: rows => by
    have ih := heads_expand rows
    have e : expand ((p :: rest) :: rows) = p.alts.map (· :: rest) ++ expand rows := rfl
    rw [e, heads_append, ih, heads_alts]
    rfl

theorem heads_single (P : List Pat) : heads (single P) = P := by
  induction P with
  | nil => rfl
  | cons p P ih => simp [single, heads] at ih ⊢; exact ih

theorem mem_single {P : List Pat} {r : List Pat} : r ∈ single P ↔ ∃ p ∈ P, r = [p] := by
  simp [single, eq_comm]

/-- The rows of an expanded column are its alternatives, one to a row. -/
theorem mem_expand_single {P : List Pat} {r : List Pat} :
    r ∈ expand (single P) ↔ ∃ q ∈ P.flatMap Pat.alts, r = [q] := by
  simp only [expand, single, List.flatMap_map, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨p, hp, q, hq, rfl⟩
    exact ⟨q, ⟨p, hp, hq⟩, rfl⟩
  · rintro ⟨q, ⟨p, hp, hq⟩, rfl⟩
    exact ⟨p, hp, q, hq, rfl⟩

theorem getElem?_eq_some_split {l : List Pat} {i : Nat} {p : Pat} :
    l[i]? = some p ↔ ∃ ps r, ps.length = i ∧ l = ps ++ p :: r := by
  constructor
  · intro h
    have hi : i < l.length := by
      rcases Nat.lt_or_ge i l.length with hi | hi
      · exact hi
      · rw [List.getElem?_eq_none hi] at h; cases h
    refine ⟨l.take i, l.drop (i + 1), by simp; omega, ?_⟩
    have hp : l[i] = p := by rw [List.getElem?_eq_getElem hi] at h; exact Option.some.inj h
    conv => lhs; rw [← List.take_append_drop i l]
    rw [List.drop_eq_getElem_cons hi, hp]
  · rintro ⟨ps, r, rfl, rfl⟩
    simp

/-- A column's members are the patterns at its index. -/
theorem mem_col {i : Nat} {R : Rows} {p : Pat} : p ∈ col i R ↔ ∃ l ∈ R, l[i]? = some p := by
  simp only [col, mem_heads, mem_drops, getElem?_eq_some_split]
  constructor
  · rintro ⟨r, ps, hl, hr⟩
    exact ⟨_, hr, ps, r, hl, rfl⟩
  · rintro ⟨l, hl, ps, r, hlen, rfl⟩
    exact ⟨r, ps, hlen, hl⟩

theorem col_zero (R : Rows) : col 0 R = heads R := rfl

theorem col_tails (i : Nat) (R : Rows) : col i (tails R) = col (i + 1) R := rfl

/-! ## The measure's arithmetic -/

theorem cost_pos (τ : Ty) (P : List Pat) : 1 ≤ cost τ P := by
  cases τ <;> simp only [cost] <;> split <;> omega

theorem costs_append : ∀ (us vs : List Ty) (R : Rows),
    costs (us ++ vs) R = costs us R + costs vs (drops us.length R)
  | [], _, _ => by simp [costs, drops]
  | u :: us, vs, R => by
    simp only [List.cons_append, costs, costs_append us vs (tails R), List.length_cons, drops]
    omega

theorem spread_eq (t : Ty) : ∀ (k : Nat) (R : Rows), spread t k R = costs (List.replicate k t) R
  | 0, _ => by simp [spread, costs]
  | k + 1, R => by simp [spread, costs, List.replicate_succ, spread_eq t k (tails R)]

theorem spread_le_add (t : Ty) : ∀ (k d : Nat) (R : Rows), spread t k R ≤ spread t (k + d) R
  | 0, _, _ => by simp [spread]
  | k + 1, d, R => by
    rw [Nat.add_right_comm]
    simp only [spread]
    have := spread_le_add t k d (tails R)
    omega

/-- Columns `i < k` of the first rows are among those of the second. -/
def ColSub (k : Nat) (R' R : Rows) : Prop := ∀ i < k, Sub (col i R') (col i R)

theorem ColSub.of_sub {k : Nat} {R' R : Rows} (h : Sub R' R) : ColSub k R' R :=
  fun i _ => col_sub i h

theorem ColSub.tail {k : Nat} {R' R : Rows} (h : ColSub (k + 1) R' R) : ColSub k (tails R') (tails R) :=
  fun i hi => by rw [col_tails, col_tails]; exact h (i + 1) (by omega)

theorem ColSub.head {k : Nat} {R' R : Rows} (h : ColSub (k + 1) R' R) : Sub (heads R') (heads R) := by
  have := h 0 (by omega)
  rwa [col_zero, col_zero] at this

/-! ## Inclusion -/

theorem allWild_sub {P P' : List Pat} (h : Sub P' P) (hw : allWild P = true) : allWild P' = true := by
  simp only [allWild, List.all_eq_true, List.mem_flatMap] at hw ⊢
  rintro q ⟨p, hp, hq⟩
  exact hw q ⟨p, h p hp, hq⟩

theorem single_sub {P P' : List Pat} (h : Sub P' P) : Sub (single P') (single P) := by
  intro r hr
  obtain ⟨p, hp, rfl⟩ := mem_single.1 hr
  exact mem_single.2 ⟨p, h p hp, rfl⟩

theorem expand_sub {R R' : Rows} (h : Sub R' R) : Sub (expand R') (expand R) := by
  intro r hr
  obtain ⟨r', hr', hrow⟩ := List.mem_flatMap.1 hr
  exact List.mem_flatMap.2 ⟨r', h r' hr', hrow⟩

theorem spec_sub (f : Pat → Option (List Pat)) {R R' : Rows} (h : Sub R' R) :
    Sub (spec f R') (spec f R) := by
  intro r hr
  obtain ⟨r', hr', hrow⟩ := List.mem_filterMap.1 hr
  exact List.mem_filterMap.2 ⟨r', h r' hr', hrow⟩

/-- The length that a list pattern beginning a row names, if it is one. -/
def listLength : List Pat → Option Nat
  | .list ps :: _ | .prefix ps _ :: _ => some ps.length
  | _ => none

theorem longest_eq (rows : Rows) :
    longest rows = rows.foldr (fun r n => max ((listLength r).getD 0) n) 0 := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simp only [longest, List.foldr_cons] at ih ⊢
    rw [← ih]
    match r with
    | .list ps :: _ | .prefix ps _ :: _ => rfl
    | [] | .wild :: _ | .bind _ :: _ | .int _ :: _ | .bool _ :: _ | .unit :: _ | .const _ _ :: _
    | .tuple _ :: _ | .none :: _ | .some _ :: _ | .or _ _ :: _ => simp [listLength]

theorem le_longest {rows : Rows} {r : List Pat} {n : Nat} (hr : r ∈ rows) (hl : listLength r = some n) :
    n ≤ longest rows := by
  rw [longest_eq]
  induction rows with
  | nil => nomatch hr
  | cons r' rows ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hr with rfl | hr
    · simp only [hl, Option.getD_some]; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hr) (Nat.le_max_right _ _)

theorem longest_le {rows : Rows} {m : Nat} (h : ∀ r ∈ rows, ∀ n, listLength r = some n → n ≤ m) :
    longest rows ≤ m := by
  rw [longest_eq]
  induction rows with
  | nil => exact Nat.zero_le _
  | cons r rows ih =>
    simp only [List.foldr_cons]
    refine Nat.max_le.2 ⟨?_, ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr')⟩
    cases hl : listLength r with
    | none => exact Nat.zero_le _
    | some n => exact h r List.mem_cons_self n hl

theorem longest_sub {R R' : Rows} (h : Sub R' R) : longest R' ≤ longest R :=
  longest_le fun r hr _ hl => le_longest (h r hr) hl

theorem le_foldr_max (g : Nat → Nat) : ∀ {l : List Nat} {k : Nat}, k ∈ l →
    g k ≤ l.foldr (fun k acc => max acc (g k)) 0
  | k' :: l, k, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_right _ _
    · exact Nat.le_trans (le_foldr_max g h) (Nat.le_max_left _ _)

theorem foldr_max_le (g : Nat → Nat) {X : Nat} : ∀ {l : List Nat}, (∀ k ∈ l, g k ≤ X) →
    l.foldr (fun k acc => max acc (g k)) 0 ≤ X
  | [], _ => Nat.zero_le _
  | k :: l, h => by
    simp only [List.foldr_cons]
    exact Nat.max_le.2 ⟨foldr_max_le g fun k' hk' => h k' (List.mem_cons_of_mem _ hk'),
      h k List.mem_cons_self⟩

theorem getElem?_wilds {m i : Nat} (h : i < m) : (wilds m)[i]? = some .wild := by
  simp [wilds, h]

/-- A pattern of a row padded with wildcards: the pattern's own, or a wildcard. -/
theorem getElem?_padded {qs rest : List Pat} {m i : Nat} (h : i < qs.length + m) :
    (qs ++ wilds m ++ rest)[i]? = if i < qs.length then qs[i]? else some .wild := by
  rw [List.append_assoc]
  split
  · rename_i hi; rw [List.getElem?_append_left hi]
  · rename_i hi
    rw [List.getElem?_append_right (by omega), List.getElem?_append_left (by simp [wilds]; omega),
      getElem?_wilds (by omega)]

/-- Below the bound of the shorter, the lists longer than two bounds have the
same patterns at an index. -/
theorem longC_index {k' k i : Nat} (hk : k' ≤ k) (hi : i < k') {q : Pat} {ps' : List Pat} {p : Pat}
    (h : longC k' q = some ps') (hp : ps'[i]? = some p) :
    ∃ ps, longC k q = some ps ∧ ps[i]? = some p := by
  cases q with
  | «prefix» qs o =>
    simp only [longC] at h
    split at h
    · rename_i hq
      cases h
      refine ⟨qs ++ wilds (k - qs.length) ++ [.wild], by simp [longC]; omega, ?_⟩
      rw [getElem?_padded (by omega)] at hp ⊢
      exact hp
    · cases h
  | wild | bind _ =>
    simp only [longC, Pat.isWild, ite_true] at h
    cases h
    rw [getElem?_wilds (by omega)] at hp
    exact ⟨wilds (k + 1), by simp [longC, Pat.isWild], by rw [getElem?_wilds (by omega)]; exact hp⟩
  | _ => simp [longC, Pat.isWild] at h

/-! ## Monotonicity -/

theorem spread_mono_of (t : Ty) (h : ∀ {P P' : List Pat}, Sub P' P → cost t P' ≤ cost t P) :
    ∀ (k : Nat) {R R' : Rows}, ColSub k R' R → spread t k R' ≤ spread t k R
  | 0, _, _, _ => by simp [spread]
  | k + 1, _, _, hc => by
    simp only [spread]
    have := spread_mono_of t h k hc.tail
    have := h hc.head
    omega

theorem costs_mono_of : ∀ (ts : List Ty), (∀ t ∈ ts, ∀ {P P' : List Pat}, Sub P' P → cost t P' ≤ cost t P) →
    ∀ {R R' : Rows}, ColSub ts.length R' R → costs ts R' ≤ costs ts R
  | [], _, _, _, _ => by simp [costs]
  | t :: ts, h, _, _, hc => by
    simp only [costs]
    have := costs_mono_of ts (fun t' ht' => h t' (List.mem_cons_of_mem _ ht')) hc.tail
    have := h t List.mem_cons_self hc.head
    omega

/-- A column whose patterns are among another's costs no more. -/
theorem cost_mono : ∀ (τ : Ty) {P P' : List Pat}, Sub P' P → cost τ P' ≤ cost τ P
  | τ, P, P', h => by
    by_cases hw : allWild P' = true
    · have : cost τ P' = 1 := by cases τ <;> simp [cost, hw]
      rw [this]
      exact cost_pos τ P
    have hw' : allWild P = false := by
      cases e : allWild P
      · rfl
      · exact absurd (allWild_sub h e) hw
    have hw'' : allWild P' = false := by simpa using hw
    have hE := expand_sub (single_sub h)
    match τ with
    | .int | .bool | .unit => simp [cost, hw', hw'']
    | .option t =>
      simp only [cost, hw', hw'', Bool.false_eq_true, ite_false]
      have := cost_mono t (heads_sub (spec_sub someC hE))
      omega
    | .tuple ts =>
      simp only [cost, hw', hw'', Bool.false_eq_true, ite_false]
      have := costs_mono_of ts (fun t _ => cost_mono t) (.of_sub (spec_sub (tupleC ts.length) hE))
      omega
    | .list t =>
      simp only [cost, hw', hw'', Bool.false_eq_true, ite_false]
      have hL := longest_sub hE
      have hlen := foldr_max_le (X := (List.range (longest (expand (single P)) + 1)).foldr
          (fun k acc => max acc (spread t k (spec (lenC k) (expand (single P))))) 0)
        (fun k => spread t k (spec (lenC k) (expand (single P'))))
        (l := List.range (longest (expand (single P')) + 1)) fun k hk => by
          have hk' : k ∈ List.range (longest (expand (single P)) + 1) := by
            simp only [List.mem_range] at hk ⊢; omega
          exact Nat.le_trans (spread_mono_of t (cost_mono t) k (.of_sub (spec_sub (lenC k) hE)))
            (le_foldr_max (fun k => spread t k (spec (lenC k) (expand (single P)))) hk')
      have hlong : spread t (longest (expand (single P')) + 1)
          (spec (longC (longest (expand (single P')) + 1)) (expand (single P'))) ≤
          spread t (longest (expand (single P)) + 1)
          (spec (longC (longest (expand (single P)) + 1)) (expand (single P))) := by
        refine Nat.le_trans (spread_mono_of t (cost_mono t) _ (R := spec (longC
          (longest (expand (single P)) + 1)) (expand (single P))) ?_) ?_
        · intro i hi x hx
          obtain ⟨l, hl, hx⟩ := mem_col.1 hx
          obtain ⟨r, hr, hrow⟩ := List.mem_filterMap.1 hl
          obtain ⟨q, hq, rfl⟩ := mem_expand_single.1 hr
          simp only [Option.map_eq_some_iff] at hrow
          obtain ⟨ps', hps', rfl⟩ := hrow
          rw [List.append_nil] at hx
          obtain ⟨ps, hps, hx'⟩ := longC_index (k := longest (expand (single P)) + 1)
            (by omega) hi hps' hx
          refine mem_col.2 ⟨ps ++ [], List.mem_filterMap.2 ⟨[q], ?_, by simp [hps]⟩, by simpa using hx'⟩
          exact mem_expand_single.2 ⟨q, by
            simp only [List.mem_flatMap] at hq ⊢
            obtain ⟨p, hp, hq⟩ := hq
            exact ⟨p, h p hp, hq⟩, rfl⟩
        · have := spread_le_add t (longest (expand (single P')) + 1)
            (longest (expand (single P)) - longest (expand (single P')))
            (spec (longC (longest (expand (single P)) + 1)) (expand (single P)))
          rwa [show longest (expand (single P')) + 1 +
              (longest (expand (single P)) - longest (expand (single P'))) =
              longest (expand (single P)) + 1 by omega] at this
      omega
termination_by τ => sizeOf τ
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem ‹_ ∈ ts›; omega)

end Stilt.Guards
