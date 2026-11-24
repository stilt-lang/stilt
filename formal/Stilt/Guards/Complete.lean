import Stilt.Guards.Steps

/-!
# The check is complete

The converse of `check_sound`: when every vector of values of the types matches
a row, and no row holds a constant, as the rows of `exhaustive` never do, the
check says yes once its fuel exceeds the measure of the rows
(`check_complete`), the cost of their columns (`Stilt.Guards.Measure`). Each
step's rows cover the parts of the values its constructor builds and cost less
than the rows they come from (`Stilt.Guards.Steps`), and every type has a
value, so a column of wildcards loses nothing. An integer that no literal of
the column names is matched by wildcards alone, which is why only they count
(patterns.algorithm). A list column splits into its lengths up to the longest
pattern's and the longer lists, whose list after their elements comes back as a
column of wildcards.
-/

namespace Stilt.Guards

/-- A bound on the integer literals that begin the rows. -/
def litBound (rows : Rows) : Nat :=
  rows.foldr (fun r acc => match r with
    | .int m :: _ => m.natAbs + acc
    | _ => acc) 0

theorem le_litBound : ∀ {rows : Rows} {m : Int} {rest : List Pat},
    .int m :: rest ∈ rows → m.natAbs ≤ litBound rows
  | r :: rows, m, rest, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [litBound]
    · have := le_litBound (rows := rows) h
      simp only [litBound, List.foldr_cons] at this ⊢
      split <;> omega

/-- An integer that no literal beginning a row names is matched only by the rows
that begin with a wildcard. -/
theorem int_wild {rows : Rows} {q : Pat} {rest : List Pat} (hr : q :: rest ∈ rows)
    (hno : q.noOr = true) (hqc : q.hasConst = false)
    (hm : Matches q (.int ((litBound rows : Int) + 1))) : q.isWild = true := by
  cases q with
  | wild | bind _ => rfl
  | int m =>
    have hb := le_litBound hr
    have : m = (litBound rows : Int) + 1 := by
      by_cases h : m = (litBound rows : Int) + 1
      · exact h
      · simp [Matches, Pat.ways, h] at hm
    omega
  | or _ _ => simp [Pat.noOr] at hno
  | const _ _ => simp [Pat.hasConst] at hqc
  | _ => simp [Matches, Pat.ways] at hm

/-! ## Rows of a shape -/

/-- Rows of `n` patterns each. -/
def Shaped (rows : Rows) (n : Nat) : Prop := ∀ r ∈ rows, r.length = n

theorem Shaped.spec {f : Pat → Option (List Pat)} {k m : Nat} (hf : Arity f k) {rows : Rows}
    (h : Shaped rows (m + 1)) : Shaped (spec f (expand rows)) (k + m) := by
  intro r hr
  obtain ⟨row, hrow, he⟩ := List.mem_filterMap.1 hr
  obtain ⟨r', hr', hrow'⟩ := List.mem_flatMap.1 hrow
  match r', hrow' with
  | p :: rest, hrow' =>
    obtain ⟨q, _, rfl⟩ := List.mem_map.1 hrow'
    simp only [Option.map_eq_some_iff] at he
    obtain ⟨ps, hps, rfl⟩ := he
    have := h _ hr'
    simp only [List.length_cons] at this
    simp [hf q ps hps]
    omega
  | [], _ => exact absurd (h _ hr') (by simp)

/-- In rows of at least one pattern, a first column that isn't all wildcards has
a row that doesn't begin with one. -/
theorem not_allWild {rows : Rows} {m : Nat} (h : Shaped rows (m + 1))
    (hall : ¬(expand rows).all (fun r => match r with | p :: _ => p.isWild | [] => false) = true) :
    allWild (heads rows) = false := by
  simp only [Bool.not_eq_true, List.all_eq_false] at hall
  obtain ⟨r, hr, hw⟩ := hall
  obtain ⟨r', hr', hrow⟩ := List.mem_flatMap.1 hr
  match r', hrow with
  | p :: rest, hrow =>
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hrow
    simp only [allWild, List.all_eq_false, List.mem_flatMap]
    exact ⟨q, ⟨p, mem_heads.2 ⟨rest, hr'⟩, hq⟩, by simpa using hw⟩
  | [], _ => exact absurd (h _ hr') (by simp)

theorem keeps_lenC (k : Nat) : KeepsConstFree (lenC k) := by
  intro p ps h hc q hq
  cases p
  case list rs =>
    simp only [lenC] at h; split at h <;> cases h
    exact Pat.anyConst_false hc q hq
  case «prefix» rs o =>
    simp only [lenC] at h; split at h <;> cases h
    rcases List.mem_append.1 hq with hq | hq
    · exact Pat.anyConst_false hc q hq
    · exact wilds_constFree _ q hq
  all_goals
    simp only [lenC] at h; split at h <;> cases h
    exact wilds_constFree k q hq

theorem keeps_longC (k : Nat) : KeepsConstFree (longC k) := by
  intro p ps h hc q hq
  cases p
  case «prefix» rs o =>
    simp only [longC] at h; split at h <;> cases h
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (hq | hq) | rfl
    · exact Pat.anyConst_false hc q hq
    · exact wilds_constFree _ q hq
    · rfl
  all_goals
    simp only [longC] at h; split at h <;> cases h
    exact wilds_constFree _ q hq

theorem cost_wild {τ : Ty} {P : List Pat} (h : allWild P = true) : cost τ P = 1 := by
  cases τ <;> simp [cost, h]

/-- A step's rows cost less than the rows they come from, when its constructor's
parts of the first column cost less than the column. -/
theorem step_lt {f : Pat → Option (List Pat)} {us : List Ty} (hf : Arity f us.length) {rows : Rows}
    {τ : Ty} {τs : List Ty} {n : Nat}
    (hu : costs us (spec f (expand (single (heads rows)))) < cost τ (heads rows))
    (hs : cost τ (heads rows) + costs τs (tails rows) < n + 1) :
    costs (us ++ τs) (spec f (expand rows)) < n := by
  have := spec_costs hf rows τs
  omega

/-! ## The check says yes -/

/-- The check is complete: when every vector of values of the types matches a
row of as many patterns and no row holds a constant, a check whose fuel exceeds
the rows' measure says yes. -/
theorem check_complete : ∀ (n : Nat) {rows : Rows} {τs : List Ty},
    costs τs rows < n → Shaped rows τs.length → ConstFree rows → Covers rows τs →
    check n rows τs = true
  | 0, _, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, rows, [], _, _, _, hcov => by
    obtain ⟨r, hr, hm⟩ := hcov [] .nil
    have hl := rowMatches_length hm
    match r, hl with
    | [], _ =>
      simp only [check, List.any_eq_true]
      exact ⟨[], hr, rfl⟩
  | n + 1, rows, τ :: τs, hs, hsh, hc, hcov => by
    simp only [costs] at hs
    simp only [List.length_cons] at hsh
    have hE := expand_constFree hc
    have hτ := cost_pos τ (heads rows)
    have go := fun {f : Pat → Option (List Pat)} {us : List Ty} (hf : Arity f us.length)
        (hk : KeepsConstFree f) (hu : costs us (spec f (expand (single (heads rows)))) <
          cost τ (heads rows)) (hcv : Covers (spec f (expand rows)) (us ++ τs)) =>
      check_complete n (step_lt hf hu hs) (by simpa using Shaped.spec hf hsh)
        (spec_constFree hk hE) hcv
    simp only [check]
    split
    · rename_i hall
      refine go (us := []) arity_anyC keeps_anyC (by simp [costs]; omega) ?_
      intro vs hvs
      obtain ⟨q, rest, hr, _, _, _, hrest⟩ :=
        expand_row hc (hcov _ (.cons (Ty.witness_ty τ) hvs))
      have hw : q.isWild = true := by simpa using List.all_eq_true.1 hall _ hr
      exact ⟨rest, mem_spec (ps := []) hr (by simp [anyC, hw]), hrest⟩
    · rename_i hall
      have hw := not_allWild hsh hall
      cases τ with
      | int =>
        refine go (us := []) arity_anyC keeps_anyC (by simp [costs]; omega) ?_
        intro vs hvs
        obtain ⟨q, rest, hr, hno, hqc, hqm, hrest⟩ := expand_row hc (hcov _ (.cons .int hvs))
        have hw := int_wild hr hno hqc hqm
        exact ⟨rest, mem_spec (ps := []) hr (by simp [anyC, hw]), hrest⟩
      | bool =>
        simp only [Bool.and_eq_true]
        have cover (b : Bool) : Covers (spec (boolC b) (expand rows)) ([] ++ τs) :=
          spec_covers (us := []) hc hcov fun ws hws => by
            cases hws
            exact ⟨.bool b, .bool, (boolC_full b).on _⟩
        exact ⟨go (us := []) (arity_boolC true) (keeps_boolC true) (by simp [costs]; omega) (cover true),
          go (us := []) (arity_boolC false) (keeps_boolC false) (by simp [costs]; omega) (cover false)⟩
      | unit =>
        refine go (us := []) arity_unitC keeps_unitC (by simp [costs]; omega) ?_
        exact spec_covers (us := []) hc hcov fun ws hws => by
          cases hws
          exact ⟨.unit, .unit, unitC_full.on _⟩
      | tuple ts =>
        refine go (us := ts) (arity_tupleC _) (keeps_tupleC _) ?_ ?_
        · simp only [cost, hw, Bool.false_eq_true, ite_false]; omega
        · exact spec_covers (us := ts) hc hcov fun ws hws =>
            ⟨.tuple ws, .tuple hws, (hws.length_eq ▸ tupleC_full ws).on _⟩
      | option t =>
        simp only [Bool.and_eq_true]
        refine ⟨go (us := []) arity_noneC keeps_noneC (by simp [costs]; omega) ?_,
          go (us := [t]) arity_someC keeps_someC ?_ ?_⟩
        · exact spec_covers (us := []) hc hcov fun ws hws => by
            cases hws
            exact ⟨.none, .none, noneC_full.on _⟩
        · simp only [cost, costs, hw, Bool.false_eq_true, ite_false]; omega
        · exact spec_covers (us := [t]) hc hcov fun ws hws => by
            cases hws with
            | cons hu hn =>
              cases hn
              exact ⟨.some _, .some hu, (someC_full _).on _⟩
      | list t =>
        have hL : longest (expand rows) = longest (expand (single (heads rows))) :=
          longest_heads (heads_expand_single rows).symm
        have hcost : cost (.list t) (heads rows) = 2 +
            (List.range (longest (expand rows) + 1)).foldr
              (fun k acc => max acc (spread t k (spec (lenC k) (expand (single (heads rows)))))) 0 +
            spread t (longest (expand rows) + 1)
              (spec (longC (longest (expand rows) + 1)) (expand (single (heads rows)))) + 1 := by
          rw [hL]; simp [cost, hw]
        simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
        refine ⟨fun k hk => ?_, ?_⟩
        · refine go (f := lenC k) (us := List.replicate k t)
            (by rw [List.length_replicate]; exact arity_lenC k) (keeps_lenC k) ?_ ?_
          · rw [← spread_eq]
            have := le_foldr_max (fun k => spread t k (spec (lenC k) (expand (single (heads rows)))))
              (l := List.range (longest (expand rows) + 1)) (List.mem_range.2 hk)
            omega
          · exact spec_covers hc hcov fun ws hws => by
              obtain ⟨hl, hall⟩ := ValsTy.of_replicate hws
              exact ⟨.list ws, .list hall, (hl ▸ lenC_full ws).on _⟩
        · have e : List.replicate (longest (expand rows) + 1) t ++ Ty.list t :: τs =
              (List.replicate (longest (expand rows) + 1) t ++ [.list t]) ++ τs := by simp
          rw [e]
          refine go (f := longC (longest (expand rows) + 1))
            (us := List.replicate (longest (expand rows) + 1) t ++ [.list t])
            (by simpa using arity_longC (longest (expand rows) + 1)) (keeps_longC _) ?_ ?_
          · rw [costs_append, ← spread_eq]
            simp only [List.length_replicate, costs]
            have hw' : cost (.list t) (heads (drops (longest (expand rows) + 1)
                (spec (longC (longest (expand rows) + 1)) (expand (single (heads rows)))))) = 1 :=
              cost_wild (allWild_long (longest (expand rows) + 1) (expand (single (heads rows))))
            omega
          · refine spec_covers hc hcov fun ws hws => ?_
            obtain ⟨xs, w, rfl, hxs, hw'⟩ := ValsTy.split hws
            cases hw' with
            | cons hy hn =>
              cases hn
              cases hy with
              | list hys =>
                rename_i ys
                obtain ⟨hl, hall⟩ := ValsTy.of_replicate hxs
                refine ⟨.list (xs ++ ys), .list fun v hv => ?_, longC_full ?_ hl⟩
                · rcases List.mem_append.1 hv with hv | hv
                  · exact hall v hv
                  · exact hys v hv
                · intro p hp m hm
                  obtain ⟨rest, hr⟩ := mem_heads.1 hp
                  exact le_longest (rows := expand rows) hr (by cases p <;> simp [listLength] at hm ⊢ <;> exact hm)

/-- A `match` whose arms without a guard or a constant cover every value of a
type is found exhaustive, with fuel beyond the cost of their patterns. -/
theorem exhaustive_complete {arms : List Arm} {τ : Ty} {n : Nat}
    (hn : cost τ ((arms.filter Arm.counts).map Arm.pat) < n)
    (h : ∀ v, ValTy v τ → ∃ a ∈ arms, a.counts = true ∧ Matches a.pat v) :
    exhaustive arms τ n = true := by
  have hh : heads ((arms.filter Arm.counts).map fun a => [a.pat]) =
      (arms.filter Arm.counts).map Arm.pat := by
    simp only [heads, List.filterMap_map]
    induction arms.filter Arm.counts with
    | nil => rfl
    | cons a as ih => simp only [List.filterMap_cons, Function.comp, List.head?_cons, List.map_cons]; rw [ih]
  refine check_complete n ?_ ?_ ?_ ?_
  · simp only [costs]; rw [hh]; omega
  · intro r hr
    obtain ⟨a, _, rfl⟩ := List.mem_map.1 hr
    rfl
  · intro r hr p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
    simp only [List.mem_singleton] at hp
    subst hp
    have := (List.mem_filter.1 ha).2
    simp only [Arm.counts, Bool.and_eq_true, Bool.not_eq_true'] at this
    exact this.2
  · intro vs hvs
    cases hvs with
    | cons hv hn =>
      cases hn
      obtain ⟨a, ha, hc, hm⟩ := h _ hv
      exact ⟨[a.pat], List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, hc⟩, rfl⟩,
        rowMatches_cons.2 ⟨hm, rowMatches_nil⟩⟩

end Stilt.Guards
