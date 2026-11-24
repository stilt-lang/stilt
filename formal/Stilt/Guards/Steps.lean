import Stilt.Guards.Measure

/-!
# The steps of the check

What each step of the check keeps, for `Stilt.Guards.Complete`: the rows of a
constructor cover the parts of the values it builds (`spec_covers`), and their
measure is less than the rows' (`spec_costs`), a constructor of `k` parts
taking apart a row's first pattern into `k` patterns (`Arity`). A list column
splits into its lengths up to the longest pattern's, each taken apart by
`lenC`, and the longer lists, which `longC` takes apart into as many elements
and a column of wildcards for the list after them.
-/

namespace Stilt.Guards

/-! ## Rows that cover -/

/-- Every vector of values of the types matches a row. -/
def Covers (rows : Rows) (τs : List Ty) : Prop := ∀ vs, ValsTy vs τs → ∃ r ∈ rows, RowMatches r vs

/-- `f` keeps each pattern of `S` that matches the value `v`, as patterns that match its
parts `ws`. -/
def SpecFullOn (S : List Pat) (f : Pat → Option (List Pat)) (v : Val) (ws : List Val) : Prop :=
  ∀ p ∈ S, p.noOr = true → p.hasConst = false → Matches p v → ∃ ps, f p = some ps ∧ RowMatches ps ws

theorem SpecFull.on {f : Pat → Option (List Pat)} {v : Val} {ws : List Val} (h : SpecFull f v ws)
    (S : List Pat) : SpecFullOn S f v ws :=
  fun p _ => h p

/-- A vector that matches a row matches a row of the expanded rows, whose first
pattern is no or-pattern. -/
theorem expand_row {rows : Rows} (hc : ConstFree rows) {v : Val} {vs : List Val}
    (h : ∃ r ∈ rows, RowMatches r (v :: vs)) :
    ∃ q rest, q :: rest ∈ expand rows ∧ q.noOr = true ∧ q.hasConst = false ∧ Matches q v ∧
      RowMatches rest vs := by
  obtain ⟨r, hr, hm⟩ := h
  match r, hm with
  | p :: rest, hm =>
    rw [rowMatches_cons] at hm
    obtain ⟨q, hq, hqm⟩ := Pat.alts_complete hm.1
    refine ⟨q, rest, ?_, Pat.alts_noOr hq, Pat.alts_constFree (hc _ hr p List.mem_cons_self) hq,
      hqm, hm.2⟩
    exact List.mem_flatMap.2 ⟨p :: rest, hr, List.mem_map.2 ⟨q, hq, rfl⟩⟩
  | [], hm => exact absurd (rowMatches_length hm) (by simp)

theorem mem_spec {f : Pat → Option (List Pat)} {rows : Rows} {q : Pat} {rest ps : List Pat}
    (hr : q :: rest ∈ rows) (hf : f q = some ps) : ps ++ rest ∈ spec f rows :=
  List.mem_filterMap.2 ⟨q :: rest, hr, by simp [hf]⟩

/-- A constructor's rows cover the parts of the values it builds. -/
theorem spec_covers {f : Pat → Option (List Pat)} {rows : Rows} {τ : Ty} {τs us : List Ty}
    (hc : ConstFree rows) (hcov : Covers rows (τ :: τs))
    (build : ∀ ws, ValsTy ws us → ∃ v, ValTy v τ ∧ SpecFullOn (heads (expand rows)) f v ws) :
    Covers (spec f (expand rows)) (us ++ τs) := by
  intro vs' hv'
  obtain ⟨ws, vs, rfl, hw, hvs⟩ := ValsTy.split hv'
  obtain ⟨v, hv, hfull⟩ := build ws hw
  obtain ⟨q, rest, hr, hno, hqc, hqm, hrest⟩ := expand_row hc (hcov (v :: vs) (.cons hv hvs))
  obtain ⟨ps, hps, hpm⟩ := hfull q (mem_heads.2 ⟨rest, hr⟩) hno hqc hqm
  exact ⟨ps ++ rest, mem_spec hr hps, rowMatches_append_of hpm hrest⟩

/-! ## Constructors of lists -/

theorem ValsTy.of_replicate {t : Ty} : ∀ {ws : List Val} {k : Nat}, ValsTy ws (List.replicate k t) →
    ws.length = k ∧ ∀ w ∈ ws, ValTy w t
  | [], 0, .nil => ⟨rfl, fun _ h => nomatch h⟩
  | _ :: _, _ + 1, .cons hw hws => by
    obtain ⟨hl, h⟩ := ValsTy.of_replicate hws
    exact ⟨by simp [hl], fun w hw' => by
      rcases List.mem_cons.1 hw' with rfl | hw'
      · exact hw
      · exact h w hw'⟩

/-- A prefix pattern that matches a list matches its first elements. -/
theorem Matches.prefix {ps : List Pat} {o : Option Name} {ws : List Val}
    (h : Matches (.prefix ps o) (.list ws)) :
    ps.length ≤ ws.length ∧ RowMatches ps (ws.take ps.length) := by
  simp only [Matches, Pat.ways] at h
  split at h
  · rename_i hl
    exact ⟨hl, fun he => h (by simp [he])⟩
  · exact absurd rfl h

/-- A prefix padded with wildcards matches a list whose first elements its prefix
matches. -/
theorem prefix_padded {ps : List Pat} {ws : List Val}
    (h : RowMatches ps (ws.take ps.length)) :
    RowMatches (ps ++ wilds (ws.length - ps.length)) ws := by
  have hw := rowMatches_wilds (ws.drop ps.length)
  rw [List.length_drop] at hw
  have := rowMatches_append_of h hw
  rwa [List.take_append_drop] at this

theorem lenC_full (ws : List Val) : SpecFull (lenC ws.length) (.list ws) ws := by
  intro p _ hc hm
  cases p with
  | list ps =>
    have hl : ps.length = ws.length := rowMatches_length hm
    exact ⟨ps, by simp [lenC, hl], hm⟩
  | «prefix» ps o =>
    obtain ⟨hl, hm⟩ := Matches.prefix hm
    exact ⟨_, by simp [lenC, hl], prefix_padded hm⟩
  | wild | bind _ => exact ⟨wilds ws.length, rfl, rowMatches_wilds ws⟩
  | or _ _ => contradiction
  | const _ _ => simp [Pat.hasConst] at hc
  | _ => simp [Matches, Pat.ways] at hm

/-- The lists longer than `k`, built from their first `k + 1` elements `xs` and the rest
`ys`: a pattern of the column, whose list patterns are no longer than `k`, keeps a row. -/
theorem longC_full {S : List Pat} {k : Nat} (hS : ∀ p ∈ S, ∀ n, listLength [p] = some n → n ≤ k)
    {xs ys : List Val} (hx : xs.length = k + 1) :
    SpecFullOn S (longC (k + 1)) (.list (xs ++ ys)) (xs ++ [.list ys]) := by
  intro p hp _ hc hm
  cases p with
  | list ps =>
    have hl : ps.length = (xs ++ ys).length := rowMatches_length hm
    have := hS _ hp ps.length rfl
    rw [List.length_append] at hl
    omega
  | «prefix» ps o =>
    obtain ⟨_, hm⟩ := Matches.prefix hm
    have hk := hS _ hp ps.length rfl
    have ht : (xs ++ ys).take ps.length = xs.take ps.length := List.take_append_of_le_length (by omega)
    rw [ht] at hm
    have hpad := prefix_padded (ws := xs) hm
    rw [hx] at hpad
    refine ⟨ps ++ wilds (k + 1 - ps.length) ++ [.wild], by simp [longC]; omega, ?_⟩
    exact rowMatches_append_of hpad
      (rowMatches_cons.2 ⟨Pat.isWild_matches (p := .wild) rfl _, rowMatches_nil⟩)
  | wild | bind _ =>
    refine ⟨wilds (k + 2), by simp [longC, Pat.isWild], ?_⟩
    have := rowMatches_wilds (xs ++ [.list ys])
    simpa [hx] using this
  | or _ _ => contradiction
  | const _ _ => simp [Pat.hasConst] at hc
  | _ => simp [Matches, Pat.ways] at hm

/-! ## The measure of a constructor's rows -/

/-- A constructor that takes a pattern apart into `k` patterns. -/
def Arity (f : Pat → Option (List Pat)) (k : Nat) : Prop := ∀ p ps, f p = some ps → ps.length = k

theorem arity_anyC : Arity anyC 0 := by
  intro p ps h; unfold anyC at h; split at h <;> cases h; rfl

theorem arity_boolC (b : Bool) : Arity (boolC b) 0 := by
  intro p ps h; cases p
  case bool c => simp only [boolC] at h; split at h <;> cases h; rfl
  all_goals exact arity_anyC _ _ h

theorem arity_unitC : Arity unitC 0 := by
  intro p ps h; cases p
  case unit => cases h; rfl
  all_goals exact arity_anyC _ _ h

theorem arity_noneC : Arity noneC 0 := by
  intro p ps h; cases p
  case none => cases h; rfl
  all_goals exact arity_anyC _ _ h

theorem arity_someC : Arity someC 1 := by
  intro p ps h; cases p
  case some => cases h; rfl
  all_goals simp only [someC] at h; split at h <;> cases h; rfl

theorem arity_tupleC (k : Nat) : Arity (tupleC k) k := by
  intro p ps h; cases p
  case tuple => simp only [tupleC] at h; split at h <;> cases h; assumption
  all_goals simp only [tupleC] at h; split at h <;> cases h; simp [wilds]

theorem arity_lenC (k : Nat) : Arity (lenC k) k := by
  intro p ps h; cases p
  case list => simp only [lenC] at h; split at h <;> cases h; assumption
  case «prefix» => simp only [lenC] at h; split at h <;> cases h; simp [wilds]; omega
  all_goals simp only [lenC] at h; split at h <;> cases h; simp [wilds]

theorem arity_longC (k : Nat) : Arity (longC k) (k + 1) := by
  intro p ps h; cases p
  case «prefix» => simp only [longC] at h; split at h <;> cases h; simp [wilds]; omega
  all_goals simp only [longC] at h; split at h <;> cases h; simp [wilds]

/-- The rows after a constructor's parts are rows after the first pattern. -/
theorem drops_spec {f : Pat → Option (List Pat)} {k : Nat} (hf : Arity f k) (rows : Rows) :
    Sub (drops k (spec f (expand rows))) (tails rows) := by
  intro r hr
  obtain ⟨ps', hl, hm⟩ := mem_drops.1 hr
  obtain ⟨row, hrow, he⟩ := List.mem_filterMap.1 hm
  match row, he with
  | q :: rest, he =>
    simp only [Option.map_eq_some_iff] at he
    obtain ⟨ps, hps, he⟩ := he
    have := List.append_inj he (by rw [hf q ps hps, hl])
    rw [this.2] at hrow
    obtain ⟨r', hr', hrow'⟩ := List.mem_flatMap.1 hrow
    match r', hrow' with
    | p :: rest', hrow' =>
      obtain ⟨_, _, he'⟩ := List.mem_map.1 hrow'
      cases he'
      exact mem_tails.2 ⟨p, hr'⟩
    | [], hrow' => simp at hrow'

/-- A constructor's parts of the rows are among its parts of their first patterns. -/
theorem cols_spec {f : Pat → Option (List Pat)} {k : Nat} (hf : Arity f k) (rows : Rows) :
    ColSub k (spec f (expand rows)) (spec f (expand (single (heads rows)))) := by
  intro i hi x hx
  obtain ⟨l, hl, hx⟩ := mem_col.1 hx
  obtain ⟨row, hrow, he⟩ := List.mem_filterMap.1 hl
  match row, he with
  | q :: rest, he =>
    simp only [Option.map_eq_some_iff] at he
    obtain ⟨ps, hps, rfl⟩ := he
    have hlen := hf q ps hps
    rw [List.getElem?_append_left (by omega)] at hx
    have hq : q ∈ heads (expand rows) := mem_heads.2 ⟨rest, hrow⟩
    rw [heads_expand] at hq
    exact mem_col.2 ⟨ps ++ [], mem_spec (mem_expand_single.2 ⟨q, hq, rfl⟩) hps, by simpa using hx⟩

theorem heads_expand_single (rows : Rows) :
    heads (expand (single (heads rows))) = heads (expand rows) := by
  rw [heads_expand, heads_expand, heads_single]

/-- The longest list pattern is the longest of the first patterns. -/
theorem longest_heads {R R' : Rows} (h : heads R = heads R') : longest R = longest R' := by
  have key : ∀ R : Rows,
      longest R = (heads R).foldr (fun p n => max ((listLength [p]).getD 0) n) 0 := by
    intro R
    rw [longest_eq]
    induction R with
    | nil => rfl
    | cons r R ih =>
      cases r with
      | nil =>
        rw [show heads ([] :: R) = heads R from rfl, ← ih]
        simp [listLength]
      | cons p rest =>
        rw [show heads ((p :: rest) :: R) = p :: heads R from rfl]
        simp only [List.foldr_cons]
        rw [ih]
        congr 2
        cases p <;> rfl
  rw [key, key, h]

/-- The measure of a constructor's rows: the parts' columns cost no more than the
constructor's parts of the first column, and the columns after them no more than
the rows' own. -/
theorem spec_costs {f : Pat → Option (List Pat)} {us : List Ty} (hf : Arity f us.length)
    (rows : Rows) (τs : List Ty) :
    costs (us ++ τs) (spec f (expand rows)) ≤
      costs us (spec f (expand (single (heads rows)))) + costs τs (tails rows) := by
  rw [costs_append]
  have h₁ := costs_mono_of us (fun t _ => cost_mono t) (cols_spec hf rows)
  have h₂ := costs_mono_of τs (fun t _ => cost_mono t) (.of_sub (drops_spec hf rows))
  omega

/-- The last part that `longC` gives, the list after the elements, is a wildcard. -/
theorem longC_last {k : Nat} {q : Pat} {ps : List Pat} (h : longC k q = some ps) :
    ps[k]? = some .wild := by
  cases q
  case «prefix» qs o =>
    simp only [longC] at h
    split at h
    · rename_i hq
      cases h
      have hl : (qs ++ wilds (k - qs.length)).length = k := by simp [wilds]; omega
      rw [List.getElem?_append_right (by omega), hl, Nat.sub_self]
      rfl
    · cases h
  all_goals
    simp only [longC] at h
    split at h <;> cases h
    exact getElem?_wilds (by omega)

/-- The column of the lists after the elements is all wildcards. -/
theorem allWild_long (k : Nat) (rows : Rows) : allWild (col k (spec (longC k) rows)) = true := by
  simp only [allWild, List.all_eq_true, List.mem_flatMap]
  rintro q ⟨p, hp, hq⟩
  obtain ⟨l, hl, hx⟩ := mem_col.1 hp
  obtain ⟨row, _, he⟩ := List.mem_filterMap.1 hl
  match row, he with
  | r :: rest, he =>
    simp only [Option.map_eq_some_iff] at he
    obtain ⟨ps, hps, rfl⟩ := he
    have hlen := arity_longC k r ps hps
    rw [List.getElem?_append_left (by omega), longC_last hps] at hx
    cases hx
    simp [Pat.alts] at hq
    rw [hq]
    rfl

end Stilt.Guards
