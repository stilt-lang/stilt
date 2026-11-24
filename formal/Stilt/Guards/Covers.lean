import Stilt.Guards.Exhaustive

/-!
# The check is sound

Each constructor's rows take its values apart soundly (`SpecOk`), and so
`check_sound`: a check that says yes means that every vector of values of the
types matches a row. A list longer than the longest pattern is taken apart into
that many elements and the list after them, which a row of wildcards matches.
-/

namespace Stilt.Guards

theorem ValsTy.length_eq : ∀ {vs : List Val} {ts : List Ty}, ValsTy vs ts → vs.length = ts.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ h => by simp [ValsTy.length_eq h]

theorem ValsTy.append : ∀ {vs ws : List Val} {ts us : List Ty}, ValsTy vs ts → ValsTy ws us →
    ValsTy (vs ++ ws) (ts ++ us)
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons hv hvs, h => .cons hv (ValsTy.append hvs h)

theorem ValsTy.replicate {τ : Ty} : ∀ {us : List Val}, (∀ v ∈ us, ValTy v τ) →
    ValsTy us (List.replicate us.length τ)
  | [], _ => .nil
  | v :: _, h =>
    .cons (h v List.mem_cons_self) (ValsTy.replicate fun u hu => h u (List.mem_cons_of_mem _ hu))

theorem anyC_ok (v : Val) : SpecOk anyC v [] := by
  intro p ps h
  unfold anyC at h
  split at h
  · cases h
    exact ⟨rfl, fun _ => Pat.isWild_matches (by assumption) v⟩
  · cases h

theorem boolC_ok (b : Bool) : SpecOk (boolC b) (.bool b) [] := by
  intro p ps h
  cases p
  case bool c =>
    simp only [boolC] at h
    split at h
    · cases h
      exact ⟨rfl, fun _ => by simp_all [Matches, Pat.ways]⟩
    · cases h
  all_goals exact anyC_ok _ _ _ h

theorem unitC_ok : SpecOk unitC .unit [] := by
  intro p ps h
  cases p
  case unit =>
    cases h
    exact ⟨rfl, fun _ => by simp [Matches, Pat.ways]⟩
  all_goals exact anyC_ok _ _ _ h

theorem noneC_ok : SpecOk noneC .none [] := by
  intro p ps h
  cases p
  case none =>
    cases h
    exact ⟨rfl, fun _ => by simp [Matches, Pat.ways]⟩
  all_goals exact anyC_ok _ _ _ h

/-- A pattern that isn't a wildcard takes nothing apart in a constructor's
catch-all case. -/
private theorem wild_case {p : Pat} {qs ps : List Pat} {v : Val} {ws : List Val}
    (h : (if p.isWild then some qs else none) = some ps) (hl : qs.length = ws.length) :
    ps.length = ws.length ∧ (RowMatches ps ws → Matches p v) := by
  split at h
  · cases h
    exact ⟨hl, fun _ => Pat.isWild_matches (by assumption) v⟩
  · cases h

theorem someC_ok (u : Val) : SpecOk someC (.some u) [u] := by
  intro p ps h
  cases p
  case some q =>
    cases h
    refine ⟨rfl, fun hm => ?_⟩
    simpa [Matches, Pat.ways] using (rowMatches_cons.1 hm).1
  all_goals exact wild_case h rfl

theorem tupleC_ok (us : List Val) : SpecOk (tupleC us.length) (.tuple us) us := by
  intro p ps h
  cases p
  case tuple qs =>
    simp only [tupleC] at h
    split at h
    · cases h
      exact ⟨by assumption, fun hm => by simpa [Matches, Pat.ways, RowMatches] using hm⟩
    · cases h
  all_goals exact wild_case h (by simp [wilds])

/-- A prefix pattern whose patterns match a list's first elements matches the
list. -/
theorem prefix_matches {ps : List Pat} {r : Option Name} {us : List Val} (hl : ps.length ≤ us.length)
    (hm : RowMatches ps (us.take ps.length)) : Matches (.prefix ps r) (.list us) := by
  simp only [Matches, Pat.ways, hl, ↓reduceIte, ne_eq, List.map_eq_nil_iff]
  exact hm

theorem lenC_ok (us : List Val) : SpecOk (lenC us.length) (.list us) us := by
  intro p ps h
  cases p
  case list qs =>
    simp only [lenC] at h
    split at h
    · cases h
      exact ⟨by assumption, fun hm => by simpa [Matches, Pat.ways, RowMatches] using hm⟩
    · cases h
  case «prefix» qs r =>
    simp only [lenC] at h
    split at h
    · cases h
      rename_i hl
      refine ⟨by simp [wilds]; omega, fun hm => ?_⟩
      rw [← List.take_append_drop qs.length us] at hm
      have := (rowMatches_append _ _ (by simp; omega) hm).1
      exact prefix_matches hl this
    · cases h
  all_goals exact wild_case h (by simp [wilds])

theorem longC_ok {k : Nat} {us : List Val} (hk : k ≤ us.length) :
    SpecOk (longC k) (.list us) (us.take k ++ [.list (us.drop k)]) := by
  intro p ps h
  cases p
  case «prefix» qs r =>
    simp only [longC] at h
    split at h
    · cases h
      rename_i hl
      refine ⟨by simp [wilds]; omega, fun hm => ?_⟩
      have h₁ := (rowMatches_append _ _ (by simp [wilds]; omega) hm).1
      rw [← List.take_append_drop qs.length (us.take k)] at h₁
      have h₂ := (rowMatches_append _ _ (by simp; omega) h₁).1
      rw [List.take_take, Nat.min_eq_left hl] at h₂
      exact prefix_matches (by omega) h₂
    · cases h
  all_goals exact wild_case h (by simp [wilds]; omega)

/-- A constructor's row that matches comes from a row that matches. -/
theorem lift {f : Pat → Option (List Pat)} {v : Val} {ws : List Val} (hf : SpecOk f v ws)
    {rows : Rows} {vs : List Val} :
    (∃ r ∈ spec f (expand rows), RowMatches r (ws ++ vs)) → ∃ r ∈ rows, RowMatches r (v :: vs) := by
  rintro ⟨r, hr, hm⟩
  obtain ⟨r', hr', hm'⟩ := spec_lift hf hr hm
  exact expand_lift hr' hm'

/-- A check that says yes: every vector of values of the types matches a row. -/
theorem check_sound : ∀ (n : Nat) {rows : Rows} {τs : List Ty} {vs : List Val},
    check n rows τs = true → ValsTy vs τs → ∃ r ∈ rows, RowMatches r vs
  | 0, _, _, _, h, _ => by simp [check] at h
  | n + 1, rows, [], vs, h, hv => by
    cases hv
    simp only [check, List.any_eq_true] at h
    obtain ⟨r, hr, he⟩ := h
    cases r
    · exact ⟨[], hr, rowMatches_nil⟩
    · simp at he
  | n + 1, rows, τ :: τs, _, h, .cons (v := v) (vs := vs) hv hvs => by
    simp only [check] at h
    split at h
    · exact lift (anyC_ok v) (check_sound n h hvs)
    · cases hv with
      | int => exact lift (anyC_ok _) (check_sound n h hvs)
      | bool =>
        rename_i b
        simp only [Bool.and_eq_true] at h
        cases b
        · exact lift (boolC_ok false) (check_sound n h.2 hvs)
        · exact lift (boolC_ok true) (check_sound n h.1 hvs)
      | unit => exact lift unitC_ok (check_sound n h hvs)
      | tuple hus =>
        rename_i us ts
        dsimp only at h
        rw [← hus.length_eq] at h
        exact lift (tupleC_ok us) (check_sound n h (hus.append hvs))
      | none =>
        simp only [Bool.and_eq_true] at h
        exact lift noneC_ok (check_sound n h.1 hvs)
      | some hu =>
        simp only [Bool.and_eq_true] at h
        exact lift (someC_ok _) (check_sound n h.2 (.cons hu hvs))
      | list hus =>
        rename_i us t
        simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
        by_cases hm : us.length ≤ longest (expand rows)
        · have hc := h.1 us.length (by omega)
          exact lift (lenC_ok us) (check_sound n hc ((ValsTy.replicate hus).append hvs))
        · have hk : longest (expand rows) + 1 ≤ us.length := by omega
          have ht : ValsTy (us.take (longest (expand rows) + 1))
              (List.replicate (longest (expand rows) + 1) t) := by
            have := ValsTy.replicate (us := us.take (longest (expand rows) + 1)) (τ := t)
              (fun u hu => hus u (List.mem_of_mem_take hu))
            rwa [List.length_take, Nat.min_eq_left hk] at this
          have hd : ValTy (.list (us.drop (longest (expand rows) + 1))) (.list t) :=
            .list fun u hu => hus u (List.mem_of_mem_drop hu)
          have hall := ht.append (.cons hd hvs)
          rw [← List.singleton_append, ← List.append_assoc] at hall
          exact lift (longC_ok hk) (check_sound n h.2 hall)

end Stilt.Guards
