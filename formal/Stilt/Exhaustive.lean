import Stilt.Patterns
import Stilt.Matching

/-!
# Steps of the usefulness algorithm

What each step of `Exhaustive` rests on, of values alone: a row of a
specialized matrix that matches the parts of a value comes from a row of the
matrix that matches the value (patterns.algorithm). The step for a type checks
the specialized matrices of the type's constructors, so a value built by one
of them, with its parts matched by a row of that constructor's matrix, is
matched by the row it came from.
-/

namespace Stilt

/-- A row of patterns matches a vector of values. -/
def RowMatches (row : List Pattern) (vs : List Value) : Prop := (matchOnAll row vs).isSome

theorem rowMatches_nil : RowMatches [] [] := rfl

theorem rowMatches_cons {p : Pattern} {ps : List Pattern} {v : Value} {vs : List Value} :
    RowMatches (p :: ps) (v :: vs) ↔ (p.matchOn v).isSome ∧ RowMatches ps vs := by
  unfold RowMatches
  simp only [matchOnAll]
  cases p.matchOn v <;> cases matchOnAll ps vs <;> simp

theorem rowMatches_append : ∀ {ps : List Pattern} {ws : List Value} (qs : List Pattern)
    (vs : List Value), ps.length = ws.length →
      (RowMatches (ps ++ qs) (ws ++ vs) ↔ RowMatches ps ws ∧ RowMatches qs vs)
  | [], [], _, _, _ => by simp [RowMatches, matchOnAll]
  | p :: ps, w :: ws, qs, vs, h => by
    rw [List.cons_append, List.cons_append, rowMatches_cons, rowMatches_cons,
      rowMatches_append qs vs (by simpa using h)]
    exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => nomatch h

theorem rowMatches_wilds : ∀ (ws : List Value), RowMatches (List.replicate ws.length .wild) ws
  | [] => rfl
  | _ :: ws => rowMatches_cons.2 ⟨rfl, rowMatches_wilds ws⟩

theorem Pattern.or_isSome {p q : Pattern} {v : Value} :
    ((Pattern.or p q).matchOn v).isSome ↔ (p.matchOn v).isSome ∨ (q.matchOn v).isSome := by
  simp only [Pattern.matchOn]
  cases p.matchOn v <;> cases q.matchOn v <;> simp

/-- The rows of a specialized matrix that come from a row. -/
theorem mem_specialize {f : Spec} {P : Rows} {row : List Pattern} :
    row ∈ specialize f P → ∃ p rest, p :: rest ∈ P ∧ row ∈ f p rest := by
  intro h
  obtain ⟨r, hr, hrow⟩ := List.mem_flatMap.1 h
  cases r with
  | nil => exact nomatch hrow
  | cons p rest => exact ⟨p, rest, hr, hrow⟩

/-- `f` takes apart the value `v` into the parts `ws`: a row it gives that
matches the parts and the rest of a vector comes from a row whose first
pattern matches `v` and whose rest matches the rest. -/
def SpecSound (f : Spec) (v : Value) (ws : List Value) : Prop :=
  ∀ p rest row vs, row ∈ f p rest → RowMatches row (ws ++ vs) →
    (p.matchOn v).isSome ∧ RowMatches rest vs

/-- A row of the specialized matrix that matches the parts of `v` gives a row
of the matrix that matches `v`. -/
theorem SpecSound.lift {f : Spec} {v : Value} {ws : List Value} (h : SpecSound f v ws)
    {P : Rows} {vs : List Value} :
    (∃ row ∈ specialize f P, RowMatches row (ws ++ vs)) → ∃ row ∈ P, RowMatches row (v :: vs) := by
  rintro ⟨row, hrow, hm⟩
  obtain ⟨p, rest, hp, hr⟩ := mem_specialize hrow
  exact ⟨p :: rest, hp, rowMatches_cons.2 (h p rest row vs hr hm)⟩

/-- Or-patterns: a row from either alternative comes from the or-pattern. -/
private theorem or_step {f : Spec} {v : Value} {ws : List Value} {p q : Pattern}
    {rest row : List Pattern} {vs : List Value}
    (hf : f (.or p q) rest = f p rest ++ f q rest)
    (hp : row ∈ f p rest → RowMatches row (ws ++ vs) → (p.matchOn v).isSome ∧ RowMatches rest vs)
    (hq : row ∈ f q rest → RowMatches row (ws ++ vs) → (q.matchOn v).isSome ∧ RowMatches rest vs)
    (h : row ∈ f (.or p q) rest) (hm : RowMatches row (ws ++ vs)) :
    ((Pattern.or p q).matchOn v).isSome ∧ RowMatches rest vs := by
  rw [hf] at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨a, b⟩ := hp h hm
    exact ⟨Pattern.or_isSome.2 (.inl a), b⟩
  · obtain ⟨a, b⟩ := hq h hm
    exact ⟨Pattern.or_isSome.2 (.inr a), b⟩

theorem defaultRow_sound (v : Value) : SpecSound defaultRow v []
  | .wild, _, _, _, h, hm | .bind _, _, _, _, h, hm => by
    simp only [defaultRow, List.mem_singleton] at h
    subst h
    exact ⟨rfl, hm⟩
  | .or p q, rest, row, vs, h, hm =>
    or_step rfl (defaultRow_sound v p rest row vs) (defaultRow_sound v q rest row vs) h hm
  | .int _, _, _, _, h, _ | .bool _, _, _, _, h, _ | .str _, _, _, _, h, _ | .unit, _, _, _, h, _
  | .tuple _, _, _, _, h, _ | .record _ _, _, _, _, h, _ | .variant _ _ _, _, _, _, h, _ => by
    simp [defaultRow] at h

theorem boolRow_sound (b : Bool) : SpecSound (boolRow b) (.bool b) []
  | .wild, _, _, _, h, hm | .bind _, _, _, _, h, hm => by
    simp only [boolRow, List.mem_singleton] at h
    subst h
    exact ⟨rfl, hm⟩
  | .bool c, _, _, _, h, hm => by
    simp only [boolRow] at h
    split at h
    · simp only [List.mem_singleton] at h
      subst h
      rename_i hc
      subst hc
      exact ⟨by simp [Pattern.matchOn], hm⟩
    · exact nomatch h
  | .or p q, rest, row, vs, h, hm =>
    or_step rfl (boolRow_sound b p rest row vs) (boolRow_sound b q rest row vs) h hm
  | .int _, _, _, _, h, _ | .str _, _, _, _, h, _ | .unit, _, _, _, h, _
  | .tuple _, _, _, _, h, _ | .record _ _, _, _, _, h, _ | .variant _ _ _, _, _, _, h, _ => by
    simp [boolRow] at h

theorem unitRow_sound : SpecSound unitRow .unit []
  | .wild, _, _, _, h, hm | .bind _, _, _, _, h, hm | .unit, _, _, _, h, hm => by
    simp only [unitRow, List.mem_singleton] at h
    subst h
    exact ⟨rfl, hm⟩
  | .or p q, rest, row, vs, h, hm =>
    or_step rfl (unitRow_sound p rest row vs) (unitRow_sound q rest row vs) h hm
  | .int _, _, _, _, h, _ | .bool _, _, _, _, h, _ | .str _, _, _, _, h, _
  | .tuple _, _, _, _, h, _ | .record _ _, _, _, _, h, _ | .variant _ _ _, _, _, _, h, _ => by
    simp [unitRow] at h

/-- A row that starts with wildcards for the parts matches what follows them. -/
private theorem wilds_step {ws vs : List Value} {rest : List Pattern} {n : Nat} (hn : ws.length = n)
    (hm : RowMatches (List.replicate n .wild ++ rest) (ws ++ vs)) : RowMatches rest vs :=
  ((rowMatches_append rest vs (by simp [hn])).1 hm).2

theorem tupleRow_sound (ws : List Value) : SpecSound (tupleRow ws.length) (.tuple ws) ws
  | .wild, _, _, _, h, hm | .bind _, _, _, _, h, hm => by
    simp only [tupleRow, List.mem_singleton] at h
    subst h
    exact ⟨rfl, wilds_step rfl hm⟩
  | .tuple ps, rest, _, vs, h, hm => by
    simp only [tupleRow] at h
    split at h
    · rename_i hl
      simp only [List.mem_singleton] at h
      subst h
      obtain ⟨h₁, h₂⟩ := (rowMatches_append rest vs hl).1 hm
      refine ⟨?_, h₂⟩
      simp only [Value.tuple, Pattern.matchOn, positions, map_snd_positionsFrom]
      exact h₁
    · exact nomatch h
  | .or p q, rest, row, vs, h, hm =>
    or_step rfl (tupleRow_sound ws p rest row vs) (tupleRow_sound ws q rest row vs) h hm
  | .int _, _, _, _, h, _ | .bool _, _, _, _, h, _ | .str _, _, _, _, h, _ | .unit, _, _, _, h, _
  | .record _ _, _, _, _, h, _ | .variant _ _ _, _, _, _, h, _ => by
    simp [tupleRow] at h

theorem variantRow_sound (T C : Name) (ws : List Value) :
    SpecSound (variantRow C ws.length) (.variant T C ws) ws
  | .wild, _, _, _, h, hm | .bind _, _, _, _, h, hm => by
    simp only [variantRow, List.mem_singleton] at h
    subst h
    exact ⟨rfl, wilds_step rfl hm⟩
  | .variant _ C' ps, rest, _, vs, h, hm => by
    simp only [variantRow] at h
    split at h
    · rename_i hc
      simp only [List.mem_singleton] at h
      subst h
      obtain ⟨h₁, h₂⟩ := (rowMatches_append rest vs hc.2).1 hm
      refine ⟨?_, h₂⟩
      simp only [Pattern.matchOn, hc.1, ↓reduceIte]
      exact h₁
    · exact nomatch h
  | .or p q, rest, row, vs, h, hm =>
    or_step rfl (variantRow_sound T C ws p rest row vs) (variantRow_sound T C ws q rest row vs) h hm
  | .int _, _, _, _, h, _ | .bool _, _, _, _, h, _ | .str _, _, _, _, h, _ | .unit, _, _, _, h, _
  | .tuple _, _, _, _, h, _ | .record _ _, _, _, _, h, _ => by
    simp [variantRow] at h

theorem lookup_of_mem_nodup {β : Type} :
    ∀ {l : List (Name × β)} {k : Name} {b : β}, (l.map Prod.fst).Nodup → (k, b) ∈ l →
      l.lookup k = some b
  | [], _, _, _, h => nomatch h
  | (k', b') :: l, k, b, hnd, h => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.1 h with h | h
    · cases h
      simp
    · have hk : k ≠ k' := fun hk => hnd.1 (hk ▸ List.mem_map_of_mem (f := Prod.fst) h)
      rw [lookup_cons_ne hk]
      exact lookup_of_mem_nodup hnd.2 h

theorem lookup_of_mem_map {β : Type} :
    ∀ {l : List (Name × β)} {k : Name}, k ∈ l.map Prod.fst → ∃ b, l.lookup k = some b
  | [], _, h => nomatch h
  | (k', b') :: l, k, h => by
    by_cases hk : k = k'
    · subst hk
      exact ⟨b', by simp⟩
    · rw [lookup_cons_ne hk]
      exact lookup_of_mem_map ((List.mem_cons.1 h).resolve_left hk)

/-- The columns of the fields match the fields' values, each its own. -/
private theorem columns_match (g : Name → Pattern) :
    ∀ {fields : List (Name × Value)},
      RowMatches ((fields.map Prod.fst).map g) (fields.map Prod.snd) →
        ∀ fv ∈ fields, ((g fv.1).matchOn fv.2).isSome
  | [], _ => fun _ h => nomatch h
  | (f, v) :: fields, h => by
    simp only [List.map_cons] at h
    obtain ⟨h₁, h₂⟩ := rowMatches_cons.1 h
    intro fv hfv
    rcases List.mem_cons.1 hfv with rfl | hfv
    · exact h₁
    · exact columns_match g h₂ fv hfv

private theorem matchOnFields_isSome {fields : List (Name × Value)} :
    ∀ {fps : List (Name × Pattern)},
      (∀ fp ∈ fps, ∃ v, fields.lookup fp.1 = some v ∧ (fp.2.matchOn v).isSome) →
        (matchOnFields fps fields).isSome
  | [], _ => rfl
  | (f, p) :: fps, h => by
    obtain ⟨v, hv, hm⟩ := h (f, p) List.mem_cons_self
    have hrest := matchOnFields_isSome (fps := fps) fun fp hfp => h fp (List.mem_cons_of_mem _ hfp)
    simp only [matchOnFields, hv]
    cases hp : p.matchOn v with
    | none => rw [hp] at hm; exact nomatch hm
    | some us =>
      cases hr : matchOnFields fps fields with
      | none => rw [hr] at hrest; exact nomatch hrest
      | some us' => rfl

/-- A record pattern whose listed fields match the columns of a record's
fields matches the record. -/
private theorem record_matches {R R' : Name} {fields : List (Name × Value)}
    {fps : List (Name × Pattern)}
    (hfps : (fps.map Prod.fst).Nodup ∧ ∀ f ∈ fps.map Prod.fst, f ∈ fields.map Prod.fst)
    (hm : RowMatches (fieldColumns (fields.map Prod.fst) fps) (fields.map Prod.snd)) :
    ((Pattern.record R' fps).matchOn (.record R fields)).isSome := by
  simp only [Pattern.matchOn]
  have hcols := columns_match (fun f => (fps.lookup f).getD .wild)
    (by simpa only [fieldColumns, List.map_map] using hm)
  refine matchOnFields_isSome fun fp hfp => ?_
  obtain ⟨v, hv⟩ := lookup_of_mem_map (hfps.2 fp.1 (List.mem_map_of_mem hfp))
  refine ⟨v, hv, ?_⟩
  have h := hcols (fp.1, v) (mem_of_lookup hv)
  simpa [lookup_of_mem_nodup hfps.1 hfp] using h

theorem recordRow_sound (R : Name) (fields : List (Name × Value)) :
    SpecSound (recordRow (fields.map Prod.fst)) (.record R fields) (fields.map Prod.snd)
  | .wild, _, _, _, h, hm | .bind _, _, _, _, h, hm => by
    simp only [recordRow, List.mem_singleton] at h
    subst h
    exact ⟨rfl, wilds_step (by simp) hm⟩
  | .record _ fps, rest, _, vs, h, hm => by
    simp only [recordRow] at h
    split at h
    · rename_i hfps
      simp only [List.mem_singleton] at h
      subst h
      obtain ⟨h₁, h₂⟩ := (rowMatches_append rest vs (by simp [fieldColumns])).1 hm
      exact ⟨record_matches hfps h₁, h₂⟩
    · exact nomatch h
  | .or p q, rest, row, vs, h, hm =>
    or_step rfl (recordRow_sound R fields p rest row vs) (recordRow_sound R fields q rest row vs)
      h hm
  | .int _, _, _, _, h, _ | .bool _, _, _, _, h, _ | .str _, _, _, _, h, _ | .unit, _, _, _, h, _
  | .tuple _, _, _, _, h, _ | .variant _ _ _, _, _, _, h, _ => by
    simp [recordRow] at h

/-- A list pattern whose elements match a list's first elements matches the
list when the list is long enough, and, for an exact rest, no longer. -/
theorem matchOnList_isSome : ∀ (ps : List Pattern) (r : ListRest) (vs : List Value),
    RowMatches ps (vs.take ps.length) → ps.length ≤ vs.length →
      (r = .exact → vs.length = ps.length) → (matchOnList ps r vs).isSome
  | [], .exact, [], _, _, _ | [], .any, _, _, _, _ | [], .bind _, _, _, _, _ => rfl
  | [], .exact, _ :: _, _, _, h => nomatch h rfl
  | _ :: _, _, [], _, h, _ => by simp at h
  | p :: ps, r, v :: vs, hm, hl, he => by
    rw [List.length_cons, List.take_succ_cons, rowMatches_cons] at hm
    have ih := matchOnList_isSome ps r vs hm.2 (by simpa using hl)
      (fun h => by simpa using he h)
    simp only [matchOnList]
    obtain ⟨us, hus⟩ := Option.isSome_iff_exists.1 hm.1
    obtain ⟨us', hus'⟩ := Option.isSome_iff_exists.1 ih
    simp [hus, hus']

/-- A row that starts with a list pattern before a rest, its rest `_`s, matches
the elements and what follows them. -/
private theorem rest_step {ps rest : List Pattern} {ws vs : List Value} {n : Nat}
    (hk : ps.length ≤ ws.length) (hn : ws.length = n)
    (hm : RowMatches (ps ++ List.replicate (n - ps.length) .wild ++ rest) (ws ++ vs)) :
    RowMatches ps (ws.take ps.length) ∧ RowMatches rest vs := by
  rw [← List.take_append_drop ps.length ws, List.append_assoc, List.append_assoc] at hm
  obtain ⟨h₁, h₂⟩ := (rowMatches_append _ _ (by simp; omega)).1 hm
  exact ⟨h₁, wilds_step (by simp; omega) h₂⟩

theorem listRow_sound (vs : List Value) : SpecSound (listRow vs.length false) (.list vs) vs
  | .wild, _, _, _, h, hm | .bind _, _, _, _, h, hm => by
    simp only [listRow, List.mem_singleton] at h
    subst h
    exact ⟨rfl, wilds_step rfl hm⟩
  | .list ps .exact, rest, _, others, h, hm => by
    simp only [listRow] at h
    split at h
    · rename_i hl
      simp only [List.mem_singleton] at h; subst h
      obtain ⟨h₁, h₂⟩ := (rowMatches_append rest others hl.2).1 hm
      refine ⟨matchOnList_isSome ps .exact vs ?_ (by omega) (fun _ => hl.2.symm), h₂⟩
      rwa [hl.2, List.take_length]
    · simp at h
  | .list ps .any, rest, _, others, h, hm | .list ps (.bind _), rest, _, others, h, hm => by
    simp only [listRow] at h
    split at h
    · rename_i hk
      simp only [List.mem_singleton] at h; subst h
      obtain ⟨h₁, h₂⟩ := rest_step hk rfl hm
      exact ⟨matchOnList_isSome ps _ vs h₁ hk (fun h => nomatch h), h₂⟩
    · simp at h
  | .or p q, rest, row, vs', h, hm =>
    or_step rfl (listRow_sound vs p rest row vs') (listRow_sound vs q rest row vs') h hm
  | .int _, _, _, _, h, _ | .bool _, _, _, _, h, _ | .str _, _, _, _, h, _ | .unit, _, _, _, h, _
  | .tuple _, _, _, _, h, _ | .record _ _, _, _, _, h, _ | .variant _ _ _, _, _, _, h, _ => by
    simp [listRow] at h

/-- The rows for lists longer than `m`, over their first `m` elements. -/
theorem listRow_long_sound (m : Nat) (vs : List Value) (hm : m < vs.length) :
    SpecSound (listRow m true) (.list vs) (vs.take m)
  | .wild, _, _, _, h, hr | .bind _, _, _, _, h, hr => by
    simp only [listRow, List.mem_singleton] at h
    subst h
    exact ⟨rfl, wilds_step (by simp; omega) hr⟩
  | .list ps .exact, _, _, _, h, _ => by simp [listRow] at h
  | .list ps .any, rest, _, others, h, hr | .list ps (.bind _), rest, _, others, h, hr => by
    simp only [listRow] at h
    split at h
    · rename_i hk
      simp only [List.mem_singleton] at h; subst h
      obtain ⟨h₁, h₂⟩ := rest_step (ws := vs.take m) (by simp; omega) (by simp; omega) hr
      rw [List.take_take, Nat.min_eq_left hk] at h₁
      exact ⟨matchOnList_isSome ps _ vs h₁ (by omega) (fun h => nomatch h), h₂⟩
    · simp at h
  | .or p q, rest, row, vs', h, hr =>
    or_step rfl (listRow_long_sound m vs hm p rest row vs')
      (listRow_long_sound m vs hm q rest row vs') h hr
  | .int _, _, _, _, h, _ | .bool _, _, _, _, h, _ | .str _, _, _, _, h, _ | .unit, _, _, _, h, _
  | .tuple _, _, _, _, h, _ | .record _ _, _, _, _, h, _ | .variant _ _ _, _, _, _, h, _ => by
    simp [listRow] at h

end Stilt
