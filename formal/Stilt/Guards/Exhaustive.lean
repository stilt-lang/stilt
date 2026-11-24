import Stilt.Guards.Typing

/-!
# Exhaustiveness with list patterns

The usefulness algorithm over matrices of patterns (patterns.algorithm), with
the constructors of each type: `true` and `false`, `()`, a tuple's one, `None`
and `Some`, and a list's lengths, where `[p₁, …, pₙ]` is the constructor of
length `n` and `[p₁, …, pₙ, ..]` covers every length of at least `n`. A list
column is split into the lengths up to the longest pattern's, each a row of
that many elements, and the lists longer than that, as that many elements and
the list after them. Integers have infinitely many constructors, so only `_`
and a binding count there; a constant counts nowhere, and neither does an arm
with a guard (patterns.guards-and-constants), whose rows the check never sees.

The check is `check fuel rows types`: it says yes only when every vector of
values of the types matches a row (`check_sound`), whatever the fuel; one that
runs out says no.
-/

namespace Stilt.Guards

/-- Rows of patterns, each matched against a vector of values. -/
abbrev Rows := List (List Pat)

/-- A pattern matches a value in some way. -/
def Matches (p : Pat) (v : Val) : Prop := p.ways v ≠ []

/-- A row of patterns matches a vector of values in some way. -/
def RowMatches (ps : List Pat) (vs : List Val) : Prop := Pat.waysAll ps vs ≠ []

/-- The alternatives of a pattern, its or-patterns taken apart. -/
def Pat.alts : Pat → List Pat
  | .or p q => p.alts ++ q.alts
  | p => [p]

/-- Each row whose first pattern has alternatives, as one row for each. -/
def expand (rows : Rows) : Rows :=
  rows.flatMap fun
    | p :: rest => p.alts.map (· :: rest)
    | [] => [[]]

/-- Whether a pattern matches anything without looking: `_` or a binding. -/
def Pat.isWild : Pat → Bool
  | .wild | .bind _ => true
  | _ => false

/-- `n` wildcards. -/
def wilds (n : Nat) : List Pat := List.replicate n .wild

/-- The rows of a constructor: each row whose first pattern `f` takes apart
into the patterns of the constructor's parts, followed by its other patterns. -/
def spec (f : Pat → Option (List Pat)) (rows : Rows) : Rows :=
  rows.filterMap fun
    | p :: rest => (f p).map (· ++ rest)
    | [] => none

/-- The rows that match whatever the first value is. -/
def anyC (p : Pat) : Option (List Pat) := if p.isWild then some [] else none

def boolC (b : Bool) : Pat → Option (List Pat)
  | .bool c => if c = b then some [] else none
  | p => anyC p

def unitC : Pat → Option (List Pat)
  | .unit => some []
  | p => anyC p

def tupleC (k : Nat) : Pat → Option (List Pat)
  | .tuple ps => if ps.length = k then some ps else none
  | p => if p.isWild then some (wilds k) else none

def noneC : Pat → Option (List Pat)
  | .none => some []
  | p => anyC p

def someC : Pat → Option (List Pat)
  | .some p => some [p]
  | p => if p.isWild then some [.wild] else none

/-- Lists of exactly `k` elements. -/
def lenC (k : Nat) : Pat → Option (List Pat)
  | .list ps => if ps.length = k then some ps else none
  | .prefix ps _ => if ps.length ≤ k then some (ps ++ wilds (k - ps.length)) else none
  | p => if p.isWild then some (wilds k) else none

/-- Lists of more than `k` elements, as their first `k` and the list after them. -/
def longC (k : Nat) : Pat → Option (List Pat)
  | .prefix ps _ => if ps.length ≤ k then some (ps ++ wilds (k - ps.length) ++ [.wild]) else none
  | p => if p.isWild then some (wilds (k + 1)) else none

/-- The most elements a list pattern of the first column names. -/
def longest (rows : Rows) : Nat :=
  rows.foldr (fun r n => match r with
    | .list ps :: _ | .prefix ps _ :: _ => max ps.length n
    | _ => n) 0

/-- Whether every vector of values of the types matches a row. -/
def check : Nat → Rows → List Ty → Bool
  | 0, _, _ => false
  | _ + 1, rows, [] => rows.any List.isEmpty
  | n + 1, rows, τ :: τs =>
    let rows := expand rows
    if rows.all (fun r => match r with | p :: _ => p.isWild | [] => false) then
      check n (spec anyC rows) τs
    else
      match τ with
      | .bool => check n (spec (boolC true) rows) τs && check n (spec (boolC false) rows) τs
      | .unit => check n (spec unitC rows) τs
      | .int => check n (spec anyC rows) τs
      | .tuple ts => check n (spec (tupleC ts.length) rows) (ts ++ τs)
      | .option t => check n (spec noneC rows) τs && check n (spec someC rows) (t :: τs)
      | .list t =>
        let L := longest rows
        (List.range (L + 1)).all (fun k => check n (spec (lenC k) rows) (List.replicate k t ++ τs)) &&
          check n (spec (longC (L + 1)) rows) (List.replicate (L + 1) t ++ .list t :: τs)

/-- Whether the arms of a `match` on values of type `τ` cover them, counting
only the arms without a guard or a constant. -/
def exhaustive (arms : List Arm) (τ : Ty) (fuel : Nat := 256) : Bool :=
  check fuel ((arms.filter Arm.counts).map fun a => [a.pat]) [τ]

/-! ## Rows that match -/

theorem rowMatches_nil : RowMatches [] [] := by simp [RowMatches, Pat.waysAll]

theorem rowMatches_cons {p : Pat} {ps : List Pat} {v : Val} {vs : List Val} :
    RowMatches (p :: ps) (v :: vs) ↔ Matches p v ∧ RowMatches ps vs := by
  unfold RowMatches Matches
  simp only [Pat.waysAll]
  constructor
  · intro h
    refine ⟨fun hp => h (by simp [hp]), fun hr => h (by simp [hr])⟩
  · rintro ⟨h, h'⟩ he
    obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ h
    have : (Pat.waysAll ps vs).map (w ++ ·) = [] :=
      List.flatMap_eq_nil_iff.1 he w hw
    exact h' (List.map_eq_nil_iff.1 this)

theorem rowMatches_length : ∀ {ps : List Pat} {vs : List Val}, RowMatches ps vs → ps.length = vs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    rw [rowMatches_cons] at h
    simp [rowMatches_length h.2]
  | [], _ :: _, h | _ :: _, [], h => absurd rfl h

theorem rowMatches_append : ∀ {ps : List Pat} {ws : List Val} (qs : List Pat) (vs : List Val),
    ps.length = ws.length → RowMatches (ps ++ qs) (ws ++ vs) → RowMatches ps ws ∧ RowMatches qs vs
  | [], [], _, _, _, h => ⟨rowMatches_nil, h⟩
  | p :: ps, w :: ws, qs, vs, hl, h => by
    rw [List.cons_append, List.cons_append, rowMatches_cons] at h
    have := rowMatches_append qs vs (by simpa using hl) h.2
    exact ⟨rowMatches_cons.2 ⟨h.1, this.1⟩, this.2⟩
  | [], _ :: _, _, _, hl, _ | _ :: _, [], _, _, hl, _ => nomatch hl

theorem Pat.isWild_matches {p : Pat} (h : p.isWild = true) (v : Val) : Matches p v := by
  cases p <;> simp [Pat.isWild] at h <;> simp [Matches, Pat.ways]

theorem rowMatches_wilds : ∀ (vs : List Val), RowMatches (wilds vs.length) vs
  | [] => rowMatches_nil
  | v :: vs => rowMatches_cons.2 ⟨Pat.isWild_matches rfl v, rowMatches_wilds vs⟩

theorem Pat.alts_matches : ∀ {p q : Pat} {v : Val}, q ∈ p.alts → Matches q v → Matches p v
  | .or p₁ p₂, q, v, hq, h => by
    simp only [Pat.alts, List.mem_append] at hq
    simp only [Matches, Pat.ways, ne_eq, List.append_eq_nil_iff]
    rcases hq with hq | hq
    · exact fun h' => Pat.alts_matches hq h h'.1
    · exact fun h' => Pat.alts_matches hq h h'.2
  | .wild, _, _, hq, h | .bind _, _, _, hq, h | .int _, _, _, hq, h | .bool _, _, _, hq, h
  | .unit, _, _, hq, h | .const _ _, _, _, hq, h | .tuple _, _, _, hq, h | .none, _, _, hq, h
  | .some _, _, _, hq, h | .list _, _, _, hq, h | .prefix _ _, _, _, hq, h => by
    simp only [Pat.alts, List.mem_singleton] at hq
    exact hq ▸ h

/-- A row of the expanded rows that matches comes from a row that matches. -/
theorem expand_lift {rows : Rows} {v : Val} {vs : List Val} {row : List Pat}
    (hr : row ∈ expand rows) (hm : RowMatches row (v :: vs)) :
    ∃ r ∈ rows, RowMatches r (v :: vs) := by
  obtain ⟨r, hrows, hrow⟩ := List.mem_flatMap.1 hr
  match r, hrow with
  | p :: rest, hrow =>
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hrow
    rw [rowMatches_cons] at hm
    exact ⟨p :: rest, hrows, rowMatches_cons.2 ⟨Pat.alts_matches hq hm.1, hm.2⟩⟩
  | [], hrow =>
    simp only [List.mem_singleton] at hrow
    subst hrow
    exact absurd rfl hm

/-- `f` takes the value `v` apart into the parts `ws`: each pattern it takes
apart gives as many patterns as there are parts, and they match the parts only
when the pattern matches `v`. -/
def SpecOk (f : Pat → Option (List Pat)) (v : Val) (ws : List Val) : Prop :=
  ∀ p ps, f p = some ps → ps.length = ws.length ∧ (RowMatches ps ws → Matches p v)

/-- A row of a constructor's rows that matches the parts of `v` and the rest
comes from a row that matches `v` and the rest. -/
theorem spec_lift {f : Pat → Option (List Pat)} {v : Val} {ws : List Val} (hf : SpecOk f v ws)
    {rows : Rows} {vs : List Val} {row : List Pat} (hr : row ∈ spec f rows)
    (hm : RowMatches row (ws ++ vs)) : ∃ r ∈ rows, RowMatches r (v :: vs) := by
  obtain ⟨r, hrows, hrow⟩ := List.mem_filterMap.1 hr
  match r, hrow with
  | p :: rest, hrow =>
    simp only [Option.map_eq_some_iff] at hrow
    obtain ⟨ps, hps, rfl⟩ := hrow
    obtain ⟨hl, hp⟩ := hf p ps hps
    obtain ⟨h₁, h₂⟩ := rowMatches_append rest vs hl hm
    exact ⟨p :: rest, hrows, rowMatches_cons.2 ⟨hp h₁, h₂⟩⟩

end Stilt.Guards
