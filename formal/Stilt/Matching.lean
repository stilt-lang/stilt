import Stilt.Generics
import Stilt.Values

/-!
# Matching

How a pattern matches a value, and how a `match` picks its arm: the arms are
tried in order and the first whose pattern matches, and whose guard, if it has one, is
true in a way the pattern matches, runs (patterns.match and patterns.guards). A
pattern that matches gives the parts of the value its binders bind, in the
order `Pattern.binders` lists them; each is a copy of the part it matched
(patterns.bindings-are-copies), and values are immutable, so a copy of a part is
the part itself (values.independent-copies).
-/

namespace Stilt

mutual

/-- The parts of `v` that the binders of `p` bind, if `p` matches `v`
(patterns.pattern-forms). A literal matches an equal value, a tuple pattern a
tuple element by element, a record pattern the fields it lists, a variant
pattern the variant it names with its payload matched by position, an
or-pattern what its first alternative matches, else what its second does, and a constant
what its value does, the values structurally equal to it (patterns.constants). -/
def Pattern.matchOn : Pattern → Value → Option (List Value)
  | .wild, _ => some []
  | .bind _, v => some [v]
  | .int n, .int m => if n = m then some [] else none
  | .bool b, .bool c => if b = c then some [] else none
  | .str s, .str t => if s = t then some [] else none
  | .unit, .unit => some []
  | .tuple ps, .record _ fields => matchOnAll ps (fields.map Prod.snd)
  | .record _ fps, .record _ fields => matchOnFields fps fields
  | .variant _ C ps, .variant _ C' vs => if C = C' then matchOnAll ps vs else none
  | .or p q, v =>
    match p.matchOn v with
    | some us => some us
    | none => q.matchOn v
  | .list ps r, .list vs => matchOnList ps r vs
  | .const _ p, v => (p.matchOn v).map fun _ => []
  | _, _ => none

/-- A list pattern's elements matching a list's from its first: with an exact
rest, no element may be left over; with any other, the elements left over are
the rest, which `..rest` binds as a list (patterns.pattern-forms). -/
def matchOnList : List Pattern → ListRest → List Value → Option (List Value)
  | [], .exact, [] => some []
  | [], .exact, _ :: _ => none
  | [], .any, _ => some []
  | [], .bind _, vs => some [.list vs]
  | _ :: _, _, [] => none
  | p :: ps, r, v :: vs =>
    match p.matchOn v, matchOnList ps r vs with
    | some us, some us' => some (us ++ us')
    | _, _ => none

/-- Patterns matching values position by position, the parts each binds in
order. -/
def matchOnAll : List Pattern → List Value → Option (List Value)
  | [], [] => some []
  | p :: ps, v :: vs =>
    match p.matchOn v, matchOnAll ps vs with
    | some us, some us' => some (us ++ us')
    | _, _ => none
  | _, _ => none

/-- The field patterns of a record pattern matching the fields of a record. -/
def matchOnFields : List (Name × Pattern) → List (Name × Value) → Option (List Value)
  | [], _ => some []
  | (f, p) :: fps, fields =>
    match fields.lookup f with
    | some v =>
      match p.matchOn v, matchOnFields fps fields with
      | some us, some us' => some (us ++ us')
      | _, _ => none
    | none => none

end

/-- Every way in which a pattern matches a value, in the order a guard tries them, each as
the parts its binders bind: one for each of its alternatives that matches
(patterns.guards). -/
def Pattern.ways (p : Pattern) (v : Value) : List (List Value) :=
  p.alternatives.filterMap (·.matchOn v)

theorem Pattern.mem_ways {p : Pattern} {v : Value} {us : List Value} (h : us ∈ p.ways v) :
    ∃ q ∈ p.alternatives, q.matchOn v = some us := by
  simpa [Pattern.ways] using h

theorem map_snd_positionsFrom {α : Type} : ∀ (i : Nat) (xs : List α),
    (positionsFrom i xs).map Prod.snd = xs
  | _, [] => rfl
  | i, x :: xs => by simp [positionsFrom, map_snd_positionsFrom (i + 1) xs]

/-! ## Parts of values -/

section

/-- A property of values that passes from records, variants and lists to their
parts, and that a list has when its elements do, so that a list's rest has it. -/
structure Value.PassesToParts (P : Value → Prop) : Prop where
  record : ∀ R fields, P (.record R fields) → ∀ fv ∈ fields, P fv.2
  variant : ∀ T C vs, P (.variant T C vs) → ∀ u ∈ vs, P u
  list : ∀ vs, P (.list vs) ↔ ∀ u ∈ vs, P u

variable {P : Value → Prop}

mutual

/-- A property that passes from records and variants to their parts holds of
every part a pattern binds. -/
theorem Pattern.matchOn_parts (hP : Value.PassesToParts P) : ∀ (p : Pattern) {v : Value} {us : List Value}, P v →
    p.matchOn v = some us → ∀ u ∈ us, P u
  | .wild, _, _, _, h => by simp [Pattern.matchOn] at h; subst h; simp
  | .bind _, _, _, hv, h => by
    simp only [Pattern.matchOn, Option.some.injEq] at h; subst h; simpa using hv
  | .int _, v, _, _, h | .bool _, v, _, _, h | .str _, v, _, _, h | .unit, v, _, _, h => by
    cases v <;> simp only [Pattern.matchOn] at h <;> (try split at h) <;> simp_all
  | .tuple ps, v, _, hv, h => by
    cases v <;> simp only [Pattern.matchOn, reduceCtorEq] at h
    rename_i R fields
    refine matchOnAll_parts hP ps (fun u hu => ?_) h
    obtain ⟨fv, hfv, rfl⟩ := List.mem_map.1 hu
    exact hP.record R fields hv fv hfv
  | .record _ fps, v, _, hv, h => by
    cases v <;> simp only [Pattern.matchOn, reduceCtorEq] at h
    exact matchOnFields_parts hP fps (hP.record _ _ hv) h
  | .variant _ C ps, v, _, hv, h => by
    cases v <;> simp only [Pattern.matchOn, reduceCtorEq] at h
    split at h
    · exact matchOnAll_parts hP ps (hP.variant _ _ _ hv) h
    · exact nomatch h
  | .or p q, v, _, hv, h => by
    simp only [Pattern.matchOn] at h
    split at h
    · rename_i us' h'
      cases h
      exact Pattern.matchOn_parts hP p hv h'
    · exact Pattern.matchOn_parts hP q hv h
  | .list ps r, v, _, hv, h => by
    cases v <;> simp only [Pattern.matchOn, reduceCtorEq] at h
    exact matchOnList_parts hP ps r ((hP.list _).1 hv) h
  | .const _ _, _, _, _, h => by
    simp only [Pattern.matchOn, Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    simp

theorem matchOnAll_parts (hP : Value.PassesToParts P) : ∀ (ps : List Pattern) {vs : List Value} {us : List Value},
    (∀ v ∈ vs, P v) → matchOnAll ps vs = some us → ∀ u ∈ us, P u
  | [], [], _, _, h => by simp [matchOnAll] at h; subst h; simp
  | p :: ps, v :: vs, us, hv, h => by
    simp only [matchOnAll] at h
    split at h
    · rename_i a b ha hb
      cases h
      intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · exact Pattern.matchOn_parts hP p (hv v List.mem_cons_self) ha u hu
      · exact matchOnAll_parts hP ps (fun w hw => hv w (List.mem_cons_of_mem _ hw)) hb u hu
    · exact nomatch h
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp [matchOnAll] at h

theorem matchOnFields_parts (hP : Value.PassesToParts P) : ∀ (fps : List (Name × Pattern)) {fields : List (Name × Value)}
    {us : List Value}, (∀ fv ∈ fields, P fv.2) → matchOnFields fps fields = some us →
      ∀ u ∈ us, P u
  | [], _, _, _, h => by simp [matchOnFields] at h; subst h; simp
  | (f, p) :: fps, fields, us, hf, h => by
    simp only [matchOnFields] at h
    split at h
    · rename_i v hl
      split at h
      · rename_i a b ha hb
        cases h
        intro u hu
        rcases List.mem_append.1 hu with hu | hu
        · exact Pattern.matchOn_parts hP p (hf (f, v) (mem_of_lookup hl)) ha u hu
        · exact matchOnFields_parts hP fps hf hb u hu
      · exact nomatch h
    · exact nomatch h

theorem matchOnList_parts (hP : Value.PassesToParts P) : ∀ (ps : List Pattern) (r : ListRest)
    {vs : List Value} {us : List Value}, (∀ v ∈ vs, P v) → matchOnList ps r vs = some us →
      ∀ u ∈ us, P u
  | [], .exact, [], _, _, h | [], .any, _, _, _, h => by
    simp [matchOnList] at h; subst h; simp
  | [], .exact, _ :: _, _, _, h | _ :: _, _, [], _, _, h => by simp [matchOnList] at h
  | [], .bind _, vs, _, hv, h => by
    simp only [matchOnList, Option.some.injEq] at h; subst h
    simpa using (hP.list vs).2 hv
  | p :: ps, r, v :: vs, us, hv, h => by
    simp only [matchOnList] at h
    split at h
    · rename_i a b ha hb
      cases h
      intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · exact Pattern.matchOn_parts hP p (hv v List.mem_cons_self) ha u hu
      · exact matchOnList_parts hP ps r (fun w hw => hv w (List.mem_cons_of_mem _ hw)) hb u hu
    · exact nomatch h

end

end

end Stilt
