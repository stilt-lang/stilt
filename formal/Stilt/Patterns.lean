import Stilt.Inhabited

/-!
# Patterns

The typing of patterns, and the exhaustiveness of a `match`'s arms.

`PatFits D p τ σs` checks a pattern against the type of the value it matches
(patterns.pattern-types): `σs` are the types of the names it binds, in the
order `Pattern.binders` lists them, each immutable (patterns.var-bindings).

`Exhaustive D P τs` is a derivation of Maranget's usefulness algorithm, which
patterns.algorithm names, showing that the rows of patterns `P` leave no vector
of values of the types `τs` unmatched. Each rule takes the first column apart:
a type whose constructors are all known (variant types, `bool`, `()`, tuples,
records and lists by their lengths) is covered when each constructor's
specialized matrix is, any type when the rows that start with a pattern that
matches anything are, and a type without values needs no row
(patterns.types-without-values), so neither does a constructor whose payload
has a type without values. The rules are the
algorithm's steps; the model proves that every derivation covers every value
(`Exhaustive.sound`), not that the algorithm finds one for every exhaustive
`match`.
-/

namespace Stilt

section

variable (D : Decls)

mutual

/-- A pattern fits the type of the value it matches, and binds names of the
types `σs` (patterns.pattern-types). An integer literal fits an integer type
that holds it, and no literal fits a float (patterns.floats); the alternatives
of an or-pattern bind the same names with the same types (patterns.or-patterns). -/
inductive PatFits : Pattern → Ty → List Ty → Prop
  | wild {τ : Ty} : PatFits .wild τ []
  | bind {x : Name} {τ : Ty} : PatFits (.bind x) τ [τ]
  | int {k : IntTy} {n : Int} : k.Contains n → PatFits (.int n) (.int k) []
  | bool {b : Bool} : PatFits (.bool b) .bool []
  | str {s : String} : PatFits (.str s) .str []
  | unit : PatFits .unit .unit []
  | tuple {ps : List Pattern} {τs σs : List Ty} :
      PatsFit ps τs σs → PatFits (.tuple ps) (.tuple τs) σs
  /-- A record pattern lists each field once, each a field of the record, at the
  scrutinee's type arguments. -/
  | record {R : Name} {args : List Ty} {r : RecordDecl} {fps : List (Name × Pattern)}
      {σs : List Ty} :
      D.record? R = some r → args.length = r.typeParams.length → (fps.map Prod.fst).Nodup →
      FieldPatsFit (r.fieldsAt args) fps σs → PatFits (.record R fps) (.record R args) σs
  /-- A variant pattern gives one pattern for each payload field, at the scrutinee's
  type arguments. -/
  | variant {T : Name} {args : List Ty} {t : VariantDecl} {C : Name} {τs : List Ty}
      {ps : List Pattern} {σs : List Ty} :
      D.variant? T = some t → args.length = t.typeParams.length →
      (t.ctorsAt args).lookup C = some τs → PatsFit ps τs σs →
      PatFits (.variant T C ps) (.variant T args) σs
  | or {p q : Pattern} {τ : Ty} {σs : List Ty} :
      PatFits p τ σs → PatFits q τ σs → q.binders = p.binders → PatFits (.or p q) τ σs
  /-- A list pattern's elements each fit the list's element type, and its rest,
  when it binds a name, binds a list of them (patterns.pattern-forms). -/
  | list {ps : List Pattern} {r : ListRest} {τ : Ty} {σs : List Ty} :
      PatsFit ps (List.replicate ps.length τ) σs →
      PatFits (.list ps r) (.list τ) (σs ++ r.binders.map fun _ => .list τ)
  /-- A constant fits the type it is declared with, and its value is its declaration's,
  the pattern of literals that matches the values equal to it (patterns.constants and
  declarations.constants-in-patterns). A constant whose type can hold a float has no such
  pattern (patterns.floats). -/
  | const {C : Name} {c : ConstDecl} {v : Pattern} {τ : Ty} :
      D.const? C = some c → c.type = τ → D.constPattern C = some v → PatFits v τ [] →
      PatFits (.const C v) τ []

/-- Patterns fit types position by position. -/
inductive PatsFit : List Pattern → List Ty → List Ty → Prop
  | nil : PatsFit [] [] []
  | cons {p : Pattern} {ps : List Pattern} {τ : Ty} {τs σs σs' : List Ty} :
      PatFits p τ σs → PatsFit ps τs σs' → PatsFit (p :: ps) (τ :: τs) (σs ++ σs')

/-- The field patterns of a record pattern fit the types the record declares
for their fields. -/
inductive FieldPatsFit : List (Name × Ty) → List (Name × Pattern) → List Ty → Prop
  | nil {declared : List (Name × Ty)} : FieldPatsFit declared [] []
  | cons {declared : List (Name × Ty)} {f : Name} {p : Pattern} {fps : List (Name × Pattern)}
      {τ : Ty} {σs σs' : List Ty} :
      declared.lookup f = some τ → PatFits p τ σs → FieldPatsFit declared fps σs' →
      FieldPatsFit declared ((f, p) :: fps) (σs ++ σs')

end

end

/-! ## Specialized matrices -/

/-- The rows of a pattern matrix, one pattern for each column. -/
abbrev Rows := List (List Pattern)

/-- How the rows that start with a pattern become the rows of a specialized
matrix, as a function of the first pattern and the rest of the row. -/
abbrev Spec := Pattern → List Pattern → Rows

/-- The matrix that one step of the algorithm checks next: each row taken
apart by `f`. -/
def specialize (f : Spec) (P : Rows) : Rows :=
  P.flatMap fun
    | p :: rest => f p rest
    | [] => []

/-- The default matrix: the rows whose first pattern matches anything, without
it. -/
def defaultRow : Spec
  | .wild, rest | .bind _, rest => [rest]
  | .or p q, rest => defaultRow p rest ++ defaultRow q rest
  | _, _ => []

/-- The rows that match the Boolean `b`. -/
def boolRow (b : Bool) : Spec
  | .wild, rest | .bind _, rest => [rest]
  | .bool c, rest => if c = b then [rest] else []
  | .or p q, rest => boolRow b p rest ++ boolRow b q rest
  | _, _ => []

/-- The rows that match `()`. -/
def unitRow : Spec
  | .wild, rest | .bind _, rest | .unit, rest => [rest]
  | .or p q, rest => unitRow p rest ++ unitRow q rest
  | _, _ => []

/-- The rows that match a tuple of `n` elements, its elements as new columns. -/
def tupleRow (n : Nat) : Spec
  | .wild, rest | .bind _, rest => [List.replicate n .wild ++ rest]
  | .tuple ps, rest => if ps.length = n then [ps ++ rest] else []
  | .or p q, rest => tupleRow n p rest ++ tupleRow n q rest
  | _, _ => []

/-- The pattern for each of the fields `names`, in their order, that a record
pattern gives, `_` for those it leaves to `..`. -/
def fieldColumns (names : List Name) (fps : List (Name × Pattern)) : List Pattern :=
  names.map fun f => (fps.lookup f).getD .wild

/-- The rows that match a record whose fields are `names`, its fields as new
columns. -/
def recordRow (names : List Name) : Spec
  | .wild, rest | .bind _, rest => [List.replicate names.length .wild ++ rest]
  | .record _ fps, rest =>
    if (fps.map Prod.fst).Nodup ∧ ∀ f ∈ fps.map Prod.fst, f ∈ names then
      [fieldColumns names fps ++ rest]
    else []
  | .or p q, rest => recordRow names p rest ++ recordRow names q rest
  | _, _ => []

/-- The rows that match the variant `C` with `n` payload fields, its payload as
new columns. -/
def variantRow (C : Name) (n : Nat) : Spec
  | .wild, rest | .bind _, rest => [List.replicate n .wild ++ rest]
  | .variant _ C' ps, rest => if C' = C ∧ ps.length = n then [ps ++ rest] else []
  | .or p q, rest => variantRow C n p rest ++ variantRow C n q rest
  | _, _ => []

/-- The rows that match a list of `n` elements, its elements as new columns: a
list pattern of `n` elements, or of at most `n` before a rest, its rest `_`s.
With `long`, the rows that match every list longer than `n`, its first `n`
elements as new columns, which only patterns with a rest do. -/
def listRow (n : Nat) (long : Bool) : Spec
  | .wild, rest | .bind _, rest => [List.replicate n .wild ++ rest]
  | .list ps .exact, rest => if ¬long ∧ ps.length = n then [ps ++ rest] else []
  | .list ps _, rest =>
    if ps.length ≤ n then [ps ++ List.replicate (n - ps.length) .wild ++ rest] else []
  | .or p q, rest => listRow n long p rest ++ listRow n long q rest
  | _, _ => []

/-- The rows `P` cover every vector of values of the types `τs`: a derivation
of the usefulness algorithm (patterns.algorithm). -/
inductive Exhaustive (D : Decls) : Rows → List Ty → Prop
  /-- With no column left, a row matches. -/
  | done {P : Rows} : [] ∈ P → Exhaustive D P []
  /-- A type without values, as `Never` and `(i64, Never)`, needs no row
  (patterns.types-without-values). -/
  | empty {P : Rows} {τ : Ty} {τs : List Ty} : ¬ Ty.Inhabited D τ → Exhaustive D P (τ :: τs)
  /-- Integers, strings, floats, lists and the other types whose constructors
  aren't listed are covered by the rows whose first pattern matches anything. -/
  | default {P : Rows} {τ : Ty} {τs : List Ty} :
      Exhaustive D (specialize defaultRow P) τs → Exhaustive D P (τ :: τs)
  | bool {P : Rows} {τs : List Ty} :
      Exhaustive D (specialize (boolRow true) P) τs → Exhaustive D (specialize (boolRow false) P) τs →
      Exhaustive D P (.bool :: τs)
  | unit {P : Rows} {τs : List Ty} :
      Exhaustive D (specialize unitRow P) τs → Exhaustive D P (.unit :: τs)
  | tuple {P : Rows} {σs τs : List Ty} :
      Exhaustive D (specialize (tupleRow σs.length) P) (σs ++ τs) → Exhaustive D P (.tuple σs :: τs)
  | record {P : Rows} {R : Name} {args : List Ty} {r : RecordDecl} {τs : List Ty} :
      D.record? R = some r → args.length = r.typeParams.length →
      Exhaustive D (specialize (recordRow (r.fields.map Prod.fst)) P)
        ((r.fieldsAt args).map Prod.snd ++ τs) →
      Exhaustive D P (.record R args :: τs)
  | variant {P : Rows} {T : Name} {args : List Ty} {t : VariantDecl} {τs : List Ty} :
      D.variant? T = some t → args.length = t.typeParams.length →
      (∀ c ∈ t.ctorsAt args,
        Exhaustive D (specialize (variantRow c.1 c.2.length) P) (c.2 ++ τs)) →
      Exhaustive D P (.variant T args :: τs)
  /-- A list's constructors are its lengths: each length up to `m` is covered by
  the rows of that length, and every longer one by the rows whose rest allows
  it (patterns.algorithm). -/
  | list {P : Rows} {τ : Ty} {τs : List Ty} (m : Nat) :
      (∀ n ≤ m, Exhaustive D (specialize (listRow n false) P) (List.replicate n τ ++ τs)) →
      Exhaustive D (specialize (listRow m true) P) (List.replicate m τ ++ τs) →
      Exhaustive D P (.list τ :: τs)

/-- The rows of a `match`'s arms: one column, the pattern of each arm that counts. An arm
with a guard, or whose pattern holds a constant, covers nothing (patterns.guards-and-constants). -/
def armRows (arms : List Arm) : Rows := (arms.filter Arm.counts).map fun a => [a.pattern]

/-! ## Lemmas -/

section

variable {D : Decls}

theorem patternsBinders_append : ∀ (ps qs : List Pattern),
    patternsBinders (ps ++ qs) = patternsBinders ps ++ patternsBinders qs
  | [], _ => rfl
  | p :: ps, qs => by simp [patternsBinders, patternsBinders_append ps qs]

mutual

/-- A pattern binds one name for each type its typing gives. -/
theorem PatFits.length : ∀ {p : Pattern} {τ : Ty} {σs : List Ty}, PatFits D p τ σs →
    p.binders.length = σs.length
  | _, _, _, .wild | _, _, _, .bind | _, _, _, .int _ | _, _, _, .bool | _, _, _, .str
  | _, _, _, .unit | _, _, _, .const .. => rfl
  | _, _, _, .tuple h | _, _, _, .variant _ _ _ h => PatsFit.length h
  | _, _, _, .record _ _ _ h => FieldPatsFit.length h
  | _, _, _, .or h _ _ => by rw [Pattern.binders]; exact PatFits.length h
  | _, _, _, .list h => by simp [Pattern.binders, PatsFit.length h]

theorem PatsFit.length : ∀ {ps : List Pattern} {τs σs : List Ty}, PatsFit D ps τs σs →
    (patternsBinders ps).length = σs.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons h hs => by simp [patternsBinders, PatFits.length h, PatsFit.length hs]

theorem FieldPatsFit.length : ∀ {declared : List (Name × Ty)} {fps : List (Name × Pattern)}
    {σs : List Ty}, FieldPatsFit D declared fps σs → (fieldPatternsBinders fps).length = σs.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ h hs => by
    simp [fieldPatternsBinders, PatFits.length h, FieldPatsFit.length hs]

end

end

/-! ## Alternatives -/

section

variable {D : Decls}

theorem PatsFit.types_length : ∀ {ps : List Pattern} {τs σs : List Ty}, PatsFit D ps τs σs →
    ps.length = τs.length
  | _, _, _, .nil => rfl
  | _, _, _, .cons _ hs => by simp [PatsFit.types_length hs]

theorem patternsBinders_eq_flatMap : ∀ ps : List Pattern,
    patternsBinders ps = ps.flatMap Pattern.binders
  | [] => rfl
  | p :: ps => by simp [patternsBinders, patternsBinders_eq_flatMap ps]

mutual

/-- Each alternative of a pattern fits its type as the pattern does, and binds its names
(patterns.or-patterns). -/
theorem PatFits.alternative : ∀ {p : Pattern} {τ : Ty} {σs : List Ty}, PatFits D p τ σs →
    ∀ q ∈ p.alternatives, PatFits D q τ σs ∧ q.binders = p.binders
  | _, _, _, h@(.wild), q, hq | _, _, _, h@(.bind), q, hq | _, _, _, h@(.int _), q, hq
  | _, _, _, h@(.bool), q, hq | _, _, _, h@(.str), q, hq | _, _, _, h@(.unit), q, hq
  | _, _, _, h@(.const ..), q, hq => by
    simp only [Pattern.alternatives, List.mem_singleton] at hq
    subst hq; exact ⟨h, rfl⟩
  | _, _, _, .tuple h, q, hq => by
    simp only [Pattern.alternatives, List.mem_map] at hq
    obtain ⟨qs, hqs, rfl⟩ := hq
    obtain ⟨h', hb⟩ := PatsFit.alternative h qs hqs
    exact ⟨.tuple h', by simp [Pattern.binders, hb]⟩
  | _, _, _, .record hr hargs hnd h, q, hq => by
    simp only [Pattern.alternatives, List.mem_map] at hq
    obtain ⟨qs, hqs, rfl⟩ := hq
    obtain ⟨h', hb, hn⟩ := FieldPatsFit.alternative h qs hqs
    exact ⟨.record hr hargs (hn ▸ hnd) h', by simp [Pattern.binders, hb]⟩
  | _, _, _, .variant ht hargs hc h, q, hq => by
    simp only [Pattern.alternatives, List.mem_map] at hq
    obtain ⟨qs, hqs, rfl⟩ := hq
    obtain ⟨h', hb⟩ := PatsFit.alternative h qs hqs
    exact ⟨.variant ht hargs hc h', by simp [Pattern.binders, hb]⟩
  | _, _, _, .or hp hq' hb, q, hq => by
    simp only [Pattern.alternatives, List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨h', hb'⟩ := PatFits.alternative hp q hq
      exact ⟨h', by simp [Pattern.binders, hb']⟩
    · obtain ⟨h', hb'⟩ := PatFits.alternative hq' q hq
      exact ⟨h', by simp [Pattern.binders, hb', hb]⟩
  | _, _, _, .list (ps := ps) (r := r) h, q, hq => by
    simp only [Pattern.alternatives, List.mem_map] at hq
    obtain ⟨qs, hqs, rfl⟩ := hq
    obtain ⟨h', hb⟩ := PatsFit.alternative h qs hqs
    have hl : qs.length = ps.length := by simpa using PatsFit.types_length h'
    refine ⟨?_, by simp [Pattern.binders, hb]⟩
    rw [← hl] at h'
    exact .list h'

theorem PatsFit.alternative : ∀ {ps : List Pattern} {τs σs : List Ty}, PatsFit D ps τs σs →
    ∀ qs ∈ patternsAlternatives ps, PatsFit D qs τs σs ∧ patternsBinders qs = patternsBinders ps
  | _, _, _, .nil, qs, hqs => by
    simp only [patternsAlternatives, List.mem_singleton] at hqs
    subst hqs; exact ⟨.nil, rfl⟩
  | _, _, _, .cons h hs, qs, hqs => by
    simp only [patternsAlternatives, List.mem_flatMap, List.mem_map] at hqs
    obtain ⟨q, hq, qs', hqs', rfl⟩ := hqs
    obtain ⟨h', hb⟩ := PatFits.alternative h q hq
    obtain ⟨hs', hbs⟩ := PatsFit.alternative hs qs' hqs'
    exact ⟨.cons h' hs', by simp [patternsBinders, hb, hbs]⟩

theorem FieldPatsFit.alternative : ∀ {declared : List (Name × Ty)} {fps : List (Name × Pattern)}
    {σs : List Ty}, FieldPatsFit D declared fps σs →
    ∀ qs ∈ fieldPatternsAlternatives fps, FieldPatsFit D declared qs σs ∧
      fieldPatternsBinders qs = fieldPatternsBinders fps ∧ qs.map Prod.fst = fps.map Prod.fst
  | _, _, _, .nil, qs, hqs => by
    simp only [fieldPatternsAlternatives, List.mem_singleton] at hqs
    subst hqs; exact ⟨.nil, rfl, rfl⟩
  | _, _, _, .cons hl h hs, qs, hqs => by
    simp only [fieldPatternsAlternatives, List.mem_flatMap, List.mem_map] at hqs
    obtain ⟨q, hq, qs', hqs', rfl⟩ := hqs
    obtain ⟨h', hb⟩ := PatFits.alternative h q hq
    obtain ⟨hs', hbs, hn⟩ := FieldPatsFit.alternative hs qs' hqs'
    exact ⟨.cons hl h' hs', by simp [fieldPatternsBinders, hb, hbs], by simp [hn]⟩

end

end

end Stilt
