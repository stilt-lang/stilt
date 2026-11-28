import Stilt.Memory

/-!
# Difference facts

The domain of the analysis of a body's integer values: terms, the difference facts between
them, and which of them are non-zero, as `Stilt.Analysis` states them. A fact set holds of a
valuation, which gives each term an integer (`Facts.Holds`); every operation on fact sets here,
closing a set, joining two, restricting one to some terms, keeps what holds, and a set that
`Facts.entails` holds whenever the first does. What a term's value is in a frame of the
calculus is `Stilt.Analysis.Frames`'s.
-/

namespace Stilt

/-- A term of the analysis (facts.terms): zero, the value of an integer binding, the length
of a list binding, a value that the evaluation has read and not yet used (the `i`th of those
pending) with its length when it is a list, and the value an expression gives, with its length.
A term stands for the value that a binding holds where the facts are, so a binding's current
term is its name, and a new one replaces the old wherever the binding changes. -/
inductive Term where
  | zero
  | res
  | reslen
  | opnd (i : Nat)
  | opndLen (i : Nat)
  | val (x : Name)
  | len (xs : Name)
  deriving DecidableEq, Repr

/-- An integer for each term. -/
abbrev Valuation := Term → Int

/-- A difference fact `t − u ≤ c` (facts.difference-facts). -/
structure Diff where
  t : Term
  u : Term
  c : Int
  deriving DecidableEq, Repr

/-- A set of difference facts, and the terms known non-zero (facts.difference-facts). -/
structure Facts where
  diffs : List Diff := []
  nonzero : List Term := []
  deriving DecidableEq, Repr

/-- A difference fact holds of a valuation. -/
def Diff.Holds (ν : Valuation) (d : Diff) : Prop := ν d.t - ν d.u ≤ d.c

/-- Every fact of a set holds of a valuation. -/
def Facts.Holds (F : Facts) (ν : Valuation) : Prop :=
  (∀ d ∈ F.diffs, d.Holds ν) ∧ ∀ t ∈ F.nonzero, ν t ≠ 0

namespace Facts

/-- No fact. -/
def top : Facts := {}

/-- A contradictory set, which no valuation meets: a point never reached. -/
def bot : Facts := { diffs := [⟨.zero, .zero, -1⟩] }

/-- Whether some `t − t ≤ c` has `c < 0`: the set is contradictory (facts.difference-facts). -/
def contra (F : Facts) : Bool := F.diffs.any fun d => d.t == d.u && decide (d.c < 0)

/-- The least `c` of the facts `t − u ≤ c`, or `0` when `t` is `u`. -/
def bound (F : Facts) (t u : Term) : Option Int :=
  if t = u then some 0 else
    F.diffs.foldl (fun acc d =>
      if d.t = t ∧ d.u = u then some (match acc with | some a => min a d.c | none => d.c) else acc)
      none

/-- The fact `d` added, the smaller `c` holding of two on one pair. -/
def insert (F : Facts) (d : Diff) : Facts :=
  match F.bound d.t d.u with
  | some c => if c ≤ d.c then F else
      { F with diffs := d :: F.diffs.filter fun e => !(e.t = d.t ∧ e.u = d.u) }
  | none => { F with diffs := d :: F.diffs }

/-- The facts of a list added. -/
def insertAll (F : Facts) (ds : List Diff) : Facts := ds.foldl insert F

/-- `t` known non-zero. -/
def addNonzero (F : Facts) (t : Term) : Facts :=
  if t ∈ F.nonzero then F else { F with nonzero := t :: F.nonzero }

/-- The facts of both sets. -/
def meet (F G : Facts) : Facts :=
  G.nonzero.foldl addNonzero (F.insertAll G.diffs)

/-- The facts on the terms that `keep` holds of, every other term dropped. -/
def restrict (F : Facts) (keep : Term → Bool) : Facts :=
  { diffs := F.diffs.filter fun d => keep d.t && keep d.u, nonzero := F.nonzero.filter keep }

/-- Every term renamed by `f`. -/
def map (F : Facts) (f : Term → Term) : Facts :=
  { diffs := F.diffs.map fun d => ⟨f d.t, f d.u, d.c⟩, nonzero := F.nonzero.map f }

/-- The terms the facts name. -/
def terms (F : Facts) : List Term :=
  (F.diffs.flatMap fun d => [d.t, d.u]) ++ F.nonzero

/-- The facts through `k`: `t − v ≤ c + d` from `t − k ≤ c` and `k − v ≤ d`. -/
def through (F : Facts) (k : Term) : List Diff :=
  F.diffs.flatMap fun d₁ => if d₁.u = k then
    (F.diffs.filter fun d₂ => d₂.t = k).map fun d₂ => ⟨d₁.t, d₂.u, d₁.c + d₂.c⟩ else []

/-- One step of closing through `k` (facts.difference-facts). -/
def closeVia (F : Facts) (k : Term) : Facts := F.insertAll (F.through k)

/-- A non-zero term bounded below by 0 bounded below by 1, and one bounded above by 0
bounded above by −1 (facts.difference-facts). -/
def tightenDiffs (F : Facts) : List Diff :=
  F.nonzero.flatMap fun t =>
    (if F.bound .zero t = some 0 then [⟨.zero, t, -1⟩] else []) ++
      (if F.bound t .zero = some 0 then [⟨t, .zero, -1⟩] else [])

/-- One round of closure: through every term, then the non-zero terms. -/
def closeRound (F : Facts) : Facts :=
  let G := F.terms.foldl closeVia F
  G.insertAll G.tightenDiffs

/-- Rounds of closure until nothing changes, at most `n` of them. -/
def closeN : Nat → Facts → Facts
  | 0, F => F
  | n + 1, F => let G := F.closeRound; if G = F then F else closeN n G

/-- The closed set (facts.difference-facts): rounds of closure until nothing changes, which
two rounds for each non-zero term bound. -/
def close (F : Facts) : Facts := closeN (2 * F.nonzero.length + 2) F

/-- What two paths both keep (facts.joins): for each pair, the greater `c` of the two, and the
terms non-zero on both. A contradictory set takes no part. -/
def join (F G : Facts) : Facts :=
  if F.contra then G else if G.contra then F else
    { diffs := F.diffs.filterMap fun d => (G.bound d.t d.u).map fun c => ⟨d.t, d.u, max d.c c⟩,
      nonzero := F.nonzero.filter fun t => t ∈ G.nonzero }

/-- Whether every fact of `G` follows from those of `F`. -/
def entails (F G : Facts) : Bool :=
  F.contra || ((G.diffs.all fun d => (F.bound d.t d.u).any (· ≤ d.c)) &&
    G.nonzero.all fun t => t ∈ F.nonzero || (F.bound .zero t).any (· ≤ -1) ||
      (F.bound t .zero).any (· ≤ -1))

/-- Only the bounds: every fact between two terms neither of which is zero dropped
(facts.large-bodies). -/
def onlyBounds (F : Facts) : Facts :=
  { F with diffs := F.diffs.filter fun d => d.t = .zero || d.u = .zero }

end Facts

/-! ## What the operations keep -/

namespace Facts

variable {F G : Facts} {ν ν' : Valuation}

theorem Holds.diff (h : F.Holds ν) {d : Diff} (hd : d ∈ F.diffs) : ν d.t - ν d.u ≤ d.c := h.1 d hd

theorem top_holds (ν : Valuation) : top.Holds ν := ⟨fun _ h => (nomatch h), fun _ h => (nomatch h)⟩

theorem not_bot (ν : Valuation) : ¬ bot.Holds ν := fun h => by
  simp [Facts.Holds, bot, Diff.Holds] at h

theorem not_of_contra (hc : F.contra = true) : ¬ F.Holds ν := fun h => by
  simp only [contra, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨d, hd, ht, hlt⟩ := hc
  have := h.1 d hd
  simp only [Diff.Holds, ht] at this
  omega

theorem bound_foldl {t u : Term} : ∀ (ds : List Diff) (acc : Option Int) (c : Int),
    ds.foldl (fun acc d =>
      if d.t = t ∧ d.u = u then some (match acc with | some a => min a d.c | none => d.c) else acc)
      acc = some c →
    acc = some c ∨ (∃ a, acc = some a ∧ a ≤ c) ∨ ∃ d ∈ ds, d.t = t ∧ d.u = u ∧ d.c ≤ c
  | [], acc, c, h => .inl h
  | d :: ds, acc, c, h => by
    simp only [List.foldl_cons] at h
    rcases bound_foldl ds _ c h with h' | ⟨a, ha, hac⟩ | ⟨e, he, het, heu, hec⟩
    · split at h'
      · rename_i hd
        cases acc with
        | none => exact .inr (.inr ⟨d, List.mem_cons_self, hd.1, hd.2, by simp at h'; omega⟩)
        | some a =>
          simp only [Option.some.injEq] at h'
          by_cases hm : a ≤ d.c
          · exact .inr (.inl ⟨a, rfl, by omega⟩)
          · exact .inr (.inr ⟨d, List.mem_cons_self, hd.1, hd.2, by omega⟩)
      · exact .inl h'
    · split at ha
      · rename_i hd
        cases acc with
        | none => exact .inr (.inr ⟨d, List.mem_cons_self, hd.1, hd.2, by simp at ha; omega⟩)
        | some b =>
          simp only [Option.some.injEq] at ha
          by_cases hm : b ≤ d.c
          · exact .inr (.inl ⟨b, rfl, by omega⟩)
          · exact .inr (.inr ⟨d, List.mem_cons_self, hd.1, hd.2, by omega⟩)
      · exact .inr (.inl ⟨a, ha, hac⟩)
    · exact .inr (.inr ⟨e, List.mem_cons_of_mem _ he, het, heu, hec⟩)

/-- A bound that a set gives holds wherever the set does. -/
theorem Holds.bound (h : F.Holds ν) {t u : Term} {c : Int} (hb : F.bound t u = some c) :
    ν t - ν u ≤ c := by
  unfold Facts.bound at hb
  split at hb
  · rename_i htu; subst htu; simp at hb; omega
  · rcases bound_foldl F.diffs none c hb with h' | ⟨a, ha, _⟩ | ⟨d, hd, ht, hu, hc⟩
    · cases h'
    · cases ha
    · have := h.1 d hd; simp only [Diff.Holds, ht, hu] at this; omega

theorem Holds.insert (h : F.Holds ν) {d : Diff} (hd : d.Holds ν) : (F.insert d).Holds ν := by
  unfold Facts.insert
  split
  · split
    · exact h
    · refine ⟨fun e he => ?_, h.2⟩
      rcases List.mem_cons.1 he with rfl | he
      · exact hd
      · exact h.1 e (List.mem_filter.1 he).1
  · refine ⟨fun e he => ?_, h.2⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact hd
    · exact h.1 e he

theorem holds_insertAll : ∀ {F : Facts} {ds : List Diff}, F.Holds ν → (∀ d ∈ ds, d.Holds ν) →
    (F.insertAll ds).Holds ν
  | _, [], h, _ => h
  | F, d :: _, h, hds => by
    unfold Facts.insertAll
    simp only [List.foldl_cons]
    exact holds_insertAll (F := F.insert d) (h.insert (hds _ List.mem_cons_self))
      fun d hd => hds d (List.mem_cons_of_mem _ hd)

theorem Holds.insertAll (h : F.Holds ν) {ds : List Diff} (hds : ∀ d ∈ ds, d.Holds ν) :
    (F.insertAll ds).Holds ν := holds_insertAll h hds

theorem Holds.addNonzero (h : F.Holds ν) {t : Term} (ht : ν t ≠ 0) : (F.addNonzero t).Holds ν := by
  unfold Facts.addNonzero
  split
  · exact h
  · exact ⟨h.1, fun u hu => (List.mem_cons.1 hu).elim (fun e => e ▸ ht) (h.2 u)⟩

theorem holds_addNonzeros : ∀ {F : Facts} {ts : List Term}, F.Holds ν → (∀ t ∈ ts, ν t ≠ 0) →
    (ts.foldl Facts.addNonzero F).Holds ν
  | _, [], h, _ => h
  | F, t :: _, h, hts => by
    simp only [List.foldl_cons]
    exact holds_addNonzeros (F := F.addNonzero t) (h.addNonzero (hts _ List.mem_cons_self))
      fun t ht => hts t (List.mem_cons_of_mem _ ht)

theorem Holds.meet (h : F.Holds ν) (h' : G.Holds ν) : (F.meet G).Holds ν :=
  holds_addNonzeros (h.insertAll h'.1) h'.2

/-- The facts on kept terms hold of any valuation that agrees on them. -/
theorem Holds.restrict (h : F.Holds ν) {keep : Term → Bool} (hk : ∀ t, keep t = true → ν' t = ν t) :
    (F.restrict keep).Holds ν' := by
  refine ⟨fun d hd => ?_, fun t ht => ?_⟩
  · obtain ⟨hd, hkd⟩ := List.mem_filter.1 hd
    simp only [Bool.and_eq_true] at hkd
    have := h.1 d hd
    simp only [Diff.Holds] at this ⊢
    rw [hk _ hkd.1, hk _ hkd.2]; exact this
  · obtain ⟨ht, hkt⟩ := List.mem_filter.1 ht
    rw [hk _ hkt]; exact h.2 t ht

theorem holds_map {f : Term → Term} : (F.map f).Holds ν ↔ F.Holds (ν ∘ f) := by
  simp [Facts.map, Facts.Holds, Diff.Holds]

theorem Holds.through (h : F.Holds ν) (k : Term) : ∀ d ∈ F.through k, d.Holds ν := by
  intro d hd
  simp only [Facts.through, List.mem_flatMap] at hd
  obtain ⟨d₁, h₁, hd⟩ := hd
  split at hd
  · rename_i hu
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hd
    obtain ⟨d₂, ⟨h₂, ht⟩, rfl⟩ := hd
    have a := h.1 d₁ h₁
    have b := h.1 d₂ h₂
    simp only [Diff.Holds, hu, ht] at a b ⊢
    omega
  · cases hd

theorem Holds.closeVia (h : F.Holds ν) (k : Term) : (F.closeVia k).Holds ν :=
  h.insertAll (h.through k)

theorem holds_closeVias : ∀ {F : Facts} (ks : List Term), F.Holds ν →
    (ks.foldl Facts.closeVia F).Holds ν
  | _, [], h => h
  | F, k :: ks, h => by
    simp only [List.foldl_cons]
    exact holds_closeVias (F := F.closeVia k) ks (h.closeVia k)

theorem Holds.tightenDiffs (h : F.Holds ν) (hz : ν .zero = 0) : ∀ d ∈ F.tightenDiffs, d.Holds ν := by
  intro d hd
  simp only [Facts.tightenDiffs, List.mem_flatMap, List.mem_append] at hd
  obtain ⟨t, ht, hd⟩ := hd
  have hnz := h.2 t ht
  rcases hd with hd | hd <;> split at hd <;> simp only [List.mem_singleton, List.not_mem_nil] at hd
  · rename_i hb; subst hd
    have := h.bound hb
    simp only [Diff.Holds, hz] at this ⊢
    omega
  · rename_i hb; subst hd
    have := h.bound hb
    simp only [Diff.Holds, hz] at this ⊢
    omega

theorem Holds.closeRound (h : F.Holds ν) (hz : ν .zero = 0) : F.closeRound.Holds ν := by
  have hg := holds_closeVias F.terms h
  exact hg.insertAll (hg.tightenDiffs hz)

theorem Holds.closeN (hz : ν .zero = 0) : ∀ (n : Nat) {F : Facts}, F.Holds ν → (F.closeN n).Holds ν
  | 0, _, h => h
  | n + 1, F, h => by
    simp only [Facts.closeN]
    split
    · exact h
    · exact Holds.closeN hz n (h.closeRound hz)

/-- Closing a set keeps what holds (facts.difference-facts). -/
theorem Holds.close (h : F.Holds ν) (hz : ν .zero = 0) : F.close.Holds ν := Holds.closeN hz _ h

/-- What either of two sets holds of, their join holds of (facts.joins). -/
theorem holds_join (h : F.Holds ν ∨ G.Holds ν) : (F.join G).Holds ν := by
  unfold Facts.join
  split
  · rename_i hc; exact h.resolve_left (not_of_contra hc)
  split
  · rename_i _ hc; exact h.resolve_right (not_of_contra hc)
  refine ⟨fun d hd => ?_, fun t ht => ?_⟩
  · simp only [List.mem_filterMap, Option.map_eq_some_iff] at hd
    obtain ⟨e, he, c, hb, rfl⟩ := hd
    simp only [Diff.Holds]
    rcases h with h | h
    · have := h.1 e he; simp only [Diff.Holds] at this; omega
    · have := h.bound hb; omega
  · obtain ⟨ht, hg⟩ := List.mem_filter.1 ht
    rcases h with h | h
    · exact h.2 t ht
    · exact h.2 t (by simpa using hg)

/-- A set that `F` entails holds wherever `F` does. -/
theorem Holds.entails (h : F.Holds ν) (hz : ν .zero = 0) (he : F.entails G = true) : G.Holds ν := by
  unfold Facts.entails at he
  simp only [Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true, Option.any_eq_true,
    decide_eq_true_eq] at he
  rcases he with hc | ⟨hd, hn⟩
  · exact absurd h (not_of_contra hc)
  refine ⟨fun d hd' => ?_, fun t ht => ?_⟩
  · obtain ⟨c, hb, hc⟩ := hd d hd'
    have := h.bound hb
    simp only [Diff.Holds]; omega
  · rcases hn t ht with (hm | ⟨c, hb, hc⟩) | ⟨c, hb, hc⟩
    · exact h.2 t hm
    · have := h.bound hb; rw [hz] at this; omega
    · have := h.bound hb; rw [hz] at this; omega

theorem Holds.onlyBounds (h : F.Holds ν) : F.onlyBounds.Holds ν :=
  ⟨fun d hd => h.1 d (List.mem_filter.1 hd).1, h.2⟩

end Facts

end Stilt
