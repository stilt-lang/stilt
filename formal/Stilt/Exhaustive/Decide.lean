import Stilt.Patterns

/-!
# Finding a derivation

`exhaustive D fuel P τs` runs the usefulness algorithm (patterns.algorithm) on
the rows `P` against the column types `τs`: at each column it tries the step of
the column's type, a constructor's matrix for each of its constructors, and,
when that fails or the type lists none, the default matrix. It says yes only
when it has found a derivation (`exhaustive_sound`), so a `match` whose arms it
accepts is exhaustive, and by `Exhaustive.sound` covers every value. It runs on
fuel, one step a column, and says no when the fuel runs out.
-/

namespace Stilt

/-- The most elements a list pattern lists, among a pattern's alternatives. -/
def Pattern.listed : Pattern → Nat
  | .list ps _ => ps.length
  | .or p q => max p.listed q.listed
  | _ => 0

/-- The most elements a list pattern in the first column lists: every longer
length is matched by the same rows as the next one, so the algorithm checks the
lengths up to it one by one, and the longer ones together. -/
def firstListed (P : Rows) : Nat :=
  P.foldl (fun m row => match row with | p :: _ => max m p.listed | [] => m) 0

/-- Whether the usefulness algorithm finds that the rows cover the types. -/
def exhaustive (D : Decls) : Nat → Rows → List Ty → Bool
  | 0, _, _ => false
  | _ + 1, P, [] => P.any List.isEmpty
  | n + 1, P, τ :: τs =>
    let byDefault := exhaustive D n (specialize defaultRow P) τs
    if D.uninhabited τ then true else
    match τ with
    | .bool =>
      (exhaustive D n (specialize (boolRow true) P) τs &&
        exhaustive D n (specialize (boolRow false) P) τs) || byDefault
    | .unit => exhaustive D n (specialize unitRow P) τs || byDefault
    | .tuple σs => exhaustive D n (specialize (tupleRow σs.length) P) (σs ++ τs) || byDefault
    | .record R =>
      match D.record? R with
      | some r =>
        exhaustive D n (specialize (recordRow (r.fields.map Prod.fst)) P)
          (r.fields.map Prod.snd ++ τs) || byDefault
      | none => byDefault
    | .variant T =>
      match D.variant? T with
      | some t =>
        t.ctors.all (fun c => exhaustive D n (specialize (variantRow c.1 c.2.length) P) (c.2 ++ τs))
          || byDefault
      | none => byDefault
    | .list σ =>
      let m := firstListed P
      ((List.range (m + 1)).all (fun k =>
          exhaustive D n (specialize (listRow k false) P) (List.replicate k σ ++ τs)) &&
        exhaustive D n (specialize (listRow m true) P) (List.replicate m σ ++ τs)) || byDefault
    | _ => byDefault

/-- What the algorithm says yes to has a derivation. -/
theorem exhaustive_sound (D : Decls) : ∀ (n : Nat) {P : Rows} {τs : List Ty},
    exhaustive D n P τs = true → Exhaustive D P τs
  | 0, _, _, h => by simp [exhaustive] at h
  | n + 1, P, [], h => by
    simp only [exhaustive, List.any_eq_true] at h
    obtain ⟨r, hr, he⟩ := h
    cases r
    · exact .done hr
    · simp at he
  | n + 1, P, τ :: τs, h => by
    have dflt : exhaustive D n (specialize defaultRow P) τs = true → Exhaustive D P (τ :: τs) :=
      fun h => .default (exhaustive_sound D n h)
    by_cases hu : D.uninhabited τ = true
    · exact .empty (Decls.uninhabited_sound hu)
    cases τ with
    | bool =>
      simp only [exhaustive, hu, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨ht, hf⟩ | h
      · exact .bool (exhaustive_sound D n ht) (exhaustive_sound D n hf)
      · exact dflt h
    | unit =>
      simp only [exhaustive, hu, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true] at h
      rcases h with h | h
      · exact .unit (exhaustive_sound D n h)
      · exact dflt h
    | tuple σs =>
      simp only [exhaustive, hu, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true] at h
      rcases h with h | h
      · exact .tuple (exhaustive_sound D n h)
      · exact dflt h
    | record R =>
      simp only [exhaustive, hu, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i r hr
        simp only [Bool.or_eq_true] at h
        rcases h with h | h
        · exact .record hr (exhaustive_sound D n h)
        · exact dflt h
      · exact dflt h
    | variant T =>
      simp only [exhaustive, hu, Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · rename_i t ht
        simp only [Bool.or_eq_true, List.all_eq_true] at h
        rcases h with h | h
        · exact .variant ht fun c hc => exhaustive_sound D n (h c hc)
        · exact dflt h
      · exact dflt h
    | list σ =>
      simp only [exhaustive, hu, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, List.all_eq_true,
        List.mem_range] at h
      rcases h with ⟨hs, hl⟩ | h
      · exact .list _ (fun k hk => exhaustive_sound D n (hs k (by omega)))
          (exhaustive_sound D n hl)
      · exact dflt h
    | _ =>
      simp only [exhaustive, hu, Bool.false_eq_true, ↓reduceIte] at h
      exact dflt h

/-- The arms of a `match` on values of type `τ` that the algorithm accepts are
exhaustive. -/
theorem armRows_exhaustive {D : Decls} {arms : List Arm} {τ : Ty} {n : Nat}
    (h : exhaustive D n (armRows arms) [τ] = true) : Exhaustive D (armRows arms) [τ] :=
  exhaustive_sound D n h

end Stilt
