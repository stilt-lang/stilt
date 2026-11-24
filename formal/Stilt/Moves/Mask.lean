import Stilt.Moves.Analysis
import Stilt.Values

/-!
# Masks

A last use ends a variable while its binding is still in scope: nothing after
it reads the variable, and under `Moving` its storage may belong to another
variable. A mask records, for each binding of a frame, the newest first,
whether it is still live. The relation of `Stilt.Moves.Relation` asks the
two models to agree on live bindings only.

* `LiveAt x m ns`: the newest binding of `x` is live, so reading `x` reads a
  live binding.
* `kill x m ns`: the mask with the newest binding of `x` ended.

`Stilt.Moves.Kills` says which bindings an expression may end.
-/

namespace Stilt.Moving

/-- The entries of a list that a mask keeps. -/
def keep {α : Type} : List Bool → List α → List α
  | b :: m, a :: l => if b then a :: keep m l else keep m l
  | _, _ => []

/-- The newest binding named `x` is live. -/
def LiveAt (x : Name) : List Bool → List Name → Prop
  | b :: m, y :: ns => if y = x then b = true else LiveAt x m ns
  | _, _ => True

/-- Ends the newest binding named `x`. -/
def kill (x : Name) : List Bool → List Name → List Bool
  | b :: m, y :: ns => if y = x then false :: m else b :: kill x m ns
  | m, _ => m

/-- Removes the newest entry named `x`. -/
def dropName {β : Type} (x : Name) : List (Name × β) → List (Name × β)
  | [] => []
  | (y, b) :: l => if y = x then l else (y, b) :: dropName x l

variable {β : Type}

/-! ## Keeping -/

theorem keep_cons_true (m : List Bool) (a : β) (l : List β) : keep (true :: m) (a :: l) = a :: keep m l :=
  rfl

theorem map_keep {γ : Type} (f : β → γ) : ∀ (m : List Bool) (l : List β), (keep m l).map f = keep m (l.map f)
  | [], _ => by simp [keep]
  | _ :: _, [] => by simp [keep]
  | b :: m, a :: l => by cases b <;> simp [keep, map_keep f m l]

theorem keep_all : ∀ {m : List Bool} {l : List β}, (∀ b ∈ m, b = true) → m.length = l.length → keep m l = l
  | [], [], _, _ => rfl
  | b :: m, a :: l, h, hl => by
    have hb : b = true := h b List.mem_cons_self
    subst hb
    simp only [keep, ↓reduceIte, List.cons.injEq, true_and]
    exact keep_all (fun c hc => h c (List.mem_cons_of_mem _ hc)) (by simpa using hl)
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

theorem sublist_keep : ∀ (m : List Bool) (l : List β), (keep m l).Sublist l
  | [], _ => by simp [keep]
  | _ :: _, [] => by simp [keep]
  | b :: m, a :: l => by
    cases b
    · exact (sublist_keep m l).cons a
    · exact (sublist_keep m l).cons_cons a

theorem lookup_keep {x : Name} : ∀ {m : List Bool} {l : List (Name × β)}, m.length = l.length →
    LiveAt x m (l.map Prod.fst) → (keep m l).lookup x = l.lookup x
  | [], [], _, _ => rfl
  | b :: m, (y, v) :: l, hl, h => by
    simp only [List.map_cons, LiveAt] at h
    by_cases hy : y = x
    · subst hy
      simp only [↓reduceIte] at h
      subst h
      simp [keep]
    · simp only [hy, ↓reduceIte] at h
      have ih := lookup_keep (m := m) (l := l) (by simpa using hl) h
      cases b <;> simp [keep, lookup_cons_ne (Ne.symm hy), ih]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem keep_assocSet {x : Name} {w : β} : ∀ {m : List Bool} {l : List (Name × β)},
    m.length = l.length → LiveAt x m (l.map Prod.fst) → keep m (assocSet l x w) = assocSet (keep m l) x w
  | [], [], _, _ => rfl
  | b :: m, (y, v) :: l, hl, h => by
    simp only [List.map_cons, LiveAt] at h
    by_cases hy : y = x
    · subst hy
      simp only [↓reduceIte] at h
      subst h
      simp [keep, assocSet]
    · simp only [hy, ↓reduceIte] at h
      have ih := keep_assocSet (w := w) (m := m) (l := l) (by simpa using hl) h
      have hxy : x ≠ y := Ne.symm hy
      cases b <;> simp [keep, assocSet, hxy, ih]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem keep_kill {x : Name} : ∀ {m : List Bool} {l : List (Name × β)}, m.length = l.length →
    LiveAt x m (l.map Prod.fst) → keep (kill x m (l.map Prod.fst)) l = dropName x (keep m l)
  | [], [], _, _ => rfl
  | b :: m, (y, v) :: l, hl, h => by
    simp only [List.map_cons, LiveAt] at h
    by_cases hy : y = x
    · subst hy
      simp only [↓reduceIte] at h
      subst h
      simp [kill, keep, dropName]
    · simp only [hy, ↓reduceIte] at h
      have ih := keep_kill (m := m) (l := l) (by simpa using hl) h
      cases b <;> simp [kill, keep, dropName, hy, ih]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem length_kill (x : Name) : ∀ (m : List Bool) (ns : List Name), (kill x m ns).length = m.length
  | [], _ => by simp [kill]
  | _ :: _, [] => by simp [kill]
  | b :: m, y :: ns => by
    by_cases hy : y = x <;> simp [kill, hy, length_kill x m ns]

theorem sublist_dropName (x : Name) : ∀ l : List (Name × β), (dropName x l).Sublist l
  | [] => .slnil
  | (y, b) :: l => by
    unfold dropName
    split
    · exact .cons _ (List.Sublist.refl l)
    · exact (sublist_dropName x l).cons_cons _

/-! ## Live bindings -/

theorem LiveAt.cons_self (x : Name) (m : List Bool) (ns : List Name) : LiveAt x (true :: m) (x :: ns) := by
  simp [LiveAt]

theorem LiveAt.cons {x y : Name} {b : Bool} {m : List Bool} {ns : List Name} (h : LiveAt x m ns)
    (hne : x ≠ y) : LiveAt x (b :: m) (y :: ns) := by
  simp [LiveAt, Ne.symm hne, h]

theorem LiveAt.of_cons {x y : Name} {b : Bool} {m : List Bool} {ns : List Name}
    (h : LiveAt x (b :: m) (y :: ns)) (hne : x ≠ y) : LiveAt x m ns := by
  simpa [LiveAt, Ne.symm hne] using h

theorem LiveAt.kill {x z : Name} : ∀ {m : List Bool} {ns : List Name}, LiveAt z m ns → z ≠ x →
    LiveAt z (Moving.kill x m ns) ns
  | [], _, _, _ => by simp [Moving.kill, LiveAt]
  | _ :: _, [], _, _ => by simp [Moving.kill, LiveAt]
  | b :: m, y :: ns, h, hne => by
    by_cases hy : y = x
    · subst hy
      simp only [Moving.kill, ↓reduceIte]
      simp only [LiveAt, Ne.symm hne, ↓reduceIte] at h ⊢
      exact h
    · simp only [Moving.kill, hy, ↓reduceIte]
      by_cases hz : y = z
      · simpa [LiveAt, hz] using h
      · simp only [LiveAt, hz, ↓reduceIte] at h ⊢
        exact LiveAt.kill h hne

end Stilt.Moving
