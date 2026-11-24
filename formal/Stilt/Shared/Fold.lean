/-!
# A fold's tree, whatever the schedule

par.fold-tree: `par.fold` combines a list of `n` elements in a balanced tree
that depends on `n` alone, its first `⌊n/2⌋` elements folded, combined with
the rest folded. `shape n` is that tree, a function of the length, and `tree`
fills it with the list's elements. A schedule runs the combinations in any
order, two halves at once included: `Step` combines any two neighbours that
are values, at any depth, and a run is any sequence of steps. `scheduled`
proves that every run that ends gives the value of the tree evaluated in
order, `fold`, which so depends on the list alone; `schedule_progress` that
a run never gets stuck before it ends; and `shape_split` and `shape_size`
that the tree is the one of par.fold-tree.
-/

namespace Stilt.Shared.Fold

/-- The shape of a tree of combinations. -/
inductive Shape where
  | leaf
  | node (l r : Shape)
  deriving DecidableEq, Repr

/-- The number of elements a shape combines. -/
def Shape.size : Shape → Nat
  | .leaf => 1
  | .node l r => l.size + r.size

/-- The tree of par.fold-tree for `n` elements, with `fuel` bounding its depth. -/
def shapeFuel : Nat → Nat → Shape
  | 0, _ => .leaf
  | fuel + 1, n =>
      if n ≤ 1 then .leaf
      else .node (shapeFuel fuel (n / 2)) (shapeFuel fuel (n - n / 2))

/-- The tree of par.fold-tree for a list of `n` elements, a function of `n` alone. -/
def shape (n : Nat) : Shape := shapeFuel n n

/-- Enough fuel gives the same tree. -/
theorem shapeFuel_enough : ∀ (fuel fuel' n : Nat), n ≤ fuel → n ≤ fuel' →
    shapeFuel fuel n = shapeFuel fuel' n := by
  intro fuel
  induction fuel with
  | zero =>
      intro fuel' n h _
      cases fuel' <;> simp [shapeFuel] <;> omega
  | succ k ih =>
      intro fuel' n h h'
      cases fuel' with
      | zero => simp [shapeFuel]; omega
      | succ k' =>
          simp only [shapeFuel]
          split
          · rfl
          · rw [ih k' (n / 2) (by omega) (by omega),
              ih k' (n - n / 2) (by omega) (by omega)]

/-- par.fold-tree: a list of two elements or more combines its first `⌊n/2⌋`
elements and the rest. -/
theorem shape_split (n : Nat) (h : 2 ≤ n) :
    shape n = .node (shape (n / 2)) (shape (n - n / 2)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [shape, shapeFuel, show ¬(k + 1 ≤ 1) by omega, ite_false]
  rw [shapeFuel_enough k ((k + 1) / 2) ((k + 1) / 2) (by omega) (by omega),
    shapeFuel_enough k (k + 1 - (k + 1) / 2) (k + 1 - (k + 1) / 2)
      (by omega) (by omega)]

/-- The tree for `n` elements combines `n` of them. -/
theorem shape_size : ∀ n, 1 ≤ n → (shape n).size = n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
      intro h
      by_cases h1 : n = 1
      · subst h1; rfl
      · rw [shape_split n (by omega), Shape.size, ih (n / 2) (by omega) (by omega),
          ih (n - n / 2) (by omega) (by omega)]
        omega

/-- A tree of combinations, partly computed: values and pending
combinations. -/
inductive Term (α : Type) where
  | val (a : α)
  | node (l r : Term α)

/-- The elements of a list in a shape, from the first; `empty` stands for a
missing one, which a shape of the list's length never needs. -/
def fill {α : Type} (empty : α) : Shape → List α → Term α
  | .leaf, [] => .val empty
  | .leaf, x :: _ => .val x
  | .node l r, xs => .node (fill empty l xs) (fill empty r (xs.drop l.size))

/-- The tree of a non-empty list (par.fold-tree). -/
def tree {α : Type} (empty : α) (xs : List α) : Term α :=
  fill empty (shape xs.length) xs

/-- The tree evaluated in order: the left half, then the right. -/
def Term.eval {α : Type} (f : α → α → α) : Term α → α
  | .val a => a
  | .node l r => f (l.eval f) (r.eval f)

/-- `par.fold(xs, empty, f)`: `empty` for an empty list, and otherwise the
tree evaluated in order. -/
def fold {α : Type} (xs : List α) (empty : α) (f : α → α → α) : α :=
  match xs with
  | [] => empty
  | _ :: _ => (tree empty xs).eval f

/-- One step of a schedule: a combination of two values, anywhere in the
tree, each half running on its own. -/
inductive Step {α : Type} (f : α → α → α) : Term α → Term α → Prop
  | combine (a b : α) : Step f (.node (.val a) (.val b)) (.val (f a b))
  | left {l l' : Term α} (r : Term α) :
      Step f l l' → Step f (.node l r) (.node l' r)
  | right (l : Term α) {r r' : Term α} :
      Step f r r' → Step f (.node l r) (.node l r')

/-- A run of a schedule: any sequence of steps. -/
inductive Run {α : Type} (f : α → α → α) : Term α → Term α → Prop
  | done (t : Term α) : Run f t t
  | step {t t' u : Term α} : Step f t t' → Run f t' u → Run f t u

/-- A step keeps the value of the tree evaluated in order. -/
theorem Step.eval {α : Type} {f : α → α → α} {t t' : Term α}
    (h : Step f t t') : t'.eval f = t.eval f := by
  induction h with
  | combine => rfl
  | left _ _ ih => simp [Term.eval, ih]
  | right _ _ ih => simp [Term.eval, ih]

theorem Run.eval {α : Type} {f : α → α → α} {t u : Term α}
    (h : Run f t u) : u.eval f = t.eval f := by
  induction h with
  | done => rfl
  | step s _ ih => rw [ih, s.eval]

/-- A schedule never gets stuck: a tree that isn't a value can step. -/
theorem schedule_progress {α : Type} (f : α → α → α) :
    ∀ t : Term α, (∀ a, t ≠ .val a) → ∃ t', Step f t t'
  | .val a, h => absurd rfl (h a)
  | .node (.val a) (.val b), _ => ⟨_, .combine a b⟩
  | .node (.node ll lr) r, _ =>
      let ⟨_, s⟩ := schedule_progress f (.node ll lr) (fun _ h => by cases h)
      ⟨_, .left r s⟩
  | .node (.val a) (.node rl rr), _ =>
      let ⟨_, s⟩ := schedule_progress f (.node rl rr) (fun _ h => by cases h)
      ⟨_, .right (.val a) s⟩

/-- par.fold-tree and parallel-like-sequential: every schedule of a fold that ends gives `fold`, the
tree evaluated in order, which depends on the list alone. -/
theorem scheduled {α : Type} (f : α → α → α) (empty : α) (x : α)
    (xs : List α) (v : α) (h : Run f (tree empty (x :: xs)) (.val v)) :
    v = fold (x :: xs) empty f := by
  have := h.eval
  simp only [Term.eval] at this
  simp [fold, this]

/-- `fold([a, b, c], e, f)` is `f(a, f(b, c))`, and with four elements,
`f(f(a, b), f(c, d))`, as par.fold-tree writes them: with `10 * p + q`, which isn't
associative, they are `10 * 1 + 23` and `10 * 12 + 34`. -/
example : fold [1, 2, 3] 0 (fun p q => 10 * p + q) = 33 := by decide
example : fold [1, 2, 3, 4] 0 (fun p q => 10 * p + q) = 154 := by decide
example : shape 3 = .node .leaf (.node .leaf .leaf) := by decide
example : shape 5 = .node (.node .leaf .leaf)
    (.node .leaf (.node .leaf .leaf)) := by decide

end Stilt.Shared.Fold
