/-!
# Hygienic expansion

macros.hygiene makes a pattern macro's expansion hygienic: a name that the
template binds is fresh, the template's other names resolve where the macro
is declared, and a fragment's tokens resolve where the use is. This calculus
states what that buys: an expansion means what its template means, with each
fragment evaluated where the use is, so no binder of the template captures a
name of the user's, whatever names the user picks.

Names carry the mark of the expansion that wrote them, as `tmp#1` (macros.showing):
`0` for a name the user wrote, and an expansion's number for a name of its
template. The expressions are integer literals, names, sums and `let`. A
template has the same forms over unmarked names, and fragments `$i`, which
the use's arguments replace.
-/

namespace Stilt.Macros

/-- A name, with the mark of the expansion that wrote it, `0` for the user's
(macros.hygiene). -/
abbrev Name := String × Nat

/-- An expression, as the user writes it or an expansion makes it. -/
inductive Expr where
  | lit : Int → Expr
  | var : Name → Expr
  | add : Expr → Expr → Expr
  /-- `let n = e; body`. -/
  | let_ : Name → Expr → Expr → Expr
  deriving Repr

/-- What the names in scope hold. -/
abbrev Env := Name → Option Int

/-- The environment with `n` bound to `v`. -/
def Env.set (ρ : Env) (n : Name) (v : Int) : Env :=
  fun m => if m = n then some v else ρ m

/-- Evaluation, which fails at a name that holds nothing. -/
def Expr.eval : Env → Expr → Option Int
  | _, .lit k => some k
  | ρ, .var n => ρ n
  | ρ, .add a b => do
      let x ← a.eval ρ
      let y ← b.eval ρ
      pure (x + y)
  | ρ, .let_ n a b => do
      let x ← a.eval ρ
      b.eval (ρ.set n x)

/-- The names that an expression reads from its scope. -/
def Expr.Free : Expr → Name → Prop
  | .lit _, _ => False
  | .var n, m => m = n
  | .add a b, m => a.Free m ∨ b.Free m
  | .let_ n a b, m => a.Free m ∨ (b.Free m ∧ m ≠ n)

/-- An expression reads only the names it has free: environments that agree
on those give it one value. -/
theorem Expr.eval_agree (e : Expr) :
    ∀ (ρ₁ ρ₂ : Env), (∀ m, e.Free m → ρ₁ m = ρ₂ m) → e.eval ρ₁ = e.eval ρ₂ := by
  induction e with
  | lit => intro _ _ _; rfl
  | var n => intro ρ₁ ρ₂ h; exact h n rfl
  | add a b iha ihb =>
      intro ρ₁ ρ₂ h
      simp only [Expr.eval]
      rw [iha ρ₁ ρ₂ (fun m hm => h m (Or.inl hm)),
        ihb ρ₁ ρ₂ (fun m hm => h m (Or.inr hm))]
  | let_ n a b iha ihb =>
      intro ρ₁ ρ₂ h
      simp only [Expr.eval]
      rw [iha ρ₁ ρ₂ (fun m hm => h m (Or.inl hm))]
      cases a.eval ρ₂ with
      | none => rfl
      | some x =>
          apply ihb
          intro m hm
          simp only [Env.set]
          by_cases hn : m = n
          · simp [hn]
          · simp only [hn, ite_false]
            exact h m (Or.inr ⟨hm, hn⟩)

/-- A template: names it writes, unmarked, its binders, and fragments `$i`
(macros.templates). -/
inductive Tmpl where
  | lit : Int → Tmpl
  /-- A name the template writes, which resolves where the macro is
  declared, or at one of the template's binders. -/
  | var : String → Tmpl
  /-- `$i`, the fragment that the use's `i`th argument gives. -/
  | frag : Nat → Tmpl
  | add : Tmpl → Tmpl → Tmpl
  /-- `let x = e; body`, a binder of the template's. -/
  | let_ : String → Tmpl → Tmpl → Tmpl
  deriving Repr

/-- The expansion numbered `k` of a template, at a use whose fragments are
`args`: each name the template writes marked with `k`, and each fragment
replaced by its argument (macros.expansion and macros.hygiene). A fragment that no argument
gives, which the declaration's checks rule out (E0221), is `0`. -/
def Tmpl.expand (k : Nat) (args : List Expr) : Tmpl → Expr
  | .lit n => .lit n
  | .var x => .var (x, k)
  | .frag i => (args[i]?).getD (.lit 0)
  | .add a b => .add (a.expand k args) (b.expand k args)
  | .let_ x a b => .let_ (x, k) (a.expand k args) (b.expand k args)

/-- What a template means: its names read from `σ`, the scope where the macro
is declared, extended by its own binders, and each fragment the value given
for it. -/
def Tmpl.eval (σ : String → Option Int) (frags : List (Option Int)) :
    Tmpl → Option Int
  | .lit n => some n
  | .var x => σ x
  | .frag i => (frags[i]?).getD (some 0)
  | .add a b => do
      let x ← a.eval σ frags
      let y ← b.eval σ frags
      pure (x + y)
  | .let_ x a b => do
      let v ← a.eval σ frags
      b.eval (fun y => if y = x then some v else σ y) frags

/-- `Hygiene`: when no argument has a name marked `k` free, the expansion
numbered `k` means what its template means, with its names read where the
macro is declared, which the names marked `k` stand for, and each fragment
evaluated in the user's environment `ρ`. So no binder of the template
captures a name that a fragment reads, and what the expansion means doesn't
depend on the names the user picks (macros.hygiene). -/
theorem hygiene (k : Nat) (args : List Expr)
    (fresh : ∀ e ∈ args, ∀ m, e.Free m → m.2 ≠ k) (t : Tmpl) :
    ∀ ρ : Env, (t.expand k args).eval ρ =
      t.eval (fun x => ρ (x, k)) (args.map (·.eval ρ)) := by
  induction t with
  | lit => intro _; rfl
  | var => intro _; rfl
  | frag i =>
      intro ρ
      simp only [Tmpl.expand, Tmpl.eval, List.getElem?_map]
      cases args[i]? <;> rfl
  | add a b iha ihb =>
      intro ρ
      simp only [Tmpl.expand, Tmpl.eval, Expr.eval, iha ρ, ihb ρ]
  | let_ x a b iha ihb =>
      intro ρ
      simp only [Tmpl.expand, Tmpl.eval, Expr.eval, iha ρ]
      cases a.eval (fun y => ρ (y, k)) (args.map (·.eval ρ)) with
      | none => rfl
      | some v =>
          -- The binder is marked `k`, which no argument reads.
          have hσ : (fun y => (ρ.set (x, k) v) (y, k)) =
              (fun y => if y = x then some v else ρ (y, k)) := by
            funext y
            simp [Env.set]
          have hargs :
              args.map (·.eval (ρ.set (x, k) v)) = args.map (·.eval ρ) := by
            apply List.map_congr_left
            intro e he
            apply Expr.eval_agree
            intro m hm
            have hne : m ≠ (x, k) := fun h => fresh e he m hm (by rw [h])
            simp [Env.set, hne]
          show (b.expand k args).eval (ρ.set (x, k) v) = _
          rw [ihb (ρ.set (x, k) v), hσ, hargs]
          rfl

/-! ## Examples: `with_tmp!(tmp + 1)` (macros.hygiene, required tests) -/

/-- `syntax with_tmp { ($body: expr) => { let tmp = 100; $body } }`, whose
binder the user's fragment names too. -/
def withTmp : Tmpl := .let_ "tmp" (.lit 100) (.frag 0)

/-- The fragment `tmp + 1`, as the user wrote it. -/
def tmpPlusOne : Expr := .add (.var ("tmp", 0)) (.lit 1)

/-- The user's scope, where `tmp` holds 2. -/
def userEnv : Env := fun n => if n = ("tmp", 0) then some 2 else none

/-- Expanded with its own mark, the fragment reads the user's `tmp`: 3. -/
theorem withTmp_hygienic : (withTmp.expand 1 [tmpPlusOne]).eval userEnv = some 3 :=
  rfl

/-- So does what `hygiene` gives it: the template's meaning, with the fragment
evaluated where the use is. -/
theorem withTmp_meaning :
    (withTmp.expand 1 [tmpPlusOne]).eval userEnv =
      withTmp.eval (fun x => userEnv (x, 1)) [tmpPlusOne.eval userEnv] :=
  hygiene 1 [tmpPlusOne]
    (fun e he m hm => by
      simp only [List.mem_singleton] at he
      subst he
      simp only [tmpPlusOne, Expr.Free] at hm
      rcases hm with hm | hm
      · subst hm; decide
      · exact hm.elim)
    withTmp userEnv

/-- Without a fresh mark, as if the template wrote the user's names, its
`tmp` captures the fragment's: 101, which is why `hygiene` asks that no
argument read a name of the expansion's mark. -/
theorem withTmp_captures : (withTmp.expand 0 [tmpPlusOne]).eval userEnv = some 101 :=
  rfl

end Stilt.Macros
