import Stilt.Ends.Syntax
import Stilt.Ends.Counter

/-!
# Self-calls that go down pass smaller measures

What the roles promise of a run, in copy-in, copy-out, whatever its order of write-back.
Code keeps every variable it doesn't write, so a variable keeps what its role says of it
(`Roles.Inv.after`); an expression with a role gives a value that its role describes
(`eval_roleIn`); and so a self-call that descends passes, at the descending position, a
value smaller than the one its caller was called with (`args_descend`), and one that shrinks
passes a counter closer to its bound (`args_shrink`): the call's measure goes down
(`Descent.measure`).
-/

namespace Stilt

/-- The size of what an argument passes by value, `0` for a place. -/
noncomputable def Passed.size : Passed → Nat
  | .value v | .moved _ v => sizeOf v
  | .place _ _ => 0

/-- The size of the argument at position `k`. -/
noncomputable def Passed.sizeAt (passed : List Passed) (k : Nat) : Nat :=
  (passed[k]?.map Passed.size).getD 0

/-- The integer an argument passes by value. -/
def Passed.int? : Passed → Option Int
  | .value v | .moved _ v => v.int?
  | .place _ _ => none

/-- The integer of the argument at position `k`. -/
def Passed.intAt (passed : List Passed) (k : Nat) : Option Int := passed[k]?.bind Passed.int?

/-- The integer a counter's bound has in a call. -/
def ShrinkBound.valAt : ShrinkBound → List Passed → Option Int
  | .lit c, _ => some c
  | .param j, passed => Passed.intAt passed j

/-- What a call's body knows of the call: for self-calls that descend, the size of the
argument at the descending position; for self-calls that shrink, the counter's distance from
its bound, which way it goes, and the integers of the counter and the bound. -/
noncomputable def Descent.meas : Descent → List Passed → Meas
  | .parts k, passed => ⟨Passed.sizeAt passed k, true, none, none⟩
  | .shrinks k grow b, passed =>
    ⟨match Passed.intAt passed k, b.valAt passed with
      | some x, some y => countDistance grow x y
      | _, _ => 0, grow, Passed.intAt passed k, b.valAt passed⟩

/-- A call's measure, which each self-call that goes down brings down. -/
noncomputable def Descent.measure (d : Descent) (passed : List Passed) : Nat := (d.meas passed).size

/-- What a run knows of a call agrees with the way its self-calls go down. -/
def Meas.Fits (μ : Meas) : Descent → Prop
  | .parts _ => True
  | .shrinks _ grow b => μ.grow = grow ∧ (∀ c, b = .lit c → μ.limit = some c) ∧
    ∀ x y, μ.start = some x → μ.limit = some y → countDistance grow x y ≤ μ.size

theorem Descent.meas_fits (d : Descent) (passed : List Passed) : (d.meas passed).Fits d := by
  cases d with
  | parts => trivial
  | shrinks k grow b =>
    refine ⟨rfl, fun c hc => by subst hc; rfl, fun x y hx hy => ?_⟩
    simp only [Descent.meas] at hx hy ⊢
    rw [hx, hy]; exact Nat.le_refl _

variable {R : Roles} {m : Meas}

/-- Code that keeps the variables outside `W` keeps the roles of a frame that `W` avoids. -/
theorem Roles.Inv.afterAt {α : Type} {W L : List Name} {P : α → Prop} {m' : Eval Copy.State α}
    {s s' : Copy.State} {a : α} (hk : Eval.Keeps W L P m') (hA : R.Avoids W)
    (hI : R.Inv s.1 m) (hd : m' s = .done a s') : R.Inv s'.1 m := by
  have := hk s
  rw [hd] at this
  exact hI.keep hA this.2

theorem Roles.Inv.after {α : Type} {W L : List Name} {P : α → Prop} {F : Nat → Eval Copy.State α}
    {s s' : Copy.State} {a : α} (hk : ∀ n, Eval.Keeps W L P (F n)) (hA : R.Avoids W)
    (hI : R.Inv s.1 m) (hd : ∃ N, ∀ n, N ≤ n → F n s = .done a s') : R.Inv s'.1 m :=
  let ⟨N, hN⟩ := hd
  hI.afterAt (hk N) hA (hN N (Nat.le_refl _))

theorem Roles.Inv.evalAt {D : Decls} {w : WriteBack} {e : Expr} {n : Nat} {s s' : Copy.State}
    {a : Value} (hA : R.Avoids e.writes) (hI : R.Inv s.1 m)
    (hd : eval D (Copy.memoryWith w) n e s = .done a s') : R.Inv s'.1 m :=
  hI.afterAt (eval_keeps D w n e e.writes e.resizes (List.Subset.refl _) (List.Subset.refl _)) hA hd

theorem Roles.Inv.afterEval {D : Decls} {w : WriteBack} {e : Expr} {s s' : Copy.State} {a : Value}
    (hA : R.Avoids e.writes) (hI : R.Inv s.1 m)
    (hd : ∃ N, ∀ n, N ≤ n → eval D (Copy.memoryWith w) n e s = .done a s') : R.Inv s'.1 m :=
  let ⟨N, hN⟩ := hd
  hI.evalAt hA (hN N (Nat.le_refl _))

/-- What an expression with a role gives, its role describes. -/
theorem eval_roleIn {D : Decls} {w : WriteBack} :
    ∀ (n : Nat) (e : Expr) {s s' : Copy.State} {u : Value}, R.Inv s.1 m → e.roleIn R ≠ .other →
      eval D (Copy.memoryWith w) n e s = .done u s' → (e.roleIn R).Holds u m
  | 0, _, _, _, _, _, _, h => by cases h
  | n + 1, .var x, s, _, _, hI, hr, h | n + 1, .move x, s, _, _, hI, hr, h => by
    obtain ⟨u', hl, hb⟩ := hI x hr
    obtain ⟨hx, -⟩ := Eval.ofExcept_done h
    obtain ⟨fr, wd⟩ := s
    change (match fr.lookup x with | some v => v.get [] | none => .error .stuck) = _ at hx
    rw [hl] at hx
    cases hx
    exact hb
  | n + 1, .field e f, s, _, _, hI, hr, h => by
    obtain ⟨u₀, s₁, h₁, h₂⟩ := Eval.bind_done h
    obtain ⟨hg, -⟩ := Eval.ofExcept_done h₂
    have hr' := Role.step_ne hr
    exact (eval_roleIn n e hI hr' h₁).step (Value.get_field_lt hg)
  | n + 1, .int _, _, _, _, _, hr, _ | n + 1, .bool _, _, _, _, _, hr, _
  | n + 1, .unit, _, _, _, _, hr, _ | n + 1, .record .., _, _, _, _, hr, _
  | n + 1, .variant .., _, _, _, _, hr, _ | n + 1, .list .., _, _, _, _, hr, _
  | n + 1, .op .., _, _, _, _, hr, _ | n + 1, .view _, _, _, _, _, hr, _
  | n + 1, .index .., _, _, _, _, hr, _ | n + 1, .fnRef .., _, _, _, _, hr, _
  | n + 1, .method .., _, _, _, _, hr, _ | n + 1, .closure .., _, _, _, _, hr, _
  | n + 1, .call .., _, _, _, _, hr, _ | n + 1, .letIn .., _, _, _, _, hr, _
  | n + 1, .varIn .., _, _, _, _, hr, _ | n + 1, .assign .., _, _, _, _, hr, _
  | n + 1, .seq .., _, _, _, _, hr, _ | n + 1, .if .., _, _, _, _, hr, _
  | n + 1, .match .., _, _, _, _, hr, _ | n + 1, .for .., _, _, _, _, hr, _
  | n + 1, .raise _, _, _, _, _, hr, _ | n + 1, .try _, _, _, _, _, hr, _
  | n + 1, .tryCatch .., _, _, _, _, hr, _ | n + 1, .while .., _, _, _, _, hr, _
  | n + 1, .loop _, _, _, _, _, hr, _ | n + 1, .break, _, _, _, _, hr, _
  | n + 1, .continue, _, _, _, _, hr, _ | n + 1, .return _, _, _, _, _, hr, _
  | n + 1, .perform .., _, _, _, _, hr, _ | n + 1, .withH .., _, _, _, _, hr, _
  | n + 1, .held .., _, _, _, _, hr, _ => absurd rfl hr

/-- What an expression gives, its role describes. -/
theorem roleIn_holds {D : Decls} {w : WriteBack} {e : Expr} {s s' : Copy.State} {u : Value}
    (hI : R.Inv s.1 m) (hd : ∃ N, ∀ n, N ≤ n → eval D (Copy.memoryWith w) n e s = .done u s') :
    (e.roleIn R).Holds u m := by
  by_cases hr : e.roleIn R = .other
  · rw [hr]; trivial
  · obtain ⟨N, hN⟩ := hd
    exact eval_roleIn N e hI hr (hN N (Nat.le_refl _))

/-- The argument at position `k` of a call whose arguments' evaluation ended: one that `ok`
accepts, evaluated from a frame that meets the roles, gives what the call passes there. -/
theorem args_at {D : Decls} {w : WriteBack} {ok : Expr → Bool} (n : Nat) :
    ∀ (k : Nat) (args : List Arg) {s s' : Copy.State} {passed : List Passed}, R.Inv s.1 m →
      R.Avoids (argsWrites args) → argWith ok k args = true →
      Eval.args (eval D (Copy.memoryWith w) n) args s = .done passed s' →
      ∃ e s₁ u s₂, ok e = true ∧ R.Inv s₁.1 m ∧ eval D (Copy.memoryWith w) n e s₁ = .done u s₂ ∧
        passed[k]? = some (Passed.ofArg e u)
  | 0, .value e :: args, s, _, _, hI, _, hp, h => by
    obtain ⟨u, s₁, h₁, h₂⟩ := Eval.bind_done h
    obtain ⟨vs, s₂, -, h₃⟩ := Eval.bind_done h₂
    cases h₃
    exact ⟨e, s, u, s₁, by simpa [argWith] using hp, hI, h₁, rfl⟩
  | k + 1, .value e :: args, s, _, _, hI, hA, hp, h => by
    obtain ⟨u, s₁, h₁, h₂⟩ := Eval.bind_done h
    obtain ⟨vs, s₂, h₃, h₄⟩ := Eval.bind_done h₂
    cases h₄
    have hI₁ : R.Inv s₁.1 m := hI.evalAt (hA.mono (List.subset_append_left _ _)) h₁
    simpa using args_at n k args hI₁ (hA.mono (List.subset_append_right _ _))
      (by simpa [argWith] using hp) h₃
  | k + 1, .inout ⟨x, ps⟩ :: args, s, _, _, hI, hA, hp, h => by
    obtain ⟨p, s₁, h₁, h₂⟩ := Eval.bind_done h
    obtain ⟨vs, s₂, h₃, h₄⟩ := Eval.bind_done h₂
    cases h₄
    have hk := Eval.Keeps.path (W := pathWrites ps) (L := pathResizes ps) (eval_keeps D w n) ps
      (List.Subset.refl _) (List.Subset.refl _) s
    rw [h₁] at hk
    have hA₁ : R.Avoids (pathWrites ps) := hA.mono fun z hz =>
      List.mem_cons_of_mem _ (List.mem_append_left _ hz)
    have hA' : R.Avoids (argsWrites args) := hA.mono fun z hz =>
      List.mem_cons_of_mem _ (List.mem_append_right _ hz)
    simpa using args_at n k args (hI.keep hA₁ hk.2) hA' (by simpa [argWith] using hp) h₃
  | 0, .inout _ :: _, _, _, _, _, _, hp, _ | 0, [], _, _, _, _, _, hp, _
  | _ + 1, [], _, _, _, _, _, hp, _ => by simp [argWith] at hp

theorem argPart_eq (R : Roles) : ∀ (k : Nat) (args : List Arg),
    argPart R k args = argWith (fun e => e.roleIn R == .part) k args
  | 0, .value _ :: _ | 0, .inout _ :: _ | 0, [] | _ + 1, [] => rfl
  | k + 1, _ :: args => by simp [argPart, argWith, argPart_eq R k args]

/-- A self-call that descends passes, at the descending position, a value smaller than the
size of the value its caller's descending parameter holds. -/
theorem args_descend {D : Decls} {w : WriteBack} (n : Nat) {k : Nat} {args : List Arg}
    {s s' : Copy.State} {passed : List Passed} (hI : R.Inv s.1 m) (hA : R.Avoids (argsWrites args))
    (hp : argPart R k args = true)
    (h : Eval.args (eval D (Copy.memoryWith w) n) args s = .done passed s') :
    Passed.sizeAt passed k < m.size := by
  rw [argPart_eq] at hp
  obtain ⟨e, s₁, u, s₂, he, hI₁, h₁, hk⟩ := args_at n k args hI hA hp h
  have hr : e.roleIn R = .part := by simpa using he
  have := eval_roleIn n e hI₁ (by rw [hr]; exact nofun) h₁
  rw [hr] at this
  simp only [Passed.sizeAt, hk, Option.map_some, Option.getD_some]
  cases e <;> exact this

/-- A step of a counter by a positive literal gives an integer moved by it. -/
theorem eval_movesBy {D : Decls} {w : WriteBack} {e : Expr} {p : Name} {grow : Bool}
    (he : e.movesBy p grow = true) {n : Nat} {s s' : Copy.State} {x : Int} {u : Value}
    (hx : s.1.lookup p = some (.int x)) (h : eval D (Copy.memoryWith w) n e s = .done u s') :
    ∃ k, 0 < k ∧ u = .int (stepped grow x k) := by
  unfold Expr.movesBy at he
  split at he
  · rename_i o kt l r
    simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true, decide_eq_true_eq] at he
    obtain ⟨⟨hl, k, hr, hk⟩, ho⟩ := he
    rw [Expr.eq_of_readVar? hl] at h
    have hr' : r = .int k := by cases r <;> simp_all [Expr.intLit?]
    rw [hr'] at h
    obtain ⟨m', us, h₅, h₆⟩ := eval_op_reaches (.of_eq h) (fun _ h => by cases h)
    obtain ⟨a, s₃, b, h₇, h₈, rfl⟩ := Eval.list_pair_reaches h₅
    obtain ⟨rfl, hl⟩ := eval_var_reaches h₇
    obtain ⟨hb, rfl⟩ := eval_int_reaches h₈
    subst hb
    rw [hx] at hl
    cases hl
    obtain ⟨x', k', r, hx', hk', hr, rfl⟩ := arith_apply h₆
    cases hx'; cases hk'
    refine ⟨k, hk, ?_⟩
    cases grow <;> simp only [Bool.false_eq_true, ↓reduceIte] at ho <;> subst ho <;>
      simp only [IntTy.arith, IntTy.check] at hr <;> split at hr <;> cases hr <;> rfl
  · cases he

/-- A counter short of its bound, stepped toward it, gets closer to it. -/
theorem countDistance_stepped {grow : Bool} {x y k : Int} (hg : if grow then x ≤ y else y ≤ x)
    (hk : 0 < k) : countDistance grow (stepped grow x k) y < countDistance grow x y := by
  cases grow <;> simp only [Bool.false_eq_true, ↓reduceIte] at hg <;>
    simp only [countDistance, stepped, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A self-call that shrinks passes a counter closer to its bound than its caller's, and the
bound unchanged, so the call's measure is smaller than the caller's. -/
theorem args_shrink {D : Decls} {w : WriteBack} (n : Nat) {k : Nat} {grow : Bool}
    {b : ShrinkBound} (hfit : m.Fits (.shrinks k grow b)) {args : List Arg} {s s' : Copy.State}
    {passed : List Passed} (hI : R.Inv s.1 m) (hA : R.Avoids (argsWrites args))
    (hp : (Descent.shrinks k grow b).calls R args = true)
    (h : Eval.args (eval D (Copy.memoryWith w) n) args s = .done passed s') :
    (Descent.shrinks k grow b).measure passed < m.size := by
  simp only [Descent.calls, Bool.and_eq_true] at hp
  obtain ⟨hpk, hpb⟩ := hp
  obtain ⟨e, s₁, u, s₂, he, hI₁, h₁, hk⟩ := args_at n k args hI hA hpk h
  unfold Expr.shrinksIn at he
  split at he
  · rename_i o t l r
    obtain ⟨p, -, hpg⟩ := (Option.any_eq_true _ _).1 he
    simp only [Bool.and_eq_true, beq_iff_eq] at hpg
    obtain ⟨hg, hmv⟩ := hpg
    obtain ⟨up, hlu, hhold⟩ := hI₁ p (by rw [hg]; exact nofun)
    rw [hg] at hhold
    obtain ⟨x, y, hx, hy, rfl, hguard, hdist⟩ := hhold
    obtain ⟨kk, hkk, rfl⟩ := eval_movesBy hmv hlu h₁
    have hint : Passed.intAt passed k = some (stepped grow x kk) := by
      simp [Passed.intAt, hk, Passed.ofArg, Passed.int?, Value.int?]
    have hb : b.valAt passed = some y := by
      cases b with
      | lit c =>
        have := hfit.2.1 c rfl
        rw [this] at hy
        cases hy
        rfl
      | param j =>
        simp only [ShrinkBound.passedIn] at hpb
        obtain ⟨e', s₃, u', s₄, he', hI₃, h₃, hj⟩ := args_at n j args hI hA hpb h
        have hr : e'.roleIn R = .limit := by simpa using he'
        have := eval_roleIn n e' hI₃ (by rw [hr]; exact nofun) h₃
        rw [hr] at this
        change u'.int? = m.limit at this
        rw [hy] at this
        simp only [ShrinkBound.valAt, Passed.intAt, hj, Option.bind_some]
        cases e' <;> exact this
    rw [hfit.1] at hguard hdist
    simp only [Descent.measure, Descent.meas, hint, hb]
    exact Nat.lt_of_lt_of_le (countDistance_stepped hguard hkk) hdist
  · simp at he

end Stilt
