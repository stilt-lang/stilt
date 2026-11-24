import Stilt.Panics.Guards
import Stilt.Panics.Reaches

/-!
# How a test runs

The tests of `Expr.test?` read their variables, and a list's length, and compare
them: from a frame, a test that reaches a value leaves the frame as it was,
and its value is the comparison of what its variables hold (`eval_test`).
-/

namespace Stilt

theorem Eval.bind_done {σ α β : Type} {m : Eval σ α} {f : α → Eval σ β} {s s' : σ} {b : β}
    (h : (m >>= f) s = .done b s') : ∃ a s₁, m s = .done a s₁ ∧ f a s₁ = .done b s' := by
  change Eval.bind m f s = _ at h
  unfold Eval.bind Outcome.bind at h
  cases hm : m s <;> rw [hm] at h <;> try cases h
  exact ⟨_, _, rfl, h⟩

theorem Eval.ofExcept_done {σ α : Type} {x : Except Fault α} {s s' : σ} {a : α}
    (h : Eval.ofExcept x s = .done a s') : x = .ok a ∧ s' = s := by
  unfold Eval.ofExcept at h
  cases x with
  | ok b => cases h; exact ⟨rfl, rfl⟩
  | error f => cases f <;> cases h

theorem Eval.list_single_reaches {σ : Type} {run : Expr → Eval σ Value} {a : Expr} {s s' : σ}
    {vs : List Value} (h : (Eval.list run [a] s).Reaches vs s') : ∃ v, (run a s).Reaches v s' ∧ vs = [v] := by
  unfold Eval.list at h
  obtain ⟨v, s₁, h₁, h₂⟩ := Eval.bind_reaches h
  obtain ⟨us, s₂, h₃, h₄⟩ := Eval.bind_reaches h₂
  unfold Eval.list at h₃
  obtain ⟨rfl, rfl⟩ := Eval.pure_reaches h₃
  obtain ⟨rfl, rfl⟩ := Eval.pure_reaches h₄
  exact ⟨v, h₁, rfl⟩

theorem Eval.list_pair_reaches {σ : Type} {run : Expr → Eval σ Value} {a b : Expr} {s s' : σ}
    {vs : List Value} (h : (Eval.list run [a, b] s).Reaches vs s') :
    ∃ u s₁ v, (run a s).Reaches u s₁ ∧ (run b s₁).Reaches v s' ∧ vs = [u, v] := by
  unfold Eval.list at h
  obtain ⟨u, s₁, h₁, h₂⟩ := Eval.bind_reaches h
  obtain ⟨us, s₂, h₃, h₄⟩ := Eval.bind_reaches h₂
  obtain ⟨v, h₅, rfl⟩ := Eval.list_single_reaches h₃
  obtain ⟨rfl, rfl⟩ := Eval.pure_reaches h₄
  exact ⟨u, s₁, v, h₁, h₅, rfl⟩

/-- An arithmetic operator that applies to two values reads two integers and gives
the integer its type's arithmetic gives. -/
theorem arith_apply {o : Arith} {k : IntTy} {x y v : Value} (h : Op.apply (.arith o k) [x, y] = .ok v) :
    ∃ a b r, x = .int a ∧ y = .int b ∧ k.arith o a b = .ok r ∧ v = .int r := by
  cases x <;> cases y <;>
    simp [Op.apply, Op.applyScalars, Value.scalar?, Op.compute, Functor.map, Except.map, Scalar.value] at h
  rename_i a b
  cases hr : k.arith o a b with
  | error f => rw [hr] at h; simp at h
  | ok r => rw [hr] at h; simp at h; exact ⟨a, b, r, rfl, rfl, hr, h.symm⟩

variable {D : Decls} {w : WriteBack}

theorem eval_var_reaches {n : Nat} {x : Name} {s s' : Copy.State} {v : Value}
    (h : (eval D (Copy.memoryWith w) n (.var x) s).Reaches v s') : s' = s ∧ s.1.lookup x = some v := by
  cases n with
  | zero => cases h
  | succ m =>
    change (Eval.inspect (fun s : Copy.State => Copy.read s.1 x []) s).Reaches _ _ at h
    obtain ⟨hr, rfl⟩ := Eval.ofExcept_reaches h
    refine ⟨rfl, ?_⟩
    simp only [Copy.read] at hr
    split at hr
    · rename_i u hu; cases hr; exact hu
    · cases hr

theorem eval_int_reaches {n : Nat} {k : Int} {s s' : Copy.State} {v : Value}
    (h : (eval D (Copy.memoryWith w) n (.int k) s).Reaches v s') : v = .int k ∧ s' = s := by
  cases n <;> cases h
  exact ⟨rfl, rfl⟩

theorem eval_op_reaches {n : Nat} {o : Op} {es : List Expr} {s s' : Copy.State} {v : Value}
    (h : (eval D (Copy.memoryWith w) n (.op o es) s).Reaches v s') (ho : ∀ k, o ≠ .world k) :
    ∃ m vs, (Eval.list (eval D (Copy.memoryWith w) m) es s).Reaches vs s' ∧ o.apply vs = .ok v := by
  cases n with
  | zero => cases h
  | succ m =>
    change ((Eval.list (eval D (Copy.memoryWith w) m) es >>= fun vs =>
      Eval.world (Copy.memoryWith w) (o.run vs)) s).Reaches _ _ at h
    obtain ⟨vs, s₁, h₁, h₂⟩ := Eval.bind_reaches h
    obtain ⟨hr, hfr⟩ := Eval.world_reaches (F := { Copy.frames with leave := _ }) h₂
    obtain ⟨hx, ha⟩ := Op.run_world ho hr
    have : s' = s₁ := Prod.ext hfr hx
    subst this
    exact ⟨m, vs, h₁, ha⟩

theorem compare_apply {c : Cmp} {k : IntTy} {x y v : Value} (h : Op.apply (.compare c k) [x, y] = .ok v) :
    ∃ a b, x = .int a ∧ y = .int b ∧ v = .bool (c.ints a b) := by
  cases x <;> cases y <;>
    simp [Op.apply, Op.applyScalars, Value.scalar?, Op.compute, Functor.map, Except.map, Scalar.value] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem len_apply {x v : Value} (h : Op.apply (.list .len) [x] = .ok v) :
    ∃ vs, x = .list vs ∧ v = .int vs.length := by
  cases x
  case list vs =>
    simp only [Op.apply, ListOp.apply, onList, Value.list?] at h
    unfold IntTy.check at h
    split at h
    · cases h; exact ⟨vs, rfl, rfl⟩
    · cases h
  all_goals simp [Op.apply, ListOp.apply, onList, Value.list?] at h

/-- What a test compares, when it ends with a value. -/
def Atom.Ran (s : Copy.Frame) (r : Bool) : Atom → Prop
  | .zero c x left => ∃ a, s.lookup x = some (.int a) ∧ r = (if left then c.ints a 0 else c.ints 0 a)
  | .len c x xs left => ∃ a vs, s.lookup x = some (.int a) ∧ s.lookup xs = some (.list vs) ∧
      r = (if left then c.ints a vs.length else c.ints vs.length a)

/-- `xs.len()` that ends with a value reads the list `xs` holds. -/
theorem eval_len_reaches {n : Nat} {xs : Name} {s s' : Copy.State} {v : Value}
    (h : (eval D (Copy.memoryWith w) n (.op (.list .len) [.var xs]) s).Reaches v s') :
    s' = s ∧ ∃ vs, s.1.lookup xs = some (.list vs) ∧ v = .int vs.length := by
  obtain ⟨m, us, h₁, h₂⟩ := eval_op_reaches h (fun _ h => by cases h)
  obtain ⟨u, h₃, rfl⟩ := Eval.list_single_reaches h₁
  obtain ⟨rfl, hl⟩ := eval_var_reaches h₃
  obtain ⟨vs, rfl, rfl⟩ := len_apply h₂
  exact ⟨rfl, vs, hl, rfl⟩

/-- A test that ends with a value leaves the frame as it was, and compares its
variables' values. -/
theorem eval_test {c : Expr} {t : Atom} (hc : c.test? = some t) {n : Nat} {s s' : Copy.State}
    {v : Value} (h : (eval D (Copy.memoryWith w) n c s).Reaches v s') :
    s' = s ∧ ∃ r, v = .bool r ∧ t.Ran s.1 r := by
  obtain ⟨k, ⟨cmp, d, rfl, rfl⟩ | ⟨cmp, d, rfl, rfl⟩ | ⟨cmp, i, xs, rfl, rfl⟩ | ⟨cmp, i, xs, rfl, rfl⟩⟩ :=
    Expr.test?_spec hc <;>
  · obtain ⟨m, vs, h₁, h₂⟩ := eval_op_reaches h (fun _ h => by cases h)
    obtain ⟨u, s₁, u', h₃, h₄, rfl⟩ := Eval.list_pair_reaches h₁
    obtain ⟨a, b, rfl, rfl, rfl⟩ := compare_apply h₂
    first
    | (obtain ⟨rfl, hl⟩ := eval_var_reaches h₃
       obtain ⟨hb, rfl⟩ := eval_int_reaches h₄
       cases hb
       exact ⟨rfl, _, rfl, a, hl, by simp⟩)
    | (obtain ⟨hb, rfl⟩ := eval_int_reaches h₃
       obtain ⟨rfl, hl⟩ := eval_var_reaches h₄
       cases hb
       exact ⟨rfl, _, rfl, b, hl, by simp⟩)
    | (obtain ⟨rfl, hl⟩ := eval_var_reaches h₃
       obtain ⟨rfl, vs, hx, hb⟩ := eval_len_reaches h₄
       cases hb
       exact ⟨rfl, _, rfl, a, vs, hl, hx, by simp⟩)
    | (obtain ⟨rfl, vs, hx, hb⟩ := eval_len_reaches h₃
       obtain ⟨rfl, hl⟩ := eval_var_reaches h₄
       cases hb
       exact ⟨rfl, _, rfl, b, vs, hl, hx, by simp⟩)

end Stilt
