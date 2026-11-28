import Stilt.Panics.Signs
import Stilt.Panics.Keys
import Stilt.Panics.Kept
import Stilt.Panics.Steps

/-!
# What known signs mean

An expression known non-negative that ends with a value ends with an integer that isn't
negative (`eval_nonneg`), and the facts that a binding gives its name hold of the frame it
binds the name in (`bindFacts_holds`).
-/

namespace Stilt

theorem check_len_ok {n : Int} (hn : 0 ≤ n) {u : Value}
    (h : (Value.int <$> IntTy.i64.check n) = .ok u) : ∃ k, u = .int k ∧ 0 ≤ k := by
  unfold IntTy.check at h
  split at h
  · cases h; exact ⟨n, rfl, hn⟩
  · cases h

/-- `len()` that applies gives an integer that isn't negative. -/
theorem Op.givesLen_apply {o : Op} (ho : o.givesLen = true) {v u : Value} (h : o.apply [v] = .ok u) :
    ∃ k, u = .int k ∧ 0 ≤ k := by
  cases o <;> simp only [Op.givesLen, reduceCtorEq] at ho
  case len =>
    cases v <;> simp [Op.apply, Op.applyScalars, Value.scalar?, Op.compute, Functor.map, Except.map] at h
    rename_i s
    unfold Str.len IntTy.check at h
    by_cases hc : IntTy.i64.Contains (s.utf8ByteSize : Int) <;> simp [hc, Scalar.value] at h
    exact ⟨_, h.symm, by omega⟩
  case list l =>
    cases l <;> simp only [reduceCtorEq] at ho
    simp only [Op.apply, ListOp.apply, onList] at h
    split at h
    · exact check_len_ok (by omega) h
    · cases h
  case map l =>
    cases l <;> simp only [reduceCtorEq] at ho
    simp only [Op.apply, MapOp.apply, onMap] at h
    split at h
    · exact check_len_ok (by omega) h
    · cases h
  case set l =>
    cases l <;> simp only [reduceCtorEq] at ho
    simp only [Op.apply, SetOp.apply, onSet] at h
    split at h
    · exact check_len_ok (by omega) h
    · cases h

/-- `+` or `*` of integers that aren't negative, when it fits its type. -/
theorem IntTy.arith_nonneg {k : IntTy} {o : Arith} {a b r : Int} (ho : (o == .add || o == .mul) = true)
    (h : k.arith o a b = .ok r) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ r := by
  cases o <;> simp only [beq_iff_eq, Bool.or_eq_true, reduceCtorEq, or_self] at ho <;>
    simp only [IntTy.arith, IntTy.check] at h <;> split at h <;> simp at h <;> subst h
  · omega
  · exact Int.mul_nonneg ha hb

variable {D : Decls} {w : WriteBack}

/-- An expression known non-negative, from a frame that meets the facts it was known by,
ends, when it reaches a value, with an integer that isn't negative (facts.known-signs). -/
theorem eval_nonneg : ∀ (e : Expr) (G : List Known) (n : Nat) {s s' : Copy.State} {v : Value},
    e.nonnegIn G = true → Frame.Meets G s.1 → (eval D (Copy.memoryWith w) n e s).Reaches v s' →
      ∃ k, v = .int k ∧ 0 ≤ k
  | .int a, _, _, _, _, _, he, _, h => by
    obtain ⟨rfl, rfl⟩ := eval_int_reaches h
    exact ⟨a, rfl, by simpa [Expr.nonnegIn] using he⟩
  | .var a, G, _, _, _, _, he, hz, h => by
    obtain ⟨rfl, hl⟩ := eval_var_reaches h
    obtain ⟨k, hk, h0⟩ := hz _ (by simpa [Expr.nonnegIn] using he)
    rw [hl] at hk
    cases hk
    exact ⟨k, rfl, h0⟩
  | .op o es, G, n, s, s', v, he, hz, h => by
    rcases es with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [Expr.nonnegIn] at he
    · have hg : o.givesLen = true := by simpa [Expr.nonnegIn] using he
      obtain ⟨m, vs, h₁, h₂⟩ := eval_op_reaches h (fun k h => by subst h; simp [Op.givesLen] at hg)
      obtain ⟨u, _, rfl⟩ := Eval.list_single_reaches h₁
      exact Op.givesLen_apply hg h₂
    · cases o
      case arith o t =>
        simp only [Expr.nonnegIn, Bool.and_eq_true] at he
        obtain ⟨m, vs, h₁, h₂⟩ := eval_op_reaches h (fun _ h => by cases h)
        obtain ⟨u, s₁, u', h₃, h₄, rfl⟩ := Eval.list_pair_reaches h₁
        obtain ⟨x, rfl, hx⟩ := eval_nonneg a G m he.1.2 hz h₃
        have hz₁ := hz.keep (h₃.keeps (eval_keeps D w m a a.writes a.resizes (List.Subset.refl _)
          (List.Subset.refl _) s)).2
        obtain ⟨y, rfl, hy⟩ := eval_nonneg b _ m he.2 hz₁ h₄
        obtain ⟨_, _, r, ha, hb, hr, rfl⟩ := arith_apply h₂
        cases ha; cases hb
        exact ⟨r, rfl, IntTy.arith_nonneg he.1.1 hr hx hy⟩
      all_goals simp [Expr.nonnegIn] at he
    · simp [Expr.nonnegIn] at he
  | .move _, _, _, _, _, _, he, _, _ | .bool _, _, _, _, _, _, he, _, _ | .unit, _, _, _, _, _, he, _, _
  | .break, _, _, _, _, _, he, _, _ | .continue, _, _, _, _, _, he, _, _
  | .record .., _, _, _, _, _, he, _, _ | .variant .., _, _, _, _, _, he, _, _
  | .list .., _, _, _, _, _, he, _, _ | .view _, _, _, _, _, _, he, _, _
  | .field .., _, _, _, _, _, he, _, _ | .index .., _, _, _, _, _, he, _, _
  | .fnRef .., _, _, _, _, _, he, _, _ | .method .., _, _, _, _, _, he, _, _
  | .closure .., _, _, _, _, _, he, _, _ | .call .., _, _, _, _, _, he, _, _
  | .letIn .., _, _, _, _, _, he, _, _ | .varIn .., _, _, _, _, _, he, _, _
  | .assign .., _, _, _, _, _, he, _, _ | .seq .., _, _, _, _, _, he, _, _
  | .if .., _, _, _, _, _, he, _, _ | .match .., _, _, _, _, _, he, _, _
  | .for .., _, _, _, _, _, he, _, _ | .raise _, _, _, _, _, _, he, _, _
  | .try _, _, _, _, _, _, he, _, _ | .form .., _, _, _, _, _, he, _, _
  | .tryCatch .., _, _, _, _, _, he, _, _ | .while .., _, _, _, _, _, he, _, _
  | .loop _, _, _, _, _, _, he, _, _ | .return _, _, _, _, _, _, he, _, _
  | .perform .., _, _, _, _, _, he, _, _ | .withH .., _, _, _, _, _, he, _, _
  | .held .., _, _, _, _, _, he, _, _ => by simp [Expr.nonnegIn] at he

/-- The facts that a binding gives its name hold of the frame it binds the name in, where
its initial value reached its value from a frame that met the facts before it. -/
theorem bindFacts_holds {G : List Known} {x : Name} {init : Expr} {n : Nat} {s s' : Copy.State}
    {v : Value} (hz : Frame.Meets G s.1) (h : (eval D (Copy.memoryWith w) n init s).Reaches v s') :
    Frame.Meets (init.bindFacts G x) ((x, v) :: s'.1) := by
  unfold Expr.bindFacts
  refine Frame.Meets.append ?_ ?_
  · split
    · rename_i hn
      obtain ⟨k, rfl, hk⟩ := eval_nonneg init G n hn hz h
      intro f hf
      simp only [List.mem_singleton] at hf
      subst hf
      exact ⟨k, by simp, hk⟩
    · exact Frame.Meets.nil _
  · split
    · rename_i a
      obtain ⟨rfl, hl⟩ := eval_var_reaches h
      intro f hf
      obtain ⟨g, hg, hfg⟩ := List.mem_flatMap.1 hf
      have hx : ((x, v) :: s'.1).lookup x = some v := by simp [List.lookup]
      have hy : ∀ (y : Name), y ≠ x → ((x, v) :: s'.1).lookup y = s'.1.lookup y := fun y hne => by
        simp [List.lookup, show (y == x) = false by simpa using hne]
      have hg' := hz _ hg
      cases g with
      | has m kt =>
        cases kt with
        | var k =>
          simp only [Known.alias] at hfg
          split at hfg
          · rename_i hk
            obtain ⟨rfl, hmx⟩ := hk
            obtain rfl := List.mem_singleton.1 hfg
            obtain ⟨mv, u, es, d, hm, hu, hmap, hhas⟩ := hg'
            simp only [KeyTerm.value] at hu
            rw [hl] at hu
            cases hu
            have hne : (m == x) = false := by simpa using hmx
            exact ⟨mv, v, es, d, by simp [List.lookup, hne, hm], by simp [KeyTerm.value], hmap, hhas⟩
          · cases hfg
        | _ => simp [Known.alias] at hfg
      | nonzero y =>
        simp only [Known.alias] at hfg
        split at hfg
        · rename_i hya; subst hya
          obtain rfl := List.mem_singleton.1 hfg
          obtain ⟨k, hk, hk0⟩ := hg'
          rw [hl] at hk; cases hk
          exact ⟨k, hx, hk0⟩
        · cases hfg
      | nonneg y =>
        simp only [Known.alias] at hfg
        split at hfg
        · rename_i hya; subst hya
          obtain rfl := List.mem_singleton.1 hfg
          obtain ⟨k, hk, hk0⟩ := hg'
          rw [hl] at hk; cases hk
          exact ⟨k, hx, hk0⟩
        · cases hfg
      | atLeast y c =>
        simp only [Known.alias] at hfg
        split at hfg
        · rename_i hya; subst hya
          obtain rfl := List.mem_singleton.1 hfg
          obtain ⟨k, hk, hk0⟩ := hg'
          rw [hl] at hk; cases hk
          exact ⟨k, hx, hk0⟩
        · cases hfg
      | below y xs =>
        simp only [Known.alias] at hfg
        split at hfg
        · rename_i hya; obtain ⟨rfl, hxs⟩ := hya
          obtain rfl := List.mem_singleton.1 hfg
          obtain ⟨k, vs, hk, hv, hlt⟩ := hg'
          rw [hl] at hk; cases hk
          exact ⟨k, vs, hx, by rw [hy _ hxs]; exact hv, hlt⟩
        · cases hfg
      | belowBy y xs c =>
        simp only [Known.alias] at hfg
        split at hfg
        · rename_i hya; obtain ⟨rfl, hxs⟩ := hya
          obtain rfl := List.mem_singleton.1 hfg
          obtain ⟨k, vs, hk, hv, hlt⟩ := hg'
          rw [hl] at hk; cases hk
          exact ⟨k, vs, hx, by rw [hy _ hxs]; exact hv, hlt⟩
        · cases hfg
      | longer _ _ => simp [Known.alias] at hfg
    · rename_i k
      obtain ⟨rfl, rfl⟩ := eval_int_reaches h
      split
      · rename_i hk
        intro f hf
        obtain rfl := List.mem_singleton.1 hf
        exact ⟨k, by simp [List.lookup], hk⟩
      · exact Frame.Meets.nil _
    · exact Frame.Meets.nil _

/-- A `let` or a `var`, whose body counts on the facts its binding gives its name. -/
theorem Eval.PanicFree.bindInit {lim : Limited} {α : Type} {P : α → Prop} {G : List Known} {x : Name}
    {init : Expr} {n : Nat} {m : Eval Copy.State α}
    (hi : Eval.PanicFree lim G (Value.PanicFree lim) (eval D (Copy.memoryWith w) n init))
    (hb : Eval.PanicFree lim (withoutNames (withoutNames G init.writes) [x] ++ init.bindFacts G x) P m) :
    Eval.PanicFree lim G P
      (eval D (Copy.memoryWith w) n init >>= fun v => Eval.withInit (Copy.memoryWith w) x init v m) := by
  intro s hs hz
  refine Outcome.PanicFree.bind (hi s hs hz) fun v s' hr hv hs' => ?_
  have hk := (hr.keeps (eval_keeps D w n init init.writes init.resizes (List.Subset.refl _)
    (List.Subset.refl _) s)).2
  have : Eval.withInit (Copy.memoryWith w) x init v m = Eval.withVar (Copy.memoryWith w) x v m := by
    funext s
    unfold Eval.withInit Eval.withVar Memory.bindInit
    cases init <;> rfl
  show Outcome.PanicFree lim P (Eval.withInit (Copy.memoryWith w) x init v m s')
  rw [this]
  exact (hb ((Copy.memoryWith w).bind s' x v) ⟨hs'.1.cons (x := x) hv, hs'.2⟩
    (((hz.keep hk).bind x v).append (bindFacts_holds hz hr))).unbind w

end Stilt
