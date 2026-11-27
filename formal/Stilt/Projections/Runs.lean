import Stilt.Projections.Paths

/-!
# A projection's body runs one `yield`

Every run of code that passes `Expr.once` yields as its paths do (`eval_yielding`): the
statements of a block run in turn, a branch runs one of its arms, a `catch`'s handler runs from
what its operand, which runs no `yield`, kept, and a `yield` calls the access once and adds its
value to the list kept. So the body of a projection that passes the checks of projections,
run from where the list is empty, ends with exactly one value in it on every path to its end
or to a `return`, and with at most one on every path to a raise or a performance
(`Program.projectionsChecked.yields`, projections.once-on-every-path).
-/

namespace Stilt

/-! ## The counts of paths -/

theorem Yields.join_left {a b : Yields} (h : a.join b ≠ none) :
    a ≠ none ∧ ∀ m, a = some (some m) → a.join b = some (some m) := by
  rcases a with _ | _ | m <;> rcases b with _ | _ | m' <;> simp_all [Yields.join]

theorem Yields.join_right {a b : Yields} (h : a.join b ≠ none) :
    b ≠ none ∧ ∀ m, b = some (some m) → a.join b = some (some m) := by
  rcases a with _ | _ | m <;> rcases b with _ | _ | m' <;> simp_all [Yields.join]

theorem Yields.andThen_ne {r : Yields} {f : Nat → Yields} (h : r.andThen f ≠ none) :
    r ≠ none ∧ ∀ m, r = some (some m) → r.andThen f = f m := by
  rcases r with _ | _ | m <;> simp_all [Yields.andThen]

theorem Yields.kept_ne {n : Nat} {ok : Bool} (h : Yields.kept n ok ≠ none) : ok = true := by
  cases ok <;> simp_all [Yields.kept]

theorem armsOnce_cons {res k : Name} {caught : Bool} {n : Nat} {p : Pattern} {bs : List Name}
    {guard : Option Expr} {body : Expr} {arms : List Arm}
    (h : armsOnce res k caught n (⟨p, bs, guard, body⟩ :: arms) ≠ none) :
    res ∉ bs ∧ (∀ g, guard = some g → g.keeps res k caught n = true) ∧
      armsOnce res k caught n (⟨p, bs, guard, body⟩ :: arms) =
        (body.once res k caught n).join (armsOnce res k caught n arms) := by
  cases guard with
  | none =>
    simp only [armsOnce, Bool.and_true] at h ⊢
    split at h
    · rename_i hc
      refine ⟨?_, (fun g hg => by cases hg), ?_⟩
      · simp only [Bool.and_eq_true] at hc
        simpa using hc.1
      · simp only [hc, ↓reduceIte]
    · exact absurd rfl h
  | some g =>
    simp only [armsOnce] at h ⊢
    split at h
    · rename_i hc
      refine ⟨?_, fun g' hg => ?_, ?_⟩
      · simp only [Bool.and_eq_true] at hc
        simpa using hc.1.1
      · cases hg
        simp only [Bool.and_eq_true] at hc
        exact hc.2
      · simp only [hc, ↓reduceIte]
    · exact absurd rfl h

theorem armsOnce_mem {res k : Name} {caught : Bool} {n : Nat} :
    ∀ {arms : List Arm} {arm : Arm}, armsOnce res k caught n arms ≠ none → arm ∈ arms →
      res ∉ arm.binders ∧ (∀ g, arm.guard = some g → g.keeps res k caught n = true) ∧
        arm.body.once res k caught n ≠ none ∧
          ∀ m, arm.body.once res k caught n = some (some m) → armsOnce res k caught n arms = some (some m)
  | ⟨p, bs, guard, body⟩ :: arms, arm, h, hm => by
    obtain ⟨hb, hgd, he⟩ := armsOnce_cons h
    rw [he] at h ⊢
    rcases List.mem_cons.1 hm with rfl | hm
    · exact ⟨hb, hgd, (Yields.join_left h).1, (Yields.join_left h).2⟩
    · obtain ⟨h₁, h₂, h₃, h₄⟩ := armsOnce_mem (Yields.join_right h).1 hm
      exact ⟨h₁, h₂, h₃, fun m hb => (Yields.join_right h).2 m (h₄ m hb)⟩

/-! ## Code that runs no `yield` -/

section

variable (D : Decls)

/-- Code that writes no `res` and ends with no jump but a `return` once a `yield` has run
yields as it started. -/
theorem keeps_yielding' (fuel : Nat) {e : Expr} {res : Name} {n : Nat} {N : List Name}
    (hres : res ∉ e.writes) (hex : e.exits false (n == 1) = true) (hn : n ≤ 1) :
    Eval.Yielding res N n (some (some n)) (fun _ => True) (eval D Copy.memory fuel e) := fun s hs =>
  Outcome.Yielding.of_keeps hres hn hs
    (eval_keeps D .leftToRight fuel e e.writes e.resizes (fun _ h => h) (fun _ h => h) s)
    (eval_exits D Copy.memory fuel false (n == 1) e hex s)

theorem Expr.keeps_parts {res k : Name} {caught : Bool} {n : Nat} {e : Expr}
    (h : e.keeps res k caught n = true) : res ∉ e.writes ∧ e.exits false (n == 1) = true := by
  simp only [Expr.keeps, Bool.and_eq_true] at h
  exact ⟨by simpa using h.1.1.1.2, h.1.2⟩

theorem keeps_yielding (fuel : Nat) {e : Expr} {res k : Name} {caught : Bool} {n : Nat} {N : List Name}
    (h : e.keeps res k caught n = true) (hn : n ≤ 1) :
    Eval.Yielding res N n (some (some n)) (fun _ => True) (eval D Copy.memory fuel e) :=
  keeps_yielding' D fuel (Expr.keeps_parts h).1 (Expr.keeps_parts h).2 hn

/-- Code whose `once` is that of code that runs no `yield`. -/
theorem kept_yielding (fuel : Nat) {e : Expr} {res k : Name} {caught : Bool} {n : Nat} {N : List Name}
    (he : e.once res k caught n = Yields.kept n (e.keeps res k caught n)) (hn : n ≤ 1)
    (hr : e.once res k caught n ≠ none) :
    Eval.Yielding res N n (e.once res k caught n) (fun _ => True) (eval D Copy.memory fuel e) := by
  rw [he] at hr ⊢
  have hk := Yields.kept_ne hr
  rw [hk]
  exact keeps_yielding D fuel hk hn

end

end Stilt
