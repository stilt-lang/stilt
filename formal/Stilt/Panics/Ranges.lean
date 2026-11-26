import Stilt.Panics.Runs

/-!
# Range loops and guarded indexes

A `for` over a range from an integer literal `a` binds its variable, at each
turn, to an integer no less than `a`, so it isn't zero when `a` is positive and
isn't negative when `a` isn't (facts.known-signs), and over a range from a variable
known not negative, to one that isn't negative either; over `a..xs.len()`, to one
below the length of the list `xs` held when the loop started, which it still
holds while the body writes no `xs` (facts.range-loops). An index `xs[i]` whose
facts give `i >= 0` and `i < xs.len()` is within the list's bounds
(facts.guards).
-/

namespace Stilt

variable {lim : Limited}

/-- What the iterable of a `for` over `a..xs.len() - c` leaves: that `xs` holds a
list longer than each element of the range plus `c`. -/
def Expr.rangeAfter : Expr → List Value → List Known
  | .op (.list (.range false)) [lo, hi], vs =>
    if lo.isLow then
      match hi.lenLess? with
      | some (xs, c) => vs.filterMap fun u => match u with
        | .int k => some (.longer xs (k + c))
        | _ => none
      | none => []
    else []
  | _, _ => []

theorem range_apply {inclusive : Bool} {u u' v : Value}
    (h : Op.apply (.list (.range inclusive)) [u, u'] = .ok v) :
    ∃ a b, u = .int a ∧ u' = .int b ∧ v = .list (rangeValues a b inclusive) := by
  cases u <;> cases u' <;> simp [Op.apply, ListOp.apply, Value.int?] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem mem_rangeValues {a b : Int} {inclusive : Bool} {u : Value} (h : u ∈ rangeValues a b inclusive) :
    ∃ k, u = .int k ∧ a ≤ k ∧ (inclusive = false → k < b) := by
  simp only [rangeValues, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  refine ⟨_, rfl, by omega, fun hinc => ?_⟩
  subst hinc
  simp only [Bool.false_eq_true, ↓reduceIte] at hi
  omega

variable {D : Decls} {w : WriteBack}

/-- `xs.len() - c` reaches, from the frame it starts in, the length of `xs` less `c`. -/
theorem eval_lenLess_reaches {n : Nat} {hi : Expr} {xs : Name} {c : Int} {s s' : Copy.State} {v : Value}
    (hx : hi.lenLess? = some (xs, c)) (h : (eval D (Copy.memoryWith w) n hi s).Reaches v s') :
    s' = s ∧ ∃ ws, s.1.lookup xs = some (.list ws) ∧ v = .int (ws.length - c) := by
  obtain ⟨-, ⟨rfl, rfl⟩ | rfl⟩ := Expr.eq_of_lenLess? hx
  · obtain ⟨rfl, ws, hw, rfl⟩ := eval_len_reaches h
    exact ⟨rfl, ws, hw, by simp⟩
  · obtain ⟨m, vs, h₁, h₂⟩ := eval_op_reaches h (fun _ h => by cases h)
    obtain ⟨u, s₁, u', h₃, h₄, rfl⟩ := Eval.list_pair_reaches h₁
    obtain ⟨rfl, ws, hw, rfl⟩ := eval_len_reaches h₃
    obtain ⟨rfl, rfl⟩ := eval_int_reaches h₄
    obtain ⟨a, b, r, ha, hb, hr, rfl⟩ := arith_apply h₂
    cases ha; cases hb
    simp only [IntTy.arith, IntTy.check] at hr
    split at hr
    · cases hr; exact ⟨rfl, ws, hw, rfl⟩
    · cases hr

/-- A range from a literal or a variable reaches the integers it bounds, from
the literal or the variable's value; up to `xs.len() - c`, from the frame it
started in, the bound `xs`'s length less `c`. -/
theorem eval_range_reaches {n : Nat} {inclusive : Bool} {lo hi : Expr} (hlo : lo.isLow = true)
    {s s' : Copy.State} {v : Value}
    (h : (eval D (Copy.memoryWith w) n (.op (.list (.range inclusive)) [lo, hi]) s).Reaches v s') :
    ∃ a b, v = .list (rangeValues a b inclusive) ∧ (∀ k, lo = .int k → a = k) ∧
      (∀ y, lo = .var y → s.1.lookup y = some (.int a)) ∧ ∀ xs c, hi.lenLess? = some (xs, c) →
        s' = s ∧ ∃ ws, s.1.lookup xs = some (.list ws) ∧ b = ws.length - c := by
  obtain ⟨m, vs, h₁, h₂⟩ := eval_op_reaches h (fun _ h => by cases h)
  obtain ⟨u, s₁, u', h₃, h₄, rfl⟩ := Eval.list_pair_reaches h₁
  have hs₁ : s₁ = s ∧ (∀ k, lo = .int k → u = .int k) ∧ ∀ y, lo = .var y → s.1.lookup y = some u := by
    cases lo <;> simp only [Expr.isLow, Bool.false_eq_true] at hlo
    case int k =>
      obtain ⟨rfl, rfl⟩ := eval_int_reaches h₃
      exact ⟨rfl, fun k hk => (by cases hk; rfl), fun _ hy => (by cases hy)⟩
    case var y =>
      obtain ⟨rfl, hl⟩ := eval_var_reaches h₃
      exact ⟨rfl, fun _ hk => (by cases hk), fun y hy => (by cases hy; exact hl)⟩
  obtain ⟨rfl, hint, hvar⟩ := hs₁
  obtain ⟨a, b, rfl, rfl, rfl⟩ := range_apply h₂
  refine ⟨a, b, rfl, fun k hk => by cases hint k hk; rfl, hvar, fun xs c hx => ?_⟩
  obtain ⟨rfl, ws, hw, hb⟩ := eval_lenLess_reaches hx h₄
  cases hb
  exact ⟨rfl, ws, hw, rfl⟩

/-- What a range's run leaves holds once it has run. -/
theorem range_after (n : Nat) (e : Expr) {s s' : Copy.State} {v : Value}
    (h : (eval D (Copy.memoryWith w) n e s).Reaches v s') (vs : List Value) (hv : v = .list vs) :
    Frame.Meets (e.rangeAfter vs) s'.1 := by
  unfold Expr.rangeAfter
  split
  · rename_i lo hi
    split
    · rename_i hlo
      split
      · rename_i xs c hx
        obtain ⟨a, b, hb, -, -, hlen⟩ := eval_range_reaches hlo h
        obtain ⟨rfl, ws, hw, rfl⟩ := hlen xs c hx
        rw [hv] at hb
        cases hb
        intro f hf
        simp only [List.mem_filterMap] at hf
        obtain ⟨u, hu, hf⟩ := hf
        obtain ⟨k, rfl, _, hk⟩ := mem_rangeValues hu
        cases hf
        exact ⟨ws, hw, by have := hk rfl; omega⟩
      · exact Frame.Meets.nil _
    · exact Frame.Meets.nil _
  · exact Frame.Meets.nil _

/-- What a range's start gives an element of the range no less than it. -/
theorem lowFacts_holds {G : List Known} {x : Name} {lo : Expr} {s s'' : Copy.Frame} {a k : Int}
    (hz : Frame.Meets G s) (hint : ∀ k, lo = .int k → a = k) (hvar : ∀ y, lo = .var y → s.lookup y = some (.int a))
    (hak : a ≤ k) : Frame.Meets (lo.lowFacts G x) ((x, .int k) :: s'') := by
  intro f hf
  cases lo <;> simp only [Expr.lowFacts, List.not_mem_nil] at hf
  case int a' =>
    cases hint a' rfl
    simp only [List.mem_append] at hf
    rcases hf with (hf | hf) | hf
    · split at hf
      · simp only [List.mem_singleton] at hf; subst hf
        exact ⟨k, by simp, by omega⟩
      · cases hf
    · split at hf
      · simp only [List.mem_singleton] at hf; subst hf
        exact ⟨k, by simp, by omega⟩
      · cases hf
    · simp only [List.mem_singleton] at hf; subst hf
      exact ⟨k, by simp, hak⟩
  case var y =>
    split at hf
    · rename_i hy
      simp only [List.mem_singleton] at hf; subst hf
      obtain ⟨n, hl, h0⟩ := hz _ hy
      rw [hvar y rfl] at hl
      cases hl
      exact ⟨k, by simp, by omega⟩
    · cases hf

/-- Each element of a range from a literal or a variable gives the loop's variable
the facts that `Expr.rangeFacts` names, from a frame that meets those of its run that
the body can't write. -/
theorem range_elem {G : List Known} (n : Nat) (x : Name) (body e : Expr) {s s' : Copy.State}
    {v : Value} (hz : Frame.Meets G s.1) (h : (eval D (Copy.memoryWith w) n e s).Reaches v s') (vs : List Value)
    (hv : v = .list vs) (u : Value) (hu : u ∈ vs) (s'' : Copy.Frame)
    (hm : Frame.Meets (withoutWrites (e.rangeAfter vs) body.writes body.resizes) s'') :
    Frame.Meets (e.rangeFacts G x body) ((x, u) :: s'') := by
  unfold Expr.rangeFacts
  split
  · rename_i inclusive lo hi
    split
    · rename_i hlo
      obtain ⟨a, b, hb, hint, hvar, hlen⟩ := eval_range_reaches hlo h
      rw [hv] at hb
      cases hb
      obtain ⟨k, rfl, hak, hkb⟩ := mem_rangeValues hu
      intro f hf
      rcases List.mem_append.1 hf with hf | hf
      · exact lowFacts_holds hz hint hvar hak f hf
      · split at hf
        · rename_i xs c hx _
          split at hf
          · rename_i hc
            simp only [List.mem_singleton] at hf; subst hf
            have hl : Known.longer xs (k + c) ∈ withoutWrites (Expr.rangeAfter (.op (.list (.range false))
                [lo, hi]) (rangeValues a b false)) body.writes body.resizes := by
              refine mem_withoutWrites.2 ⟨?_, by simp [Known.valReads], by simpa [Known.lenReads] using hc.2⟩
              simp only [Expr.rangeAfter, hlo, hx, ite_true, List.mem_filterMap]
              exact ⟨_, hu, rfl⟩
            obtain ⟨ws, hw, hlt⟩ := hm _ hl
            have hne : (xs == x) = false := by simpa using hc.1
            exact ⟨k, ws, by simp, by simpa [List.lookup_cons, hne] using hw, hlt⟩
          · cases hf
        · cases hf
    · exact Frame.Meets.nil _
  · exact Frame.Meets.nil _

/-- What `Known.bounds` reads off a frame that meets its facts: `j` and `xs` hold an
integer and a list, and `j + k` is an index of the list. -/
theorem Known.bounds_spec {G : List Known} {j xs : Name} {k : Int} (hb : Known.bounds G j xs k = true)
    {s : Copy.Frame} (hz : Frame.Meets G s) :
    ∃ nj ws, s.lookup j = some (.int nj) ∧ s.lookup xs = some (.list ws) ∧ 0 ≤ nj + k ∧
      nj + k < ws.length := by
  unfold Known.bounds at hb
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hb
  obtain ⟨hlo, hhi⟩ := hb
  have lo : ∃ n, s.lookup j = some (.int n) ∧ 0 ≤ n + k := by
    rcases hlo with ⟨hk, hn⟩ | ⟨f, hf, hfm⟩
    · obtain ⟨n, hl, h0⟩ := hz _ hn
      exact ⟨n, hl, by omega⟩
    · cases f <;> simp only [Bool.false_eq_true] at hfm
      rename_i y a
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfm
      obtain ⟨rfl, hak⟩ := hfm
      obtain ⟨n, hl, han⟩ := hz _ hf
      exact ⟨n, hl, by omega⟩
  have hi : ∃ n ws, s.lookup j = some (.int n) ∧ s.lookup xs = some (.list ws) ∧ n + k < ws.length := by
    rcases hhi with ⟨hk, hbl⟩ | ⟨f, hf, hfm⟩
    · obtain ⟨n, ws, hl, hw, hlt⟩ := hz _ hbl
      exact ⟨n, ws, hl, hw, by omega⟩
    · cases f <;> simp only [Bool.false_eq_true] at hfm
      rename_i y ys c
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hfm
      obtain ⟨⟨rfl, rfl⟩, hkc⟩ := hfm
      obtain ⟨n, ws, hl, hw, hlt⟩ := hz _ hf
      exact ⟨n, ws, hl, hw, by omega⟩
  obtain ⟨n, hl, h0⟩ := lo
  obtain ⟨n', ws, hl', hw, hlt⟩ := hi
  rw [hl] at hl'
  cases hl'
  exact ⟨n, ws, hl, hw, h0, hlt⟩

/-- `j op c`, on `i64`, from a frame where `j` holds an integer, ends as the
arithmetic of `i64` gives, with fuel enough to read its operands. -/
theorem eval_arith_lit (m : Nat) (o : Arith) {j : Name} {c nj : Int} {s : Copy.State}
    (hj : s.1.lookup j = some (.int nj)) :
    eval D (Copy.memoryWith w) (m + 2) (.op (.arith o .i64) [.var j, .int c]) s =
      match IntTy.i64.arith o nj c with
      | .ok r => .done (.int r) s
      | .error f => .fault f s := by
  have hl : Eval.list (eval D (Copy.memoryWith w) (m + 1)) [.var j, .int c] s =
      .done [.int nj, .int c] s := by
    simp [Eval.list, eval, bind, Eval.bind, Outcome.bind, pure, Eval.pure, Eval.inspect,
      Eval.ofExcept, Copy.memoryWith, Frames.withWorld, Copy.frames, Copy.read, hj, Value.get]
  show Eval.bind (Eval.list (eval D (Copy.memoryWith w) (m + 1)) _)
    (fun vs => Eval.world (Copy.memoryWith w) (Op.run (.arith o .i64) vs)) s = _
  simp only [Eval.world_memoryWith_of_ne w (o := .arith o .i64) (fun _ h => by cases h)]
  unfold Eval.bind Outcome.bind
  rw [hl]
  cases h : IntTy.i64.arith o nj c <;>
    simp [Eval.ofExcept, Op.apply, Op.applyScalars, Value.scalar?, Op.compute, Functor.map, Except.map,
      Scalar.value, List.mapM, List.mapM.loop, h]

/-- An index `j`, `j + k` or `j - k` runs out of fuel, overflows, or ends with
`j`'s integer plus `k`, from a frame where `j` holds one. -/
theorem eval_offset (n : Nat) {j : Name} {k : Int} {i : Expr} (hi : i.offset? = some (j, k))
    {s : Copy.State} {nj : Int} (hj : s.1.lookup j = some (.int nj)) :
    eval D (Copy.memoryWith w) n i s = .outOfFuel ∨
      eval D (Copy.memoryWith w) n i s = .panicked .overflow s ∨
      eval D (Copy.memoryWith w) n i s = .done (.int (nj + k)) s := by
  rcases Expr.eq_of_offset? hi with ⟨rfl, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · rcases n with _ | m
    · exact .inl rfl
    · refine .inr (.inr ?_)
      simp [eval, Eval.inspect, Eval.ofExcept, Copy.memoryWith, Frames.withWorld, Copy.frames, Copy.read, hj, Value.get]
  all_goals
    rcases n with _ | _ | m
    · exact .inl rfl
    · exact .inl rfl
    · rw [eval_arith_lit m _ hj]
      simp only [IntTy.arith, IntTy.check, Int.sub_neg]
      by_cases hc : IntTy.i64.Contains (nj + k) <;> simp [hc, Outcome.fault]

namespace Eval.PanicFree

variable {G : List Known}

/-- An index whose facts give `0 <= j + k` and `j + k < xs.len()` reads an element,
or overflows computing `j + k`. -/
theorem index (n : Nat) {xs j : Name} {k : Int} {i : Expr} (hi : i.offset? = some (j, k))
    (hb : Known.bounds G j xs k = true) :
    Eval.PanicFree lim G (Value.PanicFree lim) (eval D (Copy.memoryWith w) n (.index (.var xs) i)) := by
  rcases n with _ | m
  · exact outOfFuel
  · intro s hs hz
    obtain ⟨nj, ws, hj, hw, h0, hlt⟩ := Known.bounds_spec hb hz
    have hws : (Value.list ws).PanicFree lim := hs.1 _ (mem_of_lookup hw)
    have hx : eval D (Copy.memoryWith w) m (.var xs) s = .outOfFuel ∨
        eval D (Copy.memoryWith w) m (.var xs) s = .done (.list ws) s := by
      rcases m with _ | m
      · exact .inl rfl
      · exact .inr (by simp [eval, Eval.inspect, Eval.ofExcept, Copy.memoryWith, Frames.withWorld, Copy.frames, Copy.read,
          hw, Value.get])
    show (Outcome.PanicFree lim) _ (Eval.bind (eval D (Copy.memoryWith w) m (.var xs)) (fun v =>
      Eval.bind (Eval.bind (eval D (Copy.memoryWith w) m i) Eval.asInt)
        fun idx => Eval.ofExcept (v.get [.index idx])) s)
    unfold Eval.bind Outcome.bind
    rcases hx with hx | hx <;> rw [hx]
    · trivial
    · dsimp only
      rcases eval_offset m hi hj with h | h | h <;> rw [h]
      · trivial
      · exact ⟨.inl rfl, hs⟩
      · have he : elemAt? ws (nj + k) = some ws[(nj + k).toNat] := by
          simp [elemAt?, h0]
        have hel : ws[(nj + k).toNat].PanicFree lim := by
          cases hws with
          | list h => exact h _ (List.getElem_mem _)
        simp [Eval.asInt, Pure.pure, Eval.pure, Eval.ofExcept, Value.get, he, Outcome.PanicFree, hel, hs,
          Outcome.bind]

end Eval.PanicFree

end Stilt
