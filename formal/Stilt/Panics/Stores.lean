import Stilt.Panics.Ranges

/-!
# Stores at proved indexes

`xs[e] = v`, where `e` is a variable `j`, `j + k` or `j - k` that the facts prove
an index of `xs` (facts.guards and facts.range-loops), and where `v` doesn't resize
`xs`, stores into an element: the index is computed first, then the value, then the
store (values.assignment-order), and the list still has the length the index was
proved against (`Frame.Keeps.lookup_list`). A store into an element keeps the
list's length, so a range loop's facts survive it.
-/

namespace Stilt

variable {D : Decls} {w : WriteBack}

/-- A store into an element within a list's bounds. -/
theorem write_index {fr : Copy.Frame} {xs : Name} {ws : List Value} {i : Int} (v : Value)
    (hw : fr.lookup xs = some (.list ws)) (h0 : 0 ≤ i) (hlt : i < ws.length) :
    Copy.write fr xs [.index i] v = .ok (assocSet fr xs (.list (ws.set i.toNat v))) := by
  have he : elemAt? ws i = some ws[i.toNat] := by simp [elemAt?, h0]
  simp [Copy.write, hw, Value.set, he, Functor.map, Except.map]

/-- Storing a panic-free value into an element of a panic-free frame's list keeps it
panic-free. -/
theorem Frame.PanicFree.store {fr : Copy.Frame} (hfr : Frame.PanicFree fr) {xs : Name}
    {ws : List Value} (hw : fr.lookup xs = some (.list ws)) {v : Value} (hv : v.PanicFree) (i : Nat) :
    Frame.PanicFree (assocSet fr xs (.list (ws.set i v))) := by
  intro xv hxv
  rcases mem_assocSet hxv with hxv | hxv
  · exact hfr xv hxv
  · rw [hxv]
    have hws : (Value.list ws).PanicFree := hfr _ (mem_of_lookup hw)
    refine .list fun u hu => ?_
    rcases List.mem_or_eq_of_mem_set hu with hu | rfl
    · cases hws with
      | list h => exact h u hu
    · exact hv

/-- An offset computes, from a frame that meets `Known.bounds`, an index within the list. -/
theorem eval_index_path (n : Nat) {G : List Known} {xs j : Name} {k : Int} {e : Expr}
    (hi : e.offset? = some (j, k)) (hb : Known.bounds G j xs k = true) {s : Copy.State}
    (hz : Frame.Meets G s.1) :
    ∃ (ws : List Value) (i : Int), s.1.lookup xs = some (.list ws) ∧ 0 ≤ i ∧ i < ws.length ∧
      (Eval.path (eval D (Copy.memoryWith w) n) [.index e] s = .outOfFuel ∨
        Eval.path (eval D (Copy.memoryWith w) n) [.index e] s = .panicked .overflow s ∨
        Eval.path (eval D (Copy.memoryWith w) n) [.index e] s = .done [.index i] s) := by
  obtain ⟨nj, ws, hj, hw, h0, hlt⟩ := Known.bounds_spec hb hz
  refine ⟨ws, nj + k, hw, h0, hlt, ?_⟩
  rcases eval_offset (D := D) (w := w) n hi hj with h | h | h <;>
    simp [Eval.path, Eval.bind, Outcome.bind, bind, h, Eval.asInt, pure, Eval.pure]

namespace Eval.PanicFree

/-- `xs[e] = value` stores into an element, when `e` is proved an index of `xs` and
`value`, panic-free, doesn't resize `xs`. -/
theorem storeIndex (n : Nat) {G : List Known} {xs j : Name} {k : Int} {e value : Expr}
    (hi : e.offset? = some (j, k)) (hb : Known.bounds G j xs k = true) (hres : xs ∉ value.resizes)
    (hv : Eval.PanicFree G Value.PanicFree (eval D (Copy.memoryWith w) n value))
    (hkv : Eval.Keeps value.writes value.resizes (fun _ => True) (eval D (Copy.memoryWith w) n value)) :
    Eval.PanicFree G Value.PanicFree
      (Eval.assign (Copy.memoryWith w) (eval D (Copy.memoryWith w) n) xs [.index e] value) := by
  intro s hs hz
  obtain ⟨ws, i, hw, h0, hlt, hp⟩ := eval_index_path (D := D) (w := w) n hi hb hz
  show Outcome.PanicFree _ (Eval.bind (Eval.path (eval D (Copy.memoryWith w) n) [.index e]) (fun p =>
    Eval.bind (eval D (Copy.memoryWith w) n value) fun v =>
      Eval.bind (Eval.update fun s => (Copy.memoryWith w).write s xs p v) fun _ => Pure.pure Value.unit) s)
  rcases hp with h | h | h <;> simp only [Eval.bind, h, Outcome.bind]
  · trivial
  · exact ⟨.inl rfl, hs⟩
  · refine Outcome.PanicFree.bind (hv s hs hz) fun v s₂ hr hvp hs₂ => ?_
    obtain ⟨ws', hw', _⟩ := (hr.keeps (hkv s)).2.lookup_list hres hw
    have hwr : (Copy.memoryWith w).write s₂ xs [.index i] v =
        .ok (assocSet s₂.1 xs (.list (ws'.set i.toNat v)), s₂.2) := by
      rw [Eval.Keeps.memoryWith_write, write_index v hw' h0 (by omega)]
      rfl
    simp only [Eval.update, hwr, Pure.pure, Eval.pure, Outcome.bind, Outcome.PanicFree]
    exact ⟨.unit, hs₂.1.store hw' hvp _, hs₂.2⟩

end Eval.PanicFree

end Stilt
