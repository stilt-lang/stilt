import Stilt.Windows.Call.Args
import Stilt.Windows.Handling.Escapes

/-!
# Reads that a call keeps

What a read through windows gives when every window it may meet reads a part that holds no
window: a value that holds none, or what the same read gives in any store, since it met no
window on the way. A call leaves a caller's cell as it was or with a value that holds no
window, and the windows it holds reading such parts, so what the caller's variables read
through them is what it was, or holds no window (views.across-calls).
-/

namespace Stilt

namespace Windows

/-- A read through a value that holds no window gives one that holds none. -/
theorem getW_free {st : List (Option Value)} : ∀ (p : Path) (y : Value) {x : Value}, Free y →
    getW st y p = .ok x → Free x
  | [], y, x, hy, h => by
    have : y = x := by cases y <;> simpa [getW] using h
    exact this ▸ hy
  | s :: p, y, x, hy, h => by
    cases y with
    | window loc path ranges => simp [Free, windowsOf] at hy
    | record R fields =>
      cases s with
      | field f =>
        simp only [getW] at h
        split at h
        · rename_i v hv
          exact getW_free p v (free_of_nil fun w hw => by
            have := windowsOf_lookup hv hw
            simp only [Free, windowsOf] at hy
            rw [hy] at this
            cases this) h
        · cases h
      | index i => simp [getW] at h
    | list vs =>
      cases s with
      | index i =>
        simp only [getW] at h
        split at h
        · rename_i v hv
          exact getW_free p v (free_of_nil fun w hw => by
            have := windowsOf_elemAt? hv hw
            simp only [Free, windowsOf] at hy
            rw [hy] at this
            cases this) h
        · cases h
      | field f => simp [getW] at h
    | _ => simp [getW] at h

/-- A read through a value whose every window reads a part that holds no window gives a value
that holds none, or what the same read gives in any store. -/
theorem getW_static {st : List (Option Value)} : ∀ (p : Path) (y : Value) {x : Value},
    (∀ w ∈ windowsOf y, ∃ d, regionW st w = .ok d ∧ Free d) → getW st y p = .ok x →
      Free x ∨ ∀ st', getW st' y p = .ok x
  | [], y, x, _, h => by
    have : y = x := by cases y <;> simpa [getW] using h
    subst this
    exact .inr fun st' => by cases y <;> rfl
  | s :: p, y, x, hw, h => by
    cases y with
    | window loc path ranges =>
      left
      obtain ⟨d, hd, hf⟩ := hw (loc, path, ranges) (by simp [windowsOf])
      have hp : part st loc path ranges = regionW st (loc, path, ranges) >>= slices ranges :=
        part_eq_region st (loc, path, ranges)
      simp only [getW, hp, hd] at h
      have h' : (slices ranges d >>= fun u => u.get (s :: p)) = .ok x := h
      cases hs : slices ranges d with
      | error e => rw [hs] at h'; cases h'
      | ok u =>
        rw [hs] at h'
        replace h := h'
        exact free_get u (s :: p) (free_slices hf ranges hs) h
    | record R fields =>
      cases s with
      | field f =>
        simp only [getW] at h
        split at h
        · rename_i v hv
          rcases getW_static p v (fun w hm => hw w (windowsOf_lookup hv hm)) h with h' | h'
          · exact .inl h'
          · exact .inr fun st' => by simp only [getW, hv]; exact h' st'
        · cases h
      | index i => simp [getW] at h
    | list vs =>
      cases s with
      | index i =>
        simp only [getW] at h
        split at h
        · rename_i v hv
          rcases getW_static p v (fun w hm => hw w (windowsOf_elemAt? hv hm)) h with h' | h'
          · exact .inl h'
          · exact .inr fun st' => by simp only [getW, hv]; exact h' st'
        · cases h
      | field f => simp [getW] at h
    | _ => simp [getW] at h

end Windows

end Stilt
