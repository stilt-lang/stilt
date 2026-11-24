import Stilt.Windows.Guards.Eval
import Stilt.Windows.Resolve

/-!
# Parts that guarded evaluations keep

What the guard of the views clause gives a window: when its reference is a region that the
evaluation avoids, the in-place store reads it the same part after the evaluation as before
(`partIn_evolvesBy`), and a value whose windows are all such regions reads the same against
both stores (`resolveIn_evolvesBy`).
-/

namespace Stilt

open InPlace

namespace Windows

/-- An evolution that avoids a window's reference leaves the part the window reads. -/
theorem partIn_evolvesBy {G : List Path} {s s' : InPlace.State} (h : EvolvesBy (Avoids G) s s')
    {w : Window} (hg : w.ref.toPath ∈ G) (hl : w.1 < s.store.length) :
    partIn s'.store w.1 w.2.1 w.2.2 = partIn s.store w.1 w.2.1 w.2.2 := by
  obtain ⟨-, W, st, extra, hs, hW, hseq⟩ := h
  obtain ⟨A, B, hR, hlen, hB, -, -⟩ := setSeq_append_store (B := [])
    (fun pw hpw => atLoc_of_under (hW pw hpw).1) (by rw [List.append_nil]; exact hseq)
  have hB' : B = [] := List.eq_nil_of_length_eq_zero hB
  subst hB'
  simp only [List.append_nil, Value.list.injEq] at hR
  subst hR
  rw [hs]
  exact partIn_setSeq hseq (fun pw hpw => (hW pw hpw).2 _ hg) hl (by omega) extra

/-- A value whose every window's reference is avoided and in the store reads the same
against the store after the evolution. -/
theorem resolveIn_evolvesBy {G : List Path} {s s' : InPlace.State}
    (h : EvolvesBy (Avoids G) s s')
    {v : Value} (hw : ∀ w ∈ windowsOf v, w.ref.toPath ∈ G ∧ w.1 < s.store.length) :
    resolveIn s'.store v = resolveIn s.store v :=
  mapWindows_congr v fun w hmem => partIn_evolvesBy h (hw w hmem).1 (hw w hmem).2

end Windows

end Stilt
