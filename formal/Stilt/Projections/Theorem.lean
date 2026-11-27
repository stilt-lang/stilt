import Stilt.Projections.Once

/-!
# A projection runs its access once

What the checks of projections promise of a run: the body of every projection of an accepted
program, run from where its list of kept values is empty, ends every path to its end or to a
`return` with one value kept, the access's, and every path to a raise or a performance with
at most one (`Program.Projections.yields`, projections.once-on-every-path). So the value its
function ends with, the first kept, is there, and the caller's access ran once.
-/

namespace Stilt

/-- The bodies the projections of a program were declared with, each with the name of the list
its function keeps the access's values in. -/
def Program.projectionBodies (p : Program) : List (Name × Expr) :=
  p.decls.fns.filterMap fun d => d.body.projection?.map fun x => (x.1, x.2.2)

theorem Expr.projection?_isProjection {d : FnDecl} {x : Name × Ty × Expr}
    (h : d.body.projection? = some x) : d.isProjection = true := by
  unfold Expr.projection? at h
  split at h
  · rename_i heq
    unfold FnDecl.isProjection
    rw [heq]
  · cases h

/-- A projection's function that passes the checks has a body whose paths run one `yield`. -/
theorem FnDecl.projectionChecked_once {d : FnDecl} {res : Name} {R : Ty} {b : Expr}
    (h : d.projectionChecked = true) (hb : d.body.projection? = some (res, R, b)) :
    ∃ k, b.once res k false 0 = some (some 1) ∨ b.once res k false 0 = some none := by
  unfold FnDecl.projectionChecked at h
  rw [hb] at h
  split at h
  · rename_i res' _ b' k _ _ _ hx _
    cases hx
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    exact ⟨k, h.2⟩
  · cases h

/-- **Every path through a projection's body runs one `yield`** (projections.once-on-every-path):
from where its list of kept values is empty, the body of every projection of a program that
passes the checks of projections, run with any fuel, ends with one value kept on every path to
its end or to a `return`, and with at most one on every path to a raise or a performance, whose
rest, resumed with any value in any world, again ends so. -/
theorem Program.Projections.yields {p : Program} (h : p.Projections) :
    ∀ rb ∈ p.projectionBodies, ∀ (fuel : Nat) (s : Copy.State), s.1.lookup rb.1 = some (.list []) →
      (eval p.decls Copy.memory fuel rb.2 s).Yielding rb.1 (s.1.map Prod.fst) (some (some 1))
        (fun _ => True) := by
  intro rb hrb fuel s hs
  obtain ⟨d, hd, hx⟩ := List.mem_filterMap.1 hrb
  obtain ⟨⟨res, R, b⟩, hb, rfl⟩ := Option.map_eq_some_iff.1 hx
  have hc := h
  unfold Program.Projections Program.projectionsChecked at hc
  simp only [Bool.and_eq_true, List.all_eq_true] at hc
  have hd' := (hc.1.1 d hd).1
  simp only [Expr.projection?_isProjection hb, ↓reduceIte] at hd'
  obtain ⟨k, hk⟩ := FnDecl.projectionChecked_once hd' hb
  have hne : b.once res k false 0 ≠ none := by rcases hk with hk | hk <;> rw [hk] <;> simp
  refine Outcome.Yielding.mono (fun _ h => h) (fun m hm => ?_)
    (eval_yielding p.decls fuel b res k false 0 (s.1.map Prod.fst) (Nat.zero_le _) hne s
      ⟨rfl, [], hs, rfl⟩)
  rcases hk with hk | hk <;> rw [hk] at hm <;> cases hm
  rfl

end Stilt
