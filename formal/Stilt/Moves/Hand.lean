import Stilt.Moves.Drop
import Stilt.Moves.Args
import Stilt.InPlace.Enter

/-!
# Handing storage over

When a call starts, `Moving` passes each argument that is the last use of a
variable as the place of that variable (`Moving.handOver`), as in-place
mutation passes an `inout` argument. The variable is live when the call
starts, and holds the value that copy-in, copy-out passes. So the start of the
call is in-place mutation's, on the live bindings of the caller, with those
arguments as places: `Stilt.InPlace.Enter` applies (values.passing-values and values.inout-argument-order).

The places a call passes so don't overlap: a last use is of a variable that
no other argument mentions, so it is neither an `inout` argument's root nor
another last use (`Expr.movesOk`), and the law of exclusivity keeps the
`inout` arguments apart (modes.overlapping-inout).
-/

namespace Stilt.Moving

open InPlace

/-- A passed argument as `Moving` passes it: a last use as its variable's
place. -/
def _root_.Stilt.Passed.handOver : Passed → Passed
  | .moved x _ => .place x []
  | q => q

theorem handOver_eq (y : Name) (q : Passed) : handOver (y, q) = (y, q.handOver) := by
  cases q <;> rfl

theorem value?_handOver {q : Passed} {v : Value} (h : q.handOver.value? = some v) :
    q.value? = some v := by
  cases q <;> first | exact h | cases h

/-- Last uses that the arguments of a call pass are distinct, and no later
part of the call mentions them. -/
theorem moved_distinct : ∀ {B : Live} {as : List Arg}, argsMovesOk B as = true →
    (movedRoots as).Nodup ∧ ∀ x ∈ movedRoots as, B.mem x = false
  | _, [], _ => ⟨.nil, by simp [movedRoots]⟩
  | B, a :: as, h => by
    rcases a with e | ⟨z, ps⟩
    · simp only [argsMovesOk, Bool.and_eq_true] at h
      obtain ⟨hnd, hB⟩ := moved_distinct h.2
      by_cases hm : ∃ x, e = .move x
      · obtain ⟨x, rfl⟩ := hm
        simp only [Expr.movesOk, Live.mem_union, Bool.not_eq_true', Bool.or_eq_false_iff] at h
        refine ⟨List.nodup_cons.2 ⟨fun hx => ?_, hnd⟩, fun y hy => ?_⟩
        · rw [movedRoots_sub as x hx] at h
          exact absurd h.1.2 (by simp)
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact h.1.1
          · exact hB y hy
      · have hmr : movedRoots (.value e :: as) = movedRoots as := by
          simp [movedRoots, moved?_of_ne fun x hx => hm ⟨x, hx⟩]
        rw [hmr]
        exact ⟨hnd, hB⟩
    · simp only [argsMovesOk, Bool.and_eq_true] at h
      exact moved_distinct (as := as) h.2

theorem place_roots : ∀ {as : List Arg} {passed : List Passed}, InPlace.Sim.ArgsResolved as passed →
    ∀ {z : Name} {p : Path}, Passed.place z p ∈ passed → z ∈ inoutRoots as
  | [], [], _, _, _, h => by simp at h
  | .value _ :: as, .value _ :: qs, h, _, _, hm => by
    rcases List.mem_cons.1 hm with hm | hm
    · cases hm
    · exact place_roots (as := as) h hm
  | .value _ :: as, .moved _ _ :: qs, h, _, _, hm => by
    rcases List.mem_cons.1 hm with hm | hm
    · cases hm
    · exact place_roots (as := as) h hm
  | .inout ⟨x, _⟩ :: as, .place _ _ :: qs, ⟨rfl, _, h⟩, _, _, hm => by
    rcases List.mem_cons.1 hm with hm | hm
    · cases hm
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (place_roots h hm)
  | [], _ :: _, h, _, _, _ | .value _ :: _, [], h, _, _, _ | .inout ⟨_, _⟩ :: _, [], h, _, _, _
  | .value _ :: _, .place _ _ :: _, h, _, _, _ | .inout ⟨_, _⟩ :: _, .value _ :: _, h, _, _, _
  | .inout ⟨_, _⟩ :: _, .moved _ _ :: _, h, _, _, _ => h.elim

/-- With last uses as places, the places of a call still don't overlap. -/
theorem compat_handOver : ∀ {passed : List Passed}, passed.Pairwise Passed.Compat →
    (movedOf passed).Nodup → (∀ x ∈ movedOf passed, ∀ z p, Passed.place z p ∈ passed → x ≠ z) →
    (passed.map Passed.handOver).Pairwise Passed.Compat
  | [], _, _, _ => .nil
  | q :: qs, hc, hnd, hdis => by
    rw [List.pairwise_cons] at hc
    have hmo : movedOf (q :: qs) = (q.moved?.toList) ++ movedOf qs := by
      cases q <;> rfl
    rw [hmo, List.nodup_append] at hnd
    have hdis' : ∀ x ∈ movedOf qs, ∀ z p, Passed.place z p ∈ qs → x ≠ z := fun x hx z p hz =>
      hdis x (by rw [hmo]; exact List.mem_append_right _ hx) z p (List.mem_cons_of_mem _ hz)
    refine List.Pairwise.cons (fun q' hq' => ?_) (compat_handOver hc.2 hnd.2.1 hdis')
    obtain ⟨q', hq'', rfl⟩ := List.mem_map.1 hq'
    have hmem : ∀ x, q'.moved? = some x → x ∈ movedOf qs := fun x hx =>
      List.mem_filterMap.2 ⟨q', hq'', hx⟩
    cases q <;> cases q' <;> simp only [Passed.handOver, Passed.Compat] <;> try trivial
    · exact hc.1 _ hq''
    · rename_i z p y w
      exact .inl fun h => hdis y (by rw [hmo]; exact List.mem_append_right _ (hmem y rfl)) z p
        List.mem_cons_self h.symm
    · rename_i x v z p
      exact .inl fun h => hdis x (by simp [hmo, Passed.moved?]) z p
        (List.mem_cons_of_mem _ hq'') h
    · rename_i x v y w
      exact .inl fun h => hnd.2.2 x (by simp [Passed.moved?]) y (hmem y rfl) h

end Stilt.Moving
