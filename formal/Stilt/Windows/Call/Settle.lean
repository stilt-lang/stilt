import Stilt.Windows.Call.Leave
import Stilt.Windows.Control

/-!
# How a call ends

A callee's outcome becomes its call's (`Outcome.leaveCall`): the caller goes on with its own
variables and the store the callee left, and in the model of windows the callee's locations are
freed (`Outcome.settle`). A value the callee gives or returns reads its windows on the callee's
locations through, and keeps those the callee's parameters brought in, which lie in the
caller's store; an error it raises is read through all its windows (views.across-calls,
views.escaping). Both models end alike, from states the caller's simulation keeps.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- What a call gives, against the callee's context `c'`: values read alike, the in-place one a
value the checks accept, each window of the other on a location of the caller's and one that a
parameter of the result brought in. -/
def CallG (D : Decls) (c' : Ctx) (u v : Value) (si : IState) (sw : WState) : Prop :=
  VRel si.1.store sw.1.store v u ∧ u.Viewed D ∧
    ∀ w ∈ windowsOf v, w.1 < c'.L ∧ ∃ p ∈ c'.P, Brought c'.In p w

variable {c c' : Ctx} {pend pend' : List (Window × Value)} {si : IState} {sw : WState}

theorem leave_inPlace (si si' : IState) (bound : List (Name × Passed)) :
    InPlace.memory.leave si si' bound = .ok (leftIn si si') := rfl

theorem leave_windows (sw sw' : WState) (bound : List (Name × Passed)) :
    memory.leave sw sw' bound = .ok ({ sw.1 with store := sw'.1.store }, sw'.2) := rfl

theorem leftW_store (sw sw' : WState) :
    (leftW sw sw').1.store = freeStore sw.1.store.length sw'.1.store := rfl

/-- A value leaving the callee, its windows tracked by the result's parameters, read through
its windows on the callee's locations: what the call gives. -/
theorem leaving_settle {si' : IState} {sw' : WState} (hn : c'.L = sw.1.store.length)
    (hP : ∀ p ∈ c'.P, ∀ r, (p, r) ∈ sw'.1.env → c'.L ≤ r.loc) {v w : Value}
    (h : Leaving D c' sw'.1.env si' sw' v w) :
    ∃ w', resolveFrom sw'.1.store sw.1.store.length w = .ok w' ∧
      CallG D c' v w' (leftIn si si') (leftW sw sw') := by
  obtain ⟨w', hres, hu, hsub⟩ := resolveFrom_rel (n := sw.1.store.length) h.1.1 h.1.readAlike
  refine ⟨w', hres, ⟨hu, fun win hwin => ?_⟩, h.2.2, fun win hwin => ?_⟩
  · obtain ⟨hm, hl⟩ := hsub win hwin
    refine (h.1.2 win hm).region ?_ rfl
    rw [leftW_store]
    exact regionW_freeStore hl
  · obtain ⟨hm, hl⟩ := hsub win hwin
    refine ⟨hn ▸ hl, ?_⟩
    obtain ⟨s, hs, hcov⟩ := h.2.1 win hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
    rcases hcov with ⟨r, hr, q, hq, -⟩ | hb
    · have := hP p hp r hr
      have := Window.loc_of_toPath hq
      omega
    · exact ⟨p, hp, hb⟩

/-- An error leaving the callee, read through all its windows: the in-place one, which holds no
window. -/
theorem raised_settle {si₁ : IState} {sw₁ : WState} {env : List (Name × Ref)} {si' : IState}
    {sw' : WState} {e e' : Value} (h : Leaving D c' sw'.1.env si' sw' e e') :
    resolve sw'.1.store e' = .ok e ∧ Leaving D c env si₁ sw₁ e e :=
  ⟨h.1.resolve, VRel.free h.2.2.free, fun _ hw => absurd hw (not_mem_of_free h.2.2.free), h.2.2⟩

/-- What the caller's simulation needs of the callee's context and of the store it started
from. -/
structure Leaves (D : Decls) (c c' : Ctx) (pend pend' : List (Window × Value)) (si : IState)
    (sw : WState) (env' : List (Name × Ref)) : Prop where
  pre : Pre D c pend si sw
  length : c'.L = sw.1.store.length
  starts : StartsFrom c' sw.1.store
  old : ∀ ℓ < c'.L, ∀ w ∈ c'.Old ℓ, w.1 < ℓ
  pend : ∀ wd ∈ pend, wd ∈ pend'
  params : ∀ p ∈ c'.P, ∀ r, (p, r) ∈ env' → c'.L ≤ r.loc

theorem Pre.leave' {env' : List (Name × Ref)} {si' : IState} {sw' : WState}
    (hp' : Pre D c' pend' si' sw') (hL : Leaves D c c' pend pend' si sw env') :
    Pre D c pend (leftIn si si') (leftW sw sw') :=
  Pre.leave hL.pre hp' hL.starts hL.length hL.old hL.pend

/-- A callee's outcome, with the store it ends with, as its call's: the caller's simulation
holds again, a value given or returned is what the call gives (`CallG`), an error raised is read
through, a `break` or a `continue` is stuck in both models, and a performance's rest ends so
once resumed. -/
theorem Outcome.Rel.settle {env' : List (Name × Ref)} (hL : Leaves D c c' pend pend' si sw env')
    {S' : List Shape} (hS' : ∀ s ∈ S', s ∈ c'.P.map (fun y => (⟨y, []⟩ : Shape)))
    (bound bound' : List (Name × Passed)) :
    ∀ (o : Outcome IState Value) (o' : Outcome WState Value),
      o.Rel (CorrG D c' pend' (ValG D c' S') env') o' →
      (o.leaveCall InPlace.memory bound si).Rel (CorrG D c pend (CallG D c') sw.1.env)
        ((o'.leaveCall memory bound' sw).settle sw.1.store.length)
  | .done v si', .done w sw', ⟨hp', he, hG⟩ => by
    subst he
    obtain ⟨w', hres, hg⟩ := leaving_settle hL.length hL.params (ValG.leaving hS' hG)
    simp only [Outcome.leaveCall, leave_inPlace, leave_windows, Outcome.settle, hres]
    exact ⟨hp'.leave' hL, rfl, hg⟩
  | .raised e si', .raised e' sw', ⟨hp', he, hG⟩ => by
    subst he
    obtain ⟨hres, hg⟩ := raised_settle (si₁ := leftIn si si') (sw₁ := leftW sw sw')
      (env := sw.1.env) (c := c) hG
    simp only [Outcome.leaveCall, leave_inPlace, leave_windows, Outcome.settle, hres]
    exact ⟨hp'.leave' hL, rfl, hg⟩
  | .jumped j si', .jumped j' sw', ⟨hp', he, hG⟩ => by
    subst he
    rcases j with _ | _ | v <;> rcases j' with _ | _ | w <;> try exact absurd hG id
    · exact trivial
    · exact trivial
    simp only at hG
    obtain ⟨w', hres, hg⟩ := leaving_settle hL.length hL.params hG
    simp only [Outcome.leaveCall, leave_inPlace, leave_windows, Outcome.settle, hres]
    exact ⟨hp'.leave' hL, rfl, hg⟩
  | .panicked k si', .panicked k' sw', ⟨hp', he, hG⟩ => by
    subst he
    simp only [Outcome.leaveCall, leave_inPlace, leave_windows, Outcome.settle]
    exact ⟨hp'.leave' hL, rfl, hG⟩
  | .performed op v si' k, .performed op' v' sw' k', ⟨⟨hp', he, hG⟩, hk⟩ => by
    subst he
    simp only [Outcome.leaveCall, leave_inPlace, leave_windows, Outcome.settle]
    exact ⟨⟨hp'.leave' hL, rfl, hG⟩, fun w x w' x' hr =>
      Outcome.Rel.settle hL hS' bound bound' (k w x) (k' w' x') (hk w x w' x' hr)⟩
  | .outOfFuel, .outOfFuel, _ => trivial
  | .stuck, .stuck, _ => trivial
  | .done .., .raised .., h | .done .., .jumped .., h | .done .., .panicked .., h
  | .done .., .performed .., h | .done .., .outOfFuel, h | .done .., .stuck, h
  | .raised .., .done .., h | .raised .., .jumped .., h | .raised .., .panicked .., h
  | .raised .., .performed .., h | .raised .., .outOfFuel, h | .raised .., .stuck, h
  | .jumped .., .done .., h | .jumped .., .raised .., h | .jumped .., .panicked .., h
  | .jumped .., .performed .., h | .jumped .., .outOfFuel, h | .jumped .., .stuck, h
  | .panicked .., .done .., h | .panicked .., .raised .., h | .panicked .., .jumped .., h
  | .panicked .., .performed .., h | .panicked .., .outOfFuel, h | .panicked .., .stuck, h
  | .performed .., .done .., h | .performed .., .raised .., h | .performed .., .jumped .., h
  | .performed .., .panicked .., h | .performed .., .outOfFuel, h | .performed .., .stuck, h
  | .outOfFuel, .done .., h | .outOfFuel, .raised .., h | .outOfFuel, .jumped .., h
  | .outOfFuel, .panicked .., h | .outOfFuel, .performed .., h | .outOfFuel, .stuck, h
  | .stuck, .done .., h | .stuck, .raised .., h | .stuck, .jumped .., h
  | .stuck, .panicked .., h | .stuck, .performed .., h | .stuck, .outOfFuel, h => nomatch h

end Windows

end Stilt
