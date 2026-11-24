import Stilt.OneShot.Syntax
import Stilt.InPlace.Safe
import Stilt.Semantics
import Stilt.Cells

/-!
# Values that resume at most once

A value is one-shot when every closure it holds, at any depth, has a body that
passes the check of handlers.resume-at-most-once, as every closure that a
checked program makes has. Its parts are one-shot, and so is every value that
reading, writing, entering a call and leaving one give from one-shot values.
-/

namespace Stilt

/-- Every closure a value holds, at any depth, has a body that passes the
check for the row it was written with (handlers.resume-at-most-once). -/
inductive Value.OneShot : Value → Prop
  | int {n : Int} : Value.OneShot (.int n)
  | float {x : FloatVal} : Value.OneShot (.float x)
  | str {s : String} : Value.OneShot (.str s)
  | bool {b : Bool} : Value.OneShot (.bool b)
  | unit : Value.OneShot .unit
  | record {R : Name} {fields : List (Name × Value)} :
      (∀ fv ∈ fields, Value.OneShot fv.2) → Value.OneShot (.record R fields)
  | variant {T C : Name} {payload : List Value} :
      (∀ v ∈ payload, Value.OneShot v) → Value.OneShot (.variant T C payload)
  | list {vs : List Value} : (∀ v ∈ vs, Value.OneShot v) → Value.OneShot (.list vs)
  | closure {captured : List (Name × Value)} {ps : List Param} {result : Ty} {ρ : Row}
      {body : Expr} :
      body.bodyOneShot ρ = true → (∀ xv ∈ captured, Value.OneShot xv.2) →
      Value.OneShot (.closure captured ps result ρ body)
  | function {f : Name} {types : List Ty} {rows : List Row} :
      Value.OneShot (.function f types rows)
  | handle {u : Ty} {k : Nat} : Value.OneShot (.handle u k)

namespace Value.OneShot

theorem hereditary : Value.Hereditary Value.OneShot where
  int _ := .int
  float _ := .float
  bool _ := .bool
  str _ := .str
  record _ _ := ⟨fun h => by cases h; assumption, .record⟩
  list _ := ⟨fun h => by cases h; assumption, .list⟩
  handle _ _ := .handle

theorem passesToParts : Value.PassesToParts Value.OneShot where
  record _ _ h := by cases h; assumption
  variant _ _ _ h := by cases h; assumption
  list _ := ⟨fun h => by cases h; assumption, .list⟩

/-- A part of a one-shot value is one-shot. -/
theorem get {v w : Value} {p : Path} (hv : v.OneShot) (h : v.get p = .ok w) : w.OneShot := by
  induction p generalizing v with
  | nil => cases h; exact hv
  | cons s p ih =>
    cases s <;> cases v <;> simp only [Value.get, reduceCtorEq] at h
    · split at h
      · rename_i x hx
        cases hv with
        | record hfs => exact ih (hfs (_, x) (mem_of_lookup hx)) h
      · cases h
    · split at h
      · rename_i x hx
        cases hv with
        | list hvs => exact ih (hvs x (mem_of_elemAt? hx)) h
      · cases h

/-- Writing a one-shot value into a one-shot value gives a one-shot value. -/
theorem set {v w v' : Value} {p : Path} (hv : v.OneShot) (hw : w.OneShot) (h : v.set p w = .ok v') :
    v'.OneShot := by
  induction p generalizing v v' with
  | nil => cases h; exact hw
  | cons s p ih =>
    cases s <;> cases v <;> simp only [Value.set, reduceCtorEq] at h
    · split at h
      · rename_i x hx
        cases hx' : x.set p w with
        | error e => simp [hx', Functor.map, Except.map] at h
        | ok x' =>
          simp only [hx', Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          cases hv with
          | record hfs =>
            have h' := ih (hfs (_, x) (mem_of_lookup hx)) hx'
            refine .record fun fv hfv => ?_
            rcases mem_assocSet hfv with hfv | hfv
            · exact hfs fv hfv
            · exact hfv ▸ h'
      · cases h
    · split at h
      · rename_i x hx
        cases hx' : x.set p w with
        | error e => simp [hx', Functor.map, Except.map] at h
        | ok x' =>
          simp only [hx', Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          cases hv with
          | list hvs =>
            have h' := ih (hvs x (mem_of_elemAt? hx)) hx'
            refine .list fun u hu => ?_
            rcases List.mem_or_eq_of_mem_set hu with hu | rfl
            · exact hvs u hu
            · exact h'
      · cases h

end Value.OneShot

/-- A `return` carries a one-shot value. -/
def Jump.OneShot : Jump → Prop
  | .ret v => v.OneShot
  | _ => True

/-- Every value of a frame is one-shot. -/
def Frame.OneShot (fr : Copy.Frame) : Prop := ∀ xv ∈ fr, xv.2.OneShot

/-- Every value of a state is one-shot: those of its frame and those its world's cells hold. -/
def State.OneShot (s : Copy.State) : Prop := Frame.OneShot s.1 ∧ s.2.All Value.OneShot

/-- What a call passes: a one-shot value, or a place. -/
def Passed.OneShot : Passed → Prop
  | .value v | .moved _ v => v.OneShot
  | .place _ _ => True

namespace Frame.OneShot

theorem cons {fr : Copy.Frame} {x : Name} {v : Value} (hfr : Frame.OneShot fr) (hv : v.OneShot) :
    Frame.OneShot ((x, v) :: fr) := by
  intro xv h
  rcases List.mem_cons.1 h with rfl | h
  · exact hv
  · exact hfr xv h

theorem tail {fr : Copy.Frame} (hfr : Frame.OneShot fr) : Frame.OneShot fr.tail :=
  fun xv h => hfr xv (List.mem_of_mem_tail h)

theorem read {fr : Copy.Frame} (hfr : Frame.OneShot fr) {x : Name} {p : Path} {v : Value}
    (h : Copy.read fr x p = .ok v) : v.OneShot := by
  unfold Copy.read at h
  split at h
  · rename_i u hu
    exact Value.OneShot.get (hfr (x, u) (mem_of_lookup hu)) h
  · cases h

theorem write {fr fr' : Copy.Frame} (hfr : Frame.OneShot fr) {x : Name} {p : Path} {w : Value}
    (hw : w.OneShot) (h : Copy.write fr x p w = .ok fr') : Frame.OneShot fr' := by
  unfold Copy.write at h
  split at h
  · rename_i u hu
    cases hs : u.set p w with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok u' =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have hu' := Value.OneShot.set (hfr (x, u) (mem_of_lookup hu)) hw hs
      intro xv hxv
      rcases mem_assocSet hxv with hxv | hxv
      · exact hfr xv hxv
      · exact hxv ▸ hu'
  · cases h

/-- Entering a call binds one-shot values: the captured ones, the arguments,
and the places it reads. -/
theorem enter {caller : Copy.Frame} (hc : Frame.OneShot caller) :
    ∀ {fr fr' : Copy.Frame} (params : List (Name × Passed)), Frame.OneShot fr →
      (∀ ya ∈ params, ya.2.OneShot) → Copy.enter caller fr params = .ok fr' → Frame.OneShot fr'
  | fr, fr', [], hfr, _, h => by cases h; exact hfr
  | fr, fr', (y, a) :: params, hfr, hps, h => by
    have ha := hps (y, a) List.mem_cons_self
    have hrest : ∀ ya ∈ params, ya.2.OneShot := fun ya h => hps ya (List.mem_cons_of_mem _ h)
    unfold Copy.enter at h
    rw [List.foldlM_cons] at h
    cases a with
    | value v | moved _ v => exact enter hc params (hfr.cons ha) hrest h
    | place x path =>
      cases hr : Copy.read caller x path with
      | error e => simp [hr, Functor.map, Except.map, bind, Except.bind] at h
      | ok v =>
        simp only [hr, Functor.map, Except.map, bind, Except.bind] at h
        exact enter hc params (hfr.cons (read hc hr)) hrest h

/-- Leaving a call writes one-shot values of the callee's frame back. -/
theorem leave {callee : Copy.Frame} (hce : Frame.OneShot callee) :
    ∀ {fr fr' : Copy.Frame} (params : List (Name × Passed)), Frame.OneShot fr →
      Copy.leave fr callee params = .ok fr' → Frame.OneShot fr'
  | fr, fr', [], hfr, h => by cases h; exact hfr
  | fr, fr', (y, a) :: params, hfr, h => by
    unfold Copy.leave at h
    rw [List.foldlM_cons] at h
    cases a with
    | value v | moved _ v => exact leave hce params hfr h
    | place x path =>
      simp only [bind, Except.bind] at h
      cases hr : Copy.read callee y [] with
      | error e => simp [hr] at h
      | ok v =>
        simp only [hr] at h
        cases hw : Copy.write fr x path v with
        | error e => simp [hw] at h
        | ok fr₁ =>
          simp only [hw] at h
          exact leave hce params (write hfr (read hce hr) hw) h

end Frame.OneShot

end Stilt
