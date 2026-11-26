import Stilt.Locks.Syntax
import Stilt.Semantics
import Stilt.Cells
import Stilt.InPlace.Safe
import Stilt.Maps.Parts
import Stilt.Matching

/-!
# Values without `locks`

A value is lock-free when every function it holds, at any depth, is one whose call holds no
site of `locks`: a closure whose body holds none, a declared function outside the set that
has the fact (shared.locks). Its parts are lock-free, and so is every value that reading,
writing, entering a call and leaving one give from lock-free values. A function value made
elsewhere, one a `when` takes out of a cell among them, need not be, and calling it may lock
(facts.calls-through-function-values).
-/

namespace Stilt

variable {D : Decls} {L : List Name}

/-- Every function a value holds, at any depth, is one whose call holds no site of `locks`,
the functions of `L` being those that have it. -/
inductive Value.LockFree (D : Decls) (L : List Name) : Value → Prop
  | int {n : Int} : Value.LockFree D L (.int n)
  | float {x : FloatVal} : Value.LockFree D L (.float x)
  | str {s : String} : Value.LockFree D L (.str s)
  | bool {b : Bool} : Value.LockFree D L (.bool b)
  | unit : Value.LockFree D L .unit
  | record {R : Name} {fields : List (Name × Value)} :
      (∀ fv ∈ fields, Value.LockFree D L fv.2) → Value.LockFree D L (.record R fields)
  | variant {T C : Name} {payload : List Value} :
      (∀ v ∈ payload, Value.LockFree D L v) → Value.LockFree D L (.variant T C payload)
  | list {vs : List Value} : (∀ v ∈ vs, Value.LockFree D L v) → Value.LockFree D L (.list vs)
  | closure {captured : List (Name × Value)} {ps : List Param} {result : Ty} {ρ : Row}
      {body : Expr} :
      body.lockFree D L = true → (∀ xv ∈ captured, Value.LockFree D L xv.2) →
      Value.LockFree D L (.closure captured ps result ρ body)
  | function {f : Name} {types : List Ty} {rows : List Row} :
      f ∉ L → Value.LockFree D L (.function f types rows)
  | handle {u : Ty} {k : Nat} : Value.LockFree D L (.handle u k)

namespace Value.LockFree

theorem hereditary : Value.Hereditary (Value.LockFree D L) where
  int _ := .int
  float _ := .float
  bool _ := .bool
  str _ := .str
  record _ _ := ⟨fun h => by cases h; assumption, .record⟩
  list _ := ⟨fun h => by cases h; assumption, .list⟩
  handle _ _ := .handle

theorem passesToParts : Value.PassesToParts (Value.LockFree D L) where
  record _ _ h := by cases h; assumption
  variant _ _ _ h := by cases h; assumption
  list _ := ⟨fun h => by cases h; assumption, .list⟩

/-- A part of a lock-free value is lock-free. -/
theorem get {v w : Value} {p : Path} (hv : v.LockFree D L) (h : v.get p = .ok w) :
    w.LockFree D L := by
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

/-- Writing a lock-free value into a lock-free value gives a lock-free value. -/
theorem set {v w v' : Value} {p : Path} (hv : v.LockFree D L) (hw : w.LockFree D L)
    (h : v.set p w = .ok v') : v'.LockFree D L := by
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

/-- The clause of a lock-free handler is lock-free. -/
theorem clause {handler c : Value} {op : Name} (hh : handler.LockFree D L)
    (hc : handler.clause? op = some c) : c.LockFree D L := by
  cases handler <;> simp only [Value.clause?, reduceCtorEq] at hc
  cases hh with
  | record hfs => exact hfs _ (mem_of_lookup hc)

end Value.LockFree

/-- A `return` carries a lock-free value. -/
def Jump.LockFree (D : Decls) (L : List Name) : Jump → Prop
  | .ret v => v.LockFree D L
  | _ => True

/-- Every value of a frame is lock-free. -/
def Frame.LockFree (D : Decls) (L : List Name) (fr : Copy.Frame) : Prop :=
  ∀ xv ∈ fr, xv.2.LockFree D L

/-- What a call passes: a lock-free value, or a place. -/
def Passed.LockFree (D : Decls) (L : List Name) : Passed → Prop
  | .value v | .moved _ v => v.LockFree D L
  | .place _ _ => True

namespace Frame.LockFree

theorem nil : Frame.LockFree D L [] := fun _ h => nomatch h

theorem cons {fr : Copy.Frame} {x : Name} {v : Value} (hfr : Frame.LockFree D L fr)
    (hv : v.LockFree D L) : Frame.LockFree D L ((x, v) :: fr) := by
  intro xv h
  rcases List.mem_cons.1 h with rfl | h
  · exact hv
  · exact hfr xv h

theorem tail {fr : Copy.Frame} (hfr : Frame.LockFree D L fr) : Frame.LockFree D L fr.tail :=
  fun xv h => hfr xv (List.mem_of_mem_tail h)

theorem read {fr : Copy.Frame} (hfr : Frame.LockFree D L fr) {x : Name} {p : Path} {v : Value}
    (h : Copy.read fr x p = .ok v) : v.LockFree D L := by
  unfold Copy.read at h
  split at h
  · rename_i u hu
    exact Value.LockFree.get (hfr (x, u) (mem_of_lookup hu)) h
  · cases h

theorem write {fr fr' : Copy.Frame} (hfr : Frame.LockFree D L fr) {x : Name} {p : Path}
    {w : Value} (hw : w.LockFree D L) (h : Copy.write fr x p w = .ok fr') :
    Frame.LockFree D L fr' := by
  unfold Copy.write at h
  split at h
  · rename_i u hu
    cases hs : u.set p w with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok u' =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have hu' := Value.LockFree.set (hfr (x, u) (mem_of_lookup hu)) hw hs
      intro xv hxv
      rcases mem_assocSet hxv with hxv | hxv
      · exact hfr xv hxv
      · exact hxv ▸ hu'
  · cases h

/-- Entering a call binds lock-free values: the captured ones, the arguments, and the
places it reads. -/
theorem enter {caller : Copy.Frame} (hc : Frame.LockFree D L caller) :
    ∀ {fr fr' : Copy.Frame} (params : List (Name × Passed)), Frame.LockFree D L fr →
      (∀ ya ∈ params, ya.2.LockFree D L) → Copy.enter caller fr params = .ok fr' →
      Frame.LockFree D L fr'
  | fr, fr', [], hfr, _, h => by cases h; exact hfr
  | fr, fr', (y, a) :: params, hfr, hps, h => by
    have ha := hps (y, a) List.mem_cons_self
    have hrest : ∀ ya ∈ params, ya.2.LockFree D L := fun ya h => hps ya (List.mem_cons_of_mem _ h)
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

/-- Leaving a call writes lock-free values of the callee's frame back. -/
theorem leave {callee : Copy.Frame} (hce : Frame.LockFree D L callee) :
    ∀ {fr fr' : Copy.Frame} (params : List (Name × Passed)), Frame.LockFree D L fr →
      Copy.leave fr callee params = .ok fr' → Frame.LockFree D L fr'
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

end Frame.LockFree

end Stilt
