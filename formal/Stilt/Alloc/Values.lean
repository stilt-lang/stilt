import Stilt.Alloc.Count
import Stilt.InPlace.Safe
import Stilt.Cells

/-!
# Values that allocate nothing when called

A value allocates nothing when called, under a set of functions `lim` covers, when every
closure it holds has a body without an operation that makes a value needing storage
(`Expr.allocFreeIn`), and every function it names is one `lim` covers, so that calling it runs
such a body, wherever the value was made (facts.calls-through-function-values). Copy-in,
copy-out reads, writes, enters and leaves calls keeping every value of its frames so.
-/

namespace Stilt

/-- Every closure a value holds, at any depth, has a body that makes no value needing storage
under `lim`, and every function it names is one `lim` covers. -/
inductive Value.AllocFree (D : Decls) (lim : Limited) : Value → Prop
  | int {n : Int} : Value.AllocFree D lim (.int n)
  | float {x : FloatVal} : Value.AllocFree D lim (.float x)
  | str {s : String} : Value.AllocFree D lim (.str s)
  | bool {b : Bool} : Value.AllocFree D lim (.bool b)
  | unit : Value.AllocFree D lim .unit
  | record {R : Name} {fields : List (Name × Value)} :
      (∀ fv ∈ fields, Value.AllocFree D lim fv.2) → Value.AllocFree D lim (.record R fields)
  | variant {T C : Name} {payload : List Value} :
      (∀ v ∈ payload, Value.AllocFree D lim v) → Value.AllocFree D lim (.variant T C payload)
  | list {vs : List Value} : (∀ v ∈ vs, Value.AllocFree D lim v) → Value.AllocFree D lim (.list vs)
  | closure {captured : List (Name × Value)} {ps : List Param} {result : Ty} {ρ : Row}
      {body : Expr} :
      body.allocFreeIn D lim = true → (∀ xv ∈ captured, Value.AllocFree D lim xv.2) →
      Value.AllocFree D lim (.closure captured ps result ρ body)
  | function {f : Name} {types : List Ty} {rows : List Row} :
      lim.fn f = true → Value.AllocFree D lim (.function f types rows)
  | handle {u : Ty} {k : Nat} : Value.AllocFree D lim (.handle u k)

variable {D : Decls} {lim : Limited}

theorem Value.AllocFree.hereditary : Value.Hereditary (Value.AllocFree D lim) where
  int _ := .int
  float _ := .float
  bool _ := .bool
  str _ := .str
  record _ _ := ⟨fun h => by cases h; assumption, .record⟩
  list _ := ⟨fun h => by cases h; assumption, .list⟩
  handle _ _ := .handle

theorem Value.AllocFree.passesToParts : Value.PassesToParts (Value.AllocFree D lim) where
  record _ _ h := by cases h; assumption
  variant _ _ _ h := by cases h; assumption
  list _ := ⟨fun h => by cases h; assumption, .list⟩

namespace Value.Hereditary

variable {P : Value → Prop} (hP : Value.Hereditary P)
include hP

/-- A part of a value of a hereditary property has it. -/
theorem part {v w : Value} {p : Path} (hv : P v) (h : v.get p = .ok w) : P w := by
  induction p generalizing v with
  | nil => cases h; exact hv
  | cons s p ih =>
    cases s with
    | field f =>
      cases v with
      | record R fields =>
        simp only [Value.get] at h
        split at h
        · rename_i x hx
          exact ih ((hP.record _ _).1 hv (f, x) (mem_of_lookup hx)) h
        · cases h
      | _ => cases h
    | index i =>
      cases v with
      | list vs =>
        simp only [Value.get] at h
        split at h
        · rename_i x hx
          exact ih ((hP.list _).1 hv x (mem_of_elemAt? hx)) h
        · cases h
      | _ => cases h

/-- A value of a hereditary property written into one gives one. -/
theorem setPart {v w v' : Value} {p : Path} (hv : P v) (hw : P w) (h : v.set p w = .ok v') :
    P v' := by
  induction p generalizing v v' with
  | nil => cases h; exact hw
  | cons s p ih =>
    cases s with
    | field f =>
      cases v with
      | record R fields =>
        simp only [Value.set] at h
        split at h
        · rename_i x hx
          cases hx' : x.set p w with
          | error e => simp [hx', Functor.map, Except.map] at h
          | ok x' =>
            simp only [hx', Functor.map, Except.map, Except.ok.injEq] at h
            subst h
            have hfs := (hP.record _ _).1 hv
            have hx'' := ih (hfs (f, x) (mem_of_lookup hx)) hx'
            refine (hP.record _ _).2 fun fv hfv => ?_
            rcases mem_assocSet hfv with hfv | hfv
            · exact hfs fv hfv
            · exact hfv ▸ hx''
        · cases h
      | _ => cases h
    | index i =>
      cases v with
      | list vs =>
        simp only [Value.set] at h
        split at h
        · rename_i x hx
          cases hx' : x.set p w with
          | error e => simp [hx', Functor.map, Except.map] at h
          | ok x' =>
            simp only [hx', Functor.map, Except.map, Except.ok.injEq] at h
            subst h
            have hvs := (hP.list _).1 hv
            have hx'' := ih (hvs x (mem_of_elemAt? hx)) hx'
            refine (hP.list _).2 fun u hu => ?_
            rcases List.mem_or_eq_of_mem_set hu with hu | rfl
            · exact hvs u hu
            · exact hx''
        · cases h
      | _ => cases h

end Value.Hereditary

/-! ## Frames -/

/-- Every value of a frame allocates nothing when called. -/
def Frame.AllocFree (D : Decls) (lim : Limited) (fr : Copy.Frame) : Prop :=
  ∀ xv ∈ fr, xv.2.AllocFree D lim

/-- Every value of a state allocates nothing when called: those of its frame, and those its
world's cells hold, which a `when` takes out (shared.when). -/
def State.AllocFree (D : Decls) (lim : Limited) (s : Copy.State) : Prop :=
  Frame.AllocFree D lim s.1 ∧ s.2.All (Value.AllocFree D lim)

/-- What a call passes: a value that allocates nothing when called, or a place. -/
def Passed.AllocFree (D : Decls) (lim : Limited) : Passed → Prop
  | .value v | .moved _ v => v.AllocFree D lim
  | .place _ _ => True

/-- A jump whose `return` carries a value that allocates nothing when called. -/
def Jump.AllocFree (D : Decls) (lim : Limited) : Jump → Prop
  | .ret v => v.AllocFree D lim
  | _ => True

namespace Frame.AllocFree

theorem cons {fr : Copy.Frame} {x : Name} {v : Value} (hfr : Frame.AllocFree D lim fr)
    (hv : v.AllocFree D lim) : Frame.AllocFree D lim ((x, v) :: fr) := by
  intro xv h
  rcases List.mem_cons.1 h with rfl | h
  · exact hv
  · exact hfr xv h

theorem tail {fr : Copy.Frame} (hfr : Frame.AllocFree D lim fr) : Frame.AllocFree D lim fr.tail :=
  fun xv h => hfr xv (List.mem_of_mem_tail h)

theorem read {fr : Copy.Frame} (hfr : Frame.AllocFree D lim fr) {x : Name} {p : Path}
    {v : Value} (h : Copy.read fr x p = .ok v) : v.AllocFree D lim := by
  unfold Copy.read at h
  split at h
  · rename_i u hu
    exact Value.AllocFree.hereditary.part (hfr (x, u) (mem_of_lookup hu)) h
  · cases h

theorem write {fr fr' : Copy.Frame} (hfr : Frame.AllocFree D lim fr) {x : Name} {p : Path}
    {w : Value} (hw : w.AllocFree D lim) (h : Copy.write fr x p w = .ok fr') :
    Frame.AllocFree D lim fr' := by
  unfold Copy.write at h
  split at h
  · rename_i u hu
    cases hs : u.set p w with
    | error e => rw [hs] at h; cases h
    | ok u' =>
      rw [hs] at h
      cases h
      have hu' := Value.AllocFree.hereditary.setPart (hfr (x, u) (mem_of_lookup hu)) hw hs
      intro xv hxv
      rcases mem_assocSet hxv with hxv | hxv
      · exact hfr xv hxv
      · exact hxv ▸ hu'
  · cases h

/-- Entering a call binds values that allocate nothing when called. -/
theorem enter {caller : Copy.Frame} (hc : Frame.AllocFree D lim caller) :
    ∀ {fr fr' : Copy.Frame} (params : List (Name × Passed)), Frame.AllocFree D lim fr →
      (∀ ya ∈ params, ya.2.AllocFree D lim) → Copy.enter caller fr params = .ok fr' →
      Frame.AllocFree D lim fr'
  | fr, fr', [], hfr, _, h => by cases h; exact hfr
  | fr, fr', (y, a) :: params, hfr, hps, h => by
    have ha := hps (y, a) List.mem_cons_self
    have hrest : ∀ ya ∈ params, ya.2.AllocFree D lim :=
      fun ya h => hps ya (List.mem_cons_of_mem _ h)
    unfold Copy.enter at h
    rw [List.foldlM_cons] at h
    cases a with
    | value v | moved _ v => exact enter hc params (hfr.cons ha) hrest h
    | place x path =>
      cases hr : Copy.read caller x path with
      | error e => simp [hr, Functor.map, Except.map, bind, Except.bind] at h
      | ok v =>
        simp only [hr, Functor.map, Except.map] at h
        exact enter hc params (hfr.cons (read hc hr)) hrest h

/-- Leaving a call writes back values of the callee's frame. -/
theorem leave {callee : Copy.Frame} (hce : Frame.AllocFree D lim callee) :
    ∀ {fr fr' : Copy.Frame} (params : List (Name × Passed)), Frame.AllocFree D lim fr →
      Copy.leave fr callee params = .ok fr' → Frame.AllocFree D lim fr'
  | fr, fr', [], hfr, h => by cases h; exact hfr
  | fr, fr', (y, a) :: params, hfr, h => by
    unfold Copy.leave at h
    rw [List.foldlM_cons] at h
    cases a with
    | value v | moved _ v => exact leave hce params hfr h
    | place x path =>
      cases hr : Copy.read callee y [] with
      | error e => simp [hr, bind, Except.bind] at h
      | ok v =>
        cases hw : Copy.write fr x path v with
        | error e => simp [hr, hw, bind, Except.bind] at h
        | ok fr₁ =>
          simp only [hr, hw, bind, Except.bind] at h
          exact leave hce params (write hfr (read hce hr) hw) h

end Frame.AllocFree

end Stilt
