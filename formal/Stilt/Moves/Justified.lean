import Stilt.Moves.Analysis
import Stilt.InPlace.Safe

/-!
# Justified values

A value is justified when every closure it holds has a body whose marks are
last uses, so that calling it runs a body that `Moving` may run with its
marks. Every value a run of a justified program makes is justified, and the
parts of a justified value are justified.
-/

namespace Stilt

/-- Every closure a value holds, at any depth, has a body whose marks are
last uses, the body handing its `inout` parameters back (values.passing-values). -/
inductive Value.Justified : Value → Prop
  | int {n : Int} : Value.Justified (.int n)
  | float {x : FloatVal} : Value.Justified (.float x)
  | str {s : String} : Value.Justified (.str s)
  | bool {b : Bool} : Value.Justified (.bool b)
  | unit : Value.Justified .unit
  | record {R : Name} {fields : List (Name × Value)} :
      (∀ fv ∈ fields, Value.Justified fv.2) → Value.Justified (.record R fields)
  | variant {T C : Name} {payload : List Value} :
      (∀ v ∈ payload, Value.Justified v) → Value.Justified (.variant T C payload)
  | list {vs : List Value} : (∀ v ∈ vs, Value.Justified v) → Value.Justified (.list vs)
  | closure {captured : List (Name × Value)} {ps : List Param} {result : Ty} {ρ : Row}
      {body : Expr} :
      body.movesOk (inoutLive ps) = true → (∀ xv ∈ captured, Value.Justified xv.2) →
      Value.Justified (.closure captured ps result ρ body)
  | function {f : Name} {types : List Ty} {rows : List Row} :
      Value.Justified (.function f types rows)
  | handle {u : Ty} {k : Nat} : Value.Justified (.handle u k)

namespace Value.Justified

/-- A part of a justified value is justified. -/
theorem get {v w : Value} {p : Path} (hv : v.Justified) (h : v.get p = .ok w) : w.Justified := by
  induction p generalizing v with
  | nil =>
    cases h
    exact hv
  | cons s p ih =>
    cases s with
    | field f =>
      cases v with
      | record R fields =>
        simp only [Value.get] at h
        split at h
        · rename_i x hx
          cases hv with
          | record hfs => exact ih (hfs (f, x) (mem_of_lookup hx)) h
        · cases h
      | _ => cases h
    | index i =>
      cases v with
      | list vs =>
        simp only [Value.get] at h
        split at h
        · rename_i x hx
          cases hv with
          | list hvs => exact ih (hvs x (mem_of_elemAt? hx)) h
        · cases h
      | _ => cases h

/-- Writing a justified value into a justified value gives a justified value. -/
theorem set {v w v' : Value} {p : Path} (hv : v.Justified) (hw : w.Justified)
    (h : v.set p w = .ok v') : v'.Justified := by
  induction p generalizing v v' with
  | nil =>
    cases h
    exact hw
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
            cases hv with
            | record hfs =>
              have hj := ih (hfs (f, x) (mem_of_lookup hx)) hx'
              refine .record fun fv hfv => ?_
              rcases mem_assocSet hfv with hfv | hfv
              · exact hfs fv hfv
              · exact hfv ▸ hj
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
            cases hv with
            | list hvs =>
              have hj := ih (hvs x (mem_of_elemAt? hx)) hx'
              refine .list fun u hu => ?_
              rcases List.mem_or_eq_of_mem_set hu with hu | rfl
              · exact hvs u hu
              · exact hj
        · cases h
      | _ => cases h

end Value.Justified

/-- Being justified holds of numbers, Booleans and strings, and passes through
records and lists. -/
theorem Value.Justified.hereditary : Value.Hereditary Value.Justified where
  int _ := .int
  float _ := .float
  bool _ := .bool
  str _ := .str
  record _ _ := ⟨fun h => by cases h; assumption, .record⟩
  list _ := ⟨fun h => by cases h; assumption, .list⟩
  handle _ _ := .handle

/-- The parts of a justified record, variant or list are justified, and a list
of justified values is. -/
theorem Value.Justified.passesToParts : Value.PassesToParts Value.Justified where
  record _ _ h := by cases h; assumption
  variant _ _ _ h := by cases h; assumption
  list _ := ⟨fun h => by cases h; assumption, .list⟩

/-- An operation builds its value from its operands' values, which keeps them
justified. -/
theorem Op.apply_justified {o : Op} {vs : List Value} (hvs : ∀ v ∈ vs, v.Justified) {w : Value}
    (h : o.apply vs = .ok w) : w.Justified :=
  Op.apply_hereditary Value.Justified.hereditary hvs h

theorem Op.run_justified {o : Op} {vs : List Value} (hvs : ∀ v ∈ vs, v.Justified) {x x' : World}
    {w : Value} (h : o.run vs x = .ok (w, x')) : w.Justified :=
  Op.run_hereditary Value.Justified.hereditary .unit hvs h

end Stilt
