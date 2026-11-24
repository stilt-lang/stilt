import Stilt.InPlace.Bodies
import Stilt.Matching

/-!
# Safe expressions and values

An expression is safe when it obeys the law of exclusivity and its closure
literals name their parameters once each: these are what in-place agreement
needs of a body. A value is safe when every closure it holds has a safe body
and distinct parameters, so that calling it runs a safe body. Every value a
run of a safe program makes is safe, and the parts of a safe value are safe.
-/

namespace Stilt

/-- The two models of memory run `e` alike: it obeys the law of exclusivity
under some places that loops around it read (modes.law), and its closure
literals name their parameters once each. -/
def Expr.Safe (e : Expr) : Prop := (∃ r, e.exclusive r = true) ∧ e.distinctParams = true

/-- Every closure a value holds, at any depth, has distinct parameters and a
body that obeys the law of exclusivity. A closure literal's body obeys it with
no place read (modes.closures). -/
inductive Value.Safe : Value → Prop
  | int {n : Int} : Value.Safe (.int n)
  | float {x : FloatVal} : Value.Safe (.float x)
  | str {s : String} : Value.Safe (.str s)
  | bool {b : Bool} : Value.Safe (.bool b)
  | unit : Value.Safe .unit
  | record {R : Name} {fields : List (Name × Value)} :
      (∀ fv ∈ fields, Value.Safe fv.2) → Value.Safe (.record R fields)
  | variant {T C : Name} {payload : List Value} :
      (∀ v ∈ payload, Value.Safe v) → Value.Safe (.variant T C payload)
  | list {vs : List Value} : (∀ v ∈ vs, Value.Safe v) → Value.Safe (.list vs)
  | closure {captured : List (Name × Value)} {ps : List Param} {result : Ty} {ρ : Row}
      {body : Expr} :
      (ps.map Param.name).Nodup → body.exclusive [] = true → body.distinctParams = true →
      (∀ xv ∈ captured, Value.Safe xv.2) → Value.Safe (.closure captured ps result ρ body)
  | function {f : Name} {types : List Ty} {rows : List Row} :
      Value.Safe (.function f types rows)
  | handle {u : Ty} {k : Nat} : Value.Safe (.handle u k)

/-- Being safe holds of numbers, Booleans and strings, and passes through
records and lists. -/
theorem Value.Safe.hereditary : Value.Hereditary Value.Safe where
  int _ := .int
  float _ := .float
  bool _ := .bool
  str _ := .str
  record _ _ := ⟨fun h => by cases h; assumption, .record⟩
  list _ := ⟨fun h => by cases h; assumption, .list⟩
  handle _ _ := .handle

/-- The parts of a safe record, variant or list are safe, and a list of safe
values is. -/
theorem Value.Safe.passesToParts : Value.PassesToParts Value.Safe where
  record _ _ h := by cases h; assumption
  variant _ _ _ h := by cases h; assumption
  list _ := ⟨fun h => by cases h; assumption, .list⟩

/-- An operation builds its value from its operands' values, which keeps them
safe. -/
theorem Op.apply_safe {o : Op} {vs : List Value} (hvs : ∀ v ∈ vs, v.Safe) {w : Value}
    (h : o.apply vs = .ok w) : w.Safe :=
  Op.apply_hereditary Value.Safe.hereditary hvs h

theorem Op.run_safe {o : Op} {vs : List Value} (hvs : ∀ v ∈ vs, v.Safe) {x x' : World} {w : Value}
    (h : o.run vs x = .ok (w, x')) : w.Safe :=
  Op.run_hereditary Value.Safe.hereditary .unit hvs h

/-! ## Parts of expressions -/

section Parts

variable {r : List Shape}

theorem exprs_safe : ∀ {es : List Expr}, exprsExclusive r es = true →
    exprsDistinctParams es = true → ∀ e ∈ es, e.Safe
  | [], _, _ => by simp
  | e :: es, h, h' => by
    simp only [exprsExclusive, exprsDistinctParams, Bool.and_eq_true] at h h'
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨⟨r, h.1⟩, h'.1⟩
    · exact exprs_safe h.2 h'.2 e' he'

theorem fields_safe : ∀ {fields : List (Name × Expr)}, fieldsExclusive r fields = true →
    fieldsDistinctParams fields = true → ∀ fe ∈ fields, fe.2.Safe
  | [], _, _ => by simp
  | (f, e) :: fields, h, h' => by
    simp only [fieldsExclusive, fieldsDistinctParams, Bool.and_eq_true] at h h'
    intro fe hfe
    rcases List.mem_cons.1 hfe with rfl | hfe
    · exact ⟨⟨r, h.1⟩, h'.1⟩
    · exact fields_safe h.2 h'.2 fe hfe

/-- The indexes of a place, each safe. -/
def PathSafe (path : List Projection) : Prop := ∀ i, Projection.index i ∈ path → i.Safe

theorem path_safe : ∀ {path : List Projection}, pathExclusive r path = true →
    pathDistinctParams path = true → PathSafe path
  | [], _, _ => by simp [PathSafe]
  | .field f :: path, h, h' => by
    simp only [pathExclusive, pathDistinctParams] at h h'
    intro i hi
    rcases List.mem_cons.1 hi with hi | hi
    · cases hi
    · exact path_safe h h' i hi
  | .index i :: path, h, h' => by
    simp only [pathExclusive, pathDistinctParams, Bool.and_eq_true] at h h'
    intro j hj
    rcases List.mem_cons.1 hj with hj | hj
    · cases hj
      exact ⟨⟨r, h.1⟩, h'.1⟩
    · exact path_safe h.2 h'.2 j hj

/-- The arguments of a call, and the indexes of its `inout` places, each
safe. -/
def ArgsSafe (args : List Arg) : Prop :=
  (∀ e, Arg.value e ∈ args → e.Safe) ∧ ∀ x ps, Arg.inout ⟨x, ps⟩ ∈ args → PathSafe ps

theorem ArgsSafe.cons_value {e : Expr} {args : List Arg} (he : e.Safe) (h : ArgsSafe args) :
    ArgsSafe (.value e :: args) := by
  refine ⟨fun e' he' => ?_, fun x ps hp => ?_⟩
  · rcases List.mem_cons.1 he' with he' | he'
    · cases he'
      exact he
    · exact h.1 e' he'
  · rcases List.mem_cons.1 hp with hp | hp
    · cases hp
    · exact h.2 x ps hp

theorem ArgsSafe.cons_inout {x : Name} {ps : List Projection} {args : List Arg}
    (hps : PathSafe ps) (h : ArgsSafe args) : ArgsSafe (.inout ⟨x, ps⟩ :: args) := by
  refine ⟨fun e' he' => ?_, fun y qs hp => ?_⟩
  · rcases List.mem_cons.1 he' with he' | he'
    · cases he'
    · exact h.1 e' he'
  · rcases List.mem_cons.1 hp with hp | hp
    · cases hp
      exact hps
    · exact h.2 y qs hp

theorem ArgsSafe.tail {a : Arg} {args : List Arg} (h : ArgsSafe (a :: args)) : ArgsSafe args :=
  ⟨fun e he => h.1 e (List.mem_cons_of_mem _ he),
    fun x ps hp => h.2 x ps (List.mem_cons_of_mem _ hp)⟩

theorem args_safe : ∀ {args : List Arg}, argsExclusive r args = true →
    argsDistinctParams args = true → ArgsSafe args
  | [], _, _ => ⟨by simp, by simp⟩
  | .value e :: args, h, h' => by
    simp only [argsExclusive, argsDistinctParams, Bool.and_eq_true] at h h'
    exact ArgsSafe.cons_value ⟨⟨r, h.1⟩, h'.1⟩ (args_safe h.2 h'.2)
  | .inout ⟨x, ps⟩ :: args, h, h' => by
    simp only [argsExclusive, argsDistinctParams, Bool.and_eq_true] at h h'
    exact ArgsSafe.cons_inout (path_safe h.1 h'.1) (args_safe h.2 h'.2)

theorem arms_safe : ∀ {arms : List Arm}, armsExclusive r arms = true →
    armsDistinctParams arms = true → ∀ arm ∈ arms, arm.body.Safe
  | [], _, _ => by simp
  | ⟨C, binders, body⟩ :: arms, h, h' => by
    simp only [armsExclusive, armsDistinctParams, Bool.and_eq_true] at h h'
    intro arm harm
    rcases List.mem_cons.1 harm with rfl | harm
    · exact ⟨⟨_, h.1⟩, h'.1⟩
    · exact arms_safe h.2 h'.2 arm harm

end Parts

/-! ## Parts of values -/

theorem mem_assocSet {β : Type} {k : Name} {b : β} :
    ∀ {l : List (Name × β)} {x : Name × β}, x ∈ assocSet l k b → x ∈ l ∨ x.2 = b
  | [], _, h => by simp [assocSet] at h
  | (k', b') :: l, x, h => by
    simp only [assocSet] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inr rfl
      · exact .inl (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inl List.mem_cons_self
      · exact (mem_assocSet h).imp_left (List.mem_cons_of_mem _)

theorem mem_of_elemAt? {vs : List Value} {i : Int} {v : Value} (h : elemAt? vs i = some v) :
    v ∈ vs := by
  unfold elemAt? at h
  split at h
  · exact List.mem_of_getElem? h
  · cases h

namespace Value.Safe

/-- A part of a safe value is safe. -/
theorem get {v w : Value} {p : Path} (hv : v.Safe) (h : v.get p = .ok w) : w.Safe := by
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

/-- Writing a safe value into a safe value gives a safe value. -/
theorem set {v w v' : Value} {p : Path} (hv : v.Safe) (hw : w.Safe) (h : v.set p w = .ok v') :
    v'.Safe := by
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
              have hsafe := ih (hfs (f, x) (mem_of_lookup hx)) hx'
              refine .record fun fv hfv => ?_
              rcases mem_assocSet hfv with hfv | hfv
              · exact hfs fv hfv
              · exact hfv ▸ hsafe
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
              have hsafe := ih (hvs x (mem_of_elemAt? hx)) hx'
              refine .list fun u hu => ?_
              rcases List.mem_or_eq_of_mem_set hu with hu | rfl
              · exact hvs u hu
              · exact hsafe
        · cases h
      | _ => cases h

end Value.Safe

end Stilt
