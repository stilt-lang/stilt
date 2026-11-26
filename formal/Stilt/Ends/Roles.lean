import Stilt.Panics.Writes
import Stilt.Matching

/-!
# Roles of variables

The check of descending self-calls (facts.descending-self-calls) follows what each variable
of a body holds: the function's descending parameter itself (`whole`), a strict part of it,
reached from it by at least one step through a field, a tuple element or a variant's payload
(`part`), or anything else (`other`). A pattern that matches a variable with a role takes the
steps of its constructors, and a place rooted in such a variable takes the steps of its
fields. A variable keeps its role only where nothing writes it.

Values are finite trees, and a part of a record, a tuple or a variant is smaller than it
(`sizeOf`). So when a variable's role is `whole`, its value is no larger than the parameter's,
and when it is `part`, smaller (`Roles.Inv`).
-/

namespace Stilt

/-- What a variable holds, as far as the check of descending self-calls knows. -/
inductive Role where
  | other
  | whole
  | part
  deriving DecidableEq, Repr

/-- The roles of a body's variables, the newest binding first. -/
abbrev Roles := List (Name × Role)

/-- The role of a variable, `other` when no binding gives it one. -/
def Roles.of : Roles → Name → Role
  | [], _ => .other
  | (y, r) :: R, x => if x = y then r else Roles.of R x

/-- The role of a part of a value of role `r`, through one step. -/
def Role.step : Role → Role
  | .other => .other
  | _ => .part

/-- The role of what an expression gives: a variable's, or, through a field, a strict part of
a value with a role. Steps are never taken through a call, an index or a function value
(facts.descending-self-calls). -/
def Expr.roleIn (R : Roles) : Expr → Role
  | .var x | .move x => R.of x
  | .field e _ => (e.roleIn R).step
  | _ => .other

mutual

/-- Whether a pattern reaches what it binds through fields, tuple elements and variants'
payloads alone: no or-pattern and no list pattern. -/
def Pattern.within : Pattern → Bool
  | .wild | .bind _ | .int _ | .bool _ | .str _ | .unit => true
  | .tuple ps | .variant _ _ ps => patternsWithin ps
  | .record _ fields => fieldPatternsWithin fields
  | .or _ _ | .list _ _ => false

def patternsWithin : List Pattern → Bool
  | [] => true
  | p :: ps => p.within && patternsWithin ps

def fieldPatternsWithin : List (Name × Pattern) → Bool
  | [] => true
  | (_, p) :: fields => p.within && fieldPatternsWithin fields

end

/-- Whether a pattern takes a step before it binds anything: a tuple, record or variant
pattern. -/
def Pattern.steps : Pattern → Bool
  | .tuple _ | .record _ _ | .variant _ _ _ => true
  | _ => false

/-- The role of what an arm binds when its scrutinee has the role `r`: a strict part when
its pattern takes a step, what the scrutinee holds when it binds the scrutinee whole, and
`other` when its pattern has an or-pattern or a list pattern, or its body writes a binder. -/
def Arm.role (r : Role) (arm : Arm) : Role :=
  if arm.pattern.within && arm.binders.all (fun x => decide (x ∉ arm.body.writes)) then
    if arm.pattern.steps then r.step else r
  else .other

/-- The roles with each of `xs` bound with the role `r`, in order. -/
def Roles.bindAll (R : Roles) (xs : List Name) (r : Role) : Roles :=
  xs.foldl (fun R x => (x, r) :: R) R

/-- The bound a role gives a value's size, against the size `m` of the parameter's. -/
def Role.Bounds : Role → Nat → Nat → Prop
  | .other, _, _ => True
  | .whole, a, m => a ≤ m
  | .part, a, m => a < m

/-- Each variable with a role holds a value that its role bounds against `m`. -/
def Roles.Inv (R : Roles) (fr : Copy.Frame) (m : Nat) : Prop :=
  ∀ x, R.of x ≠ .other → ∃ u, fr.lookup x = some u ∧ (R.of x).Bounds (sizeOf u) m

/-- No variable with a role is among `W`. -/
def Roles.Avoids (R : Roles) (W : List Name) : Prop :=
  ∀ x, R.of x ≠ .other → x ∉ W

namespace Roles

variable {R : Roles} {m : Nat}

theorem of_cons (x y : Name) (r : Role) (R : Roles) :
    Roles.of ((y, r) :: R) x = if x = y then r else R.of x := rfl

theorem Inv.nil (fr : Copy.Frame) (m : Nat) : Roles.Inv [] fr m := fun _ h => absurd rfl h

theorem Avoids.nil (W : List Name) : Roles.Avoids [] W := fun _ h => absurd rfl h

theorem Avoids.mono {W W' : List Name} (h : R.Avoids W) (hW : W' ⊆ W) : R.Avoids W' :=
  fun x hx hm => h x hx (hW hm)

theorem Avoids.cons {W : List Name} {x : Name} {r : Role} (h : R.Avoids W)
    (hx : r ≠ .other → x ∉ W) : Roles.Avoids ((x, r) :: R) W := by
  intro y hy
  rw [of_cons] at hy
  split at hy
  · subst_vars; exact hx hy
  · exact h y hy

theorem Inv.keep {W L : List Name} {fr fr' : Copy.Frame} (h : R.Inv fr m) (hA : R.Avoids W)
    (hk : Frame.Keeps W L fr fr') : R.Inv fr' m := by
  intro x hx
  rw [hk.lookup (hA x hx)]
  exact h x hx

theorem Inv.cons {fr : Copy.Frame} {x : Name} {r : Role} {u : Value} (h : R.Inv fr m)
    (hu : r.Bounds (sizeOf u) m) : Roles.Inv ((x, r) :: R) ((x, u) :: fr) m := by
  intro y hy
  rw [of_cons] at hy ⊢
  by_cases hyx : y = x
  · subst hyx
    simp only [↓reduceIte] at hy ⊢
    exact ⟨u, by simp, hu⟩
  · simp only [hyx, ↓reduceIte] at hy ⊢
    obtain ⟨v, hv, hb⟩ := h y hy
    refine ⟨v, ?_, hb⟩
    have : (y == x) = false := by simpa using hyx
    simp [List.lookup, this, hv]

/-- Binding names in order, each to a value its role bounds, keeps the roles. -/
theorem Inv.bindAll {r : Role} :
    ∀ (xs : List Name) (us : List Value) {R : Roles} {fr : Copy.Frame}, R.Inv fr m →
      xs.length = us.length → (∀ u ∈ us, r.Bounds (sizeOf u) m) →
      (R.bindAll xs r).Inv ((xs.zip us).foldl (fun fr b => (b.1, b.2) :: fr) fr) m
  | [], [], _, _, h, _, _ => h
  | x :: xs, u :: us, _, _, h, hl, hu =>
    Inv.bindAll xs us (h.cons (hu u List.mem_cons_self)) (by simpa using hl)
      fun v hv => hu v (List.mem_cons_of_mem _ hv)
  | [], _ :: _, _, _, _, hl, _ | _ :: _, [], _, _, _, hl, _ => by simp at hl

theorem Avoids.bindAll {W : List Name} {r : Role} {xs : List Name} (hx : r ≠ .other → ∀ x ∈ xs, x ∉ W) :
    ∀ {R : Roles}, R.Avoids W → (R.bindAll xs r).Avoids W := by
  induction xs with
  | nil => exact fun h => h
  | cons x xs ih =>
    intro R h
    exact ih (fun hr y hy => hx hr y (List.mem_cons_of_mem _ hy))
      (h.cons fun hr => hx hr x List.mem_cons_self)

end Roles

theorem Role.Bounds.step {r : Role} {a b m : Nat} (hr : r ≠ .other) (h : r.Bounds b m) (hab : a < b) :
    r.step.Bounds a m := by
  cases r
  · exact absurd rfl hr
  · show a < m; exact Nat.lt_of_lt_of_le hab h
  · show a < m; exact Nat.lt_trans hab h

theorem Role.Bounds.mono {r : Role} {a b m : Nat} (h : r.Bounds b m) (hab : a ≤ b) : r.Bounds a m := by
  cases r
  · trivial
  · exact Nat.le_trans hab h
  · exact Nat.lt_of_le_of_lt hab h

theorem Role.step_ne {r : Role} (h : r.step ≠ .other) : r ≠ .other := by
  cases r <;> simp_all [Role.step]

/-! ## Parts are smaller -/

theorem Value.sizeOf_field {R : Name} {fields : List (Name × Value)} {fv : Name × Value}
    (h : fv ∈ fields) : sizeOf fv.2 < sizeOf (Value.record R fields) := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨n, v⟩ := fv
  simp only [Value.record.sizeOf_spec, Prod.mk.sizeOf_spec] at this ⊢
  omega

theorem Value.sizeOf_payload {T C : Name} {vs : List Value} {u : Value} (h : u ∈ vs) :
    sizeOf u < sizeOf (Value.variant T C vs) := by
  have := List.sizeOf_lt_of_mem h
  simp only [Value.variant.sizeOf_spec]
  omega

/-- A field of a value is smaller than it. -/
theorem Value.get_field_lt {v u : Value} {f : Name} (h : v.get [.field f] = .ok u) :
    sizeOf u < sizeOf v := by
  cases v <;> simp only [Value.get, reduceCtorEq] at h
  rename_i R fields
  split at h
  · rename_i u' hl
    simp only [Except.ok.injEq] at h
    subst h
    exact Value.sizeOf_field (fv := (f, u')) (mem_of_lookup hl)
  · cases h

mutual

/-- What a pattern within binds is no larger than the value it matches. -/
theorem Pattern.matchOn_le : ∀ (p : Pattern) {v : Value} {us : List Value}, p.within = true →
    p.matchOn v = some us → ∀ u ∈ us, sizeOf u ≤ sizeOf v
  | .wild, _, _, _, h => by simp [Pattern.matchOn] at h; subst h; simp
  | .bind _, _, _, _, h => by
    simp only [Pattern.matchOn, Option.some.injEq] at h; subst h; simp
  | .int _, v, _, _, h | .bool _, v, _, _, h | .str _, v, _, _, h | .unit, v, _, _, h => by
    cases v <;> simp only [Pattern.matchOn] at h <;> (try split at h) <;> simp_all
  | .tuple ps, v, _, hw, h => fun u hu => Nat.le_of_lt (Pattern.matchOn_lt (.tuple ps) hw rfl h u hu)
  | .record R fps, v, _, hw, h => fun u hu => Nat.le_of_lt (Pattern.matchOn_lt (.record R fps) hw rfl h u hu)
  | .variant T C ps, v, _, hw, h => fun u hu =>
    Nat.le_of_lt (Pattern.matchOn_lt (.variant T C ps) hw rfl h u hu)
  | .or _ _, _, _, hw, _ | .list _ _, _, _, hw, _ => by simp [Pattern.within] at hw

/-- What a pattern within that takes a step binds is smaller than the value it matches. -/
theorem Pattern.matchOn_lt : ∀ (p : Pattern) {v : Value} {us : List Value}, p.within = true →
    p.steps = true → p.matchOn v = some us → ∀ u ∈ us, sizeOf u < sizeOf v
  | .tuple ps, v, _, hw, _, h => by
    cases v <;> simp only [Pattern.matchOn, reduceCtorEq] at h
    rename_i R fields
    refine matchOnAll_lt ps hw (fun u hu => ?_) h
    obtain ⟨fv, hfv, rfl⟩ := List.mem_map.1 hu
    exact Value.sizeOf_field hfv
  | .record _ fps, v, _, hw, _, h => by
    cases v <;> simp only [Pattern.matchOn, reduceCtorEq] at h
    exact matchOnFields_lt fps hw (fun fv hfv => Value.sizeOf_field hfv) h
  | .variant _ C ps, v, _, hw, _, h => by
    cases v <;> simp only [Pattern.matchOn, reduceCtorEq] at h
    split at h
    · exact matchOnAll_lt ps hw (fun u hu => Value.sizeOf_payload hu) h
    · exact nomatch h
  | .wild, _, _, _, hs, _ | .bind _, _, _, _, hs, _ | .int _, _, _, _, hs, _
  | .bool _, _, _, _, hs, _ | .str _, _, _, _, hs, _ | .unit, _, _, _, hs, _
  | .or _ _, _, _, _, hs, _ | .list _ _, _, _, _, hs, _ => by simp [Pattern.steps] at hs

theorem matchOnAll_lt : ∀ (ps : List Pattern) {vs us : List Value} {N : Nat},
    patternsWithin ps = true → (∀ v ∈ vs, sizeOf v < N) → matchOnAll ps vs = some us →
      ∀ u ∈ us, sizeOf u < N
  | [], [], _, _, _, _, h => by simp [matchOnAll] at h; subst h; simp
  | p :: ps, v :: vs, us, _, hw, hv, h => by
    simp only [patternsWithin, Bool.and_eq_true] at hw
    simp only [matchOnAll] at h
    split at h
    · rename_i a b ha hb
      cases h
      intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · exact Nat.lt_of_le_of_lt (Pattern.matchOn_le p hw.1 ha u hu) (hv v List.mem_cons_self)
      · exact matchOnAll_lt ps hw.2 (fun w hw => hv w (List.mem_cons_of_mem _ hw)) hb u hu
    · exact nomatch h
  | [], _ :: _, _, _, _, _, h | _ :: _, [], _, _, _, _, h => by simp [matchOnAll] at h

theorem matchOnFields_lt : ∀ (fps : List (Name × Pattern)) {fields : List (Name × Value)}
    {us : List Value} {N : Nat}, fieldPatternsWithin fps = true →
      (∀ fv ∈ fields, sizeOf fv.2 < N) → matchOnFields fps fields = some us → ∀ u ∈ us, sizeOf u < N
  | [], _, _, _, _, _, h => by simp [matchOnFields] at h; subst h; simp
  | (f, p) :: fps, fields, us, _, hw, hf, h => by
    simp only [fieldPatternsWithin, Bool.and_eq_true] at hw
    simp only [matchOnFields] at h
    split at h
    · rename_i v hl
      split at h
      · rename_i a b ha hb
        cases h
        intro u hu
        rcases List.mem_append.1 hu with hu | hu
        · exact Nat.lt_of_le_of_lt (Pattern.matchOn_le p hw.1 ha u hu) (hf (f, v) (mem_of_lookup hl))
        · exact matchOnFields_lt fps hw.2 hf hb u hu
      · exact nomatch h
    · exact nomatch h

end

/-- What an arm binds, when its scrutinee holds a value of role `r`, its role bounds. -/
theorem Arm.role_bounds {arm : Arm} {r : Role} {v : Value} {us : List Value} {m : Nat}
    (hv : r.Bounds (sizeOf v) m) (h : arm.pattern.matchOn v = some us) :
    ∀ u ∈ us, (arm.role r).Bounds (sizeOf u) m := by
  intro u hu
  unfold Arm.role
  split
  · rename_i hw
    simp only [Bool.and_eq_true] at hw
    split
    · rename_i hs
      cases r with
      | other => trivial
      | whole => exact Nat.lt_of_lt_of_le (Pattern.matchOn_lt _ hw.1 hs h u hu) hv
      | part => exact Nat.lt_trans (Pattern.matchOn_lt _ hw.1 hs h u hu) hv
    · exact hv.mono (Pattern.matchOn_le _ hw.1 h u hu)
  · trivial

/-- An arm gives its binders a role only when its body writes none of them. -/
theorem Arm.role_avoids {arm : Arm} {r : Role} (h : arm.role r ≠ .other) :
    ∀ x ∈ arm.binders, x ∉ arm.body.writes := by
  unfold Arm.role at h
  split at h
  · rename_i hw
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
    exact hw.2
  · exact absurd rfl h

end Stilt
