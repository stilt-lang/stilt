import Stilt.Paths
import Stilt.Related
import Stilt.Views.Eval
import Stilt.Views.Reads

/-!
# The relation between windows and copies

What the proof of `ViewAgreement` keeps between the two models. Their stores
are equal, since only views differ, and a view is never stored (views.view-types). A window and a copy agree when the window reads, in the store, the
part the copy holds (`Agrees`).

A window keeps reading that part while no write reaches its source. The law of
exclusivity gives that through the shapes of the places being read: a window
into the location `ℓ` is `Guarded` by the reads `R` when every variable that
names `ℓ` names it by a shape in `R`, so that a write that `R` allows, to a
place whose shape overlaps none of `R`, reaches a part disjoint from the
window's (`get_of_set_apart`). A view's sources `Cover` its window when every
binding of `ℓ`, hidden or not, names it by one of them: that survives the
scopes that end around the view, as its sources do.
-/

namespace Stilt.Views

/-! ## Paths -/

/-- The fields of a path, with its indexes removed (modes.overlap). -/
def fieldsOf : Path → List Name
  | [] => []
  | .field f :: π => f :: fieldsOf π
  | .index _ :: π => fieldsOf π

theorem fieldsOf_append : ∀ (π π' : Path), fieldsOf (π ++ π') = fieldsOf π ++ fieldsOf π'
  | [], _ => rfl
  | .field f :: π, π' => by simp [fieldsOf, fieldsOf_append π π']
  | .index _ :: π, π' => by simp [fieldsOf, fieldsOf_append π π']

/-- Paths whose fields don't extend one another reach disjoint parts of any
value, whatever their indexes: modes.overlap misses no overlap. -/
theorem disjoint_of_fields : ∀ {π π' : Path},
    (fieldsOf π).isPrefixOf (fieldsOf π') = false →
    (fieldsOf π').isPrefixOf (fieldsOf π) = false → Path.Disjoint π π'
  | [], _, h, _ => by simp [fieldsOf] at h
  | _ :: _, [], _, h => by simp [fieldsOf] at h
  | s :: π, t :: π', h₁, h₂ => by
    by_cases hst : s = t
    · subst hst
      refine .inr (disjoint_of_fields ?_ ?_)
      · cases s <;> simpa [fieldsOf, List.isPrefixOf] using h₁
      · cases s <;> simpa [fieldsOf, List.isPrefixOf] using h₂
    · exact .inl hst

/-- A write to a place whose shape doesn't overlap a source's leaves the
source as it was (modes.overlapping-inout). -/
theorem get_of_set_apart {v w v' : Value} {x : Name} {π π' : Path}
    (h : (Shape.mk x (fieldsOf π')).overlaps ⟨x, fieldsOf π⟩ = false)
    (hs : v.set π' w = .ok v') : v'.get π = v.get π := by
  simp only [Shape.overlaps, beq_self_eq_true, Bool.true_and, Bool.or_eq_false_iff] at h
  exact Value.get_of_set_disjoint (disjoint_of_fields h.1 h.2) hs

/-! ## Stores -/

theorem cell_lt {store : Store} {ℓ : Nat} {v : Value} (h : cell store ℓ = .ok v) :
    ℓ < store.length := by
  unfold cell at h
  split at h
  · rename_i heq
    exact (List.getElem?_eq_some_iff.1 heq).1
  · cases h

theorem source_lt {store : Store} {ℓ : Nat} {π : Path} {v : Value}
    (h : source store ℓ π = .ok v) : ℓ < store.length := by
  unfold source at h
  split at h
  · exact cell_lt (by assumption)
  · cases h

theorem part_lt {store : Store} {ℓ : Nat} {π : Path} {a b : Int} {part : List Value}
    (h : (RVal.window ℓ π a b).part store = .ok part) : ℓ < store.length := by
  simp only [RVal.part] at h
  split at h
  · exact source_lt (by assumption)
  · cases h

theorem cell_append {store : Store} {ℓ : Nat} (c : Store) (h : ℓ < store.length) :
    cell (store ++ c) ℓ = cell store ℓ := by
  simp [cell, List.getElem?_append_left h]

theorem source_append {store : Store} {ℓ : Nat} (c : Store) (π : Path) (h : ℓ < store.length) :
    source (store ++ c) ℓ π = source store ℓ π := by
  simp [source, cell_append c h]

theorem source_set_ne {store : Store} {ℓ ℓ' : Nat} (c : Option Value) (π : Path) (h : ℓ' ≠ ℓ) :
    source (store.set ℓ' c) ℓ π = source store ℓ π := by
  simp [source, cell, List.getElem?_set_ne h]

/-- A window reads the same part wherever its source is the same. -/
theorem part_congr {store store' : Store} {ℓ : Nat} {π : Path} (a b : Int)
    (h : source store' ℓ π = source store ℓ π) :
    (RVal.window ℓ π a b).part store' = (RVal.window ℓ π a b).part store := by
  simp only [RVal.part, h]

/-! ## Covering -/

/-- Every binding of `env` that has the location `ℓ`, hidden or not, names the
part along `π` there by a shape in `S`. -/
def Covered (S : List Shape) (env : List (Name × Binding)) (ℓ : Nat) (π : Path) : Prop :=
  ∀ x, (x, Binding.loc ℓ) ∈ env → (⟨x, fieldsOf π⟩ : Shape) ∈ S

/-- Every variable in scope that has the location `ℓ` names the part along `π`
there by a shape in `R`. -/
def Guarded (R : List Shape) (env : List (Name × Binding)) (ℓ : Nat) (π : Path) : Prop :=
  ∀ x, env.lookup x = some (Binding.loc ℓ) → (⟨x, fieldsOf π⟩ : Shape) ∈ R

theorem mem_of_lookup {β : Type} : ∀ {env : List (Name × β)} {x : Name} {b : β},
    env.lookup x = some b → (x, b) ∈ env
  | [], _, _, h => by cases h
  | (y, c) :: env, x, b, h => by
    by_cases hxy : x = y
    · subst hxy
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · rw [lookup_cons_ne hxy] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup h)

theorem Covered.guarded {S : List Shape} {env : List (Name × Binding)} {ℓ : Nat} {π : Path}
    (h : Covered S env ℓ π) (R : List Shape) : Guarded (S ++ R) env ℓ π :=
  fun x hx => List.mem_append_left _ (h x (mem_of_lookup hx))

theorem Covered.mono {S S' : List Shape} {env : List (Name × Binding)} {ℓ : Nat} {π : Path}
    (h : Covered S env ℓ π) (hS : ∀ s ∈ S, s ∈ S') : Covered S' env ℓ π :=
  fun x hx => hS _ (h x hx)

theorem Guarded.mono {R R' : List Shape} {env : List (Name × Binding)} {ℓ : Nat} {π : Path}
    (h : Guarded R env ℓ π) (hR : ∀ s ∈ R, s ∈ R') : Guarded R' env ℓ π :=
  fun x hx => hR _ (h x hx)

/-- What a view's sources cover, if it is a window. -/
def RVal.Within (S : List Shape) (env : List (Name × Binding)) : RVal → Prop
  | .window ℓ π _ _ => Covered S env ℓ π
  | _ => True

theorem RVal.Within.mono {S S' : List Shape} {env : List (Name × Binding)} {r : RVal}
    (h : r.Within S env) (hS : ∀ s ∈ S, s ∈ S') : r.Within S' env := by
  cases r <;> first | trivial | exact Covered.mono h hS

/-! ## Agreement -/

/-- A run-time value of the window model and one of the copy model agree: the
same value, or a window that reads the part the copy holds. -/
def Agrees (store : Store) : RVal → RVal → Prop
  | .val v, .val w => v = w
  | .window ℓ π a b, .copied part => (RVal.window ℓ π a b).part store = .ok part
  | _, _ => False

/-- Two bindings agree: the same location, or views that agree. -/
def BAgrees (store : Store) : Binding → Binding → Prop
  | .loc ℓ, .loc ℓ' => ℓ = ℓ'
  | .view r, .view r' => Agrees store r r'
  | _, _ => False

/-- Two lists of the same length, related element by element. -/
inductive Pointwise {α β : Type} (P : α → β → Prop) : List α → List β → Prop
  | nil : Pointwise P [] []
  | cons {a b as bs} : P a b → Pointwise P as bs → Pointwise P (a :: as) (b :: bs)

theorem Pointwise.imp {α β : Type} {P Q : α → β → Prop} (h : ∀ a b, P a b → Q a b) :
    ∀ {as : List α} {bs : List β}, Pointwise P as bs → Pointwise Q as bs
  | _, _, .nil => .nil
  | _, _, .cons hab hrest => .cons (h _ _ hab) (Pointwise.imp h hrest)

/-- Two environments bind the same names, in the same order, to bindings that
agree. -/
def EnvAgrees (store : Store) : List (Name × Binding) → List (Name × Binding) → Prop :=
  Pointwise fun b c => b.1 = c.1 ∧ BAgrees store b.2 c.2

/-- The window state and the copy state agree: the same store, environments
that agree, and every location in scope allocated. -/
structure StateAgrees (sw sc : VState) : Prop where
  store : sw.store = sc.store
  env : EnvAgrees sw.store sw.env sc.env
  locs : ∀ x ℓ, (x, Binding.loc ℓ) ∈ sw.env → ℓ < sw.store.length

/-- What the static analysis knows of an environment, with the sources `Γ` of
its bindings and the reads `R`: each location has one binding, every window in
scope is guarded by `R`, and each binding's sources cover its window. -/
structure InScope (Γ : Sources) (R : List Shape) (env : List (Name × Binding)) : Prop where
  distinct : ∀ x y ℓ, (x, Binding.loc ℓ) ∈ env → (y, Binding.loc ℓ) ∈ env → x = y
  guarded : ∀ x ℓ π a b, (x, Binding.view (.window ℓ π a b)) ∈ env → Guarded R env ℓ π
  sources : Pointwise (fun (g : Name × List Shape) (e : Name × Binding) =>
    g.1 = e.1 ∧ ∀ ℓ π a b, e.2 = .view (.window ℓ π a b) → Covered g.2 env ℓ π) Γ env

theorem InScope.mono {Γ : Sources} {R R' : List Shape} {env : List (Name × Binding)}
    (h : InScope Γ R env) (hR : ∀ s ∈ R, s ∈ R') : InScope Γ R' env :=
  ⟨h.distinct, fun x ℓ π a b hx => (h.guarded x ℓ π a b hx).mono hR, h.sources⟩

/-! ## Steps -/

/-- No part that `R` guards changed from `s` to `s'`. -/
def Preserves (R : List Shape) (s s' : VState) : Prop :=
  ∀ ℓ π, Guarded R s.env ℓ π → ℓ < s.store.length → source s'.store ℓ π = source s.store ℓ π

/-- What an evaluation does to the window state: it ends with the same
environment, a store that has grown, and every part that its reads guard as
it was. -/
structure Steps (R : List Shape) (s s' : VState) : Prop where
  env : s'.env = s.env
  grows : s.store.length ≤ s'.store.length
  preserves : Preserves R s s'

theorem Steps.refl (R : List Shape) (s : VState) : Steps R s s :=
  ⟨rfl, Nat.le_refl _, fun _ _ _ _ => rfl⟩

/-- Steps compose, the later ones under more reads. -/
theorem Steps.trans {R R' : List Shape} {s₀ s₁ s₂ : VState} (h₁ : Steps R s₀ s₁)
    (h₂ : Steps R' s₁ s₂) (hR : ∀ s ∈ R, s ∈ R') : Steps R s₀ s₂ := by
  refine ⟨h₂.env.trans h₁.env, Nat.le_trans h₁.grows h₂.grows, fun ℓ π hg hℓ => ?_⟩
  rw [h₂.preserves ℓ π (h₁.env ▸ hg.mono hR) (Nat.lt_of_lt_of_le hℓ h₁.grows),
    h₁.preserves ℓ π hg hℓ]

/-- A window that the reads guard keeps reading its part. -/
theorem Agrees.preserved {R : List Shape} {s s' : VState} {rw rc : RVal}
    (h : Agrees s.store rw rc) (hw : ∀ ℓ π a b, rw = .window ℓ π a b → Guarded R s.env ℓ π)
    (hp : Preserves R s s') : Agrees s'.store rw rc := by
  cases rw <;> cases rc <;> simp only [Agrees] at h ⊢
  · exact h
  · rename_i ℓ π a b _
    rw [part_congr a b (hp ℓ π (hw ℓ π a b rfl) (part_lt h))]
    exact h

/-- What evaluating an expression ends with, from the window state `s₀`: states
that agree, a step under the reads `R`, values that agree, and a view whose
sources `S` cover its window. -/
structure Post (R S : List Shape) (s₀ sw sc : VState) (rw rc : RVal) : Prop where
  states : StateAgrees sw sc
  steps : Steps R s₀ sw
  agrees : Agrees sw.store rw rc
  within : rw.Within S s₀.env

/-! ## Outcomes -/

/-- What two outcomes that agree relate: values with states that `Q` relates,
or the same panic. The calculus has no `raise` and performs no operation, and
no jump reaches the end of an evaluation. -/
def Agree.relation {σ α β : Type} (Q : σ → σ → α → β → Prop) : Outcome.Relation σ σ α β where
  done a sw b sc := Q sw sc a b
  raised _ _ _ _ := False
  jumped _ _ _ _ := False
  panicked k _ k' _ := k = k'
  performed _ _ _ _ _ _ := False
  resume _ _ _ _ _ := False

/-- Two outcomes agree: values with states that `Q` relates, or the same
panic, out of fuel, or stuck. -/
def Agree {σ α β : Type} (Q : σ → σ → α → β → Prop) : Outcome σ α → Outcome σ β → Prop :=
  Outcome.Rel (Agree.relation Q)

/-- Two results agree: values that `P` relates, or the same fault. -/
def ExceptAgree {α β : Type} (P : α → β → Prop) : Except Fault α → Except Fault β → Prop
  | .ok a, .ok b => P a b
  | .error f, .error f' => f = f'
  | _, _ => False

end Stilt.Views
