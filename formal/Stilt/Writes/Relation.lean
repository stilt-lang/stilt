import Stilt.Writes.Eval
import Stilt.Writes.Checks
import Stilt.Writes.Lists

/-!
# The relation between windows and copies that write

What the proof of `WriteAgreement` keeps between the two models. Their stores
have the same locations, and hold the same values but where a writable
binding writes: there the window's storage holds what the copy's would hold
once the binding's part is written back (`Restored`), and nothing else
reaches it, since E0429 keeps every binding that names it from every access
(projections.what-view-writes).

A read-only window keeps reading its part while no write reaches it: every
binding in scope that can change its location, by holding it or by writing it
through a window (`Changes`), is among the names that the reads and writes in
progress freeze (`Guarded`), as in `Stilt.Views.Relation`.
-/

namespace Stilt.Writes

open Stilt.Views (Store bounded slice cell source Pointwise)

/-! ## Bindings and locations -/

/-- The binding can change the location: it holds it, or writes it through a
window (projections.places-through-views). -/
def Changes : WBinding → Nat → Prop
  | .loc ℓ', ℓ => ℓ' = ℓ
  | .writes (.window ℓ' _ _ _), ℓ => ℓ' = ℓ
  | _, _ => False

/-- The binding writes the location through a window. -/
def Targets : WBinding → Nat → Prop
  | .writes (.window ℓ' _ _ _), ℓ => ℓ' = ℓ
  | _, _ => False

/-- The binding holds a window into the location. -/
def Refers : WBinding → Nat → Prop
  | .view (.window ℓ' _ _ _), ℓ | .writes (.window ℓ' _ _ _), ℓ => ℓ' = ℓ
  | _, _ => False

/-- Every binding of `env` that can change `ℓ`, hidden or not, is named in
`S`: the sources of a view cover its window. -/
def Cover (S : List Name) (env : List (Name × WBinding)) (ℓ : Nat) : Prop :=
  ∀ x b, (x, b) ∈ env → Changes b ℓ → x ∈ S

/-- Every variable in scope that can change `ℓ` is in `F`, which nothing
modifies. -/
def Guarded (F : List Name) (env : List (Name × WBinding)) (ℓ : Nat) : Prop :=
  ∀ x b, env.lookup x = some b → Changes b ℓ → x ∈ F

/-- No binding of `env` holds a window into `ℓ`. -/
def Alone (env : List (Name × WBinding)) (ℓ : Nat) : Prop :=
  ∀ x b, (x, b) ∈ env → ¬Refers b ℓ

theorem Cover.guarded {S : List Name} {env : List (Name × WBinding)} {ℓ : Nat}
    (h : Cover S env ℓ) (R W : List Name) : Guarded ((S ++ R) ++ W) env ℓ :=
  fun x b hx hc => by simp [h x b (Views.mem_of_lookup hx) hc]

theorem Guarded.mono {F F' : List Name} {env : List (Name × WBinding)} {ℓ : Nat}
    (h : Guarded F env ℓ) (hF : ∀ x ∈ F, x ∈ F') : Guarded F' env ℓ :=
  fun x b hx hc => hF _ (h x b hx hc)

/-! ## Agreement -/

/-- A value of the window model and one of the copy model agree: the same
value, or a window that reads the part the copy holds, with the place it
writes back to when the copy has one. -/
def Agrees (store : Store) : WVal → WVal → Prop
  | .val v, .val w => v = w
  | .window ℓ π a b, .copied part => (WVal.window ℓ π a b).part store = .ok part
  | .window ℓ π a b, .pending part ℓ' π' a' b' =>
    ℓ = ℓ' ∧ π = π' ∧ a = a' ∧ b = b' ∧ (WVal.window ℓ π a b).part store = .ok part
  | _, _ => False

/-- The window's storage at `ℓ` is the copy's with `part` written back. -/
def Restored (sw sc : Store) (ℓ : Nat) (π : Path) (a b : Int) (part : List Value) : Prop :=
  ∃ c c', cell sc ℓ = .ok c ∧ cell sw ℓ = .ok c' ∧ restore c π a b part = .ok c'

/-- Two bindings agree: the same location, views that agree, or a writable
binding's window and copy, whose part written back gives the window's
storage. -/
def BAgrees (sw sc : Store) : WBinding → WBinding → Prop
  | .loc ℓ, .loc ℓ' => ℓ = ℓ'
  | .view r, .view r' => Agrees sw r r'
  | .writes (.window ℓ π a b), .writes (.pending part ℓ' π' a' b') =>
    ℓ = ℓ' ∧ π = π' ∧ a = a' ∧ b = b' ∧ Restored sw sc ℓ π a b part
  | _, _ => False

/-- Two environments bind the same names, in the same order, to bindings that
agree. -/
def EnvAgrees (sw sc : Store) : List (Name × WBinding) → List (Name × WBinding) → Prop :=
  Pointwise fun e c => e.1 = c.1 ∧ BAgrees sw sc e.2 c.2

/-- The window state and the copy state agree: stores of the same length, the
same at every location that no writable binding writes, environments that
agree, and every location in scope allocated. -/
structure StateAgrees (sw sc : WState) : Prop where
  length : sw.store.length = sc.store.length
  env : EnvAgrees sw.store sc.store sw.env sc.env
  off : ∀ ℓ, (∀ x b, (x, b) ∈ sw.env → ¬Targets b ℓ) → sw.store[ℓ]? = sc.store[ℓ]?
  locs : ∀ x ℓ, (x, WBinding.loc ℓ) ∈ sw.env → ℓ < sw.store.length

/-- What the static analysis knows of the window state's environment, with the
sources `Γ`, the reads `R` and the writes `W`: each location has one binding
and at most one writable binding that writes it, every read-only window is
guarded, every name of a location that a writable binding writes is among the
writes (E0429), and each binding's sources cover its window. -/
structure InScope (Γ : Sources) (R W : List Name) (env : List (Name × WBinding)) : Prop where
  distinct : ∀ x y ℓ, (x, WBinding.loc ℓ) ∈ env → (y, WBinding.loc ℓ) ∈ env → x = y
  apart : env.Pairwise fun e e' => ∀ ℓ, Targets e.2 ℓ → ¬Targets e'.2 ℓ
  guarded : ∀ x ℓ π a b, (x, WBinding.view (.window ℓ π a b)) ∈ env → Guarded (R ++ W) env ℓ
  locked : ∀ x b ℓ, (x, b) ∈ env → Targets b ℓ → ∀ y, env.lookup y = some (.loc ℓ) → y ∈ W
  sources : Pointwise (fun (g : Name × List Name) (e : Name × WBinding) =>
    g.1 = e.1 ∧ ∀ ℓ, Refers e.2 ℓ → Cover g.2 env ℓ) Γ env

/-! ## Steps -/

/-- No location that `F` guards changed from `s` to `s'`. -/
def Preserves (F : List Name) (s s' : WState) : Prop :=
  ∀ ℓ, Guarded F s.env ℓ → ℓ < s.store.length → s'.store[ℓ]? = s.store[ℓ]?

/-- What an evaluation does to the window state: the same environment, a
store that has grown, and every guarded location as it was. -/
structure Steps (F : List Name) (s s' : WState) : Prop where
  env : s'.env = s.env
  grows : s.store.length ≤ s'.store.length
  preserves : Preserves F s s'

theorem Steps.refl (F : List Name) (s : WState) : Steps F s s :=
  ⟨rfl, Nat.le_refl _, fun _ _ _ => rfl⟩

/-- Steps compose, the later ones under more names frozen. -/
theorem Steps.trans {F F' : List Name} {s₀ s₁ s₂ : WState} (h₁ : Steps F s₀ s₁)
    (h₂ : Steps F' s₁ s₂) (hF : ∀ x ∈ F, x ∈ F') : Steps F s₀ s₂ := by
  refine ⟨h₂.env.trans h₁.env, Nat.le_trans h₁.grows h₂.grows, fun ℓ hg hℓ => ?_⟩
  rw [h₂.preserves ℓ (h₁.env ▸ hg.mono hF) (Nat.lt_of_lt_of_le hℓ h₁.grows),
    h₁.preserves ℓ hg hℓ]

theorem cell_congr {st st' : Store} {ℓ : Nat} (h : st'[ℓ]? = st[ℓ]?) : cell st' ℓ = cell st ℓ := by
  simp [cell, h]

theorem part_lt {store : Store} {ℓ : Nat} {π : Path} {a b : Int} {part : List Value}
    (h : (WVal.window ℓ π a b).part store = .ok part) : ℓ < store.length := by
  simp only [WVal.part] at h
  split at h
  · exact Views.source_lt (by assumption)
  · cases h

theorem part_congr {st st' : Store} {ℓ : Nat} (π : Path) (a b : Int) (h : st'[ℓ]? = st[ℓ]?) :
    (WVal.window ℓ π a b).part st' = (WVal.window ℓ π a b).part st := by
  simp only [WVal.part, source, cell_congr h]

/-- A window that a step leaves guarded keeps reading its part. -/
theorem Agrees.preserved {F : List Name} {s s' : WState} {rw rc : WVal}
    (h : Agrees s.store rw rc) (hw : ∀ ℓ π a b, rw = .window ℓ π a b → Guarded F s.env ℓ)
    (hp : Preserves F s s') : Agrees s'.store rw rc := by
  cases rw <;> cases rc <;> simp only [Agrees] at h ⊢
  · exact h
  · rename_i ℓ π a b _
    rw [part_congr π a b (hp ℓ (hw ℓ π a b rfl) (part_lt h))]
    exact h
  · rename_i ℓ π a b _ _ _ _ _
    rw [part_congr π a b (hp ℓ (hw ℓ π a b rfl) (part_lt h.2.2.2.2))]
    exact h

/-- What evaluating an expression ends with, from the window state `s₀`:
states that agree, a step under the names `F`, values that agree, a window
that the sources `S` cover, and, for an expression whose view writes (`P`), a
window and the copy with the place it writes back to, into a location that no
binding of `s₀` views and that a variable nothing freezes holds. -/
structure Post (F S : List Name) (P : Prop) (s₀ sw sc : WState) (rw rc : WVal) : Prop where
  states : StateAgrees sw sc
  steps : Steps F s₀ sw
  agrees : Agrees sw.store rw rc
  within : ∀ ℓ π a b, rw = .window ℓ π a b → Cover S s₀.env ℓ
  pend : P → ∃ part ℓ π a b, rw = .window ℓ π a b ∧ rc = .pending part ℓ π a b ∧
    Alone s₀.env ℓ ∧ ∃ y, s₀.env.lookup y = some (.loc ℓ) ∧ y ∉ F

/-- An operand's value, the same in both models, with states that agree after
a step under the names `F`. -/
structure Operand {α : Type} (F : List Name) (s₀ sw sc : WState) (a b : α) : Prop where
  eq : a = b
  states : StateAgrees sw sc
  steps : Steps F s₀ sw

theorem Post.val {F S : List Name} {P : Prop} {s₀ s sc : WState} {v : Value}
    (hst : StateAgrees s sc) (hs : Steps F s₀ s) (hP : ¬P) :
    Post F S P s₀ s sc (.val v) (.val v) :=
  ⟨hst, hs, rfl, fun _ _ _ _ h => (nomatch h), fun h => absurd h hP⟩

/-- A view that a post gives keeps reading its part through a step under its
sources. -/
theorem Post.held {F S R W : List Name} {P : Prop} {s₀ s₁ s sc₁ : WState} {rw rc : WVal}
    (h : Post F S P s₀ s₁ sc₁ rw rc) (hs : Steps ((S ++ R) ++ W) s₁ s) : Agrees s.store rw rc :=
  h.agrees.preserved (fun ℓ π a b he => h.steps.env ▸ (h.within ℓ π a b he).guarded R W)
    hs.preserves

end Stilt.Writes
