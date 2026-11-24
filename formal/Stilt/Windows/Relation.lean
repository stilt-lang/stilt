import Stilt.Windows.Inst
import Stilt.Windows.Resolve
import Stilt.Windows.Eval
import Stilt.Windows.Guards.Regions
import Stilt.ViewReads
import Stilt.ViewContained
import Stilt.Cells
import Stilt.Related

/-!
# The relation of windows to in-place mutation

What the agreement of the model of windows with the in-place model keeps of their states and
values while both run a body that the checks of views accept.

* `Holds`: a window reads the same part of both stores, live in the store of windows, a string
  or a list that holds no window.
* `VRel`: a value of windows read against the in-place store is the in-place value, and each of
  its windows holds.
* `Agree`: the states have the same variables and world and stores of the same length, every
  live location of windows read against the in-place store is the in-place one, and the
  in-place values are ones the checks accept (`Value.Viewed`).
* `Tracked`: a window lies in the part of the store that one of a value's sources names, or is
  one that the body's parameters brought in (`In`).
* `Fits`: the variables agree name by name with the scope the checks read, the newest first,
  each holding a value its sources track; the oldest, a closure's captured variables, hold no
  window.
-/

namespace Stilt

open InPlace (Ref)

namespace Windows

/-- A scope whose bindings with a type that holds no view keep no sources: the body's own, as
`ViewScope.bind` makes them, and its parameters, as `ViewScope.params` makes them. Every scope
the checks read is one. -/
structure ScopeKeeps (D : Decls) (Γ : ViewScope) : Prop where
  own : ∀ xb ∈ Γ, xb.2.param = false → ∀ τ, xb.2.type = some τ → τ.holdsView D = false →
    xb.2.sources = []
  given : ∀ xb ∈ Γ, xb.2.param = true → ∀ τ, xb.2.type = some τ → τ.holdsView D = false →
    xb.2.sources = []

theorem ScopeKeeps.nil (D : Decls) : ScopeKeeps D [] :=
  ⟨fun _ h => (nomatch h), fun _ h => nomatch h⟩

theorem ScopeKeeps.bind {D : Decls} {Γ : ViewScope} (h : ScopeKeeps D Γ) (x : Name) (τ : Ty)
    (S : List Shape) : ScopeKeeps D (Γ.bind D x τ S) := by
  refine ⟨fun xb hxb hp σ hσ hv => ?_, fun xb hxb hp σ hσ hv => ?_⟩
  · rcases List.mem_cons.1 hxb with rfl | hxb
    · simp only [Option.some.injEq] at hσ
      subst hσ
      simp [hv]
    · exact h.own xb hxb hp σ hσ hv
  · rcases List.mem_cons.1 hxb with rfl | hxb
    · cases hp
    · exact h.given xb hxb hp σ hσ hv

end Windows

/-! ## Values the checks accept -/

/-- A closure's parameters and body are an instance of a literal the checks of views accept,
in some scope that keeps its bindings' sources, the literal naming its parameters once. -/
def ClosureChecked (D : Decls) (ps : List Param) (body : Expr) : Prop :=
  ∃ (Γ : ViewScope) (ps₀ : List Param) (result₀ : Ty) (b₀ : Expr),
    Windows.ScopeKeeps D Γ ∧ (ps₀.map Param.name).Nodup ∧
    ParamsInst D ps₀ ps ∧ Expr.Inst D b₀ body ∧
      b₀.viewsRead D (Γ.enter D ps₀) [] = true ∧
      b₀.contained D (Γ.enter D ps₀) (resultParams D ps₀ result₀) = true ∧
      leaves (resultParams D ps₀ result₀) (b₀.sources D (Γ.enter D ps₀)) = true

/-- A value with no window anywhere, closures' captured values included, whose closures are
ones the checks of views accept. -/
inductive Value.Viewed (D : Decls) : Value → Prop
  | int {n : Int} : Value.Viewed D (.int n)
  | float {x : FloatVal} : Value.Viewed D (.float x)
  | str {s : String} : Value.Viewed D (.str s)
  | bool {b : Bool} : Value.Viewed D (.bool b)
  | unit : Value.Viewed D .unit
  | record {R : Name} {fields : List (Name × Value)} :
      (∀ fv ∈ fields, Value.Viewed D fv.2) → Value.Viewed D (.record R fields)
  | variant {T C : Name} {payload : List Value} :
      (∀ v ∈ payload, Value.Viewed D v) → Value.Viewed D (.variant T C payload)
  | list {vs : List Value} : (∀ v ∈ vs, Value.Viewed D v) → Value.Viewed D (.list vs)
  | closure {captured : List (Name × Value)} {ps : List Param} {result : Ty} {ρ : Row}
      {body : Expr} : (∀ xv ∈ captured, Value.Viewed D xv.2) → ClosureChecked D ps body →
      Value.Viewed D (.closure captured ps result ρ body)
  | function {f : Name} {types : List Ty} {rows : List Row} :
      Value.Viewed D (.function f types rows)
  | handle {u : Ty} {k : Nat} : Value.Viewed D (.handle u k)

theorem Value.Viewed.hereditary (D : Decls) : Value.Hereditary (Value.Viewed D) where
  int _ := .int
  float _ := .float
  bool _ := .bool
  str _ := .str
  record _ _ := ⟨fun h => by cases h; assumption, .record⟩
  list _ := ⟨fun h => by cases h; assumption, .list⟩
  handle _ _ := .handle

namespace Windows

/-! ## Windows read alike -/

/-- The value at a location of the in-place store. -/
def cellIn (si : List Value) (loc : Nat) : Except Fault Value :=
  match si[loc]? with
  | some v => .ok v
  | none => .error .stuck

/-- The part of a store of windows at a window's region, before its ranges. -/
def regionW (sw : List (Option Value)) (w : Window) : Except Fault Value :=
  cell sw w.1 >>= (·.get w.2.1)

/-- The part of the in-place store at a window's region, before its ranges. -/
def regionI (si : List Value) (w : Window) : Except Fault Value :=
  cellIn si w.1 >>= (·.get w.2.1)

/-- A window reads the same part of both stores: its region is live in the store of windows,
and holds there, as in the in-place store, a string or a list with no window. -/
def Holds (sw : List (Option Value)) (si : List Value) (w : Window) : Prop :=
  ∃ d, regionW sw w = .ok d ∧ regionI si w = .ok d ∧ Free d ∧ viewable d = true

/-- A value of windows and an in-place value: read against the in-place store, the first is
the second, and each of its windows holds. -/
def VRel (si : List Value) (sw : List (Option Value)) (w v : Value) : Prop :=
  resolveIn si w = .ok v ∧ ∀ win ∈ windowsOf w, Holds sw si win

/-- An in-place state and a state of windows that agree. -/
structure Agree (D : Decls) (si : InPlace.State × World) (sw : State × World) : Prop where
  env : sw.1.env = si.1.env
  world : sw.2 = si.2
  length : sw.1.store.length = si.1.store.length
  viewed : ∀ u ∈ si.1.store, u.Viewed D
  cells : si.2.All (Value.Viewed D)
  disjoint : si.1.env.Pairwise fun a b => a.2.Disjoint b.2
  valid : InPlace.Valid si.1
  live : ∀ (ℓ : Nat) x, sw.1.store[ℓ]? = some (some x) →
    ∃ u, si.1.store[ℓ]? = some u ∧ VRel si.1.store sw.1.store x u

/-! ## Where windows lie -/

/-- A window lies in the part of the store that the shape `s` names through a variable of its
root, shadowed or not. -/
def Covered (env : List (Name × Ref)) (s : Shape) (w : Window) : Prop :=
  ∃ r, (s.root, r) ∈ env ∧ ∃ q, w.ref.toPath = r.toPath ++ q ∧ s.fields <+: q.fieldNames

/-- No variable reaches a window's region. -/
def Unreached (env : List (Name × Ref)) (w : Window) : Prop :=
  ∀ xr ∈ env, xr.2.toPath.Disjoint w.ref.toPath

/-- A window is one of those the value of the parameter `x` brought into the body, or reads the
same region. -/
def Brought (In : List (Name × Value)) (x : Name) (w : Window) : Prop :=
  ∃ v, (x, v) ∈ In ∧ ∃ w' ∈ windowsOf v, w'.1 = w.1 ∧ w'.2.1 = w.2.1

/-- A window that one of the sources `S` tracks: it lies in the part one of them names, or the
parameter one of them names brought it in. -/
def Tracked (env : List (Name × Ref)) (In : List (Name × Value)) (S : List Shape)
    (w : Window) : Prop :=
  ∃ s ∈ S, Covered env s w ∨ Brought In s.root w

/-- What a variable of the body holds, by what the checks know of it: its location is live. A
parameter, or a captured variable seen as one, holds at its place only windows its own value
brought in, and then is its own source. Any other variable is one of the body's own, at a
location of its own from `L` on and newer than every variable before it; a pattern's binder
holds no window, and a variable with a written type holds windows its sources track. -/
def TopHolds (sw : List (Option Value)) (env : List (Name × Ref)) (In : List (Name × Value))
    (L : Nat) (xb : Name × ViewBinding) (xr : Name × Ref) (older : List (Name × Ref)) : Prop :=
  ∃ y, cell sw xr.2.loc = .ok y ∧
    if xb.2.param then ∀ x, getW sw y xr.2.path = .ok x →
      ∀ w ∈ windowsOf x, Brought In xr.1 w ∧ ⟨xr.1, []⟩ ∈ xb.2.sources
    else xr.2.path = [] ∧ L ≤ xr.2.loc ∧ (∀ yr ∈ older, yr.2.loc < xr.2.loc) ∧
      if xb.2.type.isSome then ∀ w ∈ windowsOf y, Tracked env In xb.2.sources w else Free y

/-- The reads `R` guard every window that the sources of a variable of the body with a written
type track, on a location before the variable's own. -/
def Fenced (env : List (Name × Ref)) (In : List (Name × Value)) (R : List Shape)
    (xb : Name × ViewBinding) (xr : Name × Ref) (_ : List (Name × Ref)) : Prop :=
  xb.2.param = false → xb.2.type.isSome = true →
    ∀ w, w.1 < xr.2.loc → Tracked env In xb.2.sources w → InPlace.Guarded R env w.ref.toPath

/-- The variables agree with the scope the checks read, name by name from the newest, each as
`top` says; the rest of the variables, a closure's captured ones, are as `base` says. -/
inductive Fits (top : Name × ViewBinding → Name × Ref → List (Name × Ref) → Prop)
    (base : Name × Ref → Prop) : ViewScope → List (Name × Ref) → Prop
  | base {Γ : ViewScope} {env : List (Name × Ref)} : (∀ xb ∈ Γ, xb.2.param = true) →
      (∀ xr ∈ env, base xr) → Fits top base Γ env
  | cons {xb : Name × ViewBinding} {xr : Name × Ref} {Γ : ViewScope} {env : List (Name × Ref)} :
      xb.1 = xr.1 → top xb xr env → Fits top base Γ env → Fits top base (xb :: Γ) (xr :: env)

/-- A captured variable has a location of its own, which holds no window. -/
def BaseHolds (sw : List (Option Value)) (xr : Name × Ref) : Prop :=
  ∃ y, cell sw xr.2.loc = .ok y ∧ xr.2.path = [] ∧ Free y

/-- What the body runs in: the scope the checks read, the places being read around the running
expression, the values its parameters brought in, the length of the store when the body
started, the result's parameters, which a value leaving the body may read, and the windows
the callers' locations held when the body started. -/
structure Ctx where
  Γ : ViewScope
  R : List Shape
  In : List (Name × Value)
  L : Nat
  P : List Name
  /-- The windows each location of the callers held when the body started. -/
  Old : Nat → List Window
  /-- What each location of the callers held when the body started. -/
  Start : Nat → Option Value

/-- What the simulation keeps of two states while a body runs in the context `c`, with the
windows `pend` of the values of the expressions around the running one waiting, each with the
part it reads: the states agree, the variables fit the scope, a location of the callers holds
only windows it held when the body started, a location of the body's own is a variable's and
holds windows on older locations, and each waiting window reads its part in both stores. A
location of the callers live when the body started stays live, holding what it held then or a
value with no window: the body writes only through its `inout` parameters, whose locations it
reads through first, and frees only its own locations. -/
structure Pre (D : Decls) (c : Ctx) (pend : List (Window × Value)) (si : InPlace.State × World)
    (sw : State × World) : Prop where
  agree : Agree D si sw
  fits : Fits (TopHolds sw.1.store sw.1.env c.In c.L) (BaseHolds sw.1.store) c.Γ sw.1.env
  outer : ∀ (ℓ : Nat) x, ℓ < c.L → sw.1.store[ℓ]? = some (some x) →
    (∀ w ∈ windowsOf x, w ∈ c.Old ℓ) ∧ ∃ y, c.Start ℓ = some y ∧ (x = y ∨ Free x)
  owned : ∀ (ℓ : Nat) x, c.L ≤ ℓ → sw.1.store[ℓ]? = some (some x) →
    (∃ xr ∈ sw.1.env, xr.2 = ⟨ℓ, []⟩) ∧ ∀ w ∈ windowsOf x, w.1 < ℓ
  pend : ∀ wd ∈ pend, regionW sw.1.store wd.1 = .ok wd.2 ∧ regionI si.1.store wd.1 = .ok wd.2 ∧
    Free wd.2 ∧ viewable wd.2 = true
  start : c.L ≤ sw.1.store.length
  /-- A location of the callers live when the body started is live. -/
  alive : ∀ (ℓ : Nat) y, ℓ < c.L → c.Start ℓ = some y → ∃ x, sw.1.store[ℓ]? = some (some x)

/-- What holds of a context and the variables whatever the stores hold: the reads guard what
the sources of the body's variables track (`Fenced`), the windows the
parameters brought in lie before the body's locations and no variable reaches them, the windows
each location of the callers held lie before it and no variable reaches them, and the windows of
the waiting values are guarded. -/
structure Guards (D : Decls) (c : Ctx) (pend : List (Window × Value)) (env : List (Name × Ref)) :
    Prop where
  fenced : Fits (Fenced env c.In c.R) (fun _ => True) c.Γ env
  brought : ∀ xv ∈ c.In, ∀ w ∈ windowsOf xv.2, w.1 < c.L ∧ Unreached env w
  old : ∀ ℓ < c.L, ∀ w ∈ c.Old ℓ, w.1 < ℓ ∧ Unreached env w
  pend : ∀ wd ∈ pend, InPlace.Guarded c.R env wd.1.ref.toPath
  /-- A location of the callers that a variable reaches, an `inout` parameter's, held no window
  when the body started: the call read it through its windows first. -/
  start : ∀ xr ∈ env, xr.2.loc < c.L → ∀ y, c.Start xr.2.loc = some y → Free y

end Windows

end Stilt
