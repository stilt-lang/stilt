/-!
# Spreads over packs

variadics.spread-expressions and variadics.pack-tuples gives a body no way to take a pack apart, only to map over it: a pack
tuple `xs: (..T)` is mapped by a spread `(..e)`, where `xs` stands in `e` for
its element, and `(..e)` has the type `(..U)` when `e` has the type `U`
(variadics.spread-checks). A pack's arity isn't known in the body, so the spread is checked
once, with the pack's element a type of its own. This calculus states the
fact that rests on: at a pack of `n` elements, mapping the spread over the
pack tuple gives a tuple of `n` values, whose types are `U` at each element
in turn, so that `(..List<Ts>)` at `Ts = (i64, bool)` is
`(List<i64>, List<bool>)` (variadics.type-spreads).

A spread's body is written in the types of one element: `i64`, `elem`, the
element of the pack, which a pack replaces by each of its elements, and the
lists of those, as `List<Ts>`. Its terms are `x`, the pack tuple's element,
integer literals, and the one-element list of a term, which stand for the
expressions that build on the element.
-/

namespace Stilt.Packs

/-- A type, in which `elem` is the element of the pack. -/
inductive Ty where
  | int : Ty
  /-- The pack's element, which each of its elements replaces in turn. -/
  | elem : Ty
  | list : Ty → Ty
  deriving DecidableEq, Repr

/-- `t.at a`: `t` at the element `a` of the pack, with `elem` replaced by
`a` (variadics.type-spreads). -/
def Ty.at : Ty → Ty → Ty
  | .int, _ => .int
  | .elem, a => a
  | .list t, a => .list (t.at a)

/-- `(..t)` at the pack `ts`: one element for each of the pack's, with the
pack replaced by that element (variadics.type-spreads). -/
def spreadTy (t : Ty) (ts : List Ty) : List Ty := ts.map t.at

/-- A term of a spread's body. -/
inductive Tm where
  /-- The pack tuple, which stands for its element in the body (variadics.spread-expressions). -/
  | x : Tm
  | lit : Int → Tm
  /-- `[e]`, the list of one value. -/
  | single : Tm → Tm
  deriving DecidableEq, Repr

/-- The typing of a spread's body, where the pack tuple's element has the type
`σ`: the body of `(..σ)`'s spread. -/
inductive HasType (σ : Ty) : Tm → Ty → Prop where
  | x : HasType σ .x σ
  | lit {k : Int} : HasType σ (.lit k) .int
  | single {e : Tm} {t : Ty} : HasType σ e t → HasType σ (.single e) (.list t)

/-- A value. -/
inductive Val where
  | int : Int → Val
  | list : List Val → Val
  deriving Repr

/-- The typing of values, whose types name no `elem`. -/
inductive ValTy : Val → Ty → Prop where
  | int {k : Int} : ValTy (.int k) .int
  | list {vs : List Val} {t : Ty} :
      (∀ v ∈ vs, ValTy v t) → ValTy (.list vs) (.list t)

/-- The body evaluated once, with the pack tuple's element `v`. -/
def Tm.eval (v : Val) : Tm → Val
  | .x => v
  | .lit k => .int k
  | .single e => .list [e.eval v]

/-- `BodyAt`: the body, evaluated at an element of type `σ.at a`, has the type
`t.at a`, whichever type `a` is. -/
theorem HasType.eval {σ : Ty} {e : Tm} {t : Ty} (h : HasType σ e t) (a : Ty)
    {v : Val} (hv : ValTy v (σ.at a)) : ValTy (e.eval v) (t.at a) := by
  induction h with
  | x => exact hv
  | lit => exact .int
  | single _ ih =>
      exact .list fun w hw => by
        simp only [List.mem_singleton] at hw
        subst hw
        exact ih

/-- `Pairwise r xs ys`: `xs` and `ys` have the same length, and `r` relates
the elements in each place. -/
inductive Pairwise {α β : Type} (r : α → β → Prop) : List α → List β → Prop where
  | nil : Pairwise r [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      r a b → Pairwise r as bs → Pairwise r (a :: as) (b :: bs)

/-- `(..e)` over the values of a pack tuple: the body evaluated for each
element, from the first to the last (variadics.spread-expressions). -/
def spread (e : Tm) (vs : List Val) : List Val := vs.map (Tm.eval · e)

/-- `SpreadMap`: at a pack `ts` of `n` elements, mapping a spread `(..e)`,
whose body has type `t` where the pack tuple's element has type `σ`, over a
pack tuple of type `(..σ)` gives a tuple of `n` values, whose types are
`(..t)` at `ts`: `t` at each element in turn (variadics.type-spreads and variadics.spread-expressions). -/
theorem spread_map {σ t : Ty} {e : Tm} (h : HasType σ e t) {ts : List Ty}
    {vs : List Val} (hvs : Pairwise (fun v a => ValTy v (σ.at a)) vs ts) :
    (spread e vs).length = ts.length ∧
      Pairwise ValTy (spread e vs) (spreadTy t ts) := by
  induction hvs with
  | nil => exact ⟨rfl, .nil⟩
  | @cons v a vs ts hv _ ih =>
      refine ⟨by simp [spread, ih.1.symm], ?_⟩
      exact .cons (h.eval a hv) ih.2

/-! ## Examples: `fn lengths<..Ts>(lists: (..List<Ts>)) -> (..List<Ts>)` -/

/-- `(..[x])` over `xs: (..Ts)`, which wraps each element in a list. -/
def wrap : Tm := .single .x

theorem wrap_typed : HasType .elem wrap (.list .elem) := .single .x

/-- At `Ts = (i64, List<i64>)`, its values are `(List<i64>, List<List<i64>>)`. -/
theorem wrap_at_two :
    Pairwise ValTy (spread wrap [.int 1, .list [.int 2]])
      (spreadTy (.list .elem) [.int, .list .int]) :=
  have one : ValTy (.list [.int 2]) (Ty.elem.at (.list .int)) :=
    .list fun v hv => by
      simp only [List.mem_singleton] at hv
      subst hv
      exact .int
  (spread_map (ts := [.int, .list .int]) wrap_typed
      (.cons (ValTy.int : ValTy (.int 1) (Ty.elem.at .int)) (.cons one .nil))).2

/-- At the empty pack, it is the empty tuple (variadics.empty-pack). -/
theorem wrap_at_none : spread wrap [] = [] ∧ spreadTy (.list .elem) [] = [] :=
  ⟨rfl, rfl⟩

end Stilt.Packs
