import Stilt.Rows

/-!
# Run-time types

The types that values have while a program runs. A body is typed once, in the
row variables of its function, and runs under an instantiation that composes
the uses that led to it from `main` down (effects.inference). Each use leaves a
row of the signature one `raise` label (effects.one-error-type), but a variable that no
signature pairs may still be given two error types along the way: a use may
give it `{raise<A>, r}`, and a later one may give `r` a `raise<B>`. So a row,
read at run time, is the set of error types that its labels and its
variables' instantiations bring, and it may hold several.

`STy` is a type with every row read that way. A row variable stands for the
error types its instantiation can raise (`REnv`), and `Ty.close` reads a type
under such an environment. The model checks no `io`, so a run-time row keeps
only its error types, and beside them the labels of the effects it may perform
and of the `resume` of a handler's body, which no value has: a row variable
stands for the effects of its instantiation too. Rows are sets, so two run-time types are equivalent
(`STy.Eqv`) when they differ only in the order and repetition of their rows'
error types, and a type fits another (`STy.Fits`) through equivalences and
rows that grow (effects.function-values).
-/

namespace Stilt

/-- A type at run time: closed, with each row the list of error types it can
raise once its variables are instantiated (effects.one-error-type and effects.inference). -/
inductive STy where
  | int (k : IntTy)
  | float (k : FloatTy)
  | bool
  | str
  | unit
  | never
  | record (name : Name)
  | variant (name : Name)
  | list (elem : STy)
  | tuple (elems : List STy)
  | map (key value : STy)
  | set (elem : STy)
  /-- `Shared<T>`, of a cell whose values have the type `elem` (shared.std-sync). -/
  | shared (elem : STy)
  /-- A type parameter, which no value has: a call instantiates the type
  parameters of the body it runs (types.no-type-arguments). -/
  | param (name : Name)
  | fn (params : List (Mode × STy)) (result : STy) (raises : List STy)
  /-- The label of an effect in a run-time row (handlers.effects-in-rows). -/
  | effect (name : Name)
  /-- The label of the `resume` of a handler's body in a run-time row, with the
  closed types the row gives it (handlers.resuming). -/
  | resume (arg result : Ty)

/-- The label of an effect or of a `resume`, which no value has. -/
def STy.IsLabel : STy → Prop
  | .effect _ | .resume _ _ => True
  | _ => False

/-- `i64` at run time. -/
@[match_pattern] abbrev STy.i64 : STy := .int .i64

/-- What each row variable stands for at run time: the error types that its
instantiation can raise, and the labels of the effects it may perform
(effects.inference). -/
abbrev REnv := Name → List STy

/-- The labels of a row's effects and its `resume`. -/
def Row.labelsOf (effects : List Name) (resume : Option (Ty × Ty)) : List STy :=
  effects.map STy.effect ++ resume.toList.map fun p => STy.resume p.1 p.2

mutual

/-- A type read under an environment for its row variables, which the uses
that led to it instantiated (effects.inference). -/
def Ty.close (η : REnv) : Ty → STy
  | .int k => .int k
  | .float k => .float k
  | .bool => .bool
  | .str => .str
  | .unit => .unit
  | .never => .never
  | .record R => .record R
  | .variant T => .variant T
  | .list τ => .list (τ.close η)
  | .tuple τs => .tuple (closeTys η τs)
  | .map κ τ => .map (κ.close η) (τ.close η)
  | .set τ => .set (τ.close η)
  | .view τ => τ.close η
  | .shared τ => .shared (τ.close η)
  | .param T => .param T
  | .fn ps r ρ => .fn (closeParams η ps) (r.close η) (ρ.close η)

/-- Types read under an environment. -/
def closeTys (η : REnv) : List Ty → List STy
  | [] => []
  | τ :: τs => τ.close η :: closeTys η τs

/-- Parameter types read under an environment. -/
def closeParams (η : REnv) : List (Mode × Ty) → List (Mode × STy)
  | [] => []
  | (m, τ) :: ps => (m, τ.close η) :: closeParams η ps

/-- The error types a row can raise, its own label's and those its variables
stand for, and the labels of its effects and its `resume`. -/
def Row.close (η : REnv) : Row → List STy
  | ⟨_, some E, vs, es, r⟩ => E.close η :: (vs.flatMap η ++ Row.labelsOf es r)
  | ⟨_, none, vs, es, r⟩ => vs.flatMap η ++ Row.labelsOf es r

end

/-- A closed type at run time: no row variable stands for anything. -/
def Ty.sem (τ : Ty) : STy := τ.close fun _ => []

mutual

/-- Two run-time types are equivalent: they differ only in the order and
repetition of the error types of their rows. -/
inductive STy.Eqv : STy → STy → Prop
  | int (k : IntTy) : STy.Eqv (.int k) (.int k)
  | float (k : FloatTy) : STy.Eqv (.float k) (.float k)
  | bool : STy.Eqv .bool .bool
  | str : STy.Eqv .str .str
  | unit : STy.Eqv .unit .unit
  | never : STy.Eqv .never .never
  | record (R : Name) : STy.Eqv (.record R) (.record R)
  | variant (T : Name) : STy.Eqv (.variant T) (.variant T)
  | list {a b : STy} : STy.Eqv a b → STy.Eqv (.list a) (.list b)
  | tuple {as bs : List STy} : STysEqv as bs → STy.Eqv (.tuple as) (.tuple bs)
  | map {a a' b b' : STy} : STy.Eqv a a' → STy.Eqv b b' → STy.Eqv (.map a b) (.map a' b')
  | set {a b : STy} : STy.Eqv a b → STy.Eqv (.set a) (.set b)
  | shared {a b : STy} : STy.Eqv a b → STy.Eqv (.shared a) (.shared b)
  | param (T : Name) : STy.Eqv (.param T) (.param T)
  | fn {ps ps' : List (Mode × STy)} {r r' : STy} {R R' : List STy} :
      SParamsEqv ps ps' → STy.Eqv r r' → Covers R R' → Covers R' R →
      STy.Eqv (.fn ps r R) (.fn ps' r' R')
  | effect (E : Name) : STy.Eqv (.effect E) (.effect E)
  | resume (a r : Ty) : STy.Eqv (.resume a r) (.resume a r)

/-- Types pairwise equivalent. -/
inductive STysEqv : List STy → List STy → Prop
  | nil : STysEqv [] []
  | cons {a b : STy} {as bs : List STy} : STy.Eqv a b → STysEqv as bs → STysEqv (a :: as) (b :: bs)

/-- Parameter types pairwise equivalent, with the same modes. -/
inductive SParamsEqv : List (Mode × STy) → List (Mode × STy) → Prop
  | nil : SParamsEqv [] []
  | cons {m : Mode} {a b : STy} {ps ps' : List (Mode × STy)} :
      STy.Eqv a b → SParamsEqv ps ps' → SParamsEqv ((m, a) :: ps) ((m, b) :: ps')

/-- Every error type of the first list is equivalent to one of the second. -/
inductive Covers : List STy → List STy → Prop
  | nil {R : List STy} : Covers [] R
  | cons {x : STy} {xs R : List STy} : Has R x → Covers xs R → Covers (x :: xs) R

/-- Some error type of the list is equivalent to `x`. -/
inductive Has : List STy → STy → Prop
  | here {x y : STy} {R : List STy} : STy.Eqv x y → Has (y :: R) x
  | there {x y : STy} {R : List STy} : Has R x → Has (y :: R) x

end

/-- A run-time type fits another: a chain of equivalences and of rows that
grow, the outermost row of a function type only (effects.function-values), or `Never`,
which converts to any type (declarations.never). -/
inductive STy.Fits : STy → STy → Prop
  | refl (a : STy) : STy.Fits a a
  | eqv {a b c : STy} : STy.Eqv a b → STy.Fits b c → STy.Fits a c
  | grow {ps : List (Mode × STy)} {r : STy} {R R' : List STy} {c : STy} :
      Covers R R' → STy.Fits (.fn ps r R') c → STy.Fits (.fn ps r R) c
  | never (c : STy) : STy.Fits .never c

/-! ## Equivalence -/

theorem Has.exists : ∀ {R : List STy} {x : STy}, Has R x → ∃ y ∈ R, x.Eqv y
  | _, _, .here hxy => ⟨_, List.mem_cons_self, hxy⟩
  | _, _, .there h =>
    let ⟨y, hy, hxy⟩ := Has.exists h
    ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

theorem Has.of_mem_eqv {R : List STy} {x y : STy} (hy : y ∈ R) (hxy : x.Eqv y) : Has R x := by
  induction R with
  | nil => exact nomatch hy
  | cons z R ih =>
    rcases List.mem_cons.1 hy with rfl | hy
    · exact .here hxy
    · exact .there (ih hy)

theorem Has.iff_exists {R : List STy} {x : STy} : Has R x ↔ ∃ y ∈ R, x.Eqv y :=
  ⟨Has.exists, fun ⟨_, hy, hxy⟩ => Has.of_mem_eqv hy hxy⟩

theorem Covers.forall : ∀ {R R' : List STy}, Covers R R' → ∀ x ∈ R, Has R' x
  | _, _, .nil => fun _ hx => nomatch hx
  | _, _, .cons hx h => fun y hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hx
    · exact Covers.forall h y hy

theorem Covers.of_forall {R R' : List STy} (h : ∀ x ∈ R, Has R' x) : Covers R R' := by
  induction R with
  | nil => exact .nil
  | cons x R ih => exact .cons (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem Covers.iff_forall {R R' : List STy} : Covers R R' ↔ ∀ x ∈ R, Has R' x :=
  ⟨Covers.forall, Covers.of_forall⟩

mutual

theorem STy.Eqv.refl : ∀ a : STy, a.Eqv a
  | .int k => .int k
  | .float k => .float k
  | .bool => .bool
  | .str => .str
  | .unit => .unit
  | .never => .never
  | .record R => .record R
  | .variant T => .variant T
  | .list a => .list (STy.Eqv.refl a)
  | .tuple as => .tuple (STysEqv.refl as)
  | .map a b => .map (STy.Eqv.refl a) (STy.Eqv.refl b)
  | .set a => .set (STy.Eqv.refl a)
  | .shared a => .shared (STy.Eqv.refl a)
  | .param T => .param T
  | .fn ps r R =>
    .fn (SParamsEqv.refl ps) (STy.Eqv.refl r) (Covers.refl_append R []) (Covers.refl_append R [])
  | .effect E => .effect E
  | .resume a r => .resume a r

theorem STysEqv.refl : ∀ as : List STy, STysEqv as as
  | [] => .nil
  | a :: as => .cons (STy.Eqv.refl a) (STysEqv.refl as)

theorem SParamsEqv.refl : ∀ ps : List (Mode × STy), SParamsEqv ps ps
  | [] => .nil
  | (_, a) :: ps => .cons (STy.Eqv.refl a) (SParamsEqv.refl ps)

/-- A list covers every list that ends with it. -/
theorem Covers.refl_append : ∀ (R S : List STy), Covers R (S ++ R)
  | [], _ => .nil
  | x :: R, S =>
    .cons (Has.of_mem_eqv (by simp) (STy.Eqv.refl x)) (by
      simpa using Covers.refl_append R (S ++ [x]))

end

theorem Covers.refl (R : List STy) : Covers R R := Covers.refl_append R []

mutual

theorem STy.Eqv.symm : ∀ {a b : STy}, a.Eqv b → b.Eqv a
  | _, _, .int k => .int k
  | _, _, .float k => .float k
  | _, _, .bool => .bool
  | _, _, .str => .str
  | _, _, .unit => .unit
  | _, _, .never => .never
  | _, _, .record R => .record R
  | _, _, .variant T => .variant T
  | _, _, .list h => .list (STy.Eqv.symm h)
  | _, _, .tuple h => .tuple (STysEqv.symm h)
  | _, _, .map h h' => .map (STy.Eqv.symm h) (STy.Eqv.symm h')
  | _, _, .set h => .set (STy.Eqv.symm h)
  | _, _, .shared h => .shared (STy.Eqv.symm h)
  | _, _, .param T => .param T
  | _, _, .fn hp hr hc hc' => .fn (SParamsEqv.symm hp) (STy.Eqv.symm hr) hc' hc
  | _, _, .effect E => .effect E
  | _, _, .resume a r => .resume a r

theorem STysEqv.symm : ∀ {as bs : List STy}, STysEqv as bs → STysEqv bs as
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (STy.Eqv.symm h) (STysEqv.symm hs)

theorem SParamsEqv.symm : ∀ {ps ps' : List (Mode × STy)}, SParamsEqv ps ps' → SParamsEqv ps' ps
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (STy.Eqv.symm h) (SParamsEqv.symm hs)

end

theorem Has.of_mem {R : List STy} {x : STy} (h : x ∈ R) : Has R x :=
  Has.of_mem_eqv h (STy.Eqv.refl x)

/-- A list covers every list that holds its elements. -/
theorem Covers.of_subset {R R' : List STy} (h : ∀ x ∈ R, x ∈ R') : Covers R R' :=
  Covers.iff_forall.2 fun x hx => Has.of_mem (h x hx)

/-- A label that a list covers is in it: a label is equivalent only to itself. -/
theorem Covers.label {L L' : List STy} (h : Covers L L') {x : STy} (hx : x ∈ L) (hl : x.IsLabel) :
    x ∈ L' := by
  obtain ⟨y, hy, hxy⟩ := (h.forall x hx).exists
  cases x <;> first | exact absurd hl id | (cases hxy; exact hy)

/-- An equivalence holds only between types of the same form. -/
theorem STy.Eqv.list_inv {a b : STy} (h : (STy.list a).Eqv b) : ∃ b', b = .list b' ∧ a.Eqv b' := by
  cases h with
  | list h => exact ⟨_, rfl, h⟩

theorem STy.Eqv.tuple_inv {as : List STy} {b : STy} (h : (STy.tuple as).Eqv b) :
    ∃ bs, b = .tuple bs ∧ STysEqv as bs := by
  cases h with
  | tuple h => exact ⟨_, rfl, h⟩

theorem STy.Eqv.map_inv {a b c : STy} (h : (STy.map a b).Eqv c) :
    ∃ a' b', c = .map a' b' ∧ a.Eqv a' ∧ b.Eqv b' := by
  cases h with
  | map h h' => exact ⟨_, _, rfl, h, h'⟩

theorem STy.Eqv.set_inv {a b : STy} (h : (STy.set a).Eqv b) : ∃ b', b = .set b' ∧ a.Eqv b' := by
  cases h with
  | set h => exact ⟨_, rfl, h⟩

theorem STy.Eqv.shared_inv {a b : STy} (h : (STy.shared a).Eqv b) :
    ∃ b', b = .shared b' ∧ a.Eqv b' := by
  cases h with
  | shared h => exact ⟨_, rfl, h⟩

theorem STy.Eqv.fn_inv {ps : List (Mode × STy)} {r : STy} {R : List STy} {b : STy}
    (h : (STy.fn ps r R).Eqv b) :
    ∃ ps' r' R', b = .fn ps' r' R' ∧ SParamsEqv ps ps' ∧ r.Eqv r' ∧ Covers R R' ∧ Covers R' R := by
  cases h with
  | fn hp hr hc hc' => exact ⟨_, _, _, rfl, hp, hr, hc, hc'⟩

/-! ## Fitting -/

namespace STy.Fits

theorem trans {a b c : STy} (h₁ : a.Fits b) (h₂ : b.Fits c) : a.Fits c := by
  induction h₁ with
  | refl => exact h₂
  | eqv h _ ih => exact .eqv h (ih h₂)
  | grow h _ ih => exact .grow h (ih h₂)
  | never => exact .never c

theorem of_eqv {a b : STy} (h : a.Eqv b) : a.Fits b := .eqv h (.refl b)

theorem of_covers {ps : List (Mode × STy)} {r : STy} {R R' : List STy} (h : Covers R R') :
    (STy.fn ps r R).Fits (.fn ps r R') :=
  .grow h (.refl _)

end STy.Fits

end Stilt
