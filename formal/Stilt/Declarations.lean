import Stilt.Syntax
import Stilt.Syntax.Limits
import Stilt.Syntax.Kinds

/-!
# Declarations

The declarations of the core calculus: records, variant types, functions with
their type parameters and row variables, methods in `impl` blocks, traits and
their impls, and programs.
-/

namespace Stilt

/-- `type Name<A, …> = { field: T, … }` (declarations.records): its fields, whose types may
name its type parameters, which take no bounds (declarations.type-parameters). -/
structure RecordDecl where
  name : Name
  fields : List (Name × Ty)
  typeParams : List Name

/-- `type Name<A, …> = | C(T, …) | …` (declarations.variant-types): its variants, whose
payload types may name its type parameters, which take no bounds
(declarations.type-parameters). -/
structure VariantDecl where
  name : Name
  ctors : List (Name × List Ty)
  typeParams : List Name

/-- A type parameter of a function, with its bounds, the traits that the
types it stands for implement (declarations.function-declarations and traits.bounds). -/
structure TypeParam where
  name : Name
  bounds : List Name
  /-- The arguments that a bound gives its trait's parameters, as `C: Collection<i64>`, for
  each bound that writes them; a bound without them, as `C: Collection`, leaves them open
  (traits.bound-arguments). They may name the function's type parameters. -/
  args : List (Name × List Ty) := []
  /-- Its record bound, `P: { f: T, .. }`, the fields it names with their types, which may name
  the function's type parameters; none when it has none (records.record-bounds). A record bound
  is always open, as one written without its `..` is read (records.bound-fields), and a parameter
  of an open record type, `p: { f: T, .. }`, is elaborated as a type parameter of its own with that
  bound, the calculus having no open record type anywhere else (records.open-parameter-types). -/
  fields : List (Name × Ty) := []

/-- The arguments a bound of a type parameter gives the trait `B`, if it writes them. -/
def TypeParam.argsOf (p : TypeParam) (B : Name) : Option (List Ty) := p.args.lookup B

/-- The functions that code under a limit may name: those that `fn` covers, and the
method `m` of the trait `t`'s impls when `method t m` covers it, each a function
without the fact the limit rules out, wherever it is named (facts.without). Under
`without panic`, `overflows` says whether the code may still overflow: it may not when
`without overflow` limits it too (effects.without-overflow). `panics` says whether it may
panic otherwise, as code limited by `without overflow` alone may. -/
structure Limited where
  fn : Name → Bool
  method : Name → Name → Bool
  overflows : Bool := true
  panics : Bool := false

/-- Every function: a limit on the whole program covers each of its functions. -/
def Limited.all : Limited := ⟨fun _ => true, fun _ _ => true, true, false⟩

/-- `fn name<T: B, …, e, …>(params) -> result / row { body } without …`
(declarations.function-declarations): its type parameters, with their bounds, its row
variables (effects.row-variables), and the limits its body is checked against. -/
structure FnDecl where
  name : Name
  /-- Its type parameters, in the order a use instantiates them
  (declarations.function-declarations). -/
  typeParams : List TypeParam
  /-- Its row variables, in the order a use instantiates them: those it
  declares (effects.row-variables), then the implicit ones of its non-escaping
  parameters (effects.non-escaping-parameters). -/
  rowParams : List Name
  params : List Param
  result : Ty
  row : Row
  body : Expr
  /-- The limits its body keeps, its own clause's and its module's (facts.without). -/
  limits : Limits := {}

/-- The type of a function, as its signature gives it (declarations.function-types). -/
def FnDecl.type (d : FnDecl) : Ty := .fn (d.params.map Param.sig) d.result d.row

/-- `self`, the first parameter of a method, which is its receiver (traits.methods). -/
def selfName : Name := "self"

/-- `Type.m`, the name of the function `m` of the `impl` blocks of `Type`
(traits.qualified-calls). -/
def qualify (type name : Name) : Name := type ++ "." ++ name

/-- A function of an `impl` block of `type`, under its qualified name. -/
def FnDecl.qualify (type : Name) (d : FnDecl) : FnDecl :=
  { d with name := Stilt.qualify type d.name }

/-- A function of an `impl` block of `type` whose type parameters are `ps`, under its
qualified name, with the block's type parameters before its own: a use gives the block's
first, then the function's (traits.bounded-blocks). -/
def FnDecl.within (ps : List TypeParam) (type : Name) (d : FnDecl) : FnDecl :=
  { d with name := Stilt.qualify type d.name, typeParams := ps ++ d.typeParams }

/-- A block without type parameters only qualifies its functions' names. -/
@[simp] theorem FnDecl.within_nil (type : Name) (d : FnDecl) : d.within [] type = d.qualify type :=
  rfl

/-- `impl<A, …> Type<A, …> { fn … }`, an inherent `impl` block of a record or variant type
(traits.impl-blocks). A function whose first parameter is `self` is a method, and `self`
takes the mode `let` or `inout`; one without `self` is an associated function, called as
`Type.f(…)` (traits.associated-functions). The block's type is `Type` at the block's type
parameters, one for each of the type's, in its order: the elaborated form of a block that
writes them in another order. The block may bound them, and its functions then exist only
for the type arguments that meet the bounds, since each takes them as its first type
parameters, which a use instantiates (traits.bounded-blocks). A constant of the block,
`Type.NAME`, is a `ConstDecl` of the program under that qualified name. -/
structure ImplDecl where
  type : Name
  fns : List FnDecl
  /-- The block's type parameters, with their bounds. -/
  typeParams : List TypeParam := []

/-- The functions of an `impl` block, under their qualified names, with the block's type
parameters. -/
def ImplDecl.members (i : ImplDecl) : List FnDecl := i.fns.map (FnDecl.within i.typeParams i.type)

/-- The head of a type that a trait impl is for: a numeric type, `bool`,
`str`, `()`, or a record or variant type (traits.implementing-trait). -/
inductive Head where
  | int (k : IntTy)
  | float (k : FloatTy)
  | bool
  | str
  | unit
  | record (name : Name)
  | variant (name : Name)
  deriving DecidableEq, Repr

/-- The type a head stands for. -/
def Head.type : Head → Ty
  | .int k => .int k
  | .float k => .float k
  | .bool => .bool
  | .str => .str
  | .unit => .unit
  | .record R => .record R []
  | .variant T => .variant T []

/-- A head at type arguments: a record or variant type at them, any other head alone. -/
def Head.at : Head → List Ty → Ty
  | .record R, args => .record R args
  | .variant T, args => .variant T args
  | h, _ => h.type

/-- The head of a type, if a trait impl can be for it: a record or variant type's at any
arguments, since an impl covers a whole constructor (traits.coherence). -/
def Ty.head? : Ty → Option Head
  | .int k => some (.int k)
  | .float k => some (.float k)
  | .bool => some .bool
  | .str => some .str
  | .unit => some .unit
  | .record R _ => some (.record R)
  | .variant T _ => some (.variant T)
  | _ => none

/-- The type arguments of a record or variant type, and none of any other type. -/
def Ty.args : Ty → List Ty
  | .record _ args | .variant _ args => args
  | _ => []

/-- `Self`, the type parameter of a trait's signatures (traits.declaring-trait). -/
def selfParam : Name := "Self"

/-- `trait Name<P, …> { fn m(self, …) -> R; … }`: its functions, each with its type, a
function type in which `Self` is the type parameter `Self`: its methods, whose first
parameter is the receiver (traits.declaring-trait), and its functions without `self`
(traits.functions-without-self). Its own parameters, `P, …`, without bounds, each name a type
throughout its functions' types, where they are type parameters too (traits.trait-parameters). -/
structure TraitDecl where
  name : Name
  methods : List (Name × Ty)
  /-- The trait's own parameters. -/
  params : List Name := []

/-- `impl<A: Bound, …> Trait<T, …> for Con<A, …> { fn … }` (traits.implementing-trait), with
an argument for each of the trait's parameters (traits.trait-arguments). Its type is `Con` at
the impl's parameters, one for each of the constructor's, in its order: the elaborated form of
an impl that writes them in another order. -/
structure TraitImpl where
  trait : Name
  type : Head
  fns : List FnDecl
  /-- The types it gives the trait's parameters, which the impl's type fixes: a trait has one
  impl per type, whatever its arguments (traits.coherence). They may name the impl's
  parameters. -/
  args : List Ty := []
  /-- The impl's parameters, with their bounds, which a type's arguments meet for the impl's
  functions to apply to it. -/
  typeParams : List TypeParam := []

/-- The type of an impl: its constructor at its parameters. -/
def TraitImpl.selfType (i : TraitImpl) : Ty := i.type.at (i.typeParams.map fun p => .param p.name)

/-- The instantiation of an impl's parameters by a type's arguments. -/
def TraitImpl.typeArgs (i : TraitImpl) (τs : List Ty) : List (Name × Ty) :=
  (i.typeParams.map TypeParam.name).zip τs

/-- The name of an integer type (numbers.numeric-types). -/
def IntTy.name : IntTy → Name
  | .i8 => "i8" | .i16 => "i16" | .i32 => "i32" | .i64 => "i64"
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64"

/-- The name of a float type (numbers.numeric-types). -/
def FloatTy.name : FloatTy → Name
  | .f32 => "f32" | .f64 => "f64"

/-- The name of a head, as a program writes it. -/
def Head.name : Head → Name
  | .int k => k.name
  | .float k => k.name
  | .bool => "bool"
  | .str => "str"
  | .unit => "()"
  | .record R => R
  | .variant T => T

/-- What qualifies the names of the functions of the impl of `trait` for
`type`, as a type's name qualifies its methods. -/
def implQualifier (trait : Name) (type : Head) : Name := trait ++ " for " ++ type.name
/-- The name of the function `m` of the impl of `trait` for `type`. -/
def implName (trait : Name) (type : Head) (m : Name) : Name :=
  qualify (implQualifier trait type) m

/-- The functions of a trait impl, under their qualified names, with the impl's parameters. -/
def TraitImpl.members (i : TraitImpl) : List FnDecl :=
  i.fns.map (FnDecl.within i.typeParams (implQualifier i.trait i.type))

/-- `effect Name { fn op(param: A) -> B; … }` (handlers.declaring-effect): each
operation with the type of its argument, its parameters as one value, and of
its result. That value is passed as a `let` parameter, never `inout`
(handlers.no-inout-parameter). -/
structure EffectDecl where
  name : Name
  ops : List (Name × Ty × Ty)

/-- A constant, `const NAME: T = e` (declarations.constant-declarations): at module level
under its name, or in an inherent `impl` block under its qualified name `Type.NAME`, with one
value for every type argument of its block (declarations.impl-constants). Its value is a
constant expression (`Expr.IsConstant`), which names other constants as variables. A read of a
constant in an expression is the expression of its value: constant expressions are pure, so
reading the value where the constant is read gives the value a first evaluation would
(declarations.constant-evaluation). -/
structure ConstDecl where
  name : Name
  type : Ty
  value : Expr

/-- The declarations of a program: records, variant types, the functions at
the top level, the `impl` blocks, the traits and their impls, the
effects, and the constants, in an order where each constant names only those before it. -/
structure Decls where
  records : List RecordDecl
  variants : List VariantDecl
  functions : List FnDecl
  impls : List ImplDecl
  traits : List TraitDecl
  traitImpls : List TraitImpl
  effects : List EffectDecl
  consts : List ConstDecl := []

namespace Decls

/-- Every function of the program: those at the top level, then those of its
`impl` blocks under their qualified names (traits.impl-blocks and traits.qualified-calls), then
those of its trait impls. -/
def fns (D : Decls) : List FnDecl :=
  D.functions ++ D.impls.flatMap ImplDecl.members ++ D.traitImpls.flatMap TraitImpl.members

/-- The record type with this name. -/
def record? (D : Decls) (name : Name) : Option RecordDecl :=
  D.records.find? (·.name == name)

/-- The variant type with this name. -/
def variant? (D : Decls) (name : Name) : Option VariantDecl :=
  D.variants.find? (·.name == name)

/-- The function with this name: a method is found by its qualified name. -/
def fn? (D : Decls) (name : Name) : Option FnDecl :=
  D.fns.find? (·.name == name)

/-- The trait with this name. -/
def trait? (D : Decls) (name : Name) : Option TraitDecl :=
  D.traits.find? (·.name == name)

/-- The impl of a trait for a type's head (traits.coherence). -/
def traitImpl? (D : Decls) (trait : Name) (type : Head) : Option TraitImpl :=
  D.traitImpls.find? fun i => i.trait == trait && i.type == type

/-- The effect with this name. -/
def effect? (D : Decls) (name : Name) : Option EffectDecl :=
  D.effects.find? (·.name == name)

/-- The types of an operation's argument and result (handlers.declaring-effect). -/
def operation? (D : Decls) (op : Operation) : Option (Ty × Ty) :=
  (D.effect? op.effect).bind (·.ops.lookup op.name)

/-- The constant with this name. -/
def const? (D : Decls) (name : Name) : Option ConstDecl :=
  D.consts.find? (·.name == name)

end Decls

/-! ## Constants -/

mutual

/-- A constant expression as the pattern that matches the values equal to its value, the
constants it names read through `env`: literals, a unary `-` on an integer, tuples, lists,
records and variants (declarations.constant-expressions and patterns.constants). A float,
itself or in a part, has none: no pattern matches a float (patterns.floats). -/
def Expr.constPattern (env : Name → Option Pattern) : Expr → Option Pattern
  | .int n => some (.int n)
  | .bool b => some (.bool b)
  | .unit => some .unit
  | .op (.str s) [] => some (.str s)
  | .op (.neg _) [e] =>
    match e.constPattern env with
    | some (.int n) => some (.int (-n))
    | _ => none
  | .op .tuple es => (exprsConstPatterns env es).map .tuple
  | .list _ es => (exprsConstPatterns env es).map (.list · .exact)
  | .record R _ fields => (fieldsConstPatterns env fields).map (.record R)
  | .variant T _ C es => (exprsConstPatterns env es).map (.variant T C)
  | .var x => env x
  | _ => none

def exprsConstPatterns (env : Name → Option Pattern) : List Expr → Option (List Pattern)
  | [] => some []
  | e :: es =>
    match e.constPattern env, exprsConstPatterns env es with
    | some p, some ps => some (p :: ps)
    | _, _ => none

def fieldsConstPatterns (env : Name → Option Pattern) :
    List (Name × Expr) → Option (List (Name × Pattern))
  | [] => some []
  | (f, e) :: fields =>
    match e.constPattern env, fieldsConstPatterns env fields with
    | some p, some ps => some ((f, p) :: ps)
    | _, _ => none

end

mutual

/-- A constant expression (declarations.constant-expressions): a literal, a string's
without interpolation, a unary `-`, a tuple, a list, a record or a variant of constant
expressions, or another constant, which a constant's value names as a variable. Arithmetic,
a call, a field access, a block, an `if`, a closure, a function named as a value, a hole and
anything else is E0326. -/
inductive Expr.IsConstant : Expr → Prop
  | int {n : Int} : Expr.IsConstant (.int n)
  | bool {b : Bool} : Expr.IsConstant (.bool b)
  | unit : Expr.IsConstant .unit
  | str {s : String} : Expr.IsConstant (.op (.str s) [])
  | float {k : FloatTy} {m : Nat} {neg : Bool} {e : Nat} :
      Expr.IsConstant (.op (.float k m neg e) [])
  | neg {k : IntTy} {e : Expr} : Expr.IsConstant e → Expr.IsConstant (.op (.neg k) [e])
  | fneg {k : FloatTy} {e : Expr} : Expr.IsConstant e → Expr.IsConstant (.op (.fneg k) [e])
  | tuple {es : List Expr} : ExprsConstant es → Expr.IsConstant (.op .tuple es)
  | list {τ : Ty} {es : List Expr} : ExprsConstant es → Expr.IsConstant (.list τ es)
  | record {R : Name} {args : List Ty} {fields : List (Name × Expr)} :
      FieldsConstant fields → Expr.IsConstant (.record R args fields)
  | variant {T : Name} {args : List Ty} {C : Name} {es : List Expr} :
      ExprsConstant es → Expr.IsConstant (.variant T args C es)
  | const {x : Name} : Expr.IsConstant (.var x)

inductive ExprsConstant : List Expr → Prop
  | nil : ExprsConstant []
  | cons {e : Expr} {es : List Expr} : Expr.IsConstant e → ExprsConstant es → ExprsConstant (e :: es)

inductive FieldsConstant : List (Name × Expr) → Prop
  | nil : FieldsConstant []
  | cons {f : Name} {e : Expr} {fields : List (Name × Expr)} :
      Expr.IsConstant e → FieldsConstant fields → FieldsConstant ((f, e) :: fields)

end

/-- The pattern of the constant `C` among constants listed the latest first, each naming
only those after it. -/
def constPatternIn : List ConstDecl → Name → Option Pattern
  | [], _ => none
  | c :: cs, C => if c.name = C then c.value.constPattern (constPatternIn cs) else constPatternIn cs C

/-- The value of the constant `C` as a pattern (patterns.constants). -/
def Decls.constPattern (D : Decls) (C : Name) : Option Pattern := constPatternIn D.consts.reverse C

/-- `recv.m(args)`, where `m` is a method of the `impl` blocks of `type`, the
type of `recv` (traits.method-resolution). It is the call `type.m(recv, args)` of the
method as a function, whose first parameter is the receiver (traits.qualified-calls):
the receiver is the first argument, evaluated before the others (modes.durations), passed in the mode of `self`. The receiver of a method that takes
`inout self` is a place, passed `inout`, though no `inout` marks it in the
source (expressions.inout-arguments); that of a method that takes `self` is a value. -/
def Expr.methodCall (type name : Name) (rows : List Row) (recv : Arg) (args : List Arg)
    (result : Ty) : Expr :=
  .call (.fnRef (qualify type name) [] rows) (recv :: args) result

/-- A closed program: its declarations, and the body of `main` with the row it
is checked against. `main` has no parameters and returns `()` (program.main). -/
structure Program where
  decls : Decls
  main : Expr
  row : Row
  /-- The limits `main`'s body keeps, its own clause's and its module's (facts.without). -/
  limits : Limits := {}
  /-- Its traits, impls and functions as it writes them, as kinds read them. -/
  kinds : Kinds := {}

/-! ## The functions of declarations -/

/-- Declarations without `impl` blocks have only the functions at the top
level. -/
@[simp] theorem Decls.fns_mk (records : List RecordDecl) (variants : List VariantDecl)
    (functions : List FnDecl) (traits : List TraitDecl) (effects : List EffectDecl)
    (consts : List ConstDecl) :
    (Decls.mk records variants functions [] traits [] effects consts).fns = functions := by
  simp [Decls.fns]

/-- The declarations with `f` applied to every function, at the top level and
in `impl` blocks. -/
def Decls.mapFns (f : FnDecl → FnDecl) (D : Decls) : Decls :=
  { D with
    functions := D.functions.map f
    impls := D.impls.map fun i => { i with fns := i.fns.map f }
    traitImpls := D.traitImpls.map fun i => { i with fns := i.fns.map f } }

theorem Decls.mapFns_mapFns (f g : FnDecl → FnDecl) (D : Decls) :
    (D.mapFns f).mapFns g = D.mapFns (g ∘ f) := by
  simp [Decls.mapFns, Function.comp_def]

/-- A change to functions that commutes with qualifying their names and giving them a
block's type parameters reaches every function, the methods under their qualified names
included. -/
theorem Decls.fns_mapFns {f : FnDecl → FnDecl}
    (hf : ∀ ps T d, f (d.within ps T) = (f d).within ps T)
    (D : Decls) : (D.mapFns f).fns = D.fns.map f := by
  simp only [Decls.fns, Decls.mapFns, ImplDecl.members, TraitImpl.members, List.map_append,
    List.flatMap_map, List.map_flatMap, List.map_map]
  congr 1
  · congr 1
    refine congrArg (List.flatMap · D.impls) (funext fun i => ?_)
    exact List.map_congr_left fun d _ => (hf i.typeParams i.type d).symm
  · refine congrArg (List.flatMap · D.traitImpls) (funext fun i => ?_)
    exact List.map_congr_left fun d _ => (hf i.typeParams _ d).symm

/-- A change to functions that leaves every function of the program as it is
leaves its declarations as they are. -/
theorem Decls.mapFns_eq_self {f : FnDecl → FnDecl}
    (hf : ∀ ps T d, f (d.within ps T) = (f d).within ps T) (hname : ∀ d, (f d).name = d.name)
    {D : Decls} (h : ∀ d ∈ D.fns, f d = d) : D.mapFns f = D := by
  obtain ⟨records, variants, functions, impls, traits, traitImpls, effects, consts⟩ := D
  have hq : ∀ ps T d, f (d.within ps T) = d.within ps T → f d = d := by
    intro ps T d hq
    rw [hf] at hq
    have hn := hname d
    generalize f d = g at hq hn ⊢
    cases g
    cases d
    simp_all [FnDecl.within]
  have hfun : functions.map f = functions :=
    (List.map_congr_left fun d hd => h d (List.mem_append_left _ (List.mem_append_left _ hd))).trans
      (List.map_id _)
  have himpl : (impls.map fun i => { i with fns := i.fns.map f }) = impls := by
    refine (List.map_congr_left fun i hi => ?_).trans (List.map_id _)
    obtain ⟨T, fns, ps⟩ := i
    suffices fns.map f = fns by simp [this]
    refine (List.map_congr_left fun d hd => ?_).trans (List.map_id _)
    exact hq ps T d (h (d.within ps T) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨⟨T, fns, ps⟩, hi, List.mem_map_of_mem hd⟩))))
  have htrait : (traitImpls.map fun i => { i with fns := i.fns.map f }) = traitImpls := by
    refine (List.map_congr_left fun i hi => ?_).trans (List.map_id _)
    obtain ⟨Tr, H, fns, args, ps⟩ := i
    suffices fns.map f = fns by simp [this]
    refine (List.map_congr_left fun d hd => ?_).trans (List.map_id _)
    exact hq ps _ d (h _ (List.mem_append_right _ (List.mem_flatMap.2
      ⟨⟨Tr, H, fns, args, ps⟩, hi, List.mem_map_of_mem hd⟩)))
  simp [Decls.mapFns, hfun, himpl, htrait]

end Stilt
