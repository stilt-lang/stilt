import Stilt.Syntax

/-!
# Declarations

The declarations of the core calculus: records, variant types, functions with
their type parameters and row variables, methods in `impl` blocks, traits and
their impls, and programs.
-/

namespace Stilt

/-- `type Name = { field: T, … }` (declarations.records). -/
structure RecordDecl where
  name : Name
  fields : List (Name × Ty)

/-- `type Name = | C(T, …) | …` (declarations.variant-types). -/
structure VariantDecl where
  name : Name
  ctors : List (Name × List Ty)

/-- A type parameter of a function, with its bounds, the traits that the
types it stands for implement (declarations.function-declarations and traits.bounds). -/
structure TypeParam where
  name : Name
  bounds : List Name

/-- The limits of a `without` clause that the calculus reads, `panic`, `overflow` and
`div`, each a promise that the code it covers holds no site of the fact: those a function's
own clause names, joined with those of its module's header, which cover the bodies of
the module's functions (facts.without). -/
structure Limits where
  panic : Bool := false
  overflow : Bool := false
  div : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The functions that code under a limit may name: those that `fn` covers, and the
method `m` of the trait `t`'s impls when `method t m` covers it, each a function
without the fact the limit rules out, wherever it is named (facts.without). Under
`without panic`, `overflows` says whether the code may still overflow: it may not when
`without overflow` limits it too (effects.without-overflow). -/
structure Limited where
  fn : Name → Bool
  method : Name → Name → Bool
  overflows : Bool := true

/-- Every function: a limit on the whole program covers each of its functions. -/
def Limited.all : Limited := ⟨fun _ => true, fun _ _ => true, true⟩

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

/-- `impl Type { fn … }`, an inherent `impl` block of a record or variant type
(traits.impl-blocks). A function whose first parameter is `self` is a method, and
`self` takes the mode `let` or `inout`; one without `self` is an associated
function. Type parameters of a block are outside the calculus, so the
block's type is named alone, and the block has no bounds. -/
structure ImplDecl where
  type : Name
  fns : List FnDecl

/-- The functions of an `impl` block, under their qualified names. -/
def ImplDecl.members (i : ImplDecl) : List FnDecl := i.fns.map (FnDecl.qualify i.type)

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
  | .record R => .record R
  | .variant T => .variant T

/-- The head of a type, if a trait impl can be for it. -/
def Ty.head? : Ty → Option Head
  | .int k => some (.int k)
  | .float k => some (.float k)
  | .bool => some .bool
  | .str => some .str
  | .unit => some .unit
  | .record R => some (.record R)
  | .variant T => some (.variant T)
  | _ => none

/-- `Self`, the type parameter of a trait's signatures (traits.declaring-trait). -/
def selfParam : Name := "Self"

/-- `trait Name { fn m(self, …) -> R; … }`: its methods, each with its type, a
function type whose first parameter is the receiver and in which `Self` is the
type parameter `Self` (traits.declaring-trait). -/
structure TraitDecl where
  name : Name
  methods : List (Name × Ty)

/-- `impl Trait for Type { fn … }`, for a type with no type parameters
(traits.implementing-trait). -/
structure TraitImpl where
  trait : Name
  type : Head
  fns : List FnDecl

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

/-- The functions of a trait impl, under their qualified names. -/
def TraitImpl.members (i : TraitImpl) : List FnDecl :=
  i.fns.map (FnDecl.qualify (implQualifier i.trait i.type))

/-- `effect Name { fn op(param: A) -> B; … }` (handlers.declaring-effect): each
operation with the type of its argument, its parameters as one value, and of
its result. That value is passed as a `let` parameter, never `inout`
(handlers.no-inout-parameter). -/
structure EffectDecl where
  name : Name
  ops : List (Name × Ty × Ty)

/-- The declarations of a program: records, variant types, the functions at
the top level, the `impl` blocks, the traits and their impls, and the
effects. -/
structure Decls where
  records : List RecordDecl
  variants : List VariantDecl
  functions : List FnDecl
  impls : List ImplDecl
  traits : List TraitDecl
  traitImpls : List TraitImpl
  effects : List EffectDecl

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

end Decls

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

/-! ## The functions of declarations -/

/-- Declarations without `impl` blocks have only the functions at the top
level. -/
@[simp] theorem Decls.fns_mk (records : List RecordDecl) (variants : List VariantDecl)
    (functions : List FnDecl) (traits : List TraitDecl) (effects : List EffectDecl) :
    (Decls.mk records variants functions [] traits [] effects).fns = functions := by
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

/-- A change to functions that commutes with qualifying their names reaches
every function, the methods under their qualified names included. -/
theorem Decls.fns_mapFns {f : FnDecl → FnDecl} (hf : ∀ T d, f (d.qualify T) = (f d).qualify T)
    (D : Decls) : (D.mapFns f).fns = D.fns.map f := by
  simp only [Decls.fns, Decls.mapFns, ImplDecl.members, TraitImpl.members, List.map_append,
    List.flatMap_map, List.map_flatMap, List.map_map]
  congr 1
  · congr 1
    refine congrArg (List.flatMap · D.impls) (funext fun i => ?_)
    exact List.map_congr_left fun d _ => (hf i.type d).symm
  · refine congrArg (List.flatMap · D.traitImpls) (funext fun i => ?_)
    exact List.map_congr_left fun d _ => (hf _ d).symm

/-- A change to functions that leaves every function of the program as it is
leaves its declarations as they are. -/
theorem Decls.mapFns_eq_self {f : FnDecl → FnDecl}
    (hf : ∀ T d, f (d.qualify T) = (f d).qualify T) (hname : ∀ d, (f d).name = d.name)
    {D : Decls} (h : ∀ d ∈ D.fns, f d = d) : D.mapFns f = D := by
  obtain ⟨records, variants, functions, impls, traits, traitImpls, effects⟩ := D
  have hq : ∀ T d, f (d.qualify T) = d.qualify T → f d = d := by
    intro T d hq
    rw [hf] at hq
    have hn := hname d
    generalize f d = g at hq hn ⊢
    cases g
    cases d
    simp_all [FnDecl.qualify]
  have hfun : functions.map f = functions :=
    (List.map_congr_left fun d hd => h d (List.mem_append_left _ (List.mem_append_left _ hd))).trans
      (List.map_id _)
  have himpl : (impls.map fun i => { i with fns := i.fns.map f }) = impls := by
    refine (List.map_congr_left fun i hi => ?_).trans (List.map_id _)
    obtain ⟨T, fns⟩ := i
    suffices fns.map f = fns by simp [this]
    refine (List.map_congr_left fun d hd => ?_).trans (List.map_id _)
    exact hq T d (h (d.qualify T) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨⟨T, fns⟩, hi, List.mem_map_of_mem hd⟩))))
  have htrait : (traitImpls.map fun i => { i with fns := i.fns.map f }) = traitImpls := by
    refine (List.map_congr_left fun i hi => ?_).trans (List.map_id _)
    obtain ⟨Tr, H, fns⟩ := i
    suffices fns.map f = fns by simp [this]
    refine (List.map_congr_left fun d hd => ?_).trans (List.map_id _)
    exact hq _ d (h _ (List.mem_append_right _ (List.mem_flatMap.2
      ⟨⟨Tr, H, fns⟩, hi, List.mem_map_of_mem hd⟩)))
  simp [Decls.mapFns, hfun, himpl, htrait]

end Stilt
