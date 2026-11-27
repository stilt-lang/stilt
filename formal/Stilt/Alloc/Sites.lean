import Stilt.Declarations
import Stilt.Generics

/-!
# The sites of `alloc` that make values

The operations that add the implicit effect `alloc` by making a value that needs storage of its
own (facts.allocation): a list literal, a closure literal, a string literal that interpolates
and the pieces it shows, a record literal of a recursive type and the constructor of a variant
with a payload of one, a `with`, a performance of an operation, and a native function that
allocates, which is every native but those facts.native-allocation names (`Op.allocates`). A
function named, called or as a value, adds `alloc` unless it is one of the functions a limit
covers (`Limited`, facts.inference), and a call through a function value adds nothing
(facts.calls-through-function-values).

The other sites, the writes through an index that aren't in place and the arguments a call
copies for an in-place parameter, read where a binding holds its own storage, and are in
`Stilt.Alloc.Storage`. The calculus has no key path and no `for` over an `Iter`,
so it has none of their sites. A form counts as the code it means (`Expr.form`), which the
evaluator runs: a projection's body, its `yield` and a call of a projection where a place is
mean code that keeps the values yielded in a list and passes the access as a closure literal, so
each allocates in the model.
-/

namespace Stilt

/-- Whether a function of lists allocates (facts.native-allocation): of `List<T>`, `len` and
`is_empty` don't; neither do the natives of `str` that facts.native-allocation names, `find` and
`rfind`, nor the integer methods and conversions, which give an `Option` of a number; a range,
which a `for` over it iterates, adds nothing (facts.div). Every other one allocates. -/
def ListOp.allocates : ListOp → Bool
  | .len | .isEmpty | .range _ | .find _ | .checked .. | .narrow .. | .truncate .. => false
  | _ => true

/-- Whether a function of maps allocates (facts.native-allocation): `len`, `is_empty`,
`contains`, `get`, which `m[k]` as a value is, and `==`, of an impl that no source declares whose
result names no `str`, `List` or `Map`, don't. -/
def MapOp.allocates : MapOp → Bool
  | .len | .isEmpty | .contains | .index | .equal => false
  | _ => true

/-- Whether a function of sets allocates (facts.native-allocation): every native of `Set`
does, as facts.native-allocation names none; `==`, through the structural `Eq` of `Set`, is a
method of an impl that no source declares and gives a `bool`, so it doesn't. -/
def SetOp.allocates : SetOp → Bool
  | .relate .equal => false
  | _ => true

/-- Whether a native operation allocates (facts.native-allocation). The native methods of the
integer and float types, the comparisons, the conversions and the parsers don't, and neither
do `len`, `is_empty`, `char_count`, `count`, the searches and the `is_ascii` tests of `str`, a
string literal with no interpolation, a tuple, held inline, a view (views.what-view-is), a
`panic`, whose result type is `Never`, and the methods of the structural impls of `Eq` and `Ord`,
whose results name no `str`, `List` or `Map`. An interpolating string literal and each piece it
shows allocate (facts.allocation), as the built-in `show` does, and so do `slice`, the natives
from a string to a string, `replace` and the paddings of `str`, a sort, `v.copy()` and every
operation on the world: `print`, the reads of the input and `Shared.new`. -/
def Op.allocates : Op → Bool
  | .concat | .showInt _ | .showBool | .pad .. | .inBase .. | .fixed .. | .scientific .. => true
  | .showValue | .slice | .strMap _ | .replace _ | .padStr _ | .sortedByKey .. | .copy => true
  | .list o => o.allocates
  | .map o => o.allocates
  | .set o => o.allocates
  | .world _ => true
  | _ => false

mutual

/-- The record and variant types a type names, through its type arguments and the
parameter, result and error types of its function types (facts.allocation). -/
def Ty.typeNames : Ty → List Name
  | .record R τs | .variant R τs => R :: tysTypeNames τs
  | .list τ | .set τ | .view τ | .shared τ => τ.typeNames
  | .tuple τs => tysTypeNames τs
  | .map κ τ => κ.typeNames ++ τ.typeNames
  | .fn ps r ρ => paramTypeNames ps ++ r.typeNames ++ ρ.typeNames
  | _ => []

/-- The record and variant types a list of types names. -/
def tysTypeNames : List Ty → List Name
  | [] => []
  | τ :: τs => τ.typeNames ++ tysTypeNames τs

/-- The record and variant types a list of parameter types names. -/
def paramTypeNames : List (Mode × Ty) → List Name
  | [] => []
  | (_, τ) :: ps => τ.typeNames ++ paramTypeNames ps

/-- The record and variant types a row's error type names. -/
def Row.typeNames : Row → List Name
  | ⟨_, some E, _, _, _⟩ => E.typeNames
  | ⟨_, none, _, _, _⟩ => []

end

namespace Decls

variable (D : Decls)

/-- The types a declaration writes: a record's fields' and a variant type's payloads'. -/
def declTypes (N : Name) : List Ty :=
  ((D.record? N).map fun r => r.fields.map Prod.snd).getD [] ++
    ((D.variant? N).map fun t => t.ctors.flatMap Prod.snd).getD []

/-- The record and variant types the declaration of `N` names. -/
def declNames (N : Name) : List Name := (D.declTypes N).flatMap Ty.typeNames

/-- The types that the declarations of `S` name, joined to `S`, `n` times over. -/
def reach : Nat → List Name → List Name
  | 0, S => S
  | n + 1, S => reach n (S ++ S.flatMap D.declNames).eraseDups

/-- Whether the type `N` is recursive: its declaration names it again, directly or through the
declarations of the types it names (declarations.recursive-types and facts.allocation). A
path of declarations from `N` back to it that visits no declaration twice has at most one step
for each declaration, so that many rounds find it. -/
def recursive (N : Name) : Bool :=
  (D.reach (D.records.length + D.variants.length) (D.declNames N)).contains N

/-- Whether a type is a recursive type, or may be one: a record or variant type that is one, or
a type parameter, which may stand for one. -/
def recursiveTy : Ty → Bool
  | .record N _ | .variant N _ => D.recursive N
  | .param _ => true
  | _ => false

/-- Whether the variant `C` of the variant type `T`, at the type arguments `args`, has a payload
of a recursive type, which its constructor boxes (facts.allocation): a payload declared with a
recursive type, or with a type parameter of `T` whose argument is one. In generic code an
argument that is a type parameter may stand for one, and counts as one. -/
def payloadRecursive (T : Name) (args : List Ty) (C : Name) : Bool :=
  match D.variant? T with
  | some t => ((t.ctors.lookup C).getD []).any fun τ => match τ with
    | .param A => ((t.typeArgs args).lookup A).all D.recursiveTy
    | τ => D.recursiveTy τ
  | none => false

end Decls

section

variable (D : Decls) (lim : Limited)

mutual

/-- Whether `e` holds no operation that adds `alloc` by making a value (facts.allocation and
facts.native-allocation), and names only functions that `lim` covers, which are without
`alloc` wherever they are named (facts.inference). A closure literal allocates, so its body
counts for nothing more; a call through a function value adds nothing
(facts.calls-through-function-values). -/
def Expr.allocFreeIn : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue => true
  | .fnRef f _ _ => lim.fn f
  | .method t m _ => lim.method t m
  | .record R _ fields => !D.recursive R && fieldsAllocFree fields
  | .variant T args C es => !D.payloadRecursive T args C && exprsAllocFree es
  | .list _ _ | .closure _ _ _ _ | .perform _ _ | .withH _ _ _ _ => false
  | .op o es => !o.allocates && exprsAllocFree es
  | .view es => exprsAllocFree es
  | .field e _ | .raise e | .try e | .form _ e | .return e | .loop e => e.allocFreeIn
  | .index a b | .letIn _ _ a b | .varIn _ _ a b | .seq a b | .for _ _ a b | .while a b
  | .tryCatch a _ _ b _ => a.allocFreeIn && b.allocFreeIn
  | .call f args _ => f.allocFreeIn && argsAllocFree args
  | .assign ⟨_, path⟩ v => pathAllocFree path && v.allocFreeIn
  | .if c _ a b => c.allocFreeIn && a.allocFreeIn && b.allocFreeIn
  | .match e _ arms => e.allocFreeIn && armsAllocFree arms
  | .held _ hs body => exprsAllocFree hs && body.allocFreeIn

/-- Whether no expression of a list adds `alloc` by making a value. -/
def exprsAllocFree : List Expr → Bool
  | [] => true
  | e :: es => e.allocFreeIn && exprsAllocFree es

/-- Whether no field of a record literal adds `alloc` by making a value. -/
def fieldsAllocFree : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.allocFreeIn && fieldsAllocFree fields

/-- Whether no argument of a call adds `alloc` by making a value. -/
def argsAllocFree : List Arg → Bool
  | [] => true
  | .value e :: args => e.allocFreeIn && argsAllocFree args
  | .inout ⟨_, path⟩ :: args => pathAllocFree path && argsAllocFree args

/-- Whether no index of a place adds `alloc` by making a value. -/
def pathAllocFree : List Projection → Bool
  | [] => true
  | .field _ :: path => pathAllocFree path
  | .index i :: path => i.allocFreeIn && pathAllocFree path

/-- Whether no arm of a `match`, guard or body, adds `alloc` by making a value. -/
def armsAllocFree : List Arm → Bool
  | [] => true
  | ⟨_, _, guard, body⟩ :: arms =>
    guardAllocFree guard && body.allocFreeIn && armsAllocFree arms

/-- Whether an arm's guard adds no `alloc` by making a value. -/
def guardAllocFree : Option Expr → Bool
  | none => true
  | some g => g.allocFreeIn

end

end

end Stilt
