# 11. Traits and methods: rationale

Stilt's traits are type classes with coherence, as Haskell's and Rust's are. Every name has exactly one home, so there is no overloading. Each choice below keeps that true: where methods are declared, how `x.m()` is resolved, and which trait features belong to core.

## Inherent impl blocks

A type's own functions live in its home module ([traits.impl-blocks](../11-traits.md#traits.impl-blocks)). A reader finds every method of a type where the type is declared, and two modules can't give one type two methods of one name. Swift's extensions and C#'s extension methods allow both, and a call's meaning then depends on which modules are imported. A program that wants a new method on a type it doesn't own declares a trait.

A block covers a whole type constructor, each parameter used once, so there is no specialization: no block for `List<i64>` stands beside the one for every `List<T>`. A bounded block ([traits.bounded-blocks](../11-traits.md#traits.bounded-blocks)) gives the functions that need more of the elements, as `sorted` needs `Ord`, without a second type.

## Traits and impls

Coherence and the orphan rule ([traits.coherence](../11-traits.md#traits.coherence), [traits.orphan-rule](../11-traits.md#traits.orphan-rule)) together mean that a trait and a type constructor have at most one impl in the whole program, in one of two modules. Every call then has exactly one meaning, and adding a dependency can never give a type a second impl of a trait. Haskell allows orphan instances with a warning, and two libraries can then define the same instance.

Floats show the cost: `Hash` and `f64` both live in `std.prelude`, so no program can make floats map keys. The other cost is that a type gets one impl of each trait. A program that wants another order for a type passes a comparison to `sorted_with`, or wraps the type in a single variant of its own.

An impl's members have exactly the trait's signatures ([traits.impl-signatures](../11-traits.md#traits.impl-signatures)), including which parameters are written `escaping`. A caller through a bound sees only the trait's declaration. A non-escaping parameter must then pass its argument's effects through in every impl alike, or the effects of a generic call would depend on which impl it reaches.

## Bounds

Bounds are written on the generics of functions and impls ([traits.bounds](../11-traits.md#traits.bounds)), where code needs what they provide, and never on a type's parameters. A type then stays usable by code that needs nothing of its arguments.

In a generic body, the bounds are all that is known of a type parameter ([traits.unsatisfied-bounds](../11-traits.md#traits.unsatisfied-bounds)). So a body checks once, whatever types later instantiate it. C++ templates check each instantiation instead, and report an error inside the template for a type that the caller chose.

## Method resolution

A call is resolved from the type of its receiver alone ([traits.method-resolution](../11-traits.md#traits.method-resolution), [traits.no-overloading](../11-traits.md#traits.no-overloading)). Each method has one home for each type, inherent or a trait's, and the steps of resolution find it. A call never chooses among candidates by the types of its arguments, as overloading in Java and C++ does. The receiver's type must therefore be known where the call stands, which inference in evaluation order gives ([types.known-types](../07-types.md#types.known-types)).

Where two traits give one name, the call says which, as `Labeled.name(r)` ([traits.ambiguous-methods](../11-traits.md#traits.ambiguous-methods)). An inherent method can't hide a trait's ([traits.name-clashes](../11-traits.md#traits.name-clashes)), because the inherent one would win without a word, as it does in Rust.

A trait is in scope through the current module's own `use` declarations ([traits.traits-in-scope](../11-traits.md#traits.traits-in-scope)), not through a parent module. So the imports of a module list every module whose traits its calls rely on.

## The prelude traits

Four traits stand behind the language's operators, map keys and interpolation ([traits.prelude-traits](../11-traits.md#traits.prelude-traits), [traits.required-traits](../11-traits.md#traits.required-traits)). Tuples, records, variant types and the prelude's containers get them automatically when their components have them ([traits.structural-impls](../11-traits.md#traits.structural-impls)). So every plain data type supports `==`, ordering and printing with no boilerplate. Rust asks for an explicit `derive`, which is a macro. Macros belong to the meta tier, and core code needs equality without one.

The structural impls work through components in a fixed order ([traits.structural-calls](../11-traits.md#traits.structural-calls)). The impls that the program writes may print or panic, so the calls made to them are the same in every implementation.

Comparisons of compound values go through `compare`, not through the operators of the components. With floats inside, `<` on tuples and lists would otherwise stop being a total order, and sorting by a compound key would break.

A written `Eq` turns off the structural `Hash` ([traits.hash-follows-written-eq](../11-traits.md#traits.hash-follows-written-eq)). Hashing every component could give different hashes to two values that the written `eq` calls equal, which breaks the law that maps rely on.

## Floats

Floats have two orders ([traits.floats](../11-traits.md#traits.floats)). `<` follows IEEE 754, as numeric code expects. `compare`, sorting and comparisons of compound values use a total order, so sorting by a float key is total and deterministic. The total order differs from Rust's `total_cmp` only for NaN. Hardware doesn't fix the sign bit of a NaN, so every NaN is one value that sorts last.

## Showing values

`Show` has two methods ([traits.show](../11-traits.md#traits.show)) because a string prints differently on its own and inside another value. With a single method, strings would be quoted at the top level, or left unquoted inside lists, where `["a, b"]` and `["a", "b"]` would look alike. Rust splits the same two uses between `Display` and `Debug`, which a type implements separately.

## Elaboration

Generic code is elaborated into dictionary passing, as in Haskell: each bound becomes a hidden argument that carries the impl's members. This is a way to implement the chapter, and no rule of the chapter depends on it.

The reference interpreter evaluates the elaborated program, because dispatch, the defaulting of literals and the width of integers all depend on types. A trait's dictionary also carries the types that its impl gives the trait parameters. The elaborated program reads them where a member type decides dispatch or the type of a literal. A constructor trait has one dictionary per constructor, whose methods are generic over the constructor's arguments.

## Trait parameters

A trait's parameters are determined by `Self` ([traits.trait-arguments](../11-traits.md#traits.trait-arguments)). An impl's type fixes them, so a type still has one impl of each trait, nothing is overloaded, and each path names one declaration. A parameter that `Self` determines is what Rust calls an associated type. One feature serves for both, and code names it through the type, as `C.Item` ([traits.member-types](../11-traits.md#traits.member-types)).

Three alternatives are rejected:

- Associated types beside trait parameters, as `type Item` in the trait and `type Item = T` in each impl. The language would have two spellings for one thing, and each impl would restate what its header already says.
- Trait parameters that don't depend on `Self`, as in Rust's `From<T>`. A type could then have an impl for each argument. A call would be resolved from its argument types, which is overloading, and a path to an impl's member would name several impls.
- Equality in `where`, as `where C.Item = i64`. It says what the bound `C: Collection<i64>` already says ([traits.bound-arguments](../11-traits.md#traits.bound-arguments)), and one form is enough.

A `where` clause bounds member types only ([traits.where](../11-traits.md#traits.where)), because the bound of a type parameter has its place beside the parameter. A function of a trait or a trait impl has the trait's signature, so it can't bound what the trait leaves open.

## Trait functions without `self` and trait constants

A trait may make a value with none to call a method on, as `T.empty()` ([traits.functions-without-self](../11-traits.md#traits.functions-without-self)). It is named on a type. Haskell resolves `mempty` from the type a call is expected to have, which makes the meaning of a call depend on its context, a form of overloading. So `Monoid.neutral()` is an error whose fix writes the type.

## Constructor traits

A constructor trait abstracts over `List` and `Option` alike ([traits.constructor-traits](../11-traits.md#traits.constructor-traits)), so a function written once runs on every constructor that maps. Its arity is inferred from how the trait writes `Self`.

The other choice names a constructor in the trait's header, as in `trait Functor<F<_>> { fn map<A, B>(fa: F<A>, …) }`, close to Haskell's `class Functor f`. The trait's functions then have no `self`, so `xs.map(f)` can't find them, and `Self` already names what a trait abstracts over.

Two things are left out:

- Partial application of constructors, as `impl Mappable for Result<_, E>`. It needs a syntax for the missing argument and a rule for which one is missing.
- Higher-kinded type declarations, as `type Wrap<F<_>>`. They need a kind in a type's header, so only functions take constructor parameters ([traits.constructor-parameters](../11-traits.md#traits.constructor-parameters)).

`std` declares no constructor trait, because the library lives in modules and a trait belongs to the module that needs it. `List` and `Option` keep their own `map`.

## The advanced tier

Trait parameters, member types, `where` clauses, trait functions without `self`, trait constants and constructor traits make a module advanced ([traits.advanced-tier](../11-traits.md#traits.advanced-tier)), and the tools show it, as for views. These features complicate inference and coherence, so core keeps traits over `Self` alone. A module that only calls the methods of an advanced trait stays in core.
