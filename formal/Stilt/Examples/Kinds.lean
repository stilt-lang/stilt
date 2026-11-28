import Stilt.Kinds

/-!
# Kinds of traits over type constructors

The declarations of `conformance/parameters/constructors.lt` as kinds read them, which pass the
checks of kinds, and each mistake of `conformance/parameters/constructor_errors.lt` added to
them, which fails them: `Self` written alone, a receiver whose type isn't written, a plain
trait's receiver written, an impl for `Map` or for `List<i64>`, a constructor parameter written
alone or with two arguments, a bound list that mixes a trait over constructors with `Show`, and
a use at a tuple's type, which no impl is for.
-/

namespace Stilt.Examples.Kinds

private def option : Name := "Option"
private def list : Name := "List"

private def a : KTy := .param "#0" []
private def b : KTy := .param "#1" []
private def i64 : KTy := .con "i64" []

/-- `fn transform<A, B>(self: S<A>, f: fn(A) -> B) -> S<B>`, with `S` the trait's `Self` or a
constructor. -/
private def transform (s : Name → List KTy → KTy) : KSig :=
  ⟨"transform", [("#0", []), ("#1", [])], .typed (s "x" [a]), [.other [a, b]], s "x" [b]⟩

private def mappable : KTrait :=
  ⟨"Mappable", 1, [], [transform fun _ => .param selfParam]⟩

private def implFor (c : Name) : KImpl :=
  ⟨some "Mappable", .con c [], [], [transform fun _ => .con c]⟩

/-- `fn doubled<F: Mappable>(xs: F<i64>) -> F<i64>`. -/
private def doubled : KSig :=
  ⟨"doubled", [("#0", ["Mappable"])], .none, [.param "#0" [i64]], .param "#0" [i64]⟩

private def program : Kinds where
  arities := [(option, 1), (list, 1), ("Map", 2), ("i64", 0)]
  traits := [mappable]
  impls := [implFor option, implFor list]
  functions := [doubled]
  uses := [⟨"doubled", [("#0", option)]⟩, ⟨"doubled", [("#0", list)]⟩]

/-- The program passes the checks. -/
example : program.Checked := by decide

/-- So `doubled` at `List` is made of types, `List<i64>`. -/
example : (KTy.param "#0" [i64]).substCtors [("#0", list)] = .con list [i64] := by decide

/-- `fn wrap<A>(self: Self<A>) -> Self`: `Self` alone in a trait over `Self<A>`. -/
example : ¬ { program with traits := [⟨"Mappable", 1, [],
    [⟨"wrap", [("#0", [])], .typed (.param selfParam [a]), [], .param selfParam []⟩]⟩] }.Checked := by
  decide

/-- `fn size(self) -> i64` in a trait over constructors: no receiver's type. -/
example : ¬ { program with traits := [⟨"Mappable", 1, [],
    [⟨"size", [], .bare, [], i64⟩]⟩] }.Checked := by decide

/-- `fn name(self: Self) -> str` in a trait over types: a receiver's type written. -/
example : ¬ { program with traits := [mappable, ⟨"Named", 0, [],
    [⟨"name", [], .typed (.param selfParam []), [], .con "str" []⟩]⟩] }.Checked := by decide

/-- `impl Mappable for Map {}`: a constructor of two arguments. -/
example : ¬ { program with
    impls := program.impls ++ [(⟨some "Mappable", .con "Map" [], [], []⟩ : KImpl)] }.Checked := by
  decide

/-- `impl Mappable for List<i64> {}`: an applied type. -/
example : ¬ { program with
    impls := [implFor option, ⟨some "Mappable", .con list [i64], [], []⟩] }.Checked := by
  decide

/-- `fn bare<F: Mappable>(x: F) -> i64`: `F` alone. -/
example : ¬ { program with functions := [doubled,
    ⟨"bare", [("#0", ["Mappable"])], .none, [.param "#0" []], i64⟩] }.Checked := by decide

/-- `fn two<F: Mappable>(x: F<i64, i64>) -> i64`: two arguments. -/
example : ¬ { program with functions := [doubled,
    ⟨"two", [("#0", ["Mappable"])], .none, [.param "#0" [i64, i64]], i64⟩] }.Checked := by decide

/-- `fn mixed<F: Mappable + Show>(x: F<i64>) -> i64`: bounds of two arities. -/
example : ¬ { program with
    traits := [mappable, ⟨"Show", 0, [], []⟩]
    functions := [doubled,
      ⟨"mixed", [("#0", ["Mappable", "Show"])], .none, [.param "#0" [i64]], i64⟩] }.Checked := by
  decide

/-- `doubled((1, 2))`: a tuple's type has no constructor, so no impl, written `?` by the export. -/
example : ¬ { program with uses := [⟨"doubled", [("#0", "?")]⟩] }.Checked := by decide

end Stilt.Examples.Kinds
