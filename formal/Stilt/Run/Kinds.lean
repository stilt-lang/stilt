import Stilt.Run.Decode
import Stilt.Syntax.Kinds

/-!
# Declarations as kinds read them, from JSON

A program's traits, impls, functions and uses of constructor parameters as kinds read them
(`Stilt.Syntax.Kinds`): a type is `["con", name, args]`, `["param", name, args]` or
`["other", parts]`; a receiver `"none"`, `"bare"` or `["typed", type]`; a signature
`[name, generics, receiver, params, result]`, each generic `[name, bounds]`, and an arity a
string of its digits.
-/

namespace Stilt.Run

open Lean (Json)

/-- A type as kinds read it. -/
partial def kty (j : Json) : Except String KTy := do
  match ← tagged j with
  | ("con", #[n, as]) => return .con (← str n) (← list kty as)
  | ("param", #[n, as]) => return .param (← str n) (← list kty as)
  | ("other", #[ps]) => return .other (← list kty ps)
  | _ => throw s!"a type as kinds read it, not {j.compress}"

def kreceiver (j : Json) : Except String KReceiver := do
  match ← tagged j with
  | ("none", #[]) => return .none
  | ("bare", #[]) => return .bare
  | ("typed", #[t]) => return .typed (← kty t)
  | _ => throw s!"a receiver, not {j.compress}"

/-- A number of arguments, written as a JSON string as an integer is. -/
def arity (j : Json) : Except String Nat := do return (← int j).toNat

def kgenerics : Decoder (List (Name × List Name)) := list (pair str (list str))

def ksig : Decoder KSig
  | .arr #[n, gs, r, ps, res] =>
    return ⟨← str n, ← kgenerics gs, ← kreceiver r, ← list kty ps, ← kty res⟩
  | j => throw s!"a signature, not {j.compress}"

/-- The declarations as kinds read them, each list optional, none for a program without them. -/
def kinds (j : Json) : Except String Kinds := do
  let get (k : String) : Json := (j.getObjVal? k).toOption.getD (.arr #[])
  return {
    arities := ← list (pair str arity) (get "arities")
    traits := ← get "traits" |> list fun t => match t with
      | .arr #[n, a, ps, ms] => return ⟨← str n, ← arity a, ← list str ps, ← list ksig ms⟩
      | _ => throw s!"a trait, not {t.compress}"
    impls := ← get "impls" |> list fun i => match i with
      | .arr #[t, ty, gs, ms] =>
        return ⟨← option str t, ← kty ty, ← kgenerics gs, ← list ksig ms⟩
      | _ => throw s!"an impl, not {i.compress}"
    functions := ← list ksig (get "functions")
    uses := ← get "uses" |> list fun u => do
      let (f, cs) ← pair str (list (pair str str)) u
      pure ⟨f, cs⟩ }

end Stilt.Run
