import Stilt.Alloc.Storage

/-!
# The limits `without alloc` and `without copy`

The checks of `without alloc` and `without copy`, as the Reference infers facts
(facts.inferred-facts and facts.inference): a function has a fact when its own body holds a
site of it, or names a function that has it, the functions of a recursive group solved together.
A limit is kept when some set of functions holding every function it is on holds no site of the
fact and names only functions of the set, the greatest such set being those that the inference
finds without it, as for `without panic` (`Program.PanicKeptBy`).

The sites of `alloc` are the operations that make a value (`Expr.allocFreeIn`), the writes
through an index that aren't in place and the `inout` arguments through an index, and the
arguments that a call copies for an in-place parameter (`Expr.storesIn`). The sites of `copy`
are the modifications that are shared, which the inference of modes.shared-writes finds
(`ModeEnv.allShared`), and the arguments that a call copies for an in-place parameter.
-/

namespace Stilt

/-- Whether `e` names only functions that `lim` covers, called or as values, the bodies of its
closure literals included (facts.inference). -/
def Expr.namesWithin (lim : Limited) (e : Expr) : Bool :=
  (e.gather (fun _ _ _ => ()) (fun _ e => match e with
    | .fnRef f _ _ => [lim.fn f]
    | .method t m _ => [lim.method t m]
    | _ => []) ()).all id

/-- The functions that `lim` covers hold no site of `alloc` and name only functions it covers, and each
impl's method `m` of a trait `t` is covered when `t.m` is: no operation of theirs makes a value that
allocates (facts.allocation and facts.native-allocation), each of their writes through an index is
in place (facts.writes-in-place) and each argument they pass to an in-place parameter needs no copy
(facts.copy-at-call), the in-place parameters being those `IP` says. The writes in place and the
copies at calls are checks of acceptance alone, with no proved run-time promise; the sites that make
a value have one (`Program.AllocsKept`). -/
structure Decls.AllocCover (D : Decls) (lim : Limited) (IP : Name → Nat → Bool) : Prop where
  fns : ∀ d ∈ D.fns, lim.fn d.name = true →
    d.body.allocFreeIn D lim = true ∧ d.storesOk D IP true = true
  methods : ∀ t m h i, lim.method t m = true → D.traitImpl? t h = some i →
    lim.fn (implName t h m) = true

/-- The functions that `lim` covers hold no site of `copy` and name only functions it covers: no
modification of theirs is shared (modes.shared-writes), in their bodies or their closure literals',
and no argument they pass to an in-place parameter needs a copy (facts.copy-at-call), the in-place
parameters being those `IP` says (facts.copy). A check of acceptance alone: the model proves no
run-time promise of it, since its values share no storage. -/
structure Decls.CopyCover (D : Decls) (lim : Limited) (IP : Name → Nat → Bool) : Prop where
  fns : ∀ d ∈ D.fns, lim.fn d.name = true →
    D.modeEnv.allShared d.params d.body = [] ∧ d.body.namesWithin lim = true ∧
      d.storesOk D IP false = true
  methods : ∀ t m h i, lim.method t m = true → D.traitImpl? t h = some i →
    lim.fn (implName t h m) = true

/-- `without alloc`, kept as the Reference infers facts (facts.without-alloc, facts.without and
facts.inference): some set of functions, holding every function limited by `without alloc`, holds no
operation that adds `alloc`, its own or one that it inherits, and names only functions of the set,
and so does `main`'s body when `main` is limited. Under the limit a function holds the storage of
its parameters (facts.own-storage), so its writes through an index can be in place, and its callers
copy what a shared argument needs (facts.copy-at-call). A function value that limited code calls
adds nothing (facts.calls-through-function-values). Of these checks, the sites that make a value
have a proved promise (`Program.AllocsKept`); the writes in place and the copies at calls are checks
of acceptance alone, with no proved run-time promise. -/
def Program.AllocLimited (p : Program) : Prop :=
  ∃ (lim : Limited) (IP : Name → Nat → Bool), p.decls.InPlaceParams IP ∧
    p.decls.AllocCover lim IP ∧
    (∀ d ∈ p.decls.fns, d.limits.alloc = true → lim.fn d.name = true) ∧
    (p.limits.alloc = true →
      p.main.allocFreeIn p.decls lim = true ∧ p.main.mainStoresOk p.decls IP true = true)

/-- `without copy`, kept as the Reference infers facts (facts.without-copy, facts.copy and
facts.without): some set of functions, holding every function limited by `without copy`, holds no
site of `copy`, its own or one that it inherits, and names only functions of the set, and so does
`main`'s body when `main` is limited. A fresh value stays within the limit: a list literal, a string
that interpolates, a `push` on a list that no copy shares. A check of acceptance alone: `without
copy` has no proved run-time promise, since the model's values share no storage. -/
def Program.CopyLimited (p : Program) : Prop :=
  ∃ (lim : Limited) (IP : Name → Nat → Bool), p.decls.InPlaceParams IP ∧
    p.decls.CopyCover lim IP ∧
    (∀ d ∈ p.decls.fns, d.limits.copy = true → lim.fn d.name = true) ∧
    (p.limits.copy = true →
      p.decls.modeEnv.allShared [] p.main = [] ∧ p.main.namesWithin lim = true ∧
        p.main.mainStoresOk p.decls IP false = true)

end Stilt
