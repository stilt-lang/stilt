import Stilt.Modes.Traverse
import Stilt.Syntax.Forms

/-!
# Capabilities

facts.capabilities: the eight capabilities below `io` (`Cap`) are facts of functions, inferred
as the implicit effects are. A function has the capabilities of the natives it names, of every
function it names, and of the bodies of the closure literals and handler literals it contains;
a call of a trait method names the impl's method, and recursive groups are solved as a fixed
point. Like `locks` (`Stilt.Locks.Syntax`), the fact ignores types: it reads the names a body
writes.

Of the natives of facts.capability-natives, the calculus has those of `console` that its world
performs, `print`, `eprint`, `write`, `ewrite`, `read_line`, `poll_line` and `read_all`
(`WorldOp.write`, `WorldOp.readLine` and `WorldOp.readAll`), and those of `spawn`, `task.spawn`
and `s.spawn`, which are forms (`Stilt.Typing.Tasks`); it has no native of the six others, so
no function of the calculus has them. A call through a function value adds nothing
(facts.calls-through-function-values): a function value is no site.

Each capability is a limit, `without console` and the others (`Limits.caps`), which
`Program.CapLimited` checks as E0204: a body that the limit covers holds no site of the
capability. Its promise, that the code reaches nothing of the capability through its own source,
the model leaves out.
-/

namespace Stilt

/-- Whether an operation is a native of the capability `c`: of `console`, a write to the output
or to standard error and a read of the input (facts.capability-natives). -/
def Op.ofCap : Cap → Op → Bool
  | .console, .world (.write _ _) | .console, .world .readLine | .console, .world .readAll => true
  | _, _ => false

/-- Whether a form is a native of the capability `c`: of `spawn`, `task.spawn` and `s.spawn`
(tasks.implicit-effects-and-capabilities). -/
def Form.ofCap : Cap → Form → Bool
  | .spawn, .spawn | .spawn, .scopeSpawn => true
  | _, _ => false

/-- Whether a method `Trait.m` may be a function of `L`: the function `m` of some impl of the
trait is. -/
def Decls.methodIn (D : Decls) (L : List Name) (trait m : Name) : Bool :=
  D.traitImpls.any fun i => i.trait == trait && decide (implName trait i.type m ∈ L)

/-- The sites of the capability `c` at one expression, the functions of `L` having it: a native
of `c`, and a function of `L` named, called or as a value, or a method one of whose impls is. -/
def capVisit (D : Decls) (c : Cap) (L : List Name) (_ : Unit) : Expr → List Unit
  | .op o _ => if o.ofCap c then [()] else []
  | .form k _ => if k.ofCap c then [()] else []
  | .fnRef f _ _ => if f ∈ L then [()] else []
  | .method t m _ => if D.methodIn L t m then [()] else []
  | _ => []

/-- Whether `e` holds no site of the capability `c`, the functions of `L` having it, at any
depth, the bodies of closure literals and of handler literals included. -/
def Expr.capFree (D : Decls) (c : Cap) (L : List Name) (e : Expr) : Bool :=
  (e.gather (fun _ _ _ => ()) (capVisit D c L) ()).isEmpty

/-- The functions whose bodies hold a site of `c`, given that those of `L` have it. -/
def Decls.capSites (D : Decls) (c : Cap) (L : List Name) : List Name :=
  (D.fns.filter fun d => !d.body.capFree D c L).map (·.name)

/-- `k` more rounds of `capSites` from `L`, stopping once a round adds nothing; every function
once no round is left, which is no less than the fixed point. -/
def Decls.capsAfter (D : Decls) (c : Cap) : Nat → List Name → List Name
  | 0, _ => D.fns.map (·.name)
  | k + 1, L =>
    let L' := D.capSites c L
    if L'.all (· ∈ L) then L else D.capsAfter c k L'

/-- The functions that have the capability `c` (facts.capabilities): the fixed point of
`capSites` from no function, each round adding the functions whose bodies hold a site given the
last. The sets grow, so they settle within one round for each function. -/
def Decls.caps (D : Decls) (c : Cap) : List Name := D.capsAfter c (D.fns.length + 1) []

/-- Every function outside `L` has a body without a site of `c`. -/
def Decls.CapsClosed (D : Decls) (c : Cap) (L : List Name) : Prop :=
  ∀ d ∈ D.fns, d.name ∉ L → d.body.capFree D c L = true

theorem Decls.capsAfter_closed (D : Decls) (c : Cap) : ∀ (k : Nat) (L : List Name),
    D.CapsClosed c (D.capsAfter c k L)
  | 0, _, d, hd, hn => absurd (List.mem_map_of_mem hd) hn
  | k + 1, L, d, hd, hn => by
    simp only [Decls.capsAfter] at hn ⊢
    split <;> rename_i hall
    · rw [ite_eq_left hall] at hn
      cases hb : d.body.capFree D c L with
      | true => rfl
      | false =>
        refine absurd (List.all_eq_true.1 hall d.name ?_) (by simpa using hn)
        exact List.mem_map_of_mem (List.mem_filter.2 ⟨hd, by simp [hb]⟩)
    · rw [ite_eq_right hall] at hn
      exact Decls.capsAfter_closed D c k _ d hd hn

/-- A function without a capability has a body that holds no site of it: the fact is closed
under the functions a body names. -/
theorem Decls.caps_closed (D : Decls) (c : Cap) : D.CapsClosed c (D.caps c) :=
  D.capsAfter_closed c _ _

/-- E0204 for the capabilities (facts.capabilities and facts.without): the body of each function
limited by `without c`, and `main`'s when it is, holds no site of `c`: no native of `c`, no
function that has `c`, named or called, and no closure literal or handler literal whose body
holds one. -/
def Program.CapLimited (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns, ∀ c ∈ d.limits.caps, d.body.capFree p.decls c (p.decls.caps c) = true) ∧
    ∀ c ∈ p.limits.caps, p.main.capFree p.decls c (p.decls.caps c) = true

instance (p : Program) : Decidable p.CapLimited := by
  unfold Program.CapLimited; exact inferInstance

end Stilt
