import Stilt.Analysis.Intervals
import Stilt.Panics.Tests

/-!
# The facts an operation gives

What an operation of the calculus gives its value, from the values read and not yet used that
its operands pushed (`opValFacts`): the exact interval of `+`, `-`, `*` and `-a`, cut to the type's
bounds, the relative bounds of `+` and `-` to an operand's linear form, a conversion's value its
operand's, a list's length, and `push`'s list one longer. A comparison gives the facts it states
where it is true and their negations where it is false (`cmpFacts`). `verifyOp` is the analysis's
proof that an operation can't panic with a kind (facts.proved-divisions,
facts.proved-overflow), and `Facts.indexOk` that an index is in range (facts.proved-indexes).
-/

namespace Stilt

/-- A type's bounds, as an interval. -/
def IntTy.interval (k : IntTy) : Interval := (some k.min, some k.max)

/-- The linear form of the `i`th operand. -/
def linOf (lins : List (Option (Term × Int))) (i : Nat) : Option (Term × Int) := lins.getD i none

/-- `res − t` within `c + i`, when the linear form `t + c` is given. -/
def relateLin (i : Interval) : Option (Term × Int) → Facts → Facts
  | some (t, c), H => H.relate t c i
  | none, H => H

/-- The facts an operation gives its value, from the facts `G` on its operands, pushed from
the `d`th value read and not yet used, whose linear forms are `lins`, one for each operand
(facts.intervals and facts.relative-bounds). -/
def opValFacts (o : Op) (d : Nat) (lins : List (Option (Term × Int))) (G : Facts) : Facts :=
  match o, lins with
  | .arith .add k, [la, lb] =>
    relateLin (G.interval (.opnd d)) (G.linAt (d + 1) lb)
      (relateLin (G.interval (.opnd (d + 1))) (G.linAt d la)
        ((G.relate .zero 0 ((G.interval (.opnd d)).add (G.interval (.opnd (d + 1))))).relate
          .zero 0 k.interval))
  | .arith .sub k, [la, _] =>
    relateLin (G.interval (.opnd (d + 1))).neg (G.linAt d la)
      ((G.relate .zero 0 ((G.interval (.opnd d)).sub (G.interval (.opnd (d + 1))))).relate
        .zero 0 k.interval)
  | .arith .mul k, [_, _] =>
    (G.relate .zero 0 ((G.interval (.opnd d)).mul (G.interval (.opnd (d + 1))))).relate
      .zero 0 k.interval
  | .arith .div k, [_, _] | .arith .rem k, [_, _] => G.relate .zero 0 k.interval
  | .neg k, [_] => (G.relate .zero 0 (G.interval (.opnd d)).neg).relate .zero 0 k.interval
  | .convert _ _, [_] => G.equate (.opnd d) 0
  | .list .len, [_] => G.equate (.opndLen d) 0
  | .list .push, [_, _] => (G.insert ⟨.reslen, .opndLen d, 1⟩).insert ⟨.opndLen d, .reslen, -1⟩
  | _, _ => G

/-- `t` non-zero, where the operand `i`'s value is `t + 0` and the operand `j`'s is the
literal 0 (facts.conditions). -/
def nonzeroPick (G : Facts) (d i j : Nat) (lins : List (Option (Term × Int))) (H : Facts) : Facts :=
  match G.linAt (d + j) (linOf lins j), G.linAt (d + i) (linOf lins i) with
  | some (.zero, 0), some (t, 0) => (H.addNonzero t).addNonzero (.opnd (d + i))
  | _, _ => H

/-- What `a != b` gives where it is true: the term of one operand non-zero when the other is
the literal 0, each way round (facts.conditions). -/
def nonzeroBy (G : Facts) (d : Nat) (lins : List (Option (Term × Int))) : Facts :=
  nonzeroPick G d 1 0 lins (nonzeroPick G d 0 1 lins G)

/-- The facts a comparison of the two values pushed from the `d`th states where it is `truth`
(facts.conditions): `a < b` states `a − b ≤ −1`, `a == b` states `a − b ≤ 0` and `b − a ≤ 0`,
`a != b` against the literal 0 makes the other's term non-zero, and the false of each states its
negation. -/
def cmpFacts (c : Cmp) (d : Nat) (lins : List (Option (Term × Int))) (G : Facts) (truth : Bool) :
    Facts :=
  match c, truth with
  | .lt, true | .ge, false => G.insert ⟨.opnd d, .opnd (d + 1), -1⟩
  | .le, true | .gt, false => G.insert ⟨.opnd d, .opnd (d + 1), 0⟩
  | .gt, true | .le, false => G.insert ⟨.opnd (d + 1), .opnd d, -1⟩
  | .ge, true | .lt, false => G.insert ⟨.opnd (d + 1), .opnd d, 0⟩
  | .eq, true | .ne, false => (G.insert ⟨.opnd d, .opnd (d + 1), 0⟩).insert ⟨.opnd (d + 1), .opnd d, 0⟩
  | .ne, true | .eq, false => nonzeroBy G d lins

/-- Whether the facts prove the value pushed `i`th non-zero: its interval leaves out zero, or it
is a non-zero term plus 0 (facts.proved-divisions). -/
def nonzeroDivisor (G : Facts) (i : Nat) (l : Option (Term × Int)) : Bool :=
  (G.interval (.opnd i)).1.any (1 ≤ ·) || (G.interval (.opnd i)).2.any (· ≤ -1) ||
    match G.linAt i l with
    | some (t, 0) => decide (t ∈ G.nonzero)
    | _ => false

/-- Whether the analysis proves that an operation on the two values pushed from the `d`th
can't panic with the kind `k`: a division or remainder whose divisor's interval leaves out
zero, or whose divisor is a non-zero term plus 0 (facts.proved-divisions); `+`, `-`, `*` and
`-a` whose exact interval lies within the type's bounds, a shift whose amount lies within 0
and the width less one, and a signed division or remainder whose dividend's interval leaves
out the type's least value or whose divisor's leaves out −1 (facts.proved-overflow). -/
def verifyOp (o : Op) (d : Nat) (lins : List (Option (Term × Int))) (G : Facts) (k : PanicKind) :
    Bool :=
  match o, k, lins with
  | .arith .div _, .divideByZero, [_, lb] | .arith .rem _, .divideByZero, [_, lb] =>
    nonzeroDivisor G (d + 1) lb
  | .arith .div t, .overflow, [_, _] | .arith .rem t, .overflow, [_, _] =>
    !t.signed || (G.interval (.opnd d)).1.any (t.min < ·) ||
      (G.interval (.opnd (d + 1))).1.any (-1 < ·) || (G.interval (.opnd (d + 1))).2.any (· < -1)
  | .arith .add t, .overflow, [_, _] =>
    ((G.interval (.opnd d)).add (G.interval (.opnd (d + 1)))).within t.min t.max
  | .arith .sub t, .overflow, [_, _] =>
    ((G.interval (.opnd d)).sub (G.interval (.opnd (d + 1)))).within t.min t.max
  | .arith .mul t, .overflow, [_, _] =>
    ((G.interval (.opnd d)).mul (G.interval (.opnd (d + 1)))).within t.min t.max
  | .neg t, .overflow, [_] => (G.interval (.opnd d)).neg.within t.min t.max
  | .shift _ t _, .overflow, [_, _] => (G.interval (.opnd (d + 1))).within 0 (t.bits - 1)
  | _, _, _ => false

namespace Facts

/-- Whether the facts give `0 ≤ i` and `i ≤ ℓ − 1`, for `i` and `ℓ` terms (facts.proved-indexes). -/
def indexOk (G : Facts) (i ℓ : Term) : Bool :=
  (G.bound .zero i).any (· ≤ 0) && (G.bound i ℓ).any (· ≤ -1)

theorem Holds.indexOk {G : Facts} {ν : Valuation} (h : G.Holds ν) (hz : ν .zero = 0) {i ℓ : Term}
    (hk : G.indexOk i ℓ = true) : 0 ≤ ν i ∧ ν i < ν ℓ := by
  simp only [Facts.indexOk, Bool.and_eq_true, Option.any_eq_true, decide_eq_true_eq] at hk
  obtain ⟨⟨a, ha, hac⟩, ⟨b, hb, hbc⟩⟩ := hk
  have := h.bound ha; have := h.bound hb; rw [hz] at *; omega

end Facts

/-- A read in range of a list is no panic. -/
theorem get_index_ok {v : Value} {k : Int} (hk : 0 ≤ k ∧ k < v.lenOr) :
    v.get [.index k] ≠ .error (.panic .bounds) := by
  cases v <;> simp only [Value.lenOr] at hk <;> try omega
  rename_i vs
  simp only [Value.get, elemAt?, hk.1, ↓reduceIte]
  rw [List.getElem?_eq_getElem (by omega)]
  simp

/-- A store in range of a list is no panic. -/
theorem set_index_ok {v w : Value} {k : Int} (hk : 0 ≤ k ∧ k < v.lenOr) :
    v.set [.index k] w ≠ .error (.panic .bounds) := by
  cases v <;> simp only [Value.lenOr] at hk <;> try omega
  rename_i vs
  simp only [Value.set, elemAt?, hk.1, ↓reduceIte]
  rw [List.getElem?_eq_getElem (by omega)]
  simp [Functor.map, Except.map]

end Stilt
