import Stilt.Optimality.Witness

/-!
# Programs without indexes

A program whose places hold no index: no place that it reads, assigns or
passes `inout` has an index among its projections (modes.places). Indexing
a value that isn't a place, as `[0][i]` does, reads no place, so such a
program may still index. In it, modes.overlap removes nothing, and each
place is its shape.

A call rule is sound on these programs (`CallRule.SoundIndexFree`) when the two
models agree on each of them that obeys the law with the rule. That asks less
than `CallRule.Sound`. The witness is such a program (`witness_indexFree`), so
`Stilt.Optimality.Theorem` bounds these rules by modes.overlapping-inout too.
-/

namespace Stilt

mutual

/-- Whether no place in `e` holds an index: no place that it reads, assigns or
passes `inout`, its closure literals' bodies included. An index of a value
that isn't a place reads no place. -/
def Expr.indexFree : Expr → Bool
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ => true
  | .record _ _ fields => fieldsIndexFree fields
  | .variant _ _ _ es => exprsIndexFree es
  | .list _ es => exprsIndexFree es
  | .op _ es | .view es => exprsIndexFree es
  | .field e _ => e.indexFree
  | .index e i => e.place?.isNone && e.indexFree && i.indexFree
  | .closure _ _ _ body => body.indexFree
  | .call callee args _ => callee.indexFree && argsIndexFree args
  | .letIn _ _ init body => init.indexFree && body.indexFree
  | .varIn _ _ init body => init.indexFree && body.indexFree
  | .assign p value => p.indexFree && value.indexFree
  | .seq a b => a.indexFree && b.indexFree
  | .if c _ a b => c.indexFree && a.indexFree && b.indexFree
  | .match e _ arms => e.indexFree && armsIndexFree arms
  | .for _ _ e body => e.indexFree && body.indexFree
  | .raise e => e.indexFree
  | .try e | .form _ e => e.indexFree
  | .tryCatch e _ _ handler _ => e.indexFree && handler.indexFree
  | .while c body => c.indexFree && body.indexFree
  | .loop body => body.indexFree
  | .return e => e.indexFree
  | .perform _ e => e.indexFree
  | .withH _ _ h b => h.indexFree && b.indexFree
  | .held _ hs body => exprsIndexFree hs && body.indexFree

/-- Whether no place in the expressions of a list holds an index. -/
def exprsIndexFree : List Expr → Bool
  | [] => true
  | e :: es => e.indexFree && exprsIndexFree es

/-- Whether no place in the fields of a record literal holds an index. -/
def fieldsIndexFree : List (Name × Expr) → Bool
  | [] => true
  | (_, e) :: fields => e.indexFree && fieldsIndexFree fields

/-- Whether no place in the arguments of a call holds an index: neither one in
a value argument nor the place of an `inout` argument. -/
def argsIndexFree : List Arg → Bool
  | [] => true
  | .value e :: args => e.indexFree && argsIndexFree args
  | .inout p :: args => p.indexFree && argsIndexFree args

/-- Whether no place in the arms of a `match` holds an index. -/
def armsIndexFree : List Arm → Bool
  | [] => true
  | ⟨_, _, guard, body⟩ :: arms => guardIndexFree guard && body.indexFree && armsIndexFree arms

/-- Whether no place in an arm's guard holds an index. -/
def guardIndexFree : Option Expr → Bool
  | none => true
  | some g => g.indexFree

end

/-- No place of the program holds an index: none in a function's body, and
none in `main`. -/
def Program.IndexFree (p : Program) : Prop :=
  (∀ d ∈ p.decls.fns, d.body.indexFree = true) ∧ p.main.indexFree = true

/-- A call rule is sound on programs without indexes when every well-typed
program whose places hold no index, and that obeys the law of exclusivity
with the rule, gives the same observation under copy-in, copy-out and in
place, with every fuel. -/
def CallRule.SoundIndexFree (rule : CallRule) : Prop :=
  ∀ p : Program, p.WellTyped → p.IndexFree → p.ExclusiveWith rule →
    ∀ fuel, (p.runCopy fuel).observe = (p.runInPlace fuel).observe

/-- A sound call rule is sound on programs without indexes. -/
theorem CallRule.Sound.indexFree {rule : CallRule} (h : rule.Sound) : rule.SoundIndexFree :=
  fun p hwt _ hex fuel => h p hwt hex fuel

/-! ## The witness holds no index -/

namespace Optimality

theorem project_indexFree : ∀ (fs : List Name) (e : Expr), (e.project fs).indexFree = e.indexFree
  | [], _ => rfl
  | f :: fs, e => (project_indexFree fs (.field e f)).trans rfl

theorem fieldsIndexFree_const {e : Expr} (he : e.indexFree = true) :
    ∀ F : List Name, fieldsIndexFree (F.map fun f => (f, e)) = true
  | [] => rfl
  | _ :: F => by simp [fieldsIndexFree, he, fieldsIndexFree_const he F]

theorem lit_indexFree (F : List Name) (v : Name) : ∀ b : Nat, (lit F v b).indexFree = true
  | 0 => rfl
  | b + 1 => by
    simp [lit, Expr.indexFree, fieldsIndexFree, fieldsIndexFree_const (lit_indexFree F v b)]

theorem vars_indexFree {τ : Ty} {init e : Expr} (hinit : init.indexFree = true)
    (he : e.indexFree = true) : ∀ xs : List Name, (vars τ init xs e).indexFree = true
  | [] => he
  | x :: xs => by simp [vars, Expr.indexFree, hinit, vars_indexFree hinit he xs]

/-- A shape's place with fields only holds no index. -/
theorem toPlace_indexFree (s : Shape) : s.toPlace.indexFree = true := by
  simp [Shape.toPlace, Place.indexFree, Projection.fieldName?]

theorem argsIndexFree_placeArgs : ∀ ss : List Shape, argsIndexFree (ss.map placeArg) = true
  | [] => rfl
  | s :: ss => by
    simp [placeArg, argsIndexFree, toPlace_indexFree, argsIndexFree_placeArgs ss]

/-- The witness's places hold no index: the place `p_b.v` it assigns, the
place `p_a.extra.v` it reads, and the places of its call's `inout` arguments
follow fields only. The probe `[0][…]` indexes a list literal, which is no
place. -/
theorem witness_indexFree (ss : List Shape) (a b : Nat) (extra : List Name) :
    (witness ss a b extra).IndexFree := by
  refine ⟨fun d hd => ?_, ?_⟩
  · simp only [witness, decls, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    simp [callee, body, probe, read, Expr.indexFree, exprsIndexFree, Place.indexFree,
      Projection.fieldName?, Expr.place?, project_indexFree]
  · exact vars_indexFree (lit_indexFree _ _ _)
      (by simp [theCall, Expr.indexFree, argsIndexFree_placeArgs]) _

end Optimality

end Stilt
