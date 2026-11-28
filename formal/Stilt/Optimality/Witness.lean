import Stilt.Optimality.Fields

/-!
# The witness

For a list of shapes `ss` and two positions `a ≠ b` whose shapes overlap, a
program that a call rule accepting `ss` must accept, and on which copy-in,
copy-out and in-place mutation disagree. `h = ss[a]` and `d = ss[b]` have one
root, and `h`'s fields followed by `extra` are `d`'s.

```
fn witness(inout p0: T…, inout p1: T…, …) {
  p_b.v = 1
  let r: i64 = [0][p_a.extra.v]
}
var x: T_K = …   // once for each shape's root, every i64 field 0
witness(inout ss[0], inout ss[1], …)
```

Each argument is the place of its shape with fields only, so the call's
`inout` shapes are exactly `ss`, in order. The program has no loop, so E0404
can't reject it. In place, `p_a.extra.v` is `p_b.v`, which the body has just
set to 1, and indexing `[0]` with it panics. Under copy-in, copy-out, `p_a` is
a copy taken when the call started, the read sees 0, and the run returns `()`.
`main` returns `()`, as program.main requires, so the two runs differ by a
panic, which is observable with its kind (effects.panic-kinds).
-/

namespace Stilt

/-- The place with a shape's root and fields, and no index (modes.places). -/
def Shape.toPlace (s : Shape) : Place := ⟨s.root, s.fields.map .field⟩

namespace Optimality

variable (ss : List Shape)

/-- The names of the fields of `ss`, each once: the fields of the witness's
record types (declarations.records). -/
def fieldNames : List Name := distinct (ss.flatMap Shape.fields)

/-- A field name that no shape of `ss` uses: the `i64` field of every record
type of the witness (declarations.unique-names). -/
def leafName : Name := freshName (fieldNames ss)

/-- The most fields that a shape of the list has: the depth of its places
once modes.overlap has removed their indexes. -/
def depth : List Shape → Nat
  | [] => 0
  | s :: ss => max s.fields.length (depth ss)

/-- The type of the variables of `main`: the record type of the greatest
budget (declarations.records). -/
def rootTy : Ty := recTy (depth ss)

/-- The type of a shape's place, and of its parameter, which an `inout`
argument must match exactly (effects.inout-function-arguments). -/
def paramTy (s : Shape) : Ty := recTy (depth ss - s.fields.length)

/-- The callee's parameters: one `inout` parameter for each shape, named by its
position (declarations.parameters). -/
def params : List Param := ss.mapIdx fun i s => ⟨.inout, nameOf 'p' i, paramTy ss s, none⟩

/-- The `inout` argument of a shape: its place, with fields only (expressions.inout-arguments). -/
def placeArg (s : Shape) : Arg := .inout s.toPlace

/-- That argument once evaluated: it has no index to evaluate (values.index-reads). -/
def placePassed (s : Shape) : Passed := .place s.root (s.fields.map Step.field)

/-- `p_a.extra.v`: a read of fields (types.field-access). -/
def read (a : Nat) (extra : List Name) : Expr :=
  .field ((Expr.var (nameOf 'p' a)).project extra) (leafName ss)

/-- `[0][e]`: a one-element list indexed with `e`, which panics with the kind
`bounds` unless `e` is 0 (effects.panic-kinds; std.lists). -/
def probe (e : Expr) : Expr := .index (.list .i64 [.int 0]) e

/-- `p_b.v = 1; let r: i64 = [0][p_a.extra.v]`: an assignment to a place
(expressions.assignment), then the read, which the probe turns into a panic unless it
sees 0. The `let` makes the body's type `()` (values.let-and-var; expressions.block-value). -/
def body (a b : Nat) (extra : List Name) : Expr :=
  .seq (.assign ⟨nameOf 'p' b, [.field (leafName ss)]⟩ (.int 1))
    (.letIn "r" .i64 (probe (read ss a extra)) .unit)

/-- The witness's only function, `witness`, which returns `()`. It declares no
row variable and its row is pure (declarations.function-declarations; effects.rows). -/
def callee (a b : Nat) (extra : List Name) : FnDecl :=
  ⟨"witness", [], [], params ss, .unit, Row.pure, body ss a b extra, {}⟩

/-- `var x: τ = init` for each name, then `e` (values.let-and-var). -/
def vars (τ : Ty) (init : Expr) : List Name → Expr → Expr
  | [], e => e
  | x :: xs, e => .varIn x τ init (vars τ init xs e)

/-- `witness(inout ss[0], inout ss[1], …)`, each argument marked `inout`
(expressions.inout-arguments). -/
def theCall : Expr := .call (.fnRef "witness" [] []) (ss.map placeArg) .unit

/-- The literal that `main` gives each variable (expressions.struct-literal-fields). -/
def rootLit : Expr := lit (fieldNames ss) (leafName ss) (depth ss)

/-- The literal is a value, not the last use of a variable. -/
theorem rootLit_not_move (y : Name) : rootLit ss ≠ .move y := by
  unfold rootLit
  cases depth ss <;> simp [lit]

/-- `main`: a `var` for each shape's root, then the call (values.let-and-var). -/
def main : Expr := vars (rootTy ss) (rootLit ss) (ss.map Shape.root) (theCall ss)

/-- The witness's declarations: its record types and its function (declarations.records and declarations.function-declarations). -/
def decls (a b : Nat) (extra : List Name) : Decls :=
  ⟨recDecls (fieldNames ss) (leafName ss) (depth ss), [], [callee ss a b extra], [], [], [], [], []⟩

/-- The witness: `main` returns the call's result, `()`, and its row is pure. -/
def witness (a b : Nat) (extra : List Name) : Program :=
  ⟨decls ss a b extra, main ss, Row.pure, {}, {}⟩

/-- What the call binds: each parameter's name, with its place (values.inout-argument-order). -/
def bound : List (Name × Passed) := ss.mapIdx fun i s => (nameOf 'p' i, placePassed s)

theorem decls_fn? (a b : Nat) (extra : List Name) :
    (decls ss a b extra).fn? "witness" = some (callee ss a b extra) := by
  simp [Decls.fn?, decls, callee, Decls.fns_mk]

theorem decls_records (a b : Nat) (extra : List Name) :
    (decls ss a b extra).records = recDecls (fieldNames ss) (leafName ss) (depth ss) := rfl

/-- Two positions of `ss` whose shapes overlap as modes.overlap says, the
shallower one first: `ss[a]` and `ss[b]` have one root, and `ss[a]`'s fields
followed by `extra` are `ss[b]`'s. -/
structure Overlap (a b : Nat) (extra : List Name) : Prop where
  lt_a : a < ss.length
  lt_b : b < ss.length
  ne : a ≠ b
  root : ss[a].root = ss[b].root
  fields : ss[a].fields ++ extra = ss[b].fields

/-! ## Facts about the layout -/

variable {ss}

theorem length_le_depth {s : Shape} :
    ∀ {ss : List Shape}, s ∈ ss → s.fields.length ≤ depth ss
  | t :: ss, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (length_le_depth h) (Nat.le_max_right _ _)

theorem mem_fieldNames {s : Shape} {f : Name} (hs : s ∈ ss) (hf : f ∈ s.fields) :
    f ∈ fieldNames ss :=
  mem_distinct.2 (List.mem_flatMap.2 ⟨s, hs, hf⟩)

theorem nodup_fieldNames : (fieldNames ss).Nodup := nodup_distinct _

theorem leafName_not_mem : leafName ss ∉ fieldNames ss := freshName_not_mem _

theorem map_mapIdx {α β γ : Type} (g : β → γ) :
    ∀ (l : List α) (f : Nat → α → β), (l.mapIdx f).map g = l.mapIdx fun i a => g (f i a)
  | [], _ => rfl
  | a :: l, f => by simp [List.mapIdx_cons, map_mapIdx g l]

/-- A list whose entries are those of the shapes, each named by its position,
finds a position's entry by its name. -/
theorem lookup_named {β : Type} (g : Shape → β) {i : Nat} (hi : i < ss.length)
    {l : List (Name × β)}
    (hl : ∀ e, e ∈ l ↔ e ∈ ss.mapIdx fun j s => (nameOf 'p' j, g s)) :
    l.lookup (nameOf 'p' i) = some (g ss[i]) := by
  refine lookup_of_unique ((hl _).2 (List.mem_mapIdx.2 ⟨i, hi, rfl⟩)) fun b' hb' => ?_
  obtain ⟨j, hj, he⟩ := List.mem_mapIdx.1 ((hl _).1 hb')
  simp only [Prod.mk.injEq] at he
  obtain rfl := nameOf_inj he.1
  exact he.2.symm

/-- The parameters' names are their positions', so they are distinct. -/
theorem nodup_paramNames : ((params ss).map Param.name).Nodup := by
  rw [params, map_mapIdx, List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij he
  simp only [List.getElem_mapIdx] at he
  exact absurd (nameOf_inj he) (by omega)

theorem mapIdx_const {α β : Type} (g : α → β) :
    ∀ l : List α, (l.mapIdx fun _ a => g a) = l.map g
  | [] => rfl
  | a :: l => by simp [List.mapIdx_cons, mapIdx_const g l]

theorem map_sig_params : (params ss).map Param.sig = ss.map fun s => (.inout, paramTy ss s) := by
  rw [params, map_mapIdx]
  exact mapIdx_const (fun s => (Mode.inout, paramTy ss s)) ss

/-! ## Exclusivity -/

variable (rule : CallRule)

theorem pathExclusiveWith_fields (r : List Shape) :
    ∀ fs : List Name, pathExclusiveWith rule r (fs.map .field) = true
  | [] => rfl
  | _ :: fs => pathExclusiveWith_fields r fs

theorem argsExclusiveWith_placeArgs (r : List Shape) :
    ∀ ss : List Shape, argsExclusiveWith rule r (ss.map placeArg) = true
  | [] => rfl
  | s :: ss => by
    simp [placeArg, Shape.toPlace, argsExclusiveWith, pathExclusiveWith_fields,
      argsExclusiveWith_placeArgs r ss]

theorem filterMap_fieldName : ∀ fs : List Name,
    (fs.map Projection.field).filterMap Projection.fieldName? = fs
  | [] => rfl
  | f :: fs => by simp [Projection.fieldName?, filterMap_fieldName fs]

/-- A shape's place with fields only has that shape (modes.overlap). -/
theorem shape_toPlace (s : Shape) : s.toPlace.shape = s := by
  simp only [Shape.toPlace, Place.shape, filterMap_fieldName]

/-- The call's `inout` shapes are exactly `ss`, in order. -/
theorem inoutShapes_placeArgs : ∀ ss : List Shape, inoutShapes (ss.map placeArg) = ss
  | [] => rfl
  | s :: ss => by
    simp only [List.map_cons, placeArg, inoutShapes, inoutShapes_placeArgs ss, shape_toPlace]

theorem fieldsExclusiveWith_const {e : Expr} (r : List Shape) (he : e.exclusiveWith rule r = true) :
    ∀ F : List Name, fieldsExclusiveWith rule r (F.map fun f => (f, e)) = true
  | [] => rfl
  | _ :: F => by simp [fieldsExclusiveWith, he, fieldsExclusiveWith_const r he F]

theorem lit_exclusiveWith (F : List Name) (v : Name) (r : List Shape) :
    ∀ b : Nat, (lit F v b).exclusiveWith rule r = true
  | 0 => rfl
  | b + 1 => by
    simp [lit, Expr.exclusiveWith, fieldsExclusiveWith,
      fieldsExclusiveWith_const rule r (lit_exclusiveWith F v r b)]

theorem project_exclusiveWith (r : List Shape) :
    ∀ (fs : List Name) (e : Expr), (e.project fs).exclusiveWith rule r = e.exclusiveWith rule r
  | [], _ => rfl
  | f :: fs, e => (project_exclusiveWith r fs (.field e f)).trans rfl

theorem vars_exclusiveWith {τ : Ty} {init e : Expr} (hinit : init.exclusiveWith rule [] = true)
    (he : e.exclusiveWith rule [] = true) :
    ∀ xs : List Name, (vars τ init xs e).exclusiveWith rule [] = true
  | [] => he
  | x :: xs => by
    simp [vars, Expr.exclusiveWith, hinit, hide, vars_exclusiveWith hinit he xs]

/-- The witness obeys the law of exclusivity under every call rule that
accepts `ss`: its only call has the `inout` shapes `ss`, and it has no loop,
so E0404 has nothing to reject (modes.change-while-iterating). -/
theorem witness_exclusiveWith {a b : Nat} {extra : List Name} (h : rule ss = true) :
    (witness ss a b extra).ExclusiveWith rule := by
  refine ⟨fun d hd => ?_, ?_⟩
  · simp only [witness, decls, Decls.fns_mk, List.mem_singleton] at hd
    subst hd
    simp [callee, body, probe, read, Expr.exclusiveWith, exprsExclusiveWith, pathExclusiveWith,
      unread, project_exclusiveWith]
  · refine vars_exclusiveWith rule (lit_exclusiveWith rule _ _ _ _) ?_ _
    simp [theCall, Expr.exclusiveWith, argsExclusiveWith_placeArgs, inoutShapes_placeArgs,
      unread, h]

end Optimality

end Stilt
