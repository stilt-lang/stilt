import Stilt.WellTyped
import Stilt.Semantics

/-!
# Generics and traits

A generic function whose bound gives it a trait's method, run in both models
of memory at two types, and the typing that checks its body once, with its type
parameter rigid and its bound all it knows of it (traits.bounds,
traits.unsatisfied-bounds, traits.method-resolution, traits.qualified-calls and
types.no-type-arguments). Each program raises the value it shows, as in
`Stilt.Examples`.
-/

namespace Stilt.Examples.Generics

/-- `trait Size { fn size(self) -> i64 }`. -/
private def size : TraitDecl := ⟨"Size", [("size", .fn [(.let, .param selfParam)] .i64 Row.pure)]⟩

/-- `type Point = { x: i64, y: i64 }`. -/
private def point : RecordDecl := ⟨"Point", [("x", .i64), ("y", .i64)]⟩

/-- A method `size` of a trait impl, whose receiver has the type `τ`. -/
private def sizeFn (τ : Ty) (body : Expr) : FnDecl :=
  ⟨"size", [], [], [⟨.let, selfName, τ, none⟩], .i64, Row.pure, body, {}⟩

/-- `impl Size for i64 { fn size(self) -> i64 { self } }`. -/
private def sizeI64 : TraitImpl := ⟨"Size", .int .i64, [sizeFn .i64 (.var selfName)]⟩

/-- `impl Size for Point { fn size(self) -> i64 { self.x + self.y } }`. -/
private def sizePoint : TraitImpl :=
  ⟨"Size", .record "Point", [sizeFn (.record "Point")
    (.op (.arith .add .i64) [.field (.var selfName) "x", .field (.var selfName) "y"])]⟩

/-- `e.size()` on a value of type `τ`, which calls `Size.size` at `τ`. -/
private def sizeOf (τ : Ty) (e : Expr) (result : Ty :=
  .i64) : Expr := .call (.method "Size" "size" τ) [.value e] result

/-- `fn twice<T: Size>(v: T) -> i64 { v.size() + v.size() }`. The calls go
through the bound (traits.method-resolution). -/
private def twice : FnDecl :=
  ⟨"twice", [⟨"T", ["Size"]⟩], [], [⟨.let, "v", .param "T", none⟩], .i64, Row.pure,
    .op (.arith .add .i64) [sizeOf (.param "T") (.var "v"), sizeOf (.param "T") (.var "v")], {}⟩

private def decls : Decls := ⟨[point], [], [twice], [], [size], [sizeI64, sizePoint], []⟩

/-- A program whose `main` raises an `i64`. -/
private def program (main : Expr) : Program := ⟨decls, main, ⟨false, some .i64, [], [], none⟩, {}⟩

/-- Both models give the same observation. -/
private def agree (p : Program) (o : Observation) : Prop :=
  (p.runCopy 64).observe = o ∧ (p.runInPlace 64).observe = o

/-- `twice(e)`, with `T` the type `τ` (types.no-type-arguments). -/
private def twiceOf (τ : Ty) (e : Expr) (result : Ty :=
  .i64) : Expr := .call (.fnRef "twice" [τ] []) [.value e] result

/-! ## Runs -/

/-- `twice(5)` takes `T` to be `i64`, whose `size` is the value itself. -/
example : agree (program (.raise (twiceOf .i64 (.int 5)))) (.raised (.int 10)) := ⟨rfl, rfl⟩

/-- `twice(Point { x: 1, y: 2 })` takes `T` to be `Point`. -/
example : agree (program (.raise (twiceOf (.record "Point")
    (.record "Point" [("x", .int 1), ("y", .int 2)])))) (.raised (.int 6)) := ⟨rfl, rfl⟩

/-- `Size.size(7)`, the qualified form, calls the impl for `i64`
(traits.qualified-calls). -/
example : agree (program (.raise (sizeOf .i64 (.int 7)))) (.raised (.int 7)) := ⟨rfl, rfl⟩

/-! ## Typing -/

private theorem param_closed (T : Name) : (Ty.param T).Closed := fun _ h => nomatch h

/-- `twice`'s body checks once, in its own scope, where `v.size()` is allowed
by the bound `T: Size` alone (traits.unsatisfied-bounds). -/
example : twice.WellTyped decls twice.scope := by
  have hT : (Ty.param "T").WellFormed twice.scope := by
    refine ⟨fun _ h => (nomatch h), fun T hT => ?_, fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
    simp only [Ty.params, List.mem_singleton] at hT
    simp [hT, FnDecl.scope, twice]
  have hsat : Satisfies decls twice.scope (.param "T") "Size" :=
    .inl ⟨⟨"T", ["Size"]⟩, by simp [FnDecl.scope, twice], rfl, by simp⟩
  have hm : HasType decls twice.scope (Ctx.params [] twice.params) ⟨Row.pure, false, false, .i64, false, false⟩
      (.method "Size" "size" (.param "T")) (.fn [(.let, .param "T")] .i64 Row.pure) :=
    .method (t := size) (m := "size") (σ := .fn [(.let, .param selfParam)] .i64 Row.pure) rfl rfl
      (param_closed _) hT hsat
  have hcall : HasType decls twice.scope (Ctx.params [] twice.params) ⟨Row.pure, false, false, .i64, false, false⟩
      (sizeOf (.param "T") (.var "v")) .i64 :=
    .call hm (.value (by decide) (.var rfl) (.refl _) .nil)
      ⟨Row.pure_within _, fun h => by simp at h, fun h => (nomatch h), rfl⟩
  exact ⟨.i64, .op .arith (.cons hcall (.refl _) (.cons hcall (.refl _) .nil)), .refl _⟩

/-- `twice(true)` has no type: `bool` has no impl of `Size`, so the bound is
unsatisfied (traits.unsatisfied-bounds). -/
example (s : RowScope) (Γ : Ctx) (fx : Effects) (τ : Ty) :
    ¬HasType decls s Γ fx (.fnRef "twice" [.bool] []) τ := by
  intro h
  cases h with
  | fnRef hd _ _ _ _ _ htys =>
    obtain rfl : twice = _ := Option.some.inj (Eq.trans rfl hd)
    cases htys with
    | cons hx _ =>
      rcases hx.2.2 "Size" (by simp) with ⟨_, _, h, _⟩ | ⟨_, hh, hi⟩
      · exact nomatch h
      · cases hh
        exact absurd hi (by decide)

/-- Without a bound, a body knows nothing of `T`: `fn bad<T>(v: T) -> i64 {
v.size() }` can't call `size` (traits.unsatisfied-bounds). -/
example : ¬Satisfies decls ⟨[], fun _ _ => False, fun _ _ => False, [⟨"T", []⟩]⟩ (.param "T") "Size" := by
  rintro (⟨p, hp, _, hB⟩ | ⟨_, hh, _⟩)
  · simp only [List.mem_singleton] at hp
    subst hp
    exact nomatch hB
  · exact nomatch hh

end Stilt.Examples.Generics
