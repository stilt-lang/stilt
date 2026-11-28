import Stilt.Generics.Commute
import Stilt.Typing.Else

/-!
# Forms of a shape

What the typing rule `HasType.shaped` of `Stilt.Typing` asks of the meaning of a compound
assignment, of an integer literal at a float type and of a field read through an `Option`: the
expression that the form's parts build, which typing then checks as it checks any
(`Form.Shaped`). An instance of a generic body keeps each shape (`Form.Shaped.substTys`); what
only a written body's types decide is `Form.Known`, which `Program.FormsKnown` checks.
-/

namespace Stilt

/-- `let t₁: τ₁ = i₁` and the others around `body`, the temporaries bound in order. -/
def Expr.lets : List (Name × Ty × Expr) → Expr → Expr
  | [], body => body
  | (t, τ, i) :: ts, body => .letIn t τ i (Expr.lets ts body)

/-- The expression that reads the part of `b`'s value that a path reaches. -/
def Expr.readPath : Expr → List Projection → Expr
  | b, [] => b
  | b, .field f :: ps => Expr.readPath (.field b f) ps
  | b, .index i :: ps => Expr.readPath (.index b i) ps

/-- The expression that reads a place. -/
def Place.read (P : Place) : Expr := Expr.readPath (.var P.root) P.path

/-- Every index of the path is one of the variables `ts`. -/
def Projection.IndexedBy (ts : List Name) (q : Projection) : Prop :=
  (∃ f, q = .field f) ∨ ∃ t ∈ ts, q = .index (.var t)

/-- `place op= e` as it runs (values.compound-assignment-order): the place's index expressions,
and a map's key, are each evaluated once, in order, into the temporaries `ts`, whose variables
are the place's indexes; then `e`, into `v`; then the place is read, `op` applied to its value
and `e`'s, and the result written back. -/
inductive Expr.Compound : Expr → Prop
  /-- A place of fields, tuple fields and list indexes, written back by `place = …`. -/
  | path {ts : List (Name × Ty × Expr)} {v : Name} {σ : Ty} {e : Expr} {o : Op} {P : Place} :
      (∀ q ∈ P.path, q.IndexedBy (ts.map (·.1))) →
      Expr.Compound (Expr.lets ts (.letIn v σ e (.assign P (.op o [P.read, .var v]))))
  /-- An element of the map at such a place, at the key `k`: it is read as `m[k]` reads it, so
  a map without a default panics with `missing-key` only after `e` has been evaluated, and the
  map with the result at `k` is written back. -/
  | entry {ts : List (Name × Ty × Expr)} {v k : Name} {σ : Ty} {e : Expr} {o : Op} {P : Place} :
      (∀ q ∈ P.path, q.IndexedBy (ts.map (·.1))) → k ∈ ts.map (·.1) →
      Expr.Compound (Expr.lets ts (.letIn v σ e (.assign P (.op (.map .insert)
        [P.read, .var k, .op o [.op (.map .index) [P.read, .var k], .var v]]))))

/-- The integers that a float type represents exactly: `m × 2^e` with `m` below `2^p`, for the
type's precision `p`, that are finite, below `2^128` for an `f32` and `2^1024` for an `f64`
(numbers.ieee-754). -/
def FloatTy.Represents : FloatTy → Nat → Prop
  | .f32, n => ∃ m e, n = m * 2 ^ e ∧ m < 2 ^ 24 ∧ e + 24 ≤ 128
  | .f64, n => ∃ m e, n = m * 2 ^ e ∧ m < 2 ^ 53 ∧ e + 53 ≤ 1024

/-- `Option<τ>`, the prelude's `Option` (`Decls.IsOption`) at `τ`. -/
abbrev Ty.option (τ : Ty) : Ty := .variant optionName [τ]

/-- `match e { Some(x) => r, None => None }` at the type `Option<U>`. -/
def Expr.throughOption (e : Expr) (U : Ty) (x : Name) (r : Expr) : Expr :=
  .match e U.option [⟨.variant optionName "Some" [.bind x], [x], none, r⟩,
    ⟨.variant optionName "None" [], [], none, .variant optionName [U] "None" []⟩]

/-- `e.f` on `e : Option<T>`, a read of the field `f` through the `Option` of the scrutinee
`e` (types.fields-through-option): `e` is evaluated once, a `None` gives `None`, and a `Some(x)`
reads the field of `x`, through `x` again when `x` is itself an `Option`. Typing gives the read
the type `Option<U>` (types.option-field-types): `x.f` itself when the field has that type,
so that the read adds no level of `Option`, a read through `x` when `x` is an `Option`, and
`Some(x.f)` when the field has the type `U`, which for a written body is no `Option`
(`Form.Known`). -/
inductive Expr.ThroughOption (f : Name) : Expr → Expr → Prop
  | field {e : Expr} {U : Ty} {x : Name} :
      Expr.ThroughOption f e (e.throughOption U x (.field (.var x) f))
  | some {e : Expr} {U : Ty} {x : Name} :
      Expr.ThroughOption f e (e.throughOption U x (.variant optionName [U] "Some" [.field (.var x) f]))
  | through {e m : Expr} {U : Ty} {x : Name} : Expr.ThroughOption f (.var x) m →
      Expr.ThroughOption f e (e.throughOption U x (.form .optionField m))

/-- A field of an update's record: a written one, named in `ws`, read from the temporary of `ts`
paired with it, or another, read from the temporary `b` that holds the base (records.update). -/
def Expr.UpdateField (ws ts : List Name) (b : Name) (fe : Name × Expr) : Prop :=
  (∃ t, (fe.1, t) ∈ ws.zip ts ∧ fe.2 = .var t) ∨ (fe.1 ∉ ws ∧ fe.2 = .field (.var b) fe.1)

/-- `{ ..base, f: e }` and `Name { ..base, f: e }` as they run (records.update-fields): `base` is
evaluated first, into `b`, then the fields written, in written order, into the temporaries `ts`;
the record of `base`'s type, `R` at `args`, is then built from them, each field written from its
temporary and every other copied from `b`. So the update's type is `base`'s, it adds and removes
no field, and with no field written it is a copy of `base` (records.update). The names written,
`ws`, are distinct and each is a field of the record built, read from its own temporary, so the
record's typing types each written value at its field's type: a field written twice, a field the
type lacks, or a value of another type has no such form (E0316, E0313, E0311). -/
inductive Expr.Update : Expr → Prop
  | mk {b R : Name} {args : List Ty} {base : Expr} {ts : List (Name × Ty × Expr)}
      {fields : List (Name × Expr)} {ws : List Name} :
      ws.Nodup → ws.length = ts.length →
      (∀ p ∈ ws.zip (ts.map (·.1)), (p.1, Expr.var p.2) ∈ fields) →
      (∀ fe ∈ fields, Expr.UpdateField ws (ts.map (·.1)) b fe) →
      Expr.Update (.letIn b (.record R args) base (Expr.lets ts (.record R args fields)))

/-- How an assignment through a map's element stores what it writes, `T w` writing `w`, and
reads the part it writes, `r` (std.map-element-places): at the element of the map at the place
`P`, at the key `k`, `w` is stored back with `insert`, and the part is read as `m[k]` reads it, so
it panics with `missing-key` when `k` is absent and the map has no default, and starts from the
default otherwise; a field or a list index after it is written into a `var` copy of the part
before it, which is then stored back. The indexes are the variables `ts`. -/
inductive Expr.ThroughEntry (ts : List Name) : (Expr → Expr) → Expr → Prop
  | entry {P : Place} {k : Name} :
      (∀ q ∈ P.path, q.IndexedBy ts) → k ∈ ts →
      Expr.ThroughEntry ts (fun w => .assign P (.op (.map .insert) [P.read, .var k, w]))
        (.op (.map .index) [P.read, .var k])
  | step {T : Expr → Expr} {r : Expr} {n : Name} {τ : Ty} {q : Projection} :
      Expr.ThroughEntry ts T r → q.IndexedBy ts →
      Expr.ThroughEntry ts (fun w => T (.varIn n τ r (.seq (.assign ⟨n, [q]⟩ w) (.var n))))
        (Expr.readPath r [q])

/-- `m[k].f = v` and `m[k].f op= e` as they run (std.map-element-places and
facts.map-element-places): the place's indexes and the map's key are evaluated once, in order,
into the temporaries `ts`, then the value, into `v`; the element is read as `m[k]` reads it, the
part changed in a copy, and the copy stored back with `insert`. So the assignment adds `panic` as
the read of `m[k]` does, which `without panic` counts as indexing, and `alloc`, as the `insert`
that stores it back does. -/
inductive Expr.ThroughElement : Expr → Prop
  | assign {ts : List (Name × Ty × Expr)} {T : Expr → Expr} {r : Expr} {v : Name} {σ : Ty}
      {e : Expr} :
      Expr.ThroughEntry (ts.map (·.1)) T r →
      Expr.ThroughElement (Expr.lets ts (.letIn v σ e (T (.var v))))
  | compound {ts : List (Name × Ty × Expr)} {T : Expr → Expr} {r : Expr} {v : Name} {σ : Ty}
      {e : Expr} {o : Op} :
      Expr.ThroughEntry (ts.map (·.1)) T r →
      Expr.ThroughElement (Expr.lets ts (.letIn v σ e (T (.op o [r, .var v]))))

/-- The meaning that each form typed by `HasType.shaped` must have. A compound assignment is
`Expr.Compound`. An integer literal at a float type is the float literal of its value, which
the type must represent exactly, so `9007199254740993` can't be an `f64`
(numbers.integer-literals); a negative one is that literal negated
(numbers.negative-literals). A record update is `Expr.Update`, and an assignment through a map's
element `Expr.ThroughElement`.

`v[i]` on a `View<List<U>>` (expressions.indexing and views.functions-of-views) is the index of
the view's `copy`, which reads the element `i` of the viewed part and panics with `bounds` as
`xs[i]` does: in copies a view is its part, and with windows `copy` reads the part through the
window. The `copy` holds the view inline in the Reference, where the calculus counts the
allocation of a `copy`, so `without alloc` rejects an index of a view that the Reference
accepts. -/
def Form.Shaped : Form → Expr → Prop
  | .compound, m => m.Compound
  | .intFloat, m => ∃ k n, m = .op (.float k n false 0) [] ∧ k.Represents n
  | .optionField, m => ∃ f e, m.ThroughOption f e
  | .update, m => m.Update
  | .element, m => m.ThroughElement
  | .viewIndex, m => ∃ v i, m = .index (.op .copy [v]) i
  | _, _ => False

/-- What a form of a written body, before any instance replaces its type parameters, asks of
its parts: a read through an `Option` adds a level of `Option` only at a field whose type,
as the read's own types give it, is no `Option` (types.option-field-types). So inside a
function generic in `T`, a field of type `T` isn't an `Option`, even where a caller instantiates
`T` with one (types.option-field-known). -/
def Form.Known : Form → Expr → Prop
  | .optionField, .match _ _ (⟨_, _, _, .variant _ [U] "Some" _⟩ :: _) => ∀ V : Ty, U ≠ V.option
  | _, _ => True

theorem Expr.lets_substTys (s : TySubst) (b : Expr) : ∀ ts : List (Name × Ty × Expr),
    (Expr.lets ts b).substTys s =
      Expr.lets (ts.map fun t => (t.1, t.2.1.substTys s, t.2.2.substTys s)) (b.substTys s)
  | [] => rfl
  | (t, τ, i) :: ts => by
    simp only [Expr.lets, Expr.substTys, List.map_cons]
    rw [Expr.lets_substTys s b ts]

theorem Expr.readPath_substTys (s : TySubst) (ts : List Name) : ∀ (ps : List Projection) (b : Expr),
    (∀ q ∈ ps, q.IndexedBy ts) → (Expr.readPath b ps).substTys s = Expr.readPath (b.substTys s) ps
  | [], _, _ => rfl
  | .field f :: ps, b, h => by
    rw [Expr.readPath, Expr.readPath_substTys s ts ps _ fun q hq => h q (.tail _ hq)]; rfl
  | .index i :: ps, b, h => by
    rw [Expr.readPath, Expr.readPath_substTys s ts ps _ fun q hq => h q (.tail _ hq)]
    rcases h _ (.head _) with ⟨_, hf⟩ | ⟨t, _, ht⟩
    · cases hf
    · cases ht; rfl

theorem substPathTys_indexed (s : TySubst) (ts : List Name) : ∀ ps : List Projection,
    (∀ q ∈ ps, q.IndexedBy ts) → substPathTys s ps = ps
  | [], _ => rfl
  | .field f :: ps, h => by
    rw [substPathTys, substPathTys_indexed s ts ps fun q hq => h q (.tail _ hq)]
  | .index i :: ps, h => by
    rw [substPathTys, substPathTys_indexed s ts ps fun q hq => h q (.tail _ hq)]
    rcases h _ (.head _) with ⟨_, hf⟩ | ⟨t, _, ht⟩
    · cases hf
    · cases ht; rfl

private theorem names_map (s : TySubst) (ts : List (Name × Ty × Expr)) :
    (ts.map fun t => (t.1, t.2.1.substTys s, t.2.2.substTys s)).map (·.1) = ts.map (·.1) := by
  simp [List.map_map, Function.comp_def]

theorem Expr.Compound.substTys (s : TySubst) {m : Expr} (h : m.Compound) :
    (m.substTys s).Compound := by
  cases h with
  | @path ts v σ e o P h =>
    obtain ⟨x, path⟩ := P
    have hr := Expr.readPath_substTys s _ path (.var x) h
    have hp := substPathTys_indexed s _ path h
    rw [Expr.lets_substTys]
    simp only [Expr.substTys, substExprTys, Place.read] at hr ⊢
    rw [hp, hr]
    exact .path (by rw [names_map]; exact h)
  | @entry ts v k σ e o P h hk =>
    obtain ⟨x, path⟩ := P
    have hr := Expr.readPath_substTys s _ path (.var x) h
    have hp := substPathTys_indexed s _ path h
    rw [Expr.lets_substTys]
    simp only [Expr.substTys, substExprTys, Place.read] at hr ⊢
    rw [hp, hr]
    exact .entry (by rw [names_map]; exact h) (by rw [names_map]; exact hk)

theorem Expr.ThroughOption.substTys (s : TySubst) {f : Name} :
    ∀ {e m : Expr}, m.ThroughOption f e → (m.substTys s).ThroughOption f (e.substTys s)
  | _, _, .field => .field
  | _, _, .some => .some
  | _, _, .through h => .through (h.substTys s)

theorem mem_substFieldTys (s : TySubst) : ∀ {fields : List (Name × Expr)} {fe : Name × Expr},
    fe ∈ substFieldTys s fields → ∃ g ∈ fields, fe = (g.1, g.2.substTys s)
  | (f, e) :: fields, fe, h => by
    simp only [substFieldTys, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨(f, e), .head _, h⟩
    · obtain ⟨g, hg, he⟩ := mem_substFieldTys s h
      exact ⟨g, .tail _ hg, he⟩

theorem subst_mem_substFieldTys (s : TySubst) : ∀ {fields : List (Name × Expr)} {g : Name × Expr},
    g ∈ fields → (g.1, g.2.substTys s) ∈ substFieldTys s fields
  | (f, e) :: fields, g, h => by
    simp only [substFieldTys, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact .inl rfl
    · exact .inr (subst_mem_substFieldTys s h)

theorem Expr.Update.substTys (s : TySubst) {m : Expr} (h : m.Update) : (m.substTys s).Update := by
  cases h with
  | @mk b R args base ts fields ws hn hl hw hf =>
    simp only [Expr.substTys]
    rw [Expr.lets_substTys]
    simp only [Expr.substTys]
    refine .mk hn (by simpa using hl) (fun p hp => ?_) (fun fe hfe => ?_)
    · rw [names_map] at hp
      have := subst_mem_substFieldTys s (hw p hp)
      simpa [Expr.substTys] using this
    · obtain ⟨⟨f, e⟩, hg, rfl⟩ := mem_substFieldTys s hfe
      rw [names_map]
      rcases hf (f, e) hg with ⟨t, ht, he⟩ | ⟨hnot, he⟩
      · exact .inl ⟨t, ht, by simp only at he ⊢; rw [he]; rfl⟩
      · exact .inr ⟨hnot, by simp only at he ⊢; rw [he]; rfl⟩

theorem Expr.ThroughEntry.substTys (s : TySubst) {ts : List Name} :
    ∀ {T : Expr → Expr} {r : Expr}, Expr.ThroughEntry ts T r →
      ∃ T' : Expr → Expr, Expr.ThroughEntry ts T' (r.substTys s) ∧
        ∀ w, (T w).substTys s = T' (w.substTys s)
  | _, _, @entry _ P k hP hk => by
    obtain ⟨x, path⟩ := P
    have hr := Expr.readPath_substTys s ts path (.var x) hP
    have hp := substPathTys_indexed s ts path hP
    refine ⟨fun w => .assign ⟨x, path⟩ (.op (.map .insert) [Place.read ⟨x, path⟩, .var k, w]),
      ?_, fun w => ?_⟩
    · have hi : (Expr.op (.map .index) [Place.read ⟨x, path⟩, .var k]).substTys s =
          .op (.map .index) [Place.read ⟨x, path⟩, .var k] := by
        simp only [Expr.substTys, substExprTys, Place.read] at hr ⊢
        rw [hr]; rfl
      rw [hi]; exact .entry hP hk
    · simp only [Expr.substTys, substExprTys, Place.read] at hr ⊢
      rw [hp, hr]; try rfl
  | _, _, @step _ T r n τ q hT hq => by
    obtain ⟨T', hT', hw⟩ := hT.substTys s
    have hp := substPathTys_indexed s ts [q] fun q' hq' => by
      simp only [List.mem_singleton] at hq'; exact hq' ▸ hq
    have hr := Expr.readPath_substTys s ts [q] r fun q' hq' => by
      simp only [List.mem_singleton] at hq'; exact hq' ▸ hq
    refine ⟨fun w => T' (.varIn n (τ.substTys s) (r.substTys s) (.seq (.assign ⟨n, [q]⟩ w) (.var n))),
      ?_, fun w => ?_⟩
    · rw [hr]; exact .step hT' hq
    · rw [hw]; simp only [Expr.substTys]; rw [hp]

theorem Expr.ThroughElement.substTys (s : TySubst) {m : Expr} (h : m.ThroughElement) :
    (m.substTys s).ThroughElement := by
  cases h with
  | @assign ts T r v σ e hT =>
    obtain ⟨T', hT', hw⟩ := hT.substTys s
    rw [Expr.lets_substTys]
    simp only [Expr.substTys]
    rw [hw]
    exact .assign (by rw [names_map]; exact hT')
  | @compound ts T r v σ e o hT =>
    obtain ⟨T', hT', hw⟩ := hT.substTys s
    rw [Expr.lets_substTys]
    simp only [Expr.substTys]
    rw [hw]
    simp only [Expr.substTys, substExprTys]
    exact .compound (by rw [names_map]; exact hT')

theorem Form.Shaped.substTys (s : TySubst) : ∀ {k : Form} {m : Expr},
    k.Shaped m → k.Shaped (m.substTys s)
  | .compound, _, h => Expr.Compound.substTys s h
  | .intFloat, _, ⟨k, n, hm, hn⟩ => ⟨k, n, by rw [hm]; rfl, hn⟩
  | .optionField, _, ⟨f, e, h⟩ => ⟨f, e.substTys s, h.substTys s⟩
  | .update, _, h => Expr.Update.substTys s h
  | .element, _, h => Expr.ThroughElement.substTys s h
  | .viewIndex, _, ⟨v, i, h⟩ => ⟨v.substTys s, i.substTys s, by rw [h]; rfl⟩

end Stilt
