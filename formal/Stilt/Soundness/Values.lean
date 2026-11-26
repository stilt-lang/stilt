import Stilt.Soundness.Compose
import Stilt.Soundness.Arguments
import Stilt.Values
import Stilt.Instances

/-!
# Values of run-time types

`Value.Typed D v σ`: the value `v` has the run-time type `σ`. A closure has the
type of its literal, read under the environment of the body that made it, with
its body well typed in the frame it captured. A function declared at the top
level has its declared type, read under the environment that its use composed.
The relation reads neither from a closure's annotations nor from a function
value's instantiation, which the evaluator keeps but never inspects: a use
instantiates them by `Row.substRows`, which keeps one `raise` label of a row
where the run-time type has them all.

A body's environment pairs each of its variables only with error types that
its signature allows (`REnv.Respects`). That is the invariant that effects.paired-row-variables and
effects.passing-to-paired-variables maintain: effects.one-error-type gives it for a concrete use, and effects.passing-to-paired-variables passes it from the enclosing function to a use that gives a variable a
row that holds the enclosing function's own.
-/

namespace Stilt

/-- An environment that keeps the promises of a scope: a variable that the
signature pairs with `E` raises only `E` (effects.paired-row-variables; effects.passing-to-paired-variables). The scope is
that of an instance, whose type parameters a call has instantiated
(types.no-type-arguments). -/
structure REnv.Respects (η : REnv) (scope : RowScope) : Prop where
  pairs : ∀ v E, scope.pairs v E → ∀ F ∈ η v, ¬ F.IsLabel → F.Fits (E.close η)
  passOn : ∀ v E, scope.passOn v E → ∀ F ∈ η v, ¬ F.IsLabel → F.Fits (E.close η)
  types : scope.types = []
  /-- No variable stands for a `resume`: the rows that instantiate one hold none. -/
  noResume : ∀ v a r, STy.resume a r ∉ η v

section

variable (D : Decls)

mutual

/-- The value `v` has the run-time type `σ`. A function value stands at every
type that its own fits (effects.function-values). -/
inductive Value.Typed : Value → STy → Prop
  /-- An integer has every integer type that holds it (numbers.numeric-types). -/
  | int {n : Int} {k : IntTy} : k.Contains n → Value.Typed (.int n) (.int k)
  | float {x : FloatVal} : Value.Typed (.float x) (.float x.type)
  | str {s : String} : Value.Typed (.str s) .str
  | bool {b : Bool} : Value.Typed (.bool b) .bool
  | unit : Value.Typed .unit .unit
  /-- A record of a type at run-time arguments, one for each of its type parameters, whose
  fields have their declared types at those arguments (declarations.type-parameters). -/
  | record {R : Name} {args : List STy} {r : RecordDecl} {fields : List (Name × Value)} :
      D.record? R = some r → args.length = r.typeParams.length →
      Fields.Typed fields r.fields (r.typeParams.zip args) →
      Value.Typed (.record R fields) (.record R args)
  /-- A variant of a type at run-time arguments, whose payload has its declared types at
  those arguments (declarations.type-parameters). -/
  | variant {T : Name} {args : List STy} {t : VariantDecl} {C : Name} {τs : List Ty}
      {payload : List Value} :
      D.variant? T = some t → args.length = t.typeParams.length → t.ctors.lookup C = some τs →
      Values.Typed payload τs (t.typeParams.zip args) →
      Value.Typed (.variant T C payload) (.variant T args)
  | list {σ : STy} {vs : List Value} :
      (∀ v ∈ vs, Value.Typed v σ) → Value.Typed (.list vs) (.list σ)
  | tuple {vs : List Value} {σs : List STy} :
      Elems.Typed vs σs → Value.Typed (.tuple vs) (.tuple σs)
  /-- A map whose keys have its key type, and whose values and default have its
  value type (std.maps). -/
  | map {es : List (Value × Value)} {d : Option Value} {κ σ : STy} :
      (∀ e ∈ es, Value.Typed e.1 κ) → (∀ e ∈ es, Value.Typed e.2 σ) →
      (∀ v, d = some v → Value.Typed v σ) → Value.Typed (.mapOf es d) (.map κ σ)
  /-- A set whose elements have its element type (std.sets). -/
  | set {ks : List Value} {κ : STy} :
      (∀ k ∈ ks, Value.Typed k κ) → Value.Typed (.setOf ks) (.set κ)
  /-- A closure that a body under `η` made from a literal of `scope`'s body, whose
  row holds the `resume` of the literal's. -/
  | closure {captured : List (Name × Value)} {ps : List Param} {result : Ty} {ρ : Row}
      {body : Expr} {σ : STy} {scope : RowScope} {Γ : Ctx} {η : REnv} {θ : RowSubst}
      {ps₀ : List Param} {result₀ : Ty} {ρ₀ : Row} {body₀ : Expr} {m : Bool} {τ : Ty} :
      ps = ps₀.map (Param.substRows θ) → body = body₀.substRows θ →
      (ps₀.map Param.name).Nodup → η.Respects scope →
      HasType D scope (Γ.freeze.params ps₀) ⟨ρ₀, m, false, result₀, false, false⟩ body₀ τ → Fits τ result₀ →
      Frame.Typed captured Γ η →
      ((Ty.fn (ps₀.map Param.sig) result₀ ρ₀).close η).Fits σ → ρ.resume = ρ₀.resume →
      Value.Typed (.closure captured ps result ρ body) σ
  /-- A function declared at the top level, with ground type arguments that
  meet its bounds, under an environment that its signature's pairs allow. -/
  | function {f : Name} {types : List Ty} {rows : List Row} {σ : STy} {d : FnDecl} {η : REnv} :
      D.fn? f = some d → (d.typeArgs types).Fits D d.scope d.scope.instantiated →
      η.Respects d.scope.instantiated → ((d.type.substTys (d.typeArgs types)).close η).Fits σ →
      Value.Typed (.function f types rows) σ
  /-- A handle on a cell of type `u`, whose values have the type `u` reads as with no row
  variable (shared.std-sync and `Stilt.World`). -/
  | handle {u : Ty} {k : Nat} {σ : STy} : (STy.shared u.sem).Fits σ → Value.Typed (.handle u k) σ

/-- A tuple's elements, with values of the run-time types at their positions
(declarations.tuples-and-unit). -/
inductive Elems.Typed : List Value → List STy → Prop
  | nil : Elems.Typed [] []
  | cons {v : Value} {σ : STy} {vs : List Value} {σs : List STy} :
      Value.Typed v σ → Elems.Typed vs σs → Elems.Typed (v :: vs) (σ :: σs)

/-- A frame whose variables hold values of their bindings' types (expressions.scope). -/
inductive Frame.Typed : List (Name × Value) → Ctx → REnv → Prop
  | nil {η : REnv} : Frame.Typed [] [] η
  | cons {x : Name} {v : Value} {b : Binding} {γ : List (Name × Value)} {Γ : Ctx} {η : REnv} :
      Value.Typed v (b.type.close η) → Frame.Typed γ Γ η →
      Frame.Typed ((x, v) :: γ) ((x, b) :: Γ) η

/-- A record's fields, in the order they are declared, with values of their
closed types, their type parameters the run-time arguments `π` (declarations.records,
declarations.type-parameters; effects.row-variables). -/
inductive Fields.Typed : List (Name × Value) → List (Name × Ty) → SParams → Prop
  | nil {π : SParams} : Fields.Typed [] [] π
  | cons {f : Name} {v : Value} {τ : Ty} {fields : List (Name × Value)}
      {declared : List (Name × Ty)} {π : SParams} :
      Value.Typed v (τ.semAt π) → Fields.Typed fields declared π →
      Fields.Typed ((f, v) :: fields) ((f, τ) :: declared) π

/-- A variant's payload, with values of its closed types, their type parameters the
run-time arguments `π` (declarations.variant-types, declarations.type-parameters;
effects.row-variables). -/
inductive Values.Typed : List Value → List Ty → SParams → Prop
  | nil {π : SParams} : Values.Typed [] [] π
  | cons {v : Value} {τ : Ty} {vs : List Value} {τs : List Ty} {π : SParams} :
      Value.Typed v (τ.semAt π) → Values.Typed vs τs π → Values.Typed (v :: vs) (τ :: τs) π

end

end

/-! ## Equivalent and larger types -/

/-- Only a function type fits a function type. -/
theorem STy.Fits.fn_fn {a c : STy} (h : a.Fits c) :
    ∀ {ps r R}, a = .fn ps r R → ∃ ps' r' R', c = .fn ps' r' R' := by
  induction h with
  | refl => intro ps r R ha; exact ⟨ps, r, R, ha⟩
  | eqv hab _ ih =>
    intro ps r R ha
    subst ha
    obtain ⟨_, _, _, rfl, -⟩ := hab.fn_inv
    exact ih rfl
  | grow _ _ ih => intro ps r R ha; cases ha; exact ih rfl
  | never => intro _ _ _ ha; cases ha

/-- Only a `Shared<T>` fits a `Shared<T>`. -/
theorem STy.Fits.shared_shared {a c : STy} (h : a.Fits c) : ∀ {b}, a = .shared b → ∃ b', c = .shared b' := by
  induction h with
  | refl => intro b ha; exact ⟨b, ha⟩
  | eqv hab _ ih =>
    intro b ha
    subst ha
    obtain ⟨_, rfl, -⟩ := hab.shared_inv
    exact ih rfl
  | grow _ _ _ => intro _ ha; cases ha
  | never => intro _ ha; cases ha

section

variable {D : Decls}

mutual

theorem Value.Typed.eqv : ∀ {v : Value} {a b : STy}, Value.Typed D v a → a.Eqv b → Value.Typed D v b
  | _, _, _, .int hk, h => by cases h; exact .int hk
  | _, _, _, .float, h => by cases h; exact .float
  | _, _, _, .str, h => by cases h; exact .str
  | _, _, _, .bool, h => by cases h; exact .bool
  | _, _, _, .unit, h => by cases h; exact .unit
  | _, _, _, .record hr hl hf, h => by
    cases h with
    | record _ hab =>
      exact .record hr (hab.length ▸ hl) (Fields.Typed.eqv hf (SParams.Eqv.zip _ hab))
  | _, _, _, .variant ht hl hc hp, h => by
    cases h with
    | variant _ hab =>
      exact .variant ht (hab.length ▸ hl) hc (Values.Typed.eqv hp (SParams.Eqv.zip _ hab))
  | _, _, _, .list hvs, h => by
    obtain ⟨b', rfl, hab⟩ := h.list_inv
    exact .list fun v hv => Value.Typed.eqv (hvs v hv) hab
  | _, _, _, .tuple hvs, h => by
    obtain ⟨bs, rfl, hab⟩ := h.tuple_inv
    exact .tuple (Elems.Typed.eqv hvs hab)
  | _, _, _, .map hk hv hd, h => by
    obtain ⟨_, _, rfl, ha, hb⟩ := h.map_inv
    exact .map (fun e he => Value.Typed.eqv (hk e he) ha) (fun e he => Value.Typed.eqv (hv e he) hb)
      fun v hv' => Value.Typed.eqv (hd v hv') hb
  | _, _, _, .set hks, h => by
    obtain ⟨_, rfl, hab⟩ := h.set_inv
    exact .set fun k hk => Value.Typed.eqv (hks k hk) hab
  | _, _, _, .closure hps hb hnd hη hty hfit hcap hσ hρ, h =>
    .closure hps hb hnd hη hty hfit hcap (hσ.trans (.of_eqv h)) hρ
  | _, _, _, .function hd hδ hη hσ, h => .function hd hδ hη (hσ.trans (.of_eqv h))
  | _, _, _, .handle hσ, h => .handle (hσ.trans (.of_eqv h))

theorem Elems.Typed.eqv : ∀ {vs : List Value} {as bs : List STy}, Elems.Typed D vs as →
    STysEqv as bs → Elems.Typed D vs bs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons hv hvs, .cons h hs => .cons (Value.Typed.eqv hv h) (Elems.Typed.eqv hvs hs)

theorem Fields.Typed.eqv : ∀ {fs : List (Name × Value)} {declared : List (Name × Ty)}
    {π π' : SParams}, Fields.Typed D fs declared π → π.Eqv π' → Fields.Typed D fs declared π'
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons (τ := τ) hv hfs, h =>
    .cons (Value.Typed.eqv hv (Ty.semAt_eqv h τ)) (Fields.Typed.eqv hfs h)

theorem Values.Typed.eqv : ∀ {vs : List Value} {τs : List Ty} {π π' : SParams},
    Values.Typed D vs τs π → π.Eqv π' → Values.Typed D vs τs π'
  | _, _, _, _, .nil, _ => .nil
  | _, _, _, _, .cons (τ := τ) hv hvs, h =>
    .cons (Value.Typed.eqv hv (Ty.semAt_eqv h τ)) (Values.Typed.eqv hvs h)

end

/-- A value of a type has every type it fits. -/
theorem Value.Typed.fits {v : Value} {a b : STy} (hv : Value.Typed D v a) (h : a.Fits b) :
    Value.Typed D v b := by
  induction h with
  | refl => exact hv
  | eqv hab _ ih => exact ih (hv.eqv hab)
  | grow hc _ ih =>
    refine ih ?_
    cases hv with
    | closure hps hb hnd hη hty hfit hcap hσ hρ =>
      exact .closure hps hb hnd hη hty hfit hcap (hσ.trans (.of_covers hc)) hρ
    | function hd hδ hη hσ => exact .function hd hδ hη (hσ.trans (.of_covers hc))
    | handle hσ =>
      obtain ⟨_, h⟩ := hσ.shared_shared rfl
      exact nomatch h
  | never =>
    cases hv with
    | closure _ _ _ _ _ _ _ hσ _ => exact absurd (hσ.fn_fn rfl) (by simp)
    | function _ _ _ hσ =>
      obtain ⟨_, _, _, h⟩ := hσ.fn_fn rfl
      exact nomatch h
    | handle hσ =>
      obtain ⟨_, h⟩ := hσ.shared_shared rfl
      exact nomatch h

/-- No value has the type of a label. -/
theorem Value.Typed.not_label {v : Value} {a : STy} (hv : Value.Typed D v a) : ¬ a.IsLabel := by
  cases hv with
  | closure _ _ _ _ _ _ _ hσ _ =>
    obtain ⟨_, _, _, rfl⟩ := hσ.fn_fn rfl
    exact id
  | function _ _ _ hσ =>
    obtain ⟨_, _, _, rfl⟩ := hσ.fn_fn rfl
    exact id
  | handle hσ =>
    obtain ⟨_, rfl⟩ := hσ.shared_shared rfl
    exact id
  | _ => exact id

/-- Parameters that correspond: the same modes, which are part of a function
type (declarations.function-types), and the same values, both ways. -/
inductive ParamsMatch (D : Decls) : List (Mode × STy) → List (Mode × STy) → Prop
  | nil : ParamsMatch D [] []
  | cons {m : Mode} {a b : STy} {ps ps' : List (Mode × STy)} :
      (∀ v, Value.Typed D v a → Value.Typed D v b) → (∀ v, Value.Typed D v b → Value.Typed D v a) →
      ParamsMatch D ps ps' → ParamsMatch D ((m, a) :: ps) ((m, b) :: ps')

/-! ## Values of each form of type -/

theorem Value.Typed.int_inv {v : Value} {k : IntTy} (hv : Value.Typed D v (.int k)) :
    ∃ n, v = .int n ∧ k.Contains n := by
  cases hv with
  | int hk => exact ⟨_, rfl, hk⟩
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

theorem Value.Typed.float_inv {v : Value} {k : FloatTy} (hv : Value.Typed D v (.float k)) :
    ∃ x, v = .float x ∧ x.type = k := by
  cases hv with
  | float => exact ⟨_, rfl, rfl⟩
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

theorem Value.Typed.str_inv {v : Value} (hv : Value.Typed D v .str) : ∃ s, v = .str s := by
  cases hv with
  | str => exact ⟨_, rfl⟩
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

theorem Value.Typed.i64_inv {v : Value} (hv : Value.Typed D v .i64) : ∃ k, v = .int k := by
  cases hv with
  | int => exact ⟨_, rfl⟩
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

theorem Value.Typed.bool_inv {v : Value} (hv : Value.Typed D v .bool) : ∃ b, v = .bool b := by
  cases hv with
  | bool => exact ⟨_, rfl⟩
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

/-- Only `()` has the type `()`: a function value has a function type, which
fits no other. -/
theorem Value.Typed.unit_inv {v : Value} (hv : Value.Typed D v .unit) : v = .unit := by
  cases hv with
  | unit => rfl
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

theorem Value.Typed.record_inv {v : Value} {R : Name} {args : List STy}
    (hv : Value.Typed D v (.record R args)) :
    ∃ r fields, v = .record R fields ∧ D.record? R = some r ∧ args.length = r.typeParams.length ∧
      Fields.Typed D fields r.fields (r.typeParams.zip args) := by
  cases hv with
  | record hr hl hfs => exact ⟨_, _, rfl, hr, hl, hfs⟩
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

theorem Value.Typed.variant_inv {v : Value} {T : Name} {args : List STy}
    (hv : Value.Typed D v (.variant T args)) :
    ∃ t C τs payload, v = .variant T C payload ∧ D.variant? T = some t ∧
      args.length = t.typeParams.length ∧ t.ctors.lookup C = some τs ∧
      Values.Typed D payload τs (t.typeParams.zip args) := by
  cases hv with
  | variant ht hl hc hp => exact ⟨_, _, _, _, rfl, ht, hl, hc, hp⟩
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

theorem Value.Typed.list_inv {v : Value} {σ : STy} (hv : Value.Typed D v (.list σ)) :
    ∃ vs, v = .list vs ∧ ∀ u ∈ vs, Value.Typed D u σ := by
  cases hv with
  | list h => exact ⟨_, rfl, h⟩
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

theorem Value.Typed.tuple_inv {v : Value} {σs : List STy} (hv : Value.Typed D v (.tuple σs)) :
    ∃ vs, v = .tuple vs ∧ Elems.Typed D vs σs := by
  cases hv with
  | tuple h => exact ⟨_, rfl, h⟩
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

theorem Value.Typed.map_inv {v : Value} {κ σ : STy} (hv : Value.Typed D v (.map κ σ)) :
    ∃ es d, v = .mapOf es d ∧ (∀ e ∈ es, Value.Typed D e.1 κ) ∧
      (∀ e ∈ es, Value.Typed D e.2 σ) ∧ ∀ u, d = some u → Value.Typed D u σ := by
  cases hv with
  | map hk hv hd => exact ⟨_, _, rfl, hk, hv, hd⟩
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

theorem Value.Typed.set_inv {v : Value} {κ : STy} (hv : Value.Typed D v (.set κ)) :
    ∃ ks, v = .setOf ks ∧ ∀ k ∈ ks, Value.Typed D k κ := by
  cases hv with
  | set h => exact ⟨_, rfl, h⟩
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

theorem Elems.Typed.forall₂ : ∀ {vs : List Value} {σs : List STy}, Elems.Typed D vs σs →
    Forall₂ (Value.Typed D) vs σs
  | _, _, .nil => .nil
  | _, _, .cons hv hvs => .cons hv hvs.forall₂

theorem Elems.Typed.of_forall₂ : ∀ {vs : List Value} {σs : List STy},
    Forall₂ (Value.Typed D) vs σs → Elems.Typed D vs σs
  | _, _, .nil => .nil
  | _, _, .cons hv hvs => .cons hv (Elems.Typed.of_forall₂ hvs)

theorem Value.Typed.not_never {v : Value} (hv : Value.Typed D v .never) : False := by
  cases hv with
  | closure _ _ _ _ _ _ _ h _ => exact absurd (h.fn_fn rfl) (by simp)
  | function _ _ _ h => obtain ⟨_, _, _, h⟩ := h.fn_fn rfl; exact nomatch h
  | handle h => obtain ⟨_, h⟩ := h.shared_shared rfl; exact nomatch h

/-- What a value of one function type may stand for in another that it fits:
the parameters correspond both ways, with the same modes, the result goes
forward, and so does each error type raised (effects.function-values). -/
structure FnFits (D : Decls) (ps₀ : List (Mode × STy)) (r₀ : STy) (R₀ : List STy)
    (ps : List (Mode × STy)) (r : STy) (R : List STy) : Prop where
  params : ParamsMatch D ps₀ ps
  result : ∀ v, Value.Typed D v r₀ → Value.Typed D v r
  raises : ∀ e, ∀ F ∈ R₀, Value.Typed D e F → ∃ F' ∈ R, Value.Typed D e F'
  /-- And each label: every effect it may perform, and its `resume`. -/
  labels : ∀ x ∈ R₀, x.IsLabel → x ∈ R

theorem SParamsEqv.paramsMatch :
    ∀ {ps ps' : List (Mode × STy)}, SParamsEqv ps ps' → ParamsMatch D ps ps'
  | _, _, .nil => .nil
  | _, _, .cons h hs => .cons (fun _ hv => hv.eqv h) (fun _ hv => hv.eqv h.symm) hs.paramsMatch

theorem ParamsMatch.trans :
    ∀ {ps₀ ps₁ ps : List (Mode × STy)}, ParamsMatch D ps₀ ps₁ → ParamsMatch D ps₁ ps →
      ParamsMatch D ps₀ ps
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons f₁ b₁ h₁, .cons f₂ b₂ h₂ =>
    .cons (fun v hv => f₂ v (f₁ v hv)) (fun v hv => b₁ v (b₂ v hv)) (ParamsMatch.trans h₁ h₂)

theorem Covers.typed {R R' : List STy} (h : Covers R R') :
    ∀ e, ∀ F ∈ R, Value.Typed D e F → ∃ F' ∈ R', Value.Typed D e F' := by
  intro e F hF he
  obtain ⟨F', hF', hFF'⟩ := (h.forall F hF).exists
  exact ⟨F', hF', he.eqv hFF'⟩

theorem FnFits.trans {ps₀ ps₁ ps : List (Mode × STy)} {r₀ r₁ r : STy} {R₀ R₁ R : List STy}
    (h₁ : FnFits D ps₀ r₀ R₀ ps₁ r₁ R₁) (h₂ : FnFits D ps₁ r₁ R₁ ps r R) :
    FnFits D ps₀ r₀ R₀ ps r R where
  params := h₁.params.trans h₂.params
  result := fun v hv => h₂.result v (h₁.result v hv)
  raises := fun e F hF he =>
    let ⟨F₁, hF₁, he₁⟩ := h₁.raises e F hF he
    h₂.raises e F₁ hF₁ he₁
  labels := fun x hx hl => h₂.labels x (h₁.labels x hx hl) hl

theorem FnFits.refl (ps : List (Mode × STy)) (r : STy) (R : List STy) : FnFits D ps r R ps r R where
  params := (SParamsEqv.refl ps).paramsMatch
  result := fun _ h => h
  raises := fun _ F hF he => ⟨F, hF, he⟩
  labels := fun _ hx _ => hx

/-- A function type fits only function types, and through `FnFits`. -/
theorem STy.Fits.fn_inv {a c : STy} (h : a.Fits c) :
    ∀ {ps₀ r₀ R₀}, a = .fn ps₀ r₀ R₀ →
      ∃ ps r R, c = .fn ps r R ∧ FnFits D ps₀ r₀ R₀ ps r R := by
  induction h with
  | refl => intro ps₀ r₀ R₀ ha; exact ⟨ps₀, r₀, R₀, ha, .refl _ _ _⟩
  | eqv hab _ ih =>
    intro ps₀ r₀ R₀ ha
    subst ha
    obtain ⟨ps₁, r₁, R₁, rfl, hp, hr, hc, _⟩ := hab.fn_inv
    obtain ⟨ps, r, R, rfl, hf⟩ := ih rfl
    exact ⟨ps, r, R, rfl,
      FnFits.trans ⟨hp.paramsMatch, fun _ hv => hv.eqv hr, hc.typed, fun _ hx => hc.label hx⟩ hf⟩
  | grow hc _ ih =>
    intro ps₀ r₀ R₀ ha
    cases ha
    obtain ⟨ps, r, R, rfl, hf⟩ := ih rfl
    exact ⟨ps, r, R, rfl,
      FnFits.trans ⟨(SParamsEqv.refl _).paramsMatch, fun _ h => h, hc.typed,
        fun _ hx => hc.label hx⟩ hf⟩
  | never => intro _ _ _ ha; cases ha

end

end Stilt
