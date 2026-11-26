import Stilt.Declarations

/-!
# Traversals with a context

Two traversals of a body that carry a context from each expression to its
parts: `Expr.gather`, which collects what a function finds at each expression,
and `Expr.gate`, which keeps the marks `move x` that a context allows and reads
the others as variables. Both read the context of a part from `child k e n`:
the context `k` of the expression `e`, and the position `n` of the part in it,
in the order values.left-to-right evaluates the parts. The indexes of an `inout`
argument's place, and of an assigned place, take the context of the argument
or of the place.

`Stilt.Modes.Facts` gives the context of the modes, so that the facts of a
body's bindings and the marks its modes allow come from one reading of it.
-/

namespace Stilt

section

variable {κ β : Type} (child : κ → Expr → Nat → κ)

mutual

/-- What `visit` finds at `e` and at each of its parts, in the order of
evaluation, the parts with their contexts. -/
def Expr.gather (visit : κ → Expr → List β) (k : κ) (e : Expr) : List β :=
  visit k e ++
    match e with
    | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _ | .method _ _ _ => []
    | .record _ _ fields => gatherFields visit (child k e) 0 fields
    | .variant _ _ _ es | .list _ es | .op _ es | .view es => gatherExprs visit (child k e) 0 es
    | .field a _ | .closure _ _ _ a | .raise a | .try a | .loop a | .return a | .perform _ a =>
      a.gather visit (child k e 0)
    | .index a b | .letIn _ _ a b | .varIn _ _ a b | .seq a b | .for _ _ a b | .while a b
    | .tryCatch a _ _ b _ | .withH _ _ a b =>
      a.gather visit (child k e 0) ++ b.gather visit (child k e 1)
    | .call f args _ => f.gather visit (child k e 0) ++ gatherArgs visit (child k e) 1 args
    | .assign ⟨_, path⟩ v => gatherPath visit (child k e 0) path ++ v.gather visit (child k e 1)
    | .if c _ a b =>
      c.gather visit (child k e 0) ++ a.gather visit (child k e 1) ++ b.gather visit (child k e 2)
    | .match s _ arms => s.gather visit (child k e 0) ++ gatherArms visit (child k e) 1 arms
    | .held _ hs body =>
      gatherExprs visit (child k e) 0 hs ++ body.gather visit (child k e hs.length)

/-- What `visit` finds in a list of expressions, the `i`th at position `n + i`. -/
def gatherExprs (visit : κ → Expr → List β) (kf : Nat → κ) (n : Nat) :
    List Expr → List β
  | [] => []
  | e :: es => e.gather visit (kf n) ++ gatherExprs visit kf (n + 1) es

/-- What `visit` finds in the fields of a record literal. -/
def gatherFields (visit : κ → Expr → List β) (kf : Nat → κ) (n : Nat) :
    List (Name × Expr) → List β
  | [] => []
  | (_, e) :: fields => e.gather visit (kf n) ++ gatherFields visit kf (n + 1) fields

/-- What `visit` finds in a call's arguments. -/
def gatherArgs (visit : κ → Expr → List β) (kf : Nat → κ) (n : Nat) : List Arg → List β
  | [] => []
  | .value e :: args => e.gather visit (kf n) ++ gatherArgs visit kf (n + 1) args
  | .inout ⟨_, path⟩ :: args => gatherPath visit (kf n) path ++ gatherArgs visit kf (n + 1) args

/-- What `visit` finds in the indexes of a place, all in the context `k`. -/
def gatherPath (visit : κ → Expr → List β) (k : κ) : List Projection → List β
  | [] => []
  | .field _ :: path => gatherPath visit k path
  | .index i :: path => i.gather visit k ++ gatherPath visit k path

/-- What `visit` finds in the arms of a `match`. -/
def gatherArms (visit : κ → Expr → List β) (kf : Nat → κ) (n : Nat) : List Arm → List β
  | [] => []
  | ⟨_, _, body⟩ :: arms => body.gather visit (kf n) ++ gatherArms visit kf (n + 1) arms

end

variable (keep : κ → Name → Bool)

mutual

/-- `e` with each mark `move x` kept where its context allows it, and read as
the variable `x` elsewhere. -/
def Expr.gate (k : κ) (e : Expr) : Expr :=
  match e with
  | .var x => .var x
  | .move x => if keep k x then .move x else .var x
  | .int n => .int n
  | .bool b => .bool b
  | .unit => .unit
  | .break => .break
  | .continue => .continue
  | .fnRef f types rows => .fnRef f types rows
  | .method t m τ => .method t m τ
  | .record R τs fields => .record R τs (gateFields (child k e) 0 fields)
  | .variant T τs C es => .variant T τs C (gateExprs (child k e) 0 es)
  | .list τ es => .list τ (gateExprs (child k e) 0 es)
  | .op o es => .op o (gateExprs (child k e) 0 es)
  | .view es => .view (gateExprs (child k e) 0 es)
  | .field a f => .field (a.gate (child k e 0)) f
  | .index a i => .index (a.gate (child k e 0)) (i.gate (child k e 1))
  | .closure ps r ρ body => .closure ps r ρ (body.gate (child k e 0))
  | .call f args τ => .call (f.gate (child k e 0)) (gateArgs (child k e) 1 args) τ
  | .letIn x τ i b => .letIn x τ (i.gate (child k e 0)) (b.gate (child k e 1))
  | .varIn x τ i b => .varIn x τ (i.gate (child k e 0)) (b.gate (child k e 1))
  | .assign ⟨x, path⟩ v => .assign ⟨x, gatePath (child k e 0) path⟩ (v.gate (child k e 1))
  | .seq a b => .seq (a.gate (child k e 0)) (b.gate (child k e 1))
  | .if c τ a b => .if (c.gate (child k e 0)) τ (a.gate (child k e 1)) (b.gate (child k e 2))
  | .match s τ arms => .match (s.gate (child k e 0)) τ (gateArms (child k e) 1 arms)
  | .for x τ a b => .for x τ (a.gate (child k e 0)) (b.gate (child k e 1))
  | .raise a => .raise (a.gate (child k e 0))
  | .try a => .try (a.gate (child k e 0))
  | .tryCatch a E x h τ => .tryCatch (a.gate (child k e 0)) E x (h.gate (child k e 1)) τ
  | .while c b => .while (c.gate (child k e 0)) (b.gate (child k e 1))
  | .loop b => .loop (b.gate (child k e 0))
  | .return a => .return (a.gate (child k e 0))
  | .perform op a => .perform op (a.gate (child k e 0))
  | .withH E c h b => .withH E c (h.gate (child k e 0)) (b.gate (child k e 1))
  | .held ns hs body => .held ns (gateExprs (child k e) 0 hs) (body.gate (child k e hs.length))

/-- A list of expressions, the `i`th gated in the context at position `n + i`. -/
def gateExprs (kf : Nat → κ) (n : Nat) : List Expr → List Expr
  | [] => []
  | e :: es => e.gate (kf n) :: gateExprs kf (n + 1) es

/-- The fields of a record literal, gated. -/
def gateFields (kf : Nat → κ) (n : Nat) : List (Name × Expr) → List (Name × Expr)
  | [] => []
  | (f, e) :: fields => (f, e.gate (kf n)) :: gateFields kf (n + 1) fields

/-- A call's arguments, gated. -/
def gateArgs (kf : Nat → κ) (n : Nat) : List Arg → List Arg
  | [] => []
  | .value e :: args => .value (e.gate (kf n)) :: gateArgs kf (n + 1) args
  | .inout ⟨x, path⟩ :: args => .inout ⟨x, gatePath (kf n) path⟩ :: gateArgs kf (n + 1) args

/-- The indexes of a place, gated in the context `k`. -/
def gatePath (k : κ) : List Projection → List Projection
  | [] => []
  | .field f :: path => .field f :: gatePath k path
  | .index i :: path => .index (i.gate k) :: gatePath k path

/-- The arms of a `match`, gated. -/
def gateArms (kf : Nat → κ) (n : Nat) : List Arm → List Arm
  | [] => []
  | ⟨C, binders, body⟩ :: arms => ⟨C, binders, body.gate (kf n)⟩ :: gateArms kf (n + 1) arms

end

end

/-! ## What a gathering holds -/

section

variable {κ β : Type} (child : κ → Expr → Nat → κ) (visit : κ → Expr → List β)
  (P : β → Prop)

mutual

/-- Everything gathered from a body is found at one of its expressions, so a
property of everything `visit` finds holds of everything gathered. -/
theorem Expr.gather_all (hv : ∀ k e, ∀ b ∈ visit k e, P b) :
    ∀ (e : Expr) (k : κ), ∀ b ∈ e.gather child visit k, P b
  | .var _, k, b, h | .move _, k, b, h | .int _, k, b, h | .bool _, k, b, h | .unit, k, b, h
  | .break, k, b, h | .continue, k, b, h | .fnRef .., k, b, h | .method .., k, b, h => by
    simp only [Expr.gather, List.append_nil] at h
    exact hv _ _ _ h
  | .record _ _ fs, k, b, h => by
    simp only [Expr.gather, List.mem_append] at h
    exact h.elim (hv _ _ _) (gatherFields_all hv fs _ 0 b)
  | .variant _ _ _ es, k, b, h | .list _ es, k, b, h | .op _ es, k, b, h | .view es, k, b, h => by
    simp only [Expr.gather, List.mem_append] at h
    exact h.elim (hv _ _ _) (gatherExprs_all hv es _ 0 b)
  | .field a _, k, b, h | .closure _ _ _ a, k, b, h | .raise a, k, b, h | .try a, k, b, h
  | .loop a, k, b, h | .return a, k, b, h | .perform _ a, k, b, h => by
    simp only [Expr.gather, List.mem_append] at h
    exact h.elim (hv _ _ _) (Expr.gather_all hv a _ b)
  | .index a c, k, b, h | .letIn _ _ a c, k, b, h | .varIn _ _ a c, k, b, h | .seq a c, k, b, h
  | .for _ _ a c, k, b, h | .while a c, k, b, h | .tryCatch a _ _ c _, k, b, h
  | .withH _ _ a c, k, b, h => by
    simp only [Expr.gather, List.mem_append] at h
    rcases h with h | h | h
    · exact hv _ _ _ h
    · exact Expr.gather_all hv a _ b h
    · exact Expr.gather_all hv c _ b h
  | .call f args _, k, b, h => by
    simp only [Expr.gather, List.mem_append] at h
    rcases h with h | h | h
    · exact hv _ _ _ h
    · exact Expr.gather_all hv f _ b h
    · exact gatherArgs_all hv args _ 1 b h
  | .held _ hs c, k, b, h => by
    simp only [Expr.gather, List.mem_append] at h
    rcases h with h | h | h
    · exact hv _ _ _ h
    · exact gatherExprs_all hv hs _ 0 b h
    · exact Expr.gather_all hv c _ b h
  | .assign ⟨_, p⟩ v, k, b, h => by
    simp only [Expr.gather, List.mem_append] at h
    rcases h with h | h | h
    · exact hv _ _ _ h
    · exact gatherPath_all hv p _ b h
    · exact Expr.gather_all hv v _ b h
  | .if c _ a d, k, b, h => by
    simp only [Expr.gather, List.mem_append] at h
    rcases h with h | (h | h) | h
    · exact hv _ _ _ h
    · exact Expr.gather_all hv c _ b h
    · exact Expr.gather_all hv a _ b h
    · exact Expr.gather_all hv d _ b h
  | .match s _ arms, k, b, h => by
    simp only [Expr.gather, List.mem_append] at h
    rcases h with h | h | h
    · exact hv _ _ _ h
    · exact Expr.gather_all hv s _ b h
    · exact gatherArms_all hv arms _ 1 b h

theorem gatherExprs_all (hv : ∀ k e, ∀ b ∈ visit k e, P b) :
    ∀ (es : List Expr) (kf : Nat → κ) (n : Nat),
    ∀ b ∈ gatherExprs child visit kf n es, P b
  | [], _, _, _, h => nomatch h
  | e :: es, kf, n, b, h => by
    simp only [gatherExprs, List.mem_append] at h
    exact h.elim (Expr.gather_all hv e _ b) (gatherExprs_all hv es kf _ b)

theorem gatherFields_all (hv : ∀ k e, ∀ b ∈ visit k e, P b) :
    ∀ (fs : List (Name × Expr)) (kf : Nat → κ) (n : Nat),
    ∀ b ∈ gatherFields child visit kf n fs, P b
  | [], _, _, _, h => nomatch h
  | (_, e) :: fs, kf, n, b, h => by
    simp only [gatherFields, List.mem_append] at h
    exact h.elim (Expr.gather_all hv e _ b) (gatherFields_all hv fs kf _ b)

theorem gatherArgs_all (hv : ∀ k e, ∀ b ∈ visit k e, P b) :
    ∀ (args : List Arg) (kf : Nat → κ) (n : Nat),
    ∀ b ∈ gatherArgs child visit kf n args, P b
  | [], _, _, _, h => nomatch h
  | .value e :: args, kf, n, b, h => by
    simp only [gatherArgs, List.mem_append] at h
    exact h.elim (Expr.gather_all hv e _ b) (gatherArgs_all hv args kf _ b)
  | .inout ⟨_, p⟩ :: args, kf, n, b, h => by
    simp only [gatherArgs, List.mem_append] at h
    exact h.elim (gatherPath_all hv p _ b) (gatherArgs_all hv args kf _ b)

theorem gatherPath_all (hv : ∀ k e, ∀ b ∈ visit k e, P b) :
    ∀ (p : List Projection) (k : κ), ∀ b ∈ gatherPath child visit k p, P b
  | [], _, _, h => nomatch h
  | .field _ :: p, k, b, h => by
    simp only [gatherPath] at h
    exact gatherPath_all hv p k b h
  | .index i :: p, k, b, h => by
    simp only [gatherPath, List.mem_append] at h
    exact h.elim (Expr.gather_all hv i _ b) (gatherPath_all hv p k b)

theorem gatherArms_all (hv : ∀ k e, ∀ b ∈ visit k e, P b) :
    ∀ (arms : List Arm) (kf : Nat → κ) (n : Nat),
    ∀ b ∈ gatherArms child visit kf n arms, P b
  | [], _, _, _, h => nomatch h
  | ⟨_, _, body⟩ :: arms, kf, n, b, h => by
    simp only [gatherArms, List.mem_append] at h
    exact h.elim (Expr.gather_all hv body _ b) (gatherArms_all hv arms kf _ b)

end

end

/-! ## Gathering with a coarser context -/

section

variable {κ κ' β : Type} (child : κ → Expr → Nat → κ) (child' : κ' → Expr → Nat → κ')
  (visit : κ → Expr → List β) (visit' : κ' → Expr → List β) (f : κ → κ')
  (hc : ∀ k e n, f (child k e n) = child' (f k) e n) (hv : ∀ k e, visit k e = visit' (f k) e)

include hc hv

omit hv in
private theorem comp_child (k : κ) (e : Expr) : f ∘ child k e = child' (f k) e :=
  funext (hc k e)

-- The theorems on lists use `hc` and `hv` through `Expr.gather_map` alone.
set_option linter.unusedSectionVars false in
mutual

/-- A gathering whose findings read only a part `f` of the context, a part that each child's
context takes from its parent's alone, gathers the same with that part as its context. -/
theorem Expr.gather_map :
    ∀ (e : Expr) (k : κ), e.gather child visit k = e.gather child' visit' (f k)
  | .var _, k | .move _, k | .int _, k | .bool _, k | .unit, k | .break, k | .continue, k
  | .fnRef .., k | .method .., k => by simp only [Expr.gather, hv]
  | .record _ _ fs, k => by
    simp only [Expr.gather, hv, gatherFields_map fs, comp_child child child' f hc]
  | .variant _ _ _ es, k | .list _ es, k | .op _ es, k | .view es, k => by
    simp only [Expr.gather, hv, gatherExprs_map es, comp_child child child' f hc]
  | .field a _, k | .closure _ _ _ a, k | .raise a, k | .try a, k | .loop a, k | .return a, k
  | .perform _ a, k => by simp only [Expr.gather, hv, Expr.gather_map a, hc]
  | .index a c, k | .letIn _ _ a c, k | .varIn _ _ a c, k | .seq a c, k | .for _ _ a c, k
  | .while a c, k | .tryCatch a _ _ c _, k | .withH _ _ a c, k => by
    simp only [Expr.gather, hv, Expr.gather_map a, Expr.gather_map c, hc]
  | .call g args _, k => by
    simp only [Expr.gather, hv, Expr.gather_map g, hc,
      gatherArgs_map args, comp_child child child' f hc]
  | .held _ hs c, k => by
    simp only [Expr.gather, hv, Expr.gather_map c, hc,
      gatherExprs_map hs, comp_child child child' f hc]
  | .assign ⟨_, p⟩ v, k => by
    simp only [Expr.gather, hv, Expr.gather_map v, hc, gatherPath_map p]
  | .if c _ a d, k => by
    simp only [Expr.gather, hv, Expr.gather_map c, Expr.gather_map a, Expr.gather_map d, hc]
  | .match s _ arms, k => by
    simp only [Expr.gather, hv, Expr.gather_map s, hc,
      gatherArms_map arms, comp_child child child' f hc]

theorem gatherExprs_map : ∀ (es : List Expr) (kf : Nat → κ) (n : Nat),
    gatherExprs child visit kf n es = gatherExprs child' visit' (f ∘ kf) n es
  | [], _, _ => rfl
  | e :: es, kf, n => by
    simp only [gatherExprs, Expr.gather_map e, gatherExprs_map es kf, Function.comp_apply]

theorem gatherFields_map : ∀ (fs : List (Name × Expr)) (kf : Nat → κ) (n : Nat),
    gatherFields child visit kf n fs = gatherFields child' visit' (f ∘ kf) n fs
  | [], _, _ => rfl
  | (_, e) :: fs, kf, n => by
    simp only [gatherFields, Expr.gather_map e, gatherFields_map fs kf, Function.comp_apply]

theorem gatherArgs_map : ∀ (args : List Arg) (kf : Nat → κ) (n : Nat),
    gatherArgs child visit kf n args = gatherArgs child' visit' (f ∘ kf) n args
  | [], _, _ => rfl
  | .value e :: args, kf, n => by
    simp only [gatherArgs, Expr.gather_map e, gatherArgs_map args kf, Function.comp_apply]
  | .inout ⟨_, p⟩ :: args, kf, n => by
    simp only [gatherArgs, gatherPath_map p, gatherArgs_map args kf, Function.comp_apply]

theorem gatherPath_map : ∀ (p : List Projection) (k : κ),
    gatherPath child visit k p = gatherPath child' visit' (f k) p
  | [], _ => rfl
  | .field _ :: p, k => by simp only [gatherPath, gatherPath_map p k]
  | .index i :: p, k => by simp only [gatherPath, Expr.gather_map i, gatherPath_map p k]

theorem gatherArms_map : ∀ (arms : List Arm) (kf : Nat → κ) (n : Nat),
    gatherArms child visit kf n arms = gatherArms child' visit' (f ∘ kf) n arms
  | [], _, _ => rfl
  | ⟨_, _, body⟩ :: arms, kf, n => by
    simp only [gatherArms, Expr.gather_map body, gatherArms_map arms kf, Function.comp_apply]

end

end

end Stilt
