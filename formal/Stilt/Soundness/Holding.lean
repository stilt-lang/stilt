import Stilt.Soundness.Lists
import Stilt.Soundness.Patterns
import Stilt.Soundness.Cells
import Stilt.Strengthen

/-!
# Holding shared values keeps outcomes sound

A `when` evaluates its handles, values of `Shared<T>`, so each names a cell whose values
are those of its `T`; it holds them, or panics with `deadlock`; it binds each name to its
cell's value, a value of its `T`; and however its block ends it puts each name's value back
in its cell, a value of the cell's type, so the world stays typed (shared.when). A `with`
lets go of cells, which changes no value.
-/

namespace Stilt

variable {D : Decls} {η : REnv} {α : Type}

/-- The cell a handle names holds the values of the type `τ` a name of a `when` reads it at. -/
def CellFor (D : Decls) (η : REnv) (p : Name × Ty) (h : Ty × Nat) : Prop :=
  ∀ v, Value.Typed D v h.1.sem ↔ Value.Typed D v (p.2.close η)

/-- The handles a `when` evaluates name cells of the types of its names. -/
theorem ValuesAt.cells : ∀ {ns : List (Name × Ty)} {vs : List Value},
    ValuesAt D η vs (ns.map fun p => .shared p.2) →
      ∃ cells, vs.mapM Value.cellOf = .ok cells ∧ Forall₂ (CellFor D η) ns cells
  | [], _, h => by cases h; exact ⟨[], rfl, .nil⟩
  | _ :: _, [], h => by cases h
  | p :: _, v :: _, h => by
    cases h with
    | cons hv hvs =>
      obtain ⟨u, k, rfl, hu⟩ := Value.Typed.shared_inv
        (show Value.Typed D v (.shared (p.2.close η)) from hv)
      obtain ⟨cells, hc, hr⟩ := ValuesAt.cells hvs
      exact ⟨(u, k) :: cells, by simp [List.mapM_cons, Value.cellOf, hc]; rfl, .cons hu hr⟩

/-- The values of typed cells, read at the types of the names that hold them. -/
theorem World.Typed.values {w : World} (hw : World.Typed D w) :
    ∀ {ns : List (Name × Ty)} {hs : List (Ty × Nat)} {cs : List Cell},
      Forall₂ (CellFor D η) ns hs → Forall₂ (fun h c => w.cell? h.1 h.2 = some c) hs cs →
        ValuesAt D η (cs.map Cell.value) (ns.map Prod.snd)
  | [], [], [], .nil, .nil => .nil
  | _ :: _, _ :: _, _ :: _, .cons hr hrs, .cons hc hcs => by
    obtain ⟨hm, ht⟩ := World.cell?_mem hc
    exact .cons ((hr _).1 (ht ▸ hw _ hm)) (hw.values hrs hcs)

theorem World.Typed.holdAll : ∀ (hs : List (Ty × Nat)) {w : World}, World.Typed D w →
    World.Typed D (hs.foldl (fun x h => x.modify h fun c => { c with held := true }) w)
  | [], _, hw => hw
  | h :: hs, _, hw => World.Typed.holdAll hs (hw.hold h)

/-- Taking the cells of a `when` gives values of its names' types in a typed world, or panics. -/
theorem World.Typed.take {w : World} (hw : World.Typed D w) {ns : List (Name × Ty)}
    {hs : List (Ty × Nat)} (hr : Forall₂ (CellFor D η) ns hs) :
    (∃ vs w', World.take hs w = .ok (vs, w') ∧ ValuesAt D η vs (ns.map Prod.snd) ∧ World.Typed D w') ∨
      World.take hs w = .error (.panic .deadlock) := by
  unfold World.take
  split
  · rename_i cs hcs
    split
    · exact .inl ⟨_, _, rfl, hw.values hr (mapM_cells hcs), World.Typed.holdAll hs hw⟩
    · exact .inr rfl
  · exact .inr rfl

/-! ## Binding the names -/

theorem Ctx.lookup_holding_of_not_mem {x : Name} : ∀ (ns : List (Name × Ty)) (Γ : Ctx),
    x ∉ ns.map Prod.fst → (Γ.holding ns).lookup x = Γ.lookup x
  | [], _, _ => rfl
  | p :: ns, Γ, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    show ((Γ.bind p.1 _).holding ns).lookup x = _
    rw [Ctx.lookup_holding_of_not_mem ns _ h.2, Ctx.lookup_bind_ne _ _ h.1]

theorem Ctx.lookup_holding : ∀ {ns : List (Name × Ty)} (Γ : Ctx), (ns.map Prod.fst).Nodup →
    ∀ p ∈ ns, (Γ.holding ns).lookup p.1 = some ⟨p.2, true⟩
  | [], _, _, _, h => nomatch h
  | q :: ns, Γ, hnd, p, hp => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    show ((Γ.bind q.1 _).holding ns).lookup p.1 = _
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [Ctx.lookup_holding_of_not_mem ns _ hnd.1, Ctx.lookup_bind_self]
    · exact Ctx.lookup_holding _ hnd.2 p hp

theorem Forall₂.mem_zip {R : Name × Ty → Ty × Nat → Prop} :
    ∀ {ns : List (Name × Ty)} {hs : List (Ty × Nat)}, Forall₂ R ns hs →
      ∀ c ∈ (ns.map Prod.fst).zip hs, ∃ p ∈ ns, p.1 = c.1 ∧ R p c.2
  | [], [], .nil, _, h => nomatch h
  | p :: _, _ :: _, .cons hr hrs, c, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨p, List.mem_cons_self, rfl, hr⟩
    · obtain ⟨q, hq, h₁, h₂⟩ := Forall₂.mem_zip hrs c h
      exact ⟨q, List.mem_cons_of_mem _ hq, h₁, h₂⟩

/-- The names of a `when`, bound to values of their types, the first one outermost. -/
theorem Eval.Ok.withHeld {X : Exits} {P : α → Prop} {m : Eval Copy.State α} :
    ∀ {Γ : Ctx} {ns : List (Name × Ty)} {vs : List Value}, ValuesAt D η vs (ns.map Prod.snd) →
      Eval.Ok D (Γ.holding ns) η X P m →
        Eval.Ok D Γ η X P (Eval.withVars Copy.memory ((ns.map Prod.fst).zip vs) m)
  | _, [], _, h, hm => by cases h; exact hm
  | Γ, p :: _, _ :: _, .cons hv hvs, hm =>
    Eval.Ok.withVar (b := ⟨p.2, true⟩) hv (Eval.Ok.withHeld (Γ := Γ.bind p.1 ⟨p.2, true⟩) hvs hm)
  | _, _ :: _, [], h, _ => nomatch h

/-! ## Putting values back -/

/-- What a `when` puts back: each name's binding, of a type whose values its cell holds. -/
def PutsBack (D : Decls) (Γ : Ctx) (η : REnv) (cells : List (Name × Ty × Nat)) : Prop :=
  ∀ c ∈ cells, ∃ b, Γ.lookup c.1 = some b ∧ ∀ v, Value.Typed D v (b.type.close η) → Value.Typed D v c.2.1.sem

/-- Putting back the names' values keeps a state typed, or panics. -/
theorem putBack_ok {Γ : Ctx} (held : Bool) : ∀ {cells : List (Name × Ty × Nat)} {s : Copy.State},
    PutsBack D Γ η cells → State.Typed D s Γ η →
      (∃ s', Copy.memory.putBack held cells s = .ok s' ∧ State.Typed D s' Γ η) ∨
        ∃ k, Copy.memory.putBack held cells s = .error (.panic k)
  | [], s, _, hs => .inl ⟨s, rfl, hs⟩
  | (x, h) :: rest, (fr, wd), hc, hs => by
    obtain ⟨b, hb, hv⟩ := hc _ List.mem_cons_self
    have hrest : PutsBack D Γ η rest := fun c hc' => hc c (List.mem_cons_of_mem _ hc')
    rcases hs.1.read hb .nil with ⟨w, hr, hw⟩ | hr
    · have hr' : Copy.memory.read (fr, wd) x [] = .ok w := hr
      have h' := putBack_ok held (s := (fr, wd.put h w held)) hrest ⟨hs.1, hs.2.put (hv w hw) held⟩
      simp only [Memory.putBack, hr', bind, Except.bind]
      exact h'
    · have hr' : Copy.memory.read (fr, wd) x [] = .error (.panic .bounds) := hr
      exact .inr ⟨.bounds, by simp only [Memory.putBack, hr', bind, Except.bind]⟩

theorem Outcome.Ok.after {Γ : Ctx} {X : Exits} {P : α → Prop} {f : Copy.State → Except Fault Copy.State}
    {s : Copy.State} {o : Copy.State → Outcome Copy.State α} (hs : State.Typed D s Γ η)
    (hf : (∃ s', f s = .ok s' ∧ State.Typed D s' Γ η) ∨ ∃ k, f s = .error (.panic k))
    (ho : ∀ s', State.Typed D s' Γ η → (o s').Ok D Γ η X P) : (Outcome.after f s o).Ok D Γ η X P := by
  unfold Outcome.after
  rcases hf with ⟨s', h, hs'⟩ | ⟨k, h⟩ <;> rw [h]
  · exact ho s' hs'
  · exact hs

/-- A `when`'s block, its names' values put back however it ends, ends soundly. -/
theorem Outcome.Ok.release {Γ : Ctx} {X : Exits} {P : α → Prop} {cells : List (Name × Ty × Nat)}
    (hc : PutsBack D Γ η cells) :
    ∀ {o : Outcome Copy.State α}, o.Ok D Γ η X P → (o.release Copy.memory cells).Ok D Γ η X P
  | .done _ _, ⟨ha, hs⟩ => Outcome.Ok.after hs (putBack_ok false hc hs) fun _ hs' => ⟨ha, hs'⟩
  | .raised _ _, ⟨he, hs⟩ => Outcome.Ok.after hs (putBack_ok false hc hs) fun _ hs' => ⟨he, hs'⟩
  | .jumped _ _, ⟨hj, hs⟩ => Outcome.Ok.after hs (putBack_ok false hc hs) fun _ hs' => ⟨hj, hs'⟩
  | .panicked _ _, hs => Outcome.Ok.after hs (putBack_ok false hc hs) fun _ hs' => hs'
  | .performed _ _ _ _, ⟨⟨τ, ρ, hop, hv, hk⟩, hs⟩ =>
    Outcome.Ok.after hs (putBack_ok true hc hs) fun _ hs' =>
      ⟨⟨τ, ρ, hop, hv, fun w x hw hx => Outcome.Ok.release hc (hk w x hw hx)⟩, hs'⟩
  | .outOfFuel, h => h
  | .stuck, h => h

/-- A `with`, letting go of the cells its dropped rests hold, ends soundly. -/
theorem Outcome.Ok.letGo {Γ : Ctx} {X : Exits} {P : α → Prop} (before : World) :
    ∀ {o : Outcome Copy.State α}, o.Ok D Γ η X P → (o.letGo Copy.memory before).Ok D Γ η X P
  | .done _ _, ⟨ha, hs⟩ => ⟨ha, hs.1, hs.2.letGo before⟩
  | .raised _ _, ⟨he, hs⟩ => ⟨he, hs.1, hs.2.letGo before⟩
  | .jumped _ _, ⟨hj, hs⟩ => ⟨hj, hs.1, hs.2.letGo before⟩
  | .panicked _ _, hs => ⟨hs.1, hs.2.letGo before⟩
  | .performed _ _ _ _, ⟨⟨τ, ρ, hop, hv, hk⟩, hs⟩ =>
    ⟨⟨τ, ρ, hop, hv, fun w x hw hx => Outcome.Ok.letGo before (hk w x hw hx)⟩, hs⟩
  | .outOfFuel, h => h
  | .stuck, h => h

theorem Eval.Ok.letGo {Γ : Ctx} {X : Exits} {P : α → Prop} {m : Eval Copy.State α}
    (hm : Eval.Ok D Γ η X P m) : Eval.Ok D Γ η X P (Eval.letGo Copy.memory m) := fun s hs =>
  (hm s hs).letGo _

/-- Reading and writing the world, which gives a value that `P` holds of in a typed world or
panics in every typed world, ends soundly. -/
theorem Eval.Ok.worldWith {Γ : Ctx} {X : Exits} {P : Value → Prop}
    {f : World → Except Fault (Value × World)}
    (h : ∀ x, World.Typed D x → (∃ v x', f x = .ok (v, x') ∧ P v ∧ World.Typed D x') ∨
      ∃ k, f x = .error (.panic k)) :
    Eval.Ok D Γ η X P (Eval.world Copy.memory f) := by
  rintro ⟨fr, x⟩ hγ
  rcases h x hγ.2 with ⟨v, x', hf, hv, hx'⟩ | ⟨k, hf⟩
  · rw [show Eval.world Copy.memory f (fr, x) = .done v (fr, x') from Eval.world_ok hf]
    exact ⟨hv, hγ.1, hx'⟩
  · rw [show Eval.world Copy.memory f (fr, x) = .fault (.panic k) (fr, x) from Eval.world_error hf]
    exact hγ

/-! ## `when` -/

section

variable {n : Nat} (hs : Sound D n) {scope : RowScope} (hη : η.Respects scope) (θ : RowSubst)
  {Γ : Ctx} {fx : Effects}
include hs hη

theorem held_ok {ns : List (Name × Ty)} {es : List Expr} {body : Expr} {σ : Ty}
    (hnd : (ns.map Prod.fst).Nodup) (hes : ExprsFit D scope Γ fx es (ns.map fun p => .shared p.2))
    (hb : HasType D scope (Γ.holding ns) fx body σ) :
    Eval.Ok D Γ η (fx.exits D η) (fun v => Value.Typed D v (σ.close η))
      (eval D Copy.memory (n + 1) ((Expr.held ns es body).substRows θ)) := by
  have hnames : (ns.map fun p => (p.1, p.2.substRows θ)).map Prod.fst = ns.map Prod.fst := by
    simp [Function.comp_def]
  show Eval.Ok D Γ η _ _ (Eval.bind (Eval.list (eval D Copy.memory n) (substExprRows θ es)) fun vs =>
    Eval.held Copy.memory (eval D Copy.memory n (body.substRows θ))
      ((ns.map fun p => (p.1, p.2.substRows θ)).map Prod.fst) vs)
  rw [hnames]
  refine Eval.Ok.bind (ExprsFit.ok hs hη θ hes) fun vs hvs => ?_
  obtain ⟨cells, hcells, hr⟩ := hvs.cells
  have hput : PutsBack D (Γ.holding ns) η ((ns.map Prod.fst).zip cells) := fun c hc => by
    obtain ⟨p, hp, h₁, h₂⟩ := hr.mem_zip c hc
    exact ⟨_, h₁ ▸ Ctx.lookup_holding Γ hnd p hp, fun v hv => (h₂ v).2 hv⟩
  unfold Eval.held
  rw [hcells]
  refine Eval.Ok.bind (Eval.Ok.ofExcept (P := (· = cells)) (.inl ⟨cells, rfl, rfl⟩)) fun c hc => ?_
  subst hc
  refine Eval.Ok.bind (P := fun vs => ValuesAt D η vs (ns.map Prod.snd))
    (Eval.Ok.bind (Q := fun vs => ValuesAt D η vs (ns.map Prod.snd)) (Eval.Ok.worldWith
    (P := fun v => ∃ vs', v = .list vs' ∧ ValuesAt D η vs' (ns.map Prod.snd)) fun x hx => ?_)
      fun v hv => ?_) fun vs' hvs' => ?_
  · rcases hx.take hr with ⟨vs', w', h, hvs', hw'⟩ | h
    · exact .inl ⟨_, _, by rw [h]; rfl, ⟨vs', rfl, hvs'⟩, hw'⟩
    · exact .inr ⟨.deadlock, by rw [h]; rfl⟩
  · obtain ⟨vs', rfl, hvs'⟩ := hv
    exact Eval.Ok.pure (P := fun vs => ValuesAt D η vs (ns.map Prod.snd)) hvs'
  · have hlen : (ns.map Prod.fst).length = vs'.length := by
      rw [hvs'.length, List.length_map, List.length_map]
    simp only [hlen, ↓reduceIte]
    exact Eval.Ok.withHeld hvs' fun s hs' => ((hs hb hη θ) s hs').release hput

end

end Stilt
