import Stilt.Cycles.Holds
import Stilt.Soundness.Outcome
import Stilt.Maps

/-!
# Cycles through shared values

cycles.through-shared-values: a value reaches itself only through a `Shared<T>`, every copy
of whose handle reaches one value. cycles.freeing frees the cycles among the values that
only can reach themselves, so the rule of cycles.can-form-cycle is sound when the value of no
other `Shared<U>` is ever on a cycle. `on_cycle_can_reach_itself` proves it of every typed
world: a cell on a cycle, a chain of cells each holding a handle to the next, is one of a
`Shared<U>` whose `U` can reach itself (`CanReachItself`).

A handle that a value of a type holds leads to a cell whose `Shared` the type holds, unless
the type holds a function type, whose closures capture values of any type
(`Value.Typed.leads`), and holding is transitive, through the `U` of each `Shared<U>`. A cell
is named by its type and its place among the cells of that type (`Stilt.World`), so the cell
a handle leads to has the type the handle names, and the world keeps each cell's value of
that type (`World.Typed`).
-/

namespace Stilt

/-- A value holds a handle when the handle is part of it: a field of a record, which tuples,
maps and sets are, a variant's payload, a list's element, or a value a closure captured,
without going through another handle's cell (cycles.through-shared-values). The handle is
named by its cell's type and place. -/
inductive Value.Holds : Value → Ty × Nat → Prop
  | handle {u : Ty} {k : Nat} : Value.Holds (.handle u k) (u, k)
  | record {R : Name} {fields : List (Name × Value)} {p : Name × Value} {c : Ty × Nat} :
      p ∈ fields → Value.Holds p.2 c → Value.Holds (.record R fields) c
  | variant {T C : Name} {payload : List Value} {v : Value} {c : Ty × Nat} :
      v ∈ payload → Value.Holds v c → Value.Holds (.variant T C payload) c
  | list {vs : List Value} {v : Value} {c : Ty × Nat} :
      v ∈ vs → Value.Holds v c → Value.Holds (.list vs) c
  | closure {captured : List (Name × Value)} {ps : List Param} {result : Ty} {ρ : Row} {body : Expr}
      {p : Name × Value} {c : Ty × Nat} :
      p ∈ captured → Value.Holds p.2 c → Value.Holds (.closure captured ps result ρ body) c

/-- The value in the cell `c`, the `c.2`-th cell of type `c.1`: while a `when` holds it, the
value it last put back. -/
def World.value? (w : World) (c : Ty × Nat) : Option Value :=
  (w.cell? c.1 c.2).map Cell.value

/-- A cell points to another when its value holds a handle to it. -/
def World.Points (w : World) (c c' : Ty × Nat) : Prop :=
  ∃ v, w.value? c = some v ∧ Value.Holds v c'

/-- A chain of cells, each pointing to the next. -/
inductive World.Chain (w : World) : Ty × Nat → Ty × Nat → Prop
  | single {c c' : Ty × Nat} : w.Points c c' → World.Chain w c c'
  | tail {c m c' : Ty × Nat} : World.Chain w c m → w.Points m c' → World.Chain w c c'

/-- Where a handle that a value of type `σ` holds may lead: to a cell of a type `u` whose
`Shared<u>` the type holds, or the type holds a function type or a type parameter. -/
def STy.Leads (D : Decls) (σ : STy) (u : Ty) : Prop :=
  STy.Holds D σ (.shared u.sem) ∨ σ.HoldsFn D ∨ ∃ T, STy.Holds D σ (.param T)

variable {D : Decls}

theorem STy.Leads.lift {σ σ' : STy} {u : Ty} (h : STy.Holds D σ' σ) : σ.Leads D u → σ'.Leads D u
  | .inl hs => .inl (h.trans hs)
  | .inr (.inl hf) => .inr (.inl (hf.of h))
  | .inr (.inr ⟨T, hT⟩) => .inr (.inr ⟨T, h.trans hT⟩)

theorem Value.Holds.record_inv {R : Name} {fields : List (Name × Value)} {c : Ty × Nat}
    (h : Value.Holds (.record R fields) c) : ∃ p ∈ fields, Value.Holds p.2 c := by
  cases h with
  | record hm h => exact ⟨_, hm, h⟩

theorem Value.Holds.list_inv {vs : List Value} {c : Ty × Nat} (h : Value.Holds (.list vs) c) :
    ∃ v ∈ vs, Value.Holds v c := by
  cases h with
  | list hm h => exact ⟨_, hm, h⟩

/-- A handle in a map's entries or default is in a key or a value of it. -/
theorem Value.Holds.map_inv {es : List (Value × Value)} {d : Option Value} {c : Ty × Nat}
    (h : Value.Holds (.mapOf es d) c) :
    (∃ e ∈ es, Value.Holds e.1 c ∨ Value.Holds e.2 c) ∨ ∃ v, d = some v ∧ Value.Holds v c := by
  obtain ⟨p, hp, hh⟩ := Value.Holds.record_inv h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · obtain ⟨x, hx, hh⟩ := hh.list_inv
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    obtain ⟨y, hy, hh⟩ := hh.list_inv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact .inl ⟨e, he, .inl hh⟩
    · exact .inl ⟨e, he, .inr hh⟩
  · obtain ⟨y, hy, hh⟩ := hh.list_inv
    exact .inr ⟨y, Option.mem_toList.1 hy, hh⟩

/-- A handle in a set is in one of its elements. -/
theorem Value.Holds.set_inv {ks : List Value} {c : Ty × Nat} (h : Value.Holds (.setOf ks) c) :
    ∃ k ∈ ks, Value.Holds k c := by
  obtain ⟨p, hp, hh⟩ := Value.Holds.record_inv h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  exact hh.list_inv

/-- A handle in a tuple is in one of its elements. -/
theorem Value.Holds.tuple_inv {vs : List Value} {c : Ty × Nat} (h : Value.Holds (.tuple vs) c) :
    ∃ v ∈ vs, Value.Holds v c := by
  obtain ⟨p, hp, hh⟩ := Value.Holds.record_inv h
  exact ⟨p.2, mem_positionsFrom hp, hh⟩

/-- A handle on a cell of type `u` has a type that leads to it. -/
theorem STy.Leads.handle {u : Ty} {σ : STy} (h : (STy.shared u.sem).Fits σ) : σ.Leads D u := by
  obtain ⟨b, rfl, hb⟩ := h.shared_eq_or_fn (D := D) rfl
  rcases hb with rfl | ⟨_, hb⟩
  · exact .inl .refl
  · exact .inr (.inl (hb.of (.shared .refl)))

mutual

/-- A handle that a typed value holds leads where its type says. -/
theorem Value.Typed.leads : ∀ {v : Value} {σ : STy}, Value.Typed D v σ →
    ∀ {c : Ty × Nat}, Value.Holds v c → σ.Leads D c.1
  | _, _, .int _, _, h | _, _, .float, _, h | _, _, .str, _, h | _, _, .bool, _, h
  | _, _, .unit, _, h | _, _, .function .., _, h => nomatch h
  | _, _, .record hr _ hf, _, h =>
    let ⟨_, hp, hh⟩ := h.record_inv
    let ⟨q, hq, hl⟩ := Fields.Typed.leads hf hp hh
    hl.lift (.record hr hq .refl)
  | _, _, .variant ht _ hC hp, _, h => by
    cases h with
    | variant hm hh =>
      obtain ⟨τ, hτ, hl⟩ := Values.Typed.leads hp hm hh
      exact hl.lift (.variant ht (mem_of_lookup hC) hτ .refl)
  | _, _, .list hvs, _, h =>
    let ⟨_, hm, hh⟩ := h.list_inv
    (Value.Typed.leads (hvs _ hm) hh).lift (.list .refl)
  | _, _, .tuple hes, _, h =>
    let ⟨_, hm, hh⟩ := h.tuple_inv
    let ⟨_, hσ, hl⟩ := Elems.Typed.leads hes hm hh
    hl.lift (.tuple hσ .refl)
  | _, _, .map hk hv hd, _, h => by
    rcases h.map_inv with ⟨e, he, hh | hh⟩ | ⟨v, hdv, hh⟩
    · exact (Value.Typed.leads (hk e he) hh).lift (.key .refl)
    · exact (Value.Typed.leads (hv e he) hh).lift (.value .refl)
    · exact (Value.Typed.leads (hd v hdv) hh).lift (.value .refl)
  | _, _, .set hks, _, h =>
    let ⟨_, hm, hh⟩ := h.set_inv
    (Value.Typed.leads (hks _ hm) hh).lift (.set .refl)
  | _, _, .closure _ _ _ _ _ _ _ hσ _, _, _ => by
    obtain ⟨ps, r, R, rfl⟩ := hσ.fn_fn (by simp only [Ty.close]; rfl)
    exact .inr (.inl ⟨ps, r, R, .refl⟩)
  | _, _, .handle hσ, _, h => by
    cases h
    exact STy.Leads.handle hσ

theorem Elems.Typed.leads : ∀ {vs : List Value} {σs : List STy}, Elems.Typed D vs σs →
    ∀ {v : Value} {c : Ty × Nat}, v ∈ vs → Value.Holds v c → ∃ σ ∈ σs, σ.Leads D c.1
  | _, _, .nil, _, _, hm, _ => nomatch hm
  | _, _, .cons hv hvs, _, _, hm, hh =>
    match List.mem_cons.1 hm with
    | .inl he => ⟨_, List.mem_cons_self, Value.Typed.leads hv (he ▸ hh)⟩
    | .inr hm =>
      let ⟨σ, hσ, hl⟩ := Elems.Typed.leads hvs hm hh
      ⟨σ, List.mem_cons_of_mem _ hσ, hl⟩

theorem Fields.Typed.leads : ∀ {fields : List (Name × Value)} {declared : List (Name × Ty)}
    {π : SParams}, Fields.Typed D fields declared π → ∀ {p : Name × Value} {c : Ty × Nat},
      p ∈ fields → Value.Holds p.2 c → ∃ q ∈ declared, (q.2.semAt π).Leads D c.1
  | _, _, _, .nil, _, _, hm, _ => nomatch hm
  | _, _, _, .cons hv hfs, _, _, hm, hh =>
    match List.mem_cons.1 hm with
    | .inl he => ⟨_, List.mem_cons_self, Value.Typed.leads hv (by subst he; exact hh)⟩
    | .inr hm =>
      let ⟨q, hq, hl⟩ := Fields.Typed.leads hfs hm hh
      ⟨q, List.mem_cons_of_mem _ hq, hl⟩

theorem Values.Typed.leads : ∀ {vs : List Value} {τs : List Ty} {π : SParams},
    Values.Typed D vs τs π → ∀ {v : Value} {c : Ty × Nat}, v ∈ vs → Value.Holds v c →
      ∃ τ ∈ τs, (τ.semAt π).Leads D c.1
  | _, _, _, .nil, _, _, hm, _ => nomatch hm
  | _, _, _, .cons hv hvs, _, _, hm, hh =>
    match List.mem_cons.1 hm with
    | .inl he => ⟨_, List.mem_cons_self, Value.Typed.leads hv (he ▸ hh)⟩
    | .inr hm =>
      let ⟨τ, hτ, hl⟩ := Values.Typed.leads hvs hm hh
      ⟨τ, List.mem_cons_of_mem _ hτ, hl⟩

end

/-- The value of a cell of a typed world has the cell's type. -/
theorem World.Typed.value {w : World} (hw : World.Typed D w) {c : Ty × Nat} {v : Value}
    (h : w.value? c = some v) : Value.Typed D v c.1.sem := by
  obtain ⟨cell, hcell, rfl⟩ := Option.map_eq_some_iff.1 h
  have hm := List.mem_of_getElem? hcell
  simp only [World.cellsOf, List.mem_filter, decide_eq_true_eq] at hm
  rw [← hm.2]
  exact hw cell hm.1

/-- Every cell that a chain reaches from a cell of type `u` is one of a type whose `Shared`
`u` holds, unless `u` holds a function type or a type parameter. -/
theorem World.Typed.chain_leads {w : World} (hw : World.Typed D w) {c c' : Ty × Nat}
    (h : w.Chain c c') : c.1.sem.Leads D c'.1 := by
  induction h with
  | single hp =>
    obtain ⟨v, hv, hh⟩ := hp
    exact (hw.value hv).leads hh
  | tail _ hp ih =>
    obtain ⟨v, hv, hh⟩ := hp
    rcases ih with hs | hf | hq
    · exact ((hw.value hv).leads hh).lift (hs.trans (.shared .refl))
    · exact .inr (.inl hf)
    · exact .inr (.inr hq)

/-- cycles.can-form-cycle is sound: a cell of a typed world on a cycle is one of a
`Shared<U>` whose `U` can reach itself. So the value of a `Shared<U>` whose `U` can't is on
no cycle, and a collector that skips such values frees every cycle. -/
theorem on_cycle_can_reach_itself {w : World} (hw : World.Typed D w) {u : Ty} {k : Nat}
    (h : w.Chain (u, k) (u, k)) : CanReachItself D u :=
  hw.chain_leads h

end Stilt
