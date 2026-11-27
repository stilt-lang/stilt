import Stilt.Ends.Body

/-!
# The roles a body starts with

A call's frame meets the roles its body starts with (`enter_startRoles`): those of its
self-calls (`FnDecl.entryRoles`), and its non-escaping parameters, which hold the function
values that the call vouches halt (facts.div).
-/

namespace Stilt

theorem Roles.of_append (R₁ R₂ : Roles) (x : Name) :
    (R₁ ++ R₂).of x = R₁.of x ∨ (R₁ ++ R₂).of x = R₂.of x := by
  induction R₁ with
  | nil => exact .inr rfl
  | cons p R₁ ih =>
    obtain ⟨y, r⟩ := p
    simp only [List.cons_append, Roles.of_cons]
    split
    · exact .inl rfl
    · exact ih

theorem Roles.of_mem : ∀ (R : Roles) (x : Name), R.of x = .other ∨ (x, R.of x) ∈ R
  | [], _ => .inl rfl
  | (y, r) :: R, x => by
    rw [Roles.of_cons]
    split
    · subst_vars; exact .inr List.mem_cons_self
    · rcases Roles.of_mem R x with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)

theorem Roles.Inv.append {R₁ R₂ : Roles} {fr : Copy.Frame} {m : Meas} (h₁ : R₁.Inv fr m)
    (h₂ : R₂.Inv fr m) : (R₁ ++ R₂).Inv fr m := by
  intro x hx
  rcases Roles.of_append R₁ R₂ x with h | h <;> rw [h] at hx ⊢
  · exact h₁ x hx
  · exact h₂ x hx

theorem Roles.Avoids.append {R₁ R₂ : Roles} {W : List Name} (h₁ : R₁.Avoids W) (h₂ : R₂.Avoids W) :
    (R₁ ++ R₂).Avoids W := by
  intro x hx
  rcases Roles.of_append R₁ R₂ x with h | h <;> rw [h] at hx
  · exact h₁ x hx
  · exact h₂ x hx

/-- The roles of a body's self-calls are none of `halting`. -/
theorem entryRoles_ne_halting (d : FnDecl) (spec : Descent) :
    ∀ p ∈ d.entryRoles spec, p.2 ≠ .halting := by
  cases spec <;> simp only [FnDecl.entryRoles] <;> repeat' split
  all_goals simp

/-- A role other than `halting` says nothing of the function values a call vouches for. -/
theorem Role.Holds.withFns {r : Role} {u : Value} {m : Meas} (F : Value → Prop) (hr : r ≠ .halting)
    (h : r.Holds u m) : r.Holds u { m with fns := F } := by
  cases r <;> first | exact absurd rfl hr | exact h

/-- The non-escaping parameters among the roles a body starts with. -/
theorem haltingRoles_of {d : FnDecl} {hs : List Nat} {x : Name}
    (hx : Roles.of (d.haltingRoles hs) x ≠ .other) :
    ∃ k ∈ hs, d.letParam? k = some x ∧ Roles.of (d.haltingRoles hs) x = .halting := by
  rcases Roles.of_mem _ x with h | h
  · exact absurd h hx
  · obtain ⟨k, hk, hm⟩ := List.mem_filterMap.1 h
    obtain ⟨y, hy, he⟩ := Option.map_eq_some_iff.1 hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, hr⟩ := he
    exact ⟨k, hk, hy, hr.symm⟩

/-- A variable that the roles of a body's self-calls don't make a strict part isn't one among the
roles it starts with either. -/
theorem startRoles_ne_part {d : FnDecl} {spec : Descent} {hs : List Nat} {x : Name}
    (h : (d.entryRoles spec).of x ≠ .part) : (d.startRoles spec hs).of x ≠ .part := by
  unfold FnDecl.startRoles
  rcases Roles.of_append (d.entryRoles spec) (d.haltingRoles hs) x with e | e <;> rw [e]
  · exact h
  · intro hp
    obtain ⟨_, _, _, hr⟩ := haltingRoles_of (d := d) (hs := hs) (x := x) (by rw [hp]; exact nofun)
    rw [hr] at hp
    cases hp

variable {D : Decls} {w : WriteBack}

/-- A call's frame meets the roles its body starts with, against what the body knows of the
call and the function values the call vouches halt. -/
theorem enter_startRoles {d : FnDecl} {spec : Descent} {hs : List Nat} {passed : List Passed}
    {bound : List (Name × Passed)} {caller callee : Copy.Frame}
    (hb : bindArgs d.params passed = some bound) (he : Copy.enter caller [] bound = .ok callee)
    (hp : Passed.HaltAt D w hs passed) :
    (d.startRoles spec hs).Inv callee { spec.meas passed with fns := Value.Halting D w } := by
  refine Roles.Inv.append ?_ ?_
  · intro x hx
    obtain ⟨u, hl, hh⟩ := enter_roles hb he x hx
    refine ⟨u, hl, hh.withFns _ ?_⟩
    rcases Roles.of_mem (d.entryRoles spec) x with h | h
    · exact absurd h hx
    · exact entryRoles_ne_halting d spec _ h
  · intro x hx
    obtain ⟨k, hk, hx', hr⟩ := haltingRoles_of hx
    rw [hr]
    obtain ⟨a, u, hl, hpk, ha⟩ := letParam_lookup hx' hb he
    obtain ⟨a', u', hpk', ha', hu'⟩ := hp k hk
    rw [hpk] at hpk'
    cases hpk'
    refine ⟨u, hl, ?_⟩
    have : u' = u := by
      rcases ha with rfl | ⟨z, rfl⟩ <;> rcases ha' with h | ⟨z', h⟩ <;> cases h <;> rfl
    exact this ▸ hu'

/-- The roles a body starts with avoid what it writes. -/
theorem startRoles_avoids (d : FnDecl) (spec : Descent) (hs : List Nat) :
    (d.startRoles spec hs).Avoids d.body.writes := by
  refine (entryRoles_avoids d spec).append fun x hx => ?_
  obtain ⟨k, _, hx', _⟩ := haltingRoles_of hx
  exact letParam_avoids hx'

end Stilt
