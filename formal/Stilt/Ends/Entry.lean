import Stilt.Ends.Descent

/-!
# A call's descending parameter

A call starts with its descending parameter, its counter and its bound holding what its
arguments passed (`enter_lookup`), so its body's frame meets the roles the body starts with,
against what the body knows of the call (`enter_roles`).
-/

namespace Stilt


/-- A call's frame holds, for a name that none of its later parameters has, what the
earlier frame held. -/
theorem Copy.enter_lookup_other {caller : Copy.Frame} {y : Name} :
    ∀ (bound : List (Name × Passed)) {init callee : Copy.Frame}, Copy.enter caller init bound = .ok callee →
      y ∉ bound.map Prod.fst → callee.lookup y = init.lookup y
  | [], _, _, h, _ => by cases h; rfl
  | (y', a) :: bound, init, callee, h, hy => by
    simp only [List.map_cons, List.mem_cons, not_or] at hy
    have hne : (y == y') = false := by simpa using hy.1
    cases a with
    | value v | moved _ v =>
      rw [Copy.enter_lookup_other bound h hy.2]
      simp [List.lookup, hne]
    | place x p =>
      change ((fun v => (y', v) :: init) <$> Copy.read caller x p >>= fun fr =>
        Copy.enter caller fr bound) = _ at h
      cases hr : Copy.read caller x p with
      | error f => rw [hr] at h; cases h
      | ok v =>
        rw [hr] at h
        rw [Copy.enter_lookup_other bound h hy.2]
        simp [List.lookup, hne]

/-- A call's frame holds what a parameter of a name no other parameter has is passed. -/
theorem Copy.enter_lookup {caller : Copy.Frame} {y : Name} {u : Value} :
    ∀ (bound : List (Name × Passed)) {init callee : Copy.Frame} {a : Passed},
      Copy.enter caller init bound = .ok callee → (bound.map Prod.fst).Nodup → (y, a) ∈ bound →
      (a = .value u ∨ ∃ z, a = .moved z u) → callee.lookup y = some u
  | [], _, _, _, _, _, hm, _ => nomatch hm
  | (y', a') :: bound, init, callee, a, h, hn, hm, ha => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hm with he | hm'
    · cases he
      rcases ha with rfl | ⟨z, rfl⟩ <;>
      · rw [Copy.enter_lookup_other bound h hn.1]
        simp [List.lookup]
    · cases a' with
      | value v | moved _ v => exact Copy.enter_lookup bound h hn.2 hm' ha
      | place x p =>
        change ((fun v => (y', v) :: init) <$> Copy.read caller x p >>= fun fr =>
          Copy.enter caller fr bound) = _ at h
        cases hr : Copy.read caller x p with
        | error f => rw [hr] at h; cases h
        | ok v => rw [hr] at h; exact Copy.enter_lookup bound h hn.2 hm' ha

/-- Pairing parameters with arguments keeps their names, and pairs a `let` parameter with a
value. -/
theorem bindArgs_spec : ∀ {params : List Param} {passed : List Passed}
    {bound : List (Name × Passed)}, bindArgs params passed = some bound →
      bound.map Prod.fst = params.map Param.name ∧ ∀ (k : Nat) (p : Param), params[k]? = some p →
        p.mode = .let →
        ∃ a u, (p.name, a) ∈ bound ∧ (a = .value u ∨ ∃ z, a = .moved z u) ∧ passed[k]? = some a
  | [], [], _, h => by cases h; exact ⟨rfl, fun _ _ hp => by simp at hp⟩
  | p :: ps, a :: as, bound, h => by
    simp only [bindArgs] at h
    have key : ∀ rest, bindArgs ps as = some rest → bound = (p.name, a) :: rest →
        bound.map Prod.fst = (p :: ps).map Param.name ∧ ∀ (k : Nat) (q : Param), (p :: ps)[k]? = some q →
          q.mode = .let → ∃ a' u, (q.name, a') ∈ bound ∧ (a' = .value u ∨ ∃ z, a' = .moved z u) ∧
            (a :: as)[k]? = some a' := by
      intro rest hr hb
      subst hb
      obtain ⟨hn, hk⟩ := bindArgs_spec hr
      refine ⟨by simp [hn], fun k q hq hmode => ?_⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
        subst hq
        rw [hmode] at h
        cases a with
        | value v => exact ⟨_, v, List.mem_cons_self, .inl rfl, rfl⟩
        | moved z v => exact ⟨_, v, List.mem_cons_self, .inr ⟨z, rfl⟩, rfl⟩
        | place x path => simp at h
      | succ k =>
        obtain ⟨a', u, hm, ha, hs⟩ := hk k q (by simpa using hq) hmode
        exact ⟨a', u, List.mem_cons_of_mem _ hm, ha, by simpa using hs⟩
    cases hpm : p.mode <;> rw [hpm] at h <;> cases a <;> simp only [reduceCtorEq] at h <;>
      (try split at h) <;>
      first
        | (obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h; exact key rest hr rfl)
        | cases h
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [bindArgs] at h

/-- A `let` parameter that `FnDecl.letParam?` finds holds, in a call's frame, what the call
passes at its position. -/
theorem letParam_lookup {d : FnDecl} {k : Nat} {x : Name} {passed : List Passed}
    {bound : List (Name × Passed)} {caller callee : Copy.Frame} (hx : d.letParam? k = some x)
    (hb : bindArgs d.params passed = some bound) (he : Copy.enter caller [] bound = .ok callee) :
    ∃ a u, callee.lookup x = some u ∧ passed[k]? = some a ∧ (a = .value u ∨ ∃ z, a = .moved z u) := by
  unfold FnDecl.letParam? at hx
  split at hx
  · rename_i p hp
    split at hx
    · rename_i hc
      cases hx
      obtain ⟨hmode, hnd, -⟩ := hc
      obtain ⟨hn, hk⟩ := bindArgs_spec hb
      obtain ⟨a, u, hm, ha, hs⟩ := hk k p hp hmode
      exact ⟨a, u, Copy.enter_lookup bound he (hn ▸ hnd) hm ha, hs, ha⟩
    · cases hx
  · cases hx

theorem letParam_avoids {d : FnDecl} {k : Nat} {x : Name} (hx : d.letParam? k = some x) :
    x ∉ d.body.writes := by
  unfold FnDecl.letParam? at hx
  split at hx
  · split at hx
    · rename_i hc; cases hx; exact hc.2.2
    · cases hx
  · cases hx

theorem Passed.size_of {a : Passed} {u : Value} (ha : a = .value u ∨ ∃ z, a = .moved z u) :
    a.size = sizeOf u := by
  rcases ha with rfl | ⟨z, rfl⟩ <;> rfl

theorem Passed.int?_of {a : Passed} {u : Value} (ha : a = .value u ∨ ∃ z, a = .moved z u) :
    a.int? = u.int? := by
  rcases ha with rfl | ⟨z, rfl⟩ <;> rfl

/-- A call's frame meets the roles its body starts with, against what the body knows of the
call. -/
theorem enter_roles {d : FnDecl} {spec : Descent} {passed : List Passed}
    {bound : List (Name × Passed)} {caller callee : Copy.Frame}
    (hb : bindArgs d.params passed = some bound) (he : Copy.enter caller [] bound = .ok callee) :
    (d.entryRoles spec).Inv callee (spec.meas passed) := by
  cases spec with
  | parts k =>
    simp only [FnDecl.entryRoles]
    split
    · rename_i x hx
      obtain ⟨a, u, hl, hk, ha⟩ := letParam_lookup hx hb he
      intro y hy
      simp only [Roles.of_cons] at hy ⊢
      split at hy
      · subst_vars
        refine ⟨u, hl, ?_⟩
        simp only [↓reduceIte]
        show sizeOf u ≤ Passed.sizeAt passed k
        simp [Passed.sizeAt, hk, Passed.size_of ha]
      · exact absurd rfl hy
    · exact Roles.Inv.nil _ _
  | shrinks k grow b =>
    simp only [FnDecl.entryRoles]
    split
    · rename_i x hx
      obtain ⟨a, u, hl, hk, ha⟩ := letParam_lookup hx hb he
      intro y hy
      simp only [Roles.of_cons] at hy ⊢
      by_cases hyx : y = x
      · subst hyx
        refine ⟨u, hl, ?_⟩
        simp only [↓reduceIte]
        show u.int? = Passed.intAt passed k
        simp [Passed.intAt, hk, Passed.int?_of ha]
      · simp only [hyx, ↓reduceIte] at hy ⊢
        split at hy
        · rename_i j
          split at hy
          · rename_i q hq
            split at hy
            · exact absurd rfl hy
            · rename_i hqx
              simp only [hqx, ↓reduceIte, Roles.of_cons] at hy ⊢
              split at hy
              · subst_vars
                obtain ⟨a', u', hl', hj, ha'⟩ := letParam_lookup hq hb he
                refine ⟨u', hl', ?_⟩
                simp only [↓reduceIte]
                show u'.int? = Passed.intAt passed j
                simp [Passed.intAt, hj, Passed.int?_of ha']
              · exact absurd rfl hy
          · exact absurd rfl hy
        · exact absurd rfl hy
    · exact Roles.Inv.nil _ _

/-- The roles a body starts with avoid what it writes. -/
theorem entryRoles_avoids (d : FnDecl) (spec : Descent) :
    (d.entryRoles spec).Avoids d.body.writes := by
  cases spec with
  | parts k =>
    simp only [FnDecl.entryRoles]
    split
    · rename_i x hx; exact (Roles.Avoids.nil _).cons fun _ => letParam_avoids hx
    · exact Roles.Avoids.nil _
  | shrinks k grow b =>
    simp only [FnDecl.entryRoles]
    split
    · rename_i x hx
      refine Roles.Avoids.cons ?_ fun _ => letParam_avoids hx
      split
      · split
        · rename_i q hq
          split
          · exact Roles.Avoids.nil _
          · exact (Roles.Avoids.nil _).cons fun _ => letParam_avoids hq
        · exact Roles.Avoids.nil _
      · exact Roles.Avoids.nil _
    · exact Roles.Avoids.nil _

end Stilt
