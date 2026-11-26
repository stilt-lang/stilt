import Stilt.Ends.Syntax
import Stilt.Ends.Counter

/-!
# Descending calls pass smaller values

What the roles promise of a run, in copy-in, copy-out, whatever its order of write-back. A
call starts with its descending parameter holding the value its argument passed
(`enter_lookup`); code keeps every variable it doesn't write, so a variable keeps its role's
bound (`Roles.Inv.after`); an expression with a role gives a value that its role bounds
(`eval_roleIn`); and so a self-call that descends passes, at the descending position, a
value smaller than the one its caller was called with (`args_descend`).
-/

namespace Stilt

/-- The size of what an argument passes by value, `0` for a place. -/
noncomputable def Passed.size : Passed → Nat
  | .value v | .moved _ v => sizeOf v
  | .place _ _ => 0

/-- The size of the argument at position `k`. -/
noncomputable def Passed.sizeAt (passed : List Passed) (k : Nat) : Nat := (passed[k]?.map Passed.size).getD 0

variable {R : Roles} {m : Nat}

/-- Code that keeps the variables outside `W` keeps the roles of a frame that `W` avoids. -/
theorem Roles.Inv.afterAt {α : Type} {W L : List Name} {P : α → Prop} {m' : Eval Copy.State α}
    {s s' : Copy.State} {a : α} (hk : Eval.Keeps W L P m') (hA : R.Avoids W)
    (hI : R.Inv s.1 m) (hd : m' s = .done a s') : R.Inv s'.1 m := by
  have := hk s
  rw [hd] at this
  exact hI.keep hA this.2

theorem Roles.Inv.after {α : Type} {W L : List Name} {P : α → Prop} {F : Nat → Eval Copy.State α}
    {s s' : Copy.State} {a : α} (hk : ∀ n, Eval.Keeps W L P (F n)) (hA : R.Avoids W)
    (hI : R.Inv s.1 m) (hd : ∃ N, ∀ n, N ≤ n → F n s = .done a s') : R.Inv s'.1 m :=
  let ⟨N, hN⟩ := hd
  hI.afterAt (hk N) hA (hN N (Nat.le_refl _))

theorem Roles.Inv.evalAt {D : Decls} {w : WriteBack} {e : Expr} {n : Nat} {s s' : Copy.State}
    {a : Value} (hA : R.Avoids e.writes) (hI : R.Inv s.1 m)
    (hd : eval D (Copy.memoryWith w) n e s = .done a s') : R.Inv s'.1 m :=
  hI.afterAt (eval_keeps D w n e e.writes e.resizes (List.Subset.refl _) (List.Subset.refl _)) hA hd

theorem Roles.Inv.afterEval {D : Decls} {w : WriteBack} {e : Expr} {s s' : Copy.State} {a : Value}
    (hA : R.Avoids e.writes) (hI : R.Inv s.1 m)
    (hd : ∃ N, ∀ n, N ≤ n → eval D (Copy.memoryWith w) n e s = .done a s') : R.Inv s'.1 m :=
  let ⟨N, hN⟩ := hd
  hI.evalAt hA (hN N (Nat.le_refl _))

/-- What an expression with a role gives is bounded by its role. -/
theorem eval_roleIn {D : Decls} {w : WriteBack} :
    ∀ (n : Nat) (e : Expr) {s s' : Copy.State} {u : Value}, R.Inv s.1 m → e.roleIn R ≠ .other →
      eval D (Copy.memoryWith w) n e s = .done u s' → (e.roleIn R).Bounds (sizeOf u) m
  | 0, _, _, _, _, _, _, h => by cases h
  | n + 1, .var x, s, _, _, hI, hr, h | n + 1, .move x, s, _, _, hI, hr, h => by
    obtain ⟨u', hl, hb⟩ := hI x hr
    obtain ⟨hx, -⟩ := Eval.ofExcept_done h
    obtain ⟨fr, wd⟩ := s
    change (match fr.lookup x with | some v => v.get [] | none => .error .stuck) = _ at hx
    rw [hl] at hx
    cases hx
    exact hb
  | n + 1, .field e f, s, _, _, hI, hr, h => by
    obtain ⟨u₀, s₁, h₁, h₂⟩ := Eval.bind_done h
    obtain ⟨hg, -⟩ := Eval.ofExcept_done h₂
    have hr' := Role.step_ne hr
    exact Role.Bounds.step hr' (eval_roleIn n e hI hr' h₁) (Value.get_field_lt hg)
  | n + 1, .int _, _, _, _, _, hr, _ | n + 1, .bool _, _, _, _, _, hr, _
  | n + 1, .unit, _, _, _, _, hr, _ | n + 1, .record .., _, _, _, _, hr, _
  | n + 1, .variant .., _, _, _, _, hr, _ | n + 1, .list .., _, _, _, _, hr, _
  | n + 1, .op .., _, _, _, _, hr, _ | n + 1, .view _, _, _, _, _, hr, _
  | n + 1, .index .., _, _, _, _, hr, _ | n + 1, .fnRef .., _, _, _, _, hr, _
  | n + 1, .method .., _, _, _, _, hr, _ | n + 1, .closure .., _, _, _, _, hr, _
  | n + 1, .call .., _, _, _, _, hr, _ | n + 1, .letIn .., _, _, _, _, hr, _
  | n + 1, .varIn .., _, _, _, _, hr, _ | n + 1, .assign .., _, _, _, _, hr, _
  | n + 1, .seq .., _, _, _, _, hr, _ | n + 1, .if .., _, _, _, _, hr, _
  | n + 1, .match .., _, _, _, _, hr, _ | n + 1, .for .., _, _, _, _, hr, _
  | n + 1, .raise _, _, _, _, _, hr, _ | n + 1, .try _, _, _, _, _, hr, _
  | n + 1, .tryCatch .., _, _, _, _, hr, _ | n + 1, .while .., _, _, _, _, hr, _
  | n + 1, .loop _, _, _, _, _, hr, _ | n + 1, .break, _, _, _, _, hr, _
  | n + 1, .continue, _, _, _, _, hr, _ | n + 1, .return _, _, _, _, _, hr, _
  | n + 1, .perform .., _, _, _, _, hr, _ | n + 1, .withH .., _, _, _, _, hr, _
  | n + 1, .held .., _, _, _, _, hr, _ => absurd rfl hr

/-- What an expression gives, its role bounds. -/
theorem roleIn_bounds {D : Decls} {w : WriteBack} {e : Expr} {s s' : Copy.State} {u : Value}
    (hI : R.Inv s.1 m) (hd : ∃ N, ∀ n, N ≤ n → eval D (Copy.memoryWith w) n e s = .done u s') :
    (e.roleIn R).Bounds (sizeOf u) m := by
  by_cases hr : e.roleIn R = .other
  · rw [hr]; trivial
  · obtain ⟨N, hN⟩ := hd
    exact eval_roleIn N e hI hr (hN N (Nat.le_refl _))

/-- A self-call that descends passes, at the descending position, a value smaller than `m`,
the size of the value its caller's descending parameter holds. -/
theorem args_descend {D : Decls} {w : WriteBack} (n : Nat) :
    ∀ (k : Nat) (args : List Arg) {s s' : Copy.State} {passed : List Passed}, R.Inv s.1 m →
      R.Avoids (argsWrites args) → argPart R k args = true →
      Eval.args (eval D (Copy.memoryWith w) n) args s = .done passed s' → Passed.sizeAt passed k < m
  | 0, .value e :: args, s, _, _, hI, _, hp, h => by
    obtain ⟨u, s₁, h₁, h₂⟩ := Eval.bind_done h
    obtain ⟨vs, s₂, -, h₃⟩ := Eval.bind_done h₂
    cases h₃
    have hr : e.roleIn R = .part := by simpa [argPart] using hp
    have := eval_roleIn n e hI (by rw [hr]; exact nofun) h₁
    rw [hr] at this
    cases e <;> exact this
  | k + 1, .value e :: args, s, _, _, hI, hA, hp, h => by
    obtain ⟨u, s₁, h₁, h₂⟩ := Eval.bind_done h
    obtain ⟨vs, s₂, h₃, h₄⟩ := Eval.bind_done h₂
    cases h₄
    have hA' : R.Avoids (argsWrites args) := hA.mono (List.subset_append_right _ _)
    have hI₁ : R.Inv s₁.1 m := hI.evalAt (hA.mono (List.subset_append_left _ _)) h₁
    simpa [Passed.sizeAt] using args_descend n k args hI₁ hA' (by simpa [argPart] using hp) h₃
  | k + 1, .inout ⟨x, ps⟩ :: args, s, _, _, hI, hA, hp, h => by
    obtain ⟨p, s₁, h₁, h₂⟩ := Eval.bind_done h
    obtain ⟨vs, s₂, h₃, h₄⟩ := Eval.bind_done h₂
    cases h₄
    have hk := Eval.Keeps.path (W := pathWrites ps) (L := pathResizes ps) (eval_keeps D w n) ps
      (List.Subset.refl _) (List.Subset.refl _) s
    rw [h₁] at hk
    have hA₁ : R.Avoids (pathWrites ps) := hA.mono fun z hz =>
      List.mem_cons_of_mem _ (List.mem_append_left _ hz)
    have hA' : R.Avoids (argsWrites args) := hA.mono fun z hz =>
      List.mem_cons_of_mem _ (List.mem_append_right _ hz)
    simpa [Passed.sizeAt] using
      args_descend n k args (hI.keep hA₁ hk.2) hA' (by simpa [argPart] using hp) h₃
  | 0, .inout _ :: _, _, _, _, _, _, hp, _ | 0, [], _, _, _, _, _, hp, _
  | _ + 1, [], _, _, _, _, _, hp, _ => by simp [argPart] at hp

/-! ## A call's descending parameter -/

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
      bound.map Prod.fst = params.map Param.name ∧ ∀ k p, params[k]? = some p → p.mode = .let →
        ∃ a u, (p.name, a) ∈ bound ∧ (a = .value u ∨ ∃ z, a = .moved z u) ∧
          sizeOf u = Passed.sizeAt passed k
  | [], [], _, h => by cases h; exact ⟨rfl, fun _ _ hp => by simp at hp⟩
  | p :: ps, a :: as, bound, h => by
    simp only [bindArgs] at h
    have key : ∀ rest, bindArgs ps as = some rest → bound = (p.name, a) :: rest →
        bound.map Prod.fst = (p :: ps).map Param.name ∧ ∀ k q, (p :: ps)[k]? = some q →
          q.mode = .let → ∃ a' u, (q.name, a') ∈ bound ∧ (a' = .value u ∨ ∃ z, a' = .moved z u) ∧
            sizeOf u = Passed.sizeAt (a :: as) k := by
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
        exact ⟨a', u, List.mem_cons_of_mem _ hm, ha, by simpa [Passed.sizeAt] using hs⟩
    cases hpm : p.mode <;> rw [hpm] at h <;> cases a <;> simp only [reduceCtorEq] at h <;>
      (try split at h) <;>
      first
        | (obtain ⟨rest, hr, rfl⟩ := Option.map_eq_some_iff.1 h; exact key rest hr rfl)
        | cases h
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [bindArgs] at h

/-- A call's frame meets the roles its body starts with, against the size of what its
argument at the descending position passes. -/
theorem enter_roles {d : FnDecl} {k : Nat} {passed : List Passed} {bound : List (Name × Passed)}
    {caller callee : Copy.Frame} (hb : bindArgs d.params passed = some bound)
    (he : Copy.enter caller [] bound = .ok callee) :
    (d.entryRoles k).Inv callee (Passed.sizeAt passed k) := by
  unfold FnDecl.entryRoles
  split
  · rename_i p hp
    split
    · rename_i hc
      obtain ⟨hmode, hnd, -⟩ := hc
      obtain ⟨hn, hk⟩ := bindArgs_spec hb
      obtain ⟨a, u, hm, ha, hs⟩ := hk k p hp hmode
      intro x hx
      simp only [Roles.of_cons] at hx ⊢
      split at hx
      · subst_vars
        refine ⟨u, Copy.enter_lookup bound he (hn ▸ hnd) hm ha, ?_⟩
        simp only [↓reduceIte]
        exact Nat.le_of_eq hs
      · exact absurd rfl hx
    · exact Roles.Inv.nil _ _
  · exact Roles.Inv.nil _ _

/-- The roles a body starts with avoid what it writes. -/
theorem entryRoles_avoids (d : FnDecl) (k : Nat) : (d.entryRoles k).Avoids d.body.writes := by
  unfold FnDecl.entryRoles
  split
  · split
    · rename_i hc
      exact (Roles.Avoids.nil _).cons fun _ => hc.2.2
    · exact Roles.Avoids.nil _
  · exact Roles.Avoids.nil _

end Stilt
