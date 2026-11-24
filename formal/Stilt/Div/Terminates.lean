import Stilt.Div.Check
import Stilt.Div.Fuel

/-!
# Checked programs end

`DescentTerminates` (facts.descending-self-calls and facts.without-div): in a program whose every body
passes the check of facts.descending-self-calls, every call ends, for some fuel, with a value.

The proof goes by induction on the function's index, since a body calls only
earlier functions and itself, and then on the size of the value in its
descending parameter's position, since a self-call passes a strict part of
it. Through a body, the roles that the check follows bound the sizes of the
variables' values: the parameter itself is no larger than the call's value,
and a strict part is smaller (`Inv`).
-/

namespace Stilt.Div

/-- The roles of `R` bound the sizes of `ρ`'s values against `v`. -/
def Inv (R : List Role) (ρ : List Val) (v : Val) : Prop :=
  ∀ y, (roleOf R y = .whole → (ρ.getD y dflt).size ≤ v.size) ∧
    (roleOf R y = .part → (ρ.getD y dflt).size < v.size)

theorem roleOf_roles (a k y : Nat) :
    roleOf (roles a k) y = if y < a then (if y = k then .whole else .other) else .other := by
  by_cases hy : y < a
  · simp [roleOf, roles, List.getD_eq_getElem?_getD, hy]
  · simp [roleOf, roles, List.getD_eq_getElem?_getD, hy]

/-- A call's own arguments meet the roles its body starts with. -/
theorem inv_roles (a k : Nat) (vs : List Val) : Inv (roles a k) vs (vs.getD k dflt) := by
  intro y
  rw [roleOf_roles]
  by_cases hy : y < a
  · by_cases hk : y = k
    · subst hk; simp [hy]
    · simp [hy, hk]
  · simp [hy]

/-- Matching a node binds its two parts, which are strict parts when the node
is the parameter or a strict part of it. -/
theorem inv_case {R : List Role} {ρ : List Val} {v l r : Val} {i : Nat}
    (hinv : Inv R ρ v) (hnode : ρ.getD i dflt = .node l r) :
    Inv (partOf (roleOf R i) :: partOf (roleOf R i) :: R) (l :: r :: ρ) v := by
  have hsmall : roleOf R i ≠ .other → l.size < v.size ∧ r.size < v.size := by
    intro hne
    have hsz : (ρ.getD i dflt).size ≤ v.size := by
      cases hr : roleOf R i with
      | other => exact absurd hr hne
      | whole => exact (hinv i).1 hr
      | part => exact Nat.le_of_lt ((hinv i).2 hr)
    rw [hnode] at hsz
    simp only [Val.size] at hsz
    omega
  generalize hq : roleOf R i = q at hsmall
  intro y
  rcases y with _ | _ | y
  · simp only [roleOf, List.getD_cons_zero]
    cases q with
    | other => simp [partOf]
    | whole => simpa [partOf] using (hsmall (by simp)).1
    | part => simpa [partOf] using (hsmall (by simp)).1
  · simp only [roleOf, List.getD_cons_succ, List.getD_cons_zero]
    cases q with
    | other => simp [partOf]
    | whole => simpa [partOf] using (hsmall (by simp)).2
    | part => simpa [partOf] using (hsmall (by simp)).2
  · simpa only [roleOf, List.getD_cons_succ] using hinv y

/-- The argument at a descending position holds a strict part. -/
theorem argPart_small {P : Prog} {R : List Role} {ρ : List Val} {v : Val} (hinv : Inv R ρ v) :
    ∀ k as n vs, argPart R k as = true → evalArgs P n ρ as = some vs →
      (vs.getD k dflt).size < v.size
  | 0, .cons (.var y) rest, n + 1, vs, hp, h => by
      simp only [evalArgs, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨w, hw, ws, _, he⟩ := h
      cases n with
      | zero => simp [eval] at hw
      | succ n =>
          simp only [eval, Option.some.injEq] at hw
          simp only [Option.some.injEq] at he
          subst he; subst hw
          simp only [argPart, beq_iff_eq] at hp
          simpa using (hinv y).2 hp
  | j + 1, .cons e rest, n + 1, vs, hp, h => by
      simp only [evalArgs, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨w, _, ws, hws, he⟩ := h
      simp only [Option.some.injEq] at he
      subst he
      simpa using argPart_small hinv j rest n ws (by simpa [argPart] using hp) hws
  | 0, .nil, _, _, hp, _ => by simp [argPart] at hp
  | 0, .cons (.num _) _, _, _, hp, _ => by simp [argPart] at hp
  | 0, .cons (.add _ _) _, _, _, hp, _ => by simp [argPart] at hp
  | 0, .cons .leaf _, _, _, hp, _ => by simp [argPart] at hp
  | 0, .cons (.node _ _) _, _, _, hp, _ => by simp [argPart] at hp
  | 0, .cons (.case _ _ _) _, _, _, hp, _ => by simp [argPart] at hp
  | 0, .cons (.call _ _) _, _, _, hp, _ => by simp [argPart] at hp
  | _ + 1, .nil, _, _, hp, _ => by simp [argPart] at hp
  | _, .cons _ _, 0, _, _, h => by simp [evalArgs] at h

/-- Two results with their fuels hold together at the larger fuel. -/
theorem both {P : Prog} {ρ : List Val} {a b : Expr} {n₁ n₂ x y}
    (ha : eval P n₁ ρ a = some x) (hb : eval P n₂ ρ b = some y) :
    eval P (max n₁ n₂) ρ a = some x ∧ eval P (max n₁ n₂) ρ b = some y :=
  ⟨eval_mono P _ _ _ _ _ (Nat.le_max_left _ _) ha,
   eval_mono P _ _ _ _ _ (Nat.le_max_right _ _) hb⟩

mutual
/-- A checked body ends, given that the calls it may make end. -/
theorem body_ends (P : Prog) (f k : Nat) (v : Val)
    (IHlt : ∀ g < f, ∀ ws, ∃ n w, evalCall P n g ws = some w)
    (IHself : ∀ ws, (ws.getD k dflt).size < v.size → ∃ n w, evalCall P n f ws = some w) :
    ∀ e R ρ, ok f k R e = true → Inv R ρ v → ∃ n w, eval P n ρ e = some w
  | .var i, _, ρ, _, _ => ⟨1, ρ.getD i dflt, by simp [eval]⟩
  | .num z, _, _, _, _ => ⟨1, .num z, by simp [eval]⟩
  | .leaf, _, _, _, _ => ⟨1, .leaf, by simp [eval]⟩
  | .add a b, R, ρ, hok, hinv => by
      simp only [ok, Bool.and_eq_true] at hok
      obtain ⟨n₁, x, hx⟩ := body_ends P f k v IHlt IHself a R ρ hok.1 hinv
      obtain ⟨n₂, y, hy⟩ := body_ends P f k v IHlt IHself b R ρ hok.2 hinv
      obtain ⟨hx', hy'⟩ := both hx hy
      exact ⟨max n₁ n₂ + 1, plus x y, by simp [eval, hx', hy']⟩
  | .node a b, R, ρ, hok, hinv => by
      simp only [ok, Bool.and_eq_true] at hok
      obtain ⟨n₁, x, hx⟩ := body_ends P f k v IHlt IHself a R ρ hok.1 hinv
      obtain ⟨n₂, y, hy⟩ := body_ends P f k v IHlt IHself b R ρ hok.2 hinv
      obtain ⟨hx', hy'⟩ := both hx hy
      exact ⟨max n₁ n₂ + 1, .node x y, by simp [eval, hx', hy']⟩
  | .case i e₁ e₂, R, ρ, hok, hinv => by
      simp only [ok, Bool.and_eq_true] at hok
      cases hv : ρ.getD i dflt with
      | node l r =>
          obtain ⟨n, w, hw⟩ := body_ends P f k v IHlt IHself e₂ _ (l :: r :: ρ) hok.2 (inv_case hinv hv)
          exact ⟨n + 1, w, by simp only [eval]; rw [hv]; exact hw⟩
      | num z =>
          obtain ⟨n, w, hw⟩ := body_ends P f k v IHlt IHself e₁ R ρ hok.1 hinv
          exact ⟨n + 1, w, by simp only [eval]; rw [hv]; exact hw⟩
      | leaf =>
          obtain ⟨n, w, hw⟩ := body_ends P f k v IHlt IHself e₁ R ρ hok.1 hinv
          exact ⟨n + 1, w, by simp only [eval]; rw [hv]; exact hw⟩
  | .call g as, R, ρ, hok, hinv => by
      simp only [ok, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
      obtain ⟨n₁, ws, hws⟩ := args_end P f k v IHlt IHself as R ρ hok.1 hinv
      have hcall : ∃ n w, evalCall P n g ws = some w := by
        rcases hok.2 with hlt | ⟨rfl, hp⟩
        · exact IHlt g hlt ws
        · exact IHself ws (argPart_small hinv k as n₁ ws hp hws)
      obtain ⟨n₂, w, hw⟩ := hcall
      simp only [evalCall, Option.bind_eq_bind, Option.bind_eq_some_iff] at hw
      obtain ⟨fn, hfn, hb⟩ := hw
      refine ⟨max n₁ n₂ + 1, w, ?_⟩
      have hws' := evalArgs_mono P _ _ _ _ _ (Nat.le_max_left n₁ n₂) hws
      have hb' := eval_mono P _ _ _ _ _ (Nat.le_max_right n₁ n₂) hb
      simp [eval, hws', hfn, hb']

/-- Checked arguments end, given that the calls they may make end. -/
theorem args_end (P : Prog) (f k : Nat) (v : Val)
    (IHlt : ∀ g < f, ∀ ws, ∃ n w, evalCall P n g ws = some w)
    (IHself : ∀ ws, (ws.getD k dflt).size < v.size → ∃ n w, evalCall P n f ws = some w) :
    ∀ as R ρ, okArgs f k R as = true → Inv R ρ v →
    ∃ n ws, evalArgs P n ρ as = some ws
  | .nil, _, _, _, _ => ⟨1, [], by simp [evalArgs]⟩
  | .cons e as, R, ρ, hok, hinv => by
      simp only [okArgs, Bool.and_eq_true] at hok
      obtain ⟨n₁, x, hx⟩ := body_ends P f k v IHlt IHself e R ρ hok.1 hinv
      obtain ⟨n₂, ws, hws⟩ := args_end P f k v IHlt IHself as R ρ hok.2 hinv
      have hx' := eval_mono P _ _ _ _ _ (Nat.le_max_left n₁ n₂) hx
      have hws' := evalArgs_mono P _ _ _ _ _ (Nat.le_max_right n₁ n₂) hws
      exact ⟨max n₁ n₂ + 1, x :: ws, by simp [evalArgs, hx', hws']⟩
end


/-- `DescentTerminates`: every call of a checked program ends with a value,
for some fuel (facts.descending-self-calls and facts.without-div). -/
theorem descentTerminates (P : Prog) (hP : Checked P) :
    ∀ f, f < P.length → ∀ vs, ∃ n w, evalCall P n f vs = some w := by
  intro f
  induction f using Nat.strongRecOn with
  | ind f IHf =>
    intro hf
    let fn := P[f]
    have hget : P[f]? = some fn := List.getElem?_eq_getElem hf
    have hlt : ∀ g < f, ∀ ws, ∃ n w, evalCall P n g ws = some w :=
      fun g hg ws => IHf g hg (Nat.lt_trans hg hf) ws
    suffices h : ∀ s vs, (vs.getD fn.desc dflt).size = s → ∃ n w, evalCall P n f vs = some w from
      fun vs => h _ vs rfl
    intro s
    induction s using Nat.strongRecOn with
    | ind s IHs =>
      intro vs hs
      have hself : ∀ ws, (ws.getD fn.desc dflt).size < (vs.getD fn.desc dflt).size →
          ∃ n w, evalCall P n f ws = some w :=
        fun ws hw => IHs _ (hs ▸ hw) ws rfl
      obtain ⟨n, w, hw⟩ := body_ends P f fn.desc (vs.getD fn.desc dflt) hlt hself fn.body
        (roles fn.arity fn.desc) vs (hP f hf) (inv_roles fn.arity fn.desc vs)
      exact ⟨n, w, by simp [evalCall, hget, hw]⟩

end Stilt.Div
