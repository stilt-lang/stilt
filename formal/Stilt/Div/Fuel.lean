import Stilt.Div.Syntax

/-!
# Fuel

More fuel never changes a result that some fuel gives, so the fuels that the
parts of an expression need combine into one.
-/

namespace Stilt.Div

mutual
theorem eval_mono (P : Prog) :
    ∀ n m ρ e v, n ≤ m → eval P n ρ e = some v → eval P m ρ e = some v
  | 0, _, _, _, _, _, h => by simp [eval] at h
  | n + 1, m + 1, ρ, e, v, hle, h => by
      have hnm : n ≤ m := Nat.le_of_succ_le_succ hle
      cases e with
      | var i => simpa [eval] using h
      | num k => simpa [eval] using h
      | leaf => simpa [eval] using h
      | add a b =>
          simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
          obtain ⟨x, hx, y, hy, he⟩ := h
          exact ⟨x, eval_mono P n m ρ a x hnm hx, y, eval_mono P n m ρ b y hnm hy, he⟩
      | node a b =>
          simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
          obtain ⟨x, hx, y, hy, he⟩ := h
          exact ⟨x, eval_mono P n m ρ a x hnm hx, y, eval_mono P n m ρ b y hnm hy, he⟩
      | case i e₁ e₂ =>
          simp only [eval] at h ⊢
          split at h <;> simp_all <;> exact eval_mono P n m _ _ v hnm h
      | call f as =>
          simp only [eval, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
          obtain ⟨vs, hvs, fn, hfn, hb⟩ := h
          exact ⟨vs, evalArgs_mono P n m ρ as vs hnm hvs, fn, hfn,
            eval_mono P n m vs fn.body v hnm hb⟩
  | _ + 1, 0, _, _, _, hle, _ => absurd hle (by omega)

theorem evalArgs_mono (P : Prog) :
    ∀ n m ρ as vs, n ≤ m → evalArgs P n ρ as = some vs → evalArgs P m ρ as = some vs
  | 0, _, _, _, _, _, h => by simp [evalArgs] at h
  | n + 1, m + 1, ρ, as, vs, hle, h => by
      have hnm : n ≤ m := Nat.le_of_succ_le_succ hle
      cases as with
      | nil => simpa [evalArgs] using h
      | cons e as =>
          simp only [evalArgs, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
          obtain ⟨v, hv, ws, hws, he⟩ := h
          exact ⟨v, eval_mono P n m ρ e v hnm hv, ws, evalArgs_mono P n m ρ as ws hnm hws, he⟩
  | _ + 1, 0, _, _, _, hle, _ => absurd hle (by omega)
end

theorem evalCall_mono {P : Prog} {n m f vs v} (hle : n ≤ m)
    (h : evalCall P n f vs = some v) : evalCall P m f vs = some v := by
  simp only [evalCall, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨fn, hfn, hb⟩ := h
  exact ⟨fn, hfn, eval_mono P n m vs fn.body v hle hb⟩

end Stilt.Div
