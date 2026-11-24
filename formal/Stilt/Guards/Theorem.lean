import Stilt.Guards.Soundness

/-!
# The theorems of guards

* `tryWays_first` and `select_first`: a `match` takes the first arm, and of its
  pattern's ways the first, whose guard is true, each earlier one tried and
  false (patterns.match and patterns.guards).
* `select_ok`: a well-typed `match` never goes wrong, and when it takes no arm,
  no arm without a guard matches the value.
* `exhaustive_covers`: when the check accepts the arms, an arm that counts, with
  no guard and no constant, matches every value of the type
  (patterns.guards-and-constants).
* `run_sound`: so a well-typed `match` that the check accepts ends with a value
  of its arms' type, never falling through.
* `let_sound` and `for_sound`: an irrefutable pattern in a `let` or a `for`
  head binds every value of its type (patterns.irrefutable-positions).
-/

namespace Stilt.Guards

/-- The way a guard takes is the first for which it is true. -/
theorem tryWays_first {ρ : Env} {g : Expr} : ∀ {ws : List Env} {w : Env} {out : List Val},
    tryWays ρ g ws = some (some w, out) → ∃ pre post, ws = pre ++ w :: post ∧
      (∃ o, eval (w ++ ρ) g = some (.bool true, o)) ∧
      ∀ u ∈ pre, ∃ o, eval (u ++ ρ) g = some (.bool false, o)
  | [], _, _, h => nomatch h
  | u :: ws, w, out, h => by
    simp only [tryWays] at h
    cases he : eval (u ++ ρ) g with
    | none => simp [he] at h
    | some vo =>
      obtain ⟨b, o⟩ := vo
      cases b with
      | bool b =>
        cases b with
        | true =>
          simp only [he, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨⟩, rfl⟩ := h
          exact ⟨[], ws, rfl, ⟨o, he⟩, by simp⟩
        | false =>
          simp only [he, Option.map_eq_some_iff] at h
          obtain ⟨⟨r, out'⟩, hr, hrr⟩ := h
          cases hrr
          obtain ⟨pre, post, rfl, ht, hf⟩ := tryWays_first hr
          refine ⟨u :: pre, post, rfl, ht, fun x hx => ?_⟩
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨o, he⟩
          · exact hf x hx
      | _ => simp [he] at h

/-- The arm a `match` takes is the first that takes the value. -/
theorem select_first {ρ : Env} {v : Val} : ∀ {arms : List Arm} {a : Arm} {w : Env} {out : List Val},
    select ρ arms v = some (some (a, w), out) → ∃ pre post, arms = pre ++ a :: post ∧
      (∃ o, a.take ρ v = some (some w, o)) ∧ ∀ b ∈ pre, ∃ o, b.take ρ v = some (none, o)
  | [], _, _, _, h => nomatch h
  | b :: arms, a, w, out, h => by
    simp only [select] at h
    cases he : b.take ρ v with
    | none => simp [he] at h
    | some ro =>
      obtain ⟨r, o⟩ := ro
      cases r with
      | some w' =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
        exact ⟨[], arms, rfl, ⟨o, he⟩, by simp⟩
      | none =>
        simp only [he, Option.map_eq_some_iff] at h
        obtain ⟨⟨r, out'⟩, hr, hrr⟩ := h
        cases hrr
        obtain ⟨pre, post, rfl, ht, hf⟩ := select_first hr
        refine ⟨b :: pre, post, rfl, ht, fun x hx => ?_⟩
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨o, he⟩
        · exact hf x hx

variable {Γ : Ctx} {ρ : Env}

/-- A well-typed guard, tried with ways that bind its pattern's names, never
goes wrong, and the way it takes is one of them. -/
theorem tryWays_ok {Δ : Ctx} {g : Expr} (hg : HasType (Δ ++ Γ) g .bool) (hρ : EnvOk ρ Γ) :
    ∀ {ws : List Env}, (∀ w ∈ ws, Agree w Δ) →
      ∃ r out, tryWays ρ g ws = some (r, out) ∧ ∀ w, r = some w → w ∈ ws
  | [], _ => ⟨none, [], rfl, fun _ h => nomatch h⟩
  | u :: ws, h => by
    obtain ⟨b, o, he, hb⟩ := eval_sound hg ((h u List.mem_cons_self).env hρ)
    cases hb
    rename_i b
    cases b
    · obtain ⟨r, out, hr, hm⟩ := tryWays_ok hg hρ fun w hw => h w (List.mem_cons_of_mem _ hw)
      exact ⟨r, o ++ out, by simp [tryWays, he, hr],
        fun w hw => List.mem_cons_of_mem _ (hm w hw)⟩
    · exact ⟨some u, o, by simp [tryWays, he], fun w hw => by cases hw; exact List.mem_cons_self⟩

/-- A well-typed arm never goes wrong on a value of its type; the way it takes
is one of its pattern's, and an arm without a guard takes none only when its
pattern doesn't match. -/
theorem take_ok {τ σ : Ty} {a : Arm} {v : Val} (ha : ArmTy Γ τ σ a) (hv : ValTy v τ)
    (hρ : EnvOk ρ Γ) : ∃ r out, a.take ρ v = some (r, out) ∧ (∀ w, r = some w → w ∈ a.pat.ways v) ∧
      (r = none → a.guard = none → a.pat.ways v = []) := by
  obtain ⟨Δ, hp, hg, _⟩ := ha
  unfold Arm.take
  cases hga : a.guard with
  | none =>
    refine ⟨_, [], rfl, fun w hw => List.mem_of_head? hw, fun h _ => ?_⟩
    exact List.head?_eq_none_iff.1 h
  | some g =>
    obtain ⟨r, out, hr, hm⟩ :=
      tryWays_ok (hg g hga) hρ fun w hw => Pat.ways_agree _ hp hv hw
    exact ⟨r, out, hr, hm, fun _ h => nomatch h⟩

/-- A well-typed `match` never goes wrong: it takes an arm, with one of its
pattern's ways, or none, when no arm without a guard matches. -/
theorem select_ok {τ σ : Ty} {v : Val} (hv : ValTy v τ) (hρ : EnvOk ρ Γ) :
    ∀ {arms : List Arm}, (∀ a ∈ arms, ArmTy Γ τ σ a) → ∃ r out, select ρ arms v = some (r, out) ∧
      (∀ a w, r = some (a, w) → a ∈ arms ∧ w ∈ a.pat.ways v) ∧
      (r = none → ∀ a ∈ arms, a.guard = none → ¬ Matches a.pat v)
  | [], _ => ⟨none, [], rfl, fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
  | a :: arms, h => by
    obtain ⟨r, out, hr, hm, hn⟩ := take_ok (h a List.mem_cons_self) hv hρ
    cases r with
    | some w =>
      refine ⟨some (a, w), out, by simp [select, hr], fun a' w' he => ?_, fun h => nomatch h⟩
      cases he
      exact ⟨List.mem_cons_self, hm w rfl⟩
    | none =>
      obtain ⟨r', out', hr', hm', hn'⟩ :=
        select_ok hv hρ (arms := arms) fun b hb => h b (List.mem_cons_of_mem _ hb)
      refine ⟨r', out ++ out', by simp [select, hr, hr'], fun b w he => ?_, fun he b hb hg => ?_⟩
      · obtain ⟨hb, hw⟩ := hm' b w he
        exact ⟨List.mem_cons_of_mem _ hb, hw⟩
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact fun hmt => hmt (hn rfl hg)
        · exact hn' he b hb hg

/-- An arm that counts has no guard. -/
theorem Arm.counts_guard {a : Arm} (h : a.counts = true) : a.guard = none := by
  simp only [Arm.counts, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact h.1

/-- When the check accepts the arms, an arm that counts matches every value of
the type. -/
theorem exhaustive_covers {arms : List Arm} {τ : Ty} {fuel : Nat} {v : Val}
    (h : exhaustive arms τ fuel = true) (hv : ValTy v τ) :
    ∃ a ∈ arms, a.counts = true ∧ Matches a.pat v := by
  obtain ⟨r, hr, hm⟩ := check_sound fuel h (.cons hv .nil)
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
  obtain ⟨ha, hc⟩ := List.mem_filter.1 ha
  exact ⟨a, ha, hc, (rowMatches_cons.1 hm).1⟩

/-- A well-typed `match` that the check accepts ends with a value of its arms'
type: it never falls through and never goes wrong. -/
theorem run_sound {τ σ : Ty} {arms : List Arm} {v : Val} {fuel : Nat}
    (harms : ∀ a ∈ arms, ArmTy Γ τ σ a) (hv : ValTy v τ) (hρ : EnvOk ρ Γ)
    (hex : exhaustive arms τ fuel = true) :
    ∃ r out, runMatch ρ v arms = .done r out ∧ ValTy r σ := by
  obtain ⟨r, out, hs, hm, hn⟩ := select_ok hv hρ harms
  cases r with
  | none =>
    obtain ⟨a, ha, hc, hmt⟩ := exhaustive_covers hex hv
    exact absurd hmt (hn rfl a ha (Arm.counts_guard hc))
  | some aw =>
    obtain ⟨a, w⟩ := aw
    obtain ⟨ha, hw⟩ := hm a w rfl
    obtain ⟨Δ, hp, _, hb⟩ := harms a ha
    obtain ⟨r, out', he, hr⟩ := eval_sound hb ((Pat.ways_agree _ hp hv hw).env hρ)
    exact ⟨r, out ++ out', by simp [runMatch, hs, he], hr⟩

/-- Without the check, a well-typed `match` still never goes wrong: it ends with
a value, or with no arm that takes the value. -/
theorem run_ok {τ σ : Ty} {arms : List Arm} {v : Val} (harms : ∀ a ∈ arms, ArmTy Γ τ σ a)
    (hv : ValTy v τ) (hρ : EnvOk ρ Γ) : runMatch ρ v arms ≠ .stuck := by
  obtain ⟨r, out, hs, hm, _⟩ := select_ok hv hρ harms
  cases r with
  | none => simp [runMatch, hs]
  | some aw =>
    obtain ⟨a, w⟩ := aw
    obtain ⟨ha, hw⟩ := hm a w rfl
    obtain ⟨Δ, hp, _, hb⟩ := harms a ha
    obtain ⟨r, out', he, _⟩ := eval_sound hb ((Pat.ways_agree _ hp hv hw).env hρ)
    simp [runMatch, hs, he]

/-- `let p = v` with an irrefutable pattern binds the value, and the rest of the
block ends with a value of its type. -/
theorem let_sound {p : Pat} {τ σ : Ty} {Δ : Ctx} {v : Val} {body : Expr} (hp : PatTy p τ Δ)
    (hi : p.irrefutable = true) (hv : ValTy v τ) (hb : HasType (Δ ++ Γ) body σ) (hρ : EnvOk ρ Γ) :
    ∃ r out, runLet ρ p v body = .done r out ∧ ValTy r σ := by
  have hm := Pat.irrefutable_matches p hp hi hv
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hm
  cases hh : (p.ways v).head? with
  | none => exact absurd (List.head?_eq_none_iff.1 hh) hm
  | some w =>
    obtain ⟨r, out, he, hr⟩ :=
      eval_sound hb ((Pat.ways_agree p hp hv (List.mem_of_head? hh)).env hρ)
    exact ⟨r, out, by simp [runLet, hh, he], hr⟩

/-- `for p in vs { body }` with an irrefutable pattern runs its body for every
element and ends with `()`. -/
theorem for_sound {p : Pat} {τ σ : Ty} {Δ : Ctx} {body : Expr} (hp : PatTy p τ Δ)
    (hi : p.irrefutable = true) (hb : HasType (Δ ++ Γ) body σ) (hρ : EnvOk ρ Γ) :
    ∀ {vs : List Val}, (∀ v ∈ vs, ValTy v τ) → ∃ out, runFor ρ p body vs = .done .unit out
  | [], _ => ⟨[], rfl⟩
  | v :: vs, h => by
    obtain ⟨r, out, hl, _⟩ := let_sound hp hi (h v List.mem_cons_self) hb hρ
    obtain ⟨out', hf⟩ := for_sound hp hi hb hρ fun u hu => h u (List.mem_cons_of_mem _ hu)
    exact ⟨out ++ out', by simp [runFor, hl, hf]⟩

end Stilt.Guards
