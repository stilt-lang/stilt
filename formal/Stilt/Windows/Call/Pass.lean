import Stilt.Windows.Call.Callee

/-!
# Passing the arguments

Once its arguments are evaluated, a call of the model of windows keeps each `let` argument for
its parameter's type and reads the others through (`passTo`), which changes no state. The
windows that remain are the arguments' own, which the call's sources track: each value
argument's `operandSources` (views.across-calls). While the call runs, the views its value
arguments pass are being read (`argViews`, E0423), so their windows and the waiting ones are
watched.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls}

/-- Windows reading the same region are tracked alike. -/
theorem Tracked.congr {env : List (Name × Ref)} {In : List (Name × Value)} {S : List Shape}
    {w w' : Window} (h : Tracked env In S w') (h₁ : w'.1 = w.1) (h₂ : w'.2.1 = w.2.1) :
    Tracked env In S w := by
  have href : w'.ref = w.ref := by simp [Window.ref, h₁, h₂]
  obtain ⟨s, hs, ⟨r, hr, q, hq, hpre⟩ | ⟨v, hv, w'', hw'', k₁, k₂⟩⟩ := h
  · exact ⟨s, hs, .inl ⟨r, hr, q, href ▸ hq, hpre⟩⟩
  · exact ⟨s, hs, .inr ⟨v, hv, w'', hw'', k₁.trans h₁, k₂.trans h₂⟩⟩

/-- A value argument's windows, tracked by its sources, are tracked by the sources the call
gives it (`operandSources`), in a scope the checks read. -/
theorem operand_tracked {Γ : ViewScope} (hΓ : ScopeKeeps D Γ) {e₀ : Expr}
    {env : List (Name × Ref)} {In : List (Name × Value)} {w : Window}
    (h : Tracked env In (e₀.sources D Γ) w) :
    Tracked env In (Γ.operandSources D e₀ (e₀.sources D Γ)) w := by
  have none_src : ∀ {S : List Shape}, S = [] → Tracked env In S w → False := by
    rintro _ rfl ⟨s, hs, -⟩
    cases hs
  unfold ViewScope.operandSources
  cases hp : e₀.place? with
  | none => exact h
  | some p =>
    cases e₀ with
    | var x | move x =>
      simp only [Expr.place?, Option.some.injEq] at hp
      subst hp
      simp only [Expr.sources] at h
      cases hb : Γ.lookup x with
      | none => exact absurd h (none_src (by simp [hb]))
      | some b =>
        simp only [hb, Option.map_some, Option.getD_some] at h
        refine h.sub (sources_sub_place hb ?_ [])
        rcases hty : b.type with _ | τ
        · exact .inl rfl
        · cases hv : τ.holdsView D
          · have hm := mem_of_lookup hb
            cases hpar : b.param
            · exact absurd h (none_src (hΓ.own (x, b) hm hpar τ hty hv))
            · exact absurd h (none_src (hΓ.given (x, b) hm hpar τ hty hv))
          · exact .inr ⟨τ, rfl, hv⟩
    | field e f => exact absurd h (none_src (by simp [Expr.sources]))
    | index e i => exact absurd h (none_src (by simp [Expr.sources]))
    | _ => simp [Expr.place?] at hp

namespace ArgsRel

variable {Γ : ViewScope} {In : List (Name × Value)} {si : IState} {sw : WState}

/-- The windows a value argument passes are tracked by the call's arguments' sources. -/
theorem trackedSources (hΓ : ScopeKeeps D Γ) : ∀ {args₀ : List Arg} {ps ps' : List Passed},
    ArgsRel D Γ In si sw args₀ ps ps' → ∀ a ∈ ps', ∀ w, a.value? = some w →
      ∀ win ∈ windowsOf w, Tracked sw.1.env In (argsSources D Γ args₀) win
  | _, _, _, .nil, _, ha, _, _, _, _ => nomatch ha
  | _, _, _, .value (e₀ := e₀) e _ _ ht h, a, ha, w, hw, win, hwin => by
    simp only [argsSources]
    rcases List.mem_cons.1 ha with rfl | ha
    · rw [value?_ofArg, Option.some.injEq] at hw
      subst hw
      exact (operand_tracked hΓ (ht win hwin)).sub fun s hs => List.mem_append_left _ hs
    · exact (trackedSources hΓ h a ha w hw win hwin).sub fun s hs => List.mem_append_right _ hs
  | _, _, _, .inout y _ h, a, ha, w, hw, win, hwin => by
    simp only [argsSources]
    rcases List.mem_cons.1 ha with rfl | ha
    · cases hw
    · exact (trackedSources hΓ h a ha w hw win hwin).sub fun s hs => List.mem_append_right _ hs

theorem passRel_cons {c : Ctx} (e : Expr) {v w : Value} {ps ps' : List Passed}
    (hv : VRel si.1.store sw.1.store w v) (hvv : v.Viewed D)
    (hw : ∀ win ∈ windowsOf w, Watched c.R sw.1.env win) (h : PassRel D c si sw ps ps') :
    PassRel D c si sw (Passed.ofArg e v :: ps) (Passed.ofArg e w :: ps') := by
  unfold Passed.ofArg
  split
  · exact .moved _ hv hvv hw h
  · exact .value hv hvv hw h

/-- Arguments evaluated alike are passed alike, in a context whose reads `R` don't overlap the
`inout` arguments and watch the windows the value arguments pass. -/
theorem passRel {c : Ctx} : ∀ {args₀ : List Arg} {ps ps' : List Passed},
    ArgsRel D Γ In si sw args₀ ps ps' → (inoutShapes args₀).all (unread c.R) = true →
    (∀ a ∈ ps', ∀ w, a.value? = some w → ∀ win ∈ windowsOf w, Watched c.R sw.1.env win) →
    PassRel D c si sw ps ps'
  | _, _, _, .nil, _, _ => .nil
  | _, _, _, .value e hv hvv _ h, hu, hw =>
    passRel_cons e hv hvv (hw _ List.mem_cons_self _ (value?_ofArg e _))
      (passRel h (by simpa only [inoutShapes] using hu) fun a ha =>
        hw a (List.mem_cons_of_mem _ ha))
  | _, _, _, .inout x (ps₀ := ps₀) hres h, hu, hw => by
    simp only [inoutShapes, List.all_cons, Bool.and_eq_true] at hu
    exact .place x _ ps₀ hres hu.1 (passRel h hu.2 fun a ha => hw a (List.mem_cons_of_mem _ ha))

end ArgsRel

theorem bind_done_eq {σ α β : Type} {m : Eval σ α} {f : α → Eval σ β} {s : σ} {a : α}
    (h : m s = .done a s) : (m >>= f) s = f a s := by
  show (m s).bind (fun a s => f a s) = _
  rw [h]
  rfl

/-- What `passTo` gives, with no change of state: each value kept as it is, or read through to
the in-place one. -/
theorem passTo_done {c : Ctx} {si : IState} {sw : WState} :
    ∀ (params : List Param) {ps ps' : List Passed}, PassRel D c si sw ps ps' →
      ∃ ps₁, passTo D params ps' sw = .done ps₁ sw ∧ PassRel D c si sw ps ps₁ ∧
        KeptFor D params ps₁ ∧ ∀ a ∈ ps₁, ∀ w, a.value? = some w → ∀ win ∈ windowsOf w,
          ∃ a₀ ∈ ps', ∃ w₀, a₀.value? = some w₀ ∧ win ∈ windowsOf w₀
  | [], _, ps', h => ⟨ps', by cases h <;> rfl, h, fun _ _ _ hp => by simp at hp,
      fun a ha w hw win hwin => ⟨a, ha, w, hw, hwin⟩⟩
  | _ :: _, _, _, .nil => ⟨[], rfl, .nil, fun _ _ _ _ ha => by simp at ha, fun _ ha => by cases ha⟩
  | p :: params, _, _, .value hv hvv hw h => by
    obtain ⟨ps₁, hpt, hrel, hk, hsub⟩ := passTo_done params h
    obtain ⟨w₁, hkeep, hrel₁, hk₁, hsub₁⟩ := keep_done p hv hvv hw
    exact ⟨.value w₁ :: ps₁,
      by simp only [passTo]; rw [bind_done_eq hkeep, bind_done_eq hpt]; rfl,
      .value hrel₁.1 hvv hrel₁.2 hrel,
      kept_cons (fun w' hw' => by
        simp only [Passed.value?, Option.some.injEq] at hw'; exact hw' ▸ hk₁) hk,
      sub_cons (.value _) (fun w' hw' win hwin => ⟨_, rfl, hsub₁ win (by
        simp only [Passed.value?, Option.some.injEq] at hw'; exact hw' ▸ hwin)⟩) hsub⟩
  | p :: params, _, _, .moved x hv hvv hw h => by
    obtain ⟨ps₁, hpt, hrel, hk, hsub⟩ := passTo_done params h
    obtain ⟨w₁, hkeep, hrel₁, hk₁, hsub₁⟩ := keep_done p hv hvv hw
    exact ⟨.moved x w₁ :: ps₁,
      by simp only [passTo]; rw [bind_done_eq hkeep, bind_done_eq hpt]; rfl,
      .moved x hrel₁.1 hvv hrel₁.2 hrel,
      kept_cons (fun w' hw' => by
        simp only [Passed.value?, Option.some.injEq] at hw'; exact hw' ▸ hk₁) hk,
      sub_cons (.moved x _) (fun w' hw' win hwin => ⟨_, rfl, hsub₁ win (by
        simp only [Passed.value?, Option.some.injEq] at hw'; exact hw' ▸ hwin)⟩) hsub⟩
  | p :: params, _, _, .place x q ps₀ hres hu h => by
    obtain ⟨ps₁, hpt, hrel, hk, hsub⟩ := passTo_done params h
    exact ⟨.place x q :: ps₁, by simp only [passTo]; rw [bind_done_eq hpt]; rfl,
      .place x q ps₀ hres hu hrel,
      kept_cons (fun w hw => by cases hw) hk, sub_cons (.place x q) (fun w hw => by cases hw) hsub⟩
where
  keep_done (p : Param) {v w : Value} (hv : VRel si.1.store sw.1.store w v) (hvv : v.Viewed D)
      (hw : ∀ win ∈ windowsOf w, Watched c.R sw.1.env win) :
      ∃ w₁, keep D p.type w sw = .done w₁ sw ∧
        (VRel si.1.store sw.1.store w₁ v ∧ ∀ win ∈ windowsOf w₁, Watched c.R sw.1.env win) ∧
        (¬Free w₁ → keepsView D p.type = true) ∧ ∀ win ∈ windowsOf w₁, win ∈ windowsOf w := by
    unfold keep
    by_cases hk : keepsView D p.type = true
    · exact ⟨w, by simp [hk]; rfl, ⟨hv, hw⟩, fun _ => hk, fun _ h => h⟩
    · have hf := hvv.free
      refine ⟨v, ?_, ⟨VRel.free hf, fun _ h => absurd h (not_mem_of_free hf)⟩,
        fun h => absurd hf h, fun _ h => absurd h (not_mem_of_free hf)⟩
      simp only [hk, Bool.false_eq_true, ↓reduceIte]
      show Eval.ofExcept (resolve sw.1.store w) sw = _
      rw [hv.resolve]
      rfl
  kept_cons {p : Param} {params : List Param} {a : Passed} {ps₁ : List Passed}
      (h₁ : ∀ w, a.value? = some w → ¬Free w → keepsView D p.type = true)
      (h : KeptFor D params ps₁) : KeptFor D (p :: params) (a :: ps₁) := by
    intro i p' a' hp ha w hw hfw
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp ha
      subst hp ha
      exact h₁ w hw hfw
    | succ i => exact h i p' a' (by simpa using hp) (by simpa using ha) w hw hfw
  sub_cons {ps' ps₁ : List Passed} (a : Passed) {a₁ : Passed}
      (h₁ : ∀ w, a₁.value? = some w → ∀ win ∈ windowsOf w,
        ∃ w₀, a.value? = some w₀ ∧ win ∈ windowsOf w₀)
      (h : ∀ a ∈ ps₁, ∀ w, a.value? = some w → ∀ win ∈ windowsOf w,
        ∃ a₀ ∈ ps', ∃ w₀, a₀.value? = some w₀ ∧ win ∈ windowsOf w₀) :
      ∀ b ∈ a₁ :: ps₁, ∀ w, b.value? = some w → ∀ win ∈ windowsOf w,
        ∃ a₀ ∈ a :: ps', ∃ w₀, a₀.value? = some w₀ ∧ win ∈ windowsOf w₀ := by
    intro b hb w hw win hwin
    rcases List.mem_cons.1 hb with rfl | hb
    · obtain ⟨w₀, h₀, hm⟩ := h₁ w hw win hwin
      exact ⟨a, List.mem_cons_self, w₀, h₀, hm⟩
    · obtain ⟨a₀, ha₀, w₀, h₀, hm⟩ := h b hb w hw win hwin
      exact ⟨a₀, List.mem_cons_of_mem _ ha₀, w₀, h₀, hm⟩

end Windows

end Stilt
