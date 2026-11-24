import Stilt.Windows.Steps

/-!
# Scalars read alike

A window reads a string or a list, sliced: never an integer or a Boolean. So a value of windows
whose reading is an integer or a Boolean is that integer or Boolean, and an index or a condition
is the same in both models.
-/

namespace Stilt

namespace Windows

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

theorem viewable_view {v w : Value} {a b : Int} (hv : viewable v = true)
    (h : Op.view.apply [v, .int a, .int b] = .ok w) : viewable w = true := by
  cases v with
  | str s =>
    have hm : [Value.str s, .int a, .int b].mapM Value.scalar? =
        some [Scalar.str s, .int a, .int b] := rfl
    simp only [Op.apply, Op.applyScalars, hm, Op.compute] at h
    cases hs : Str.slice s a b with
    | error _ => rw [hs] at h; cases h
    | ok t => rw [hs] at h; cases h; rfl
  | list xs =>
    simp only [Op.apply, ListOp.apply, onList, Value.list?] at h
    split at h
    · cases h; rfl
    · cases h
  | _ => simp [viewable] at hv

theorem viewable_slices {v w : Value} (hv : viewable v = true) :
    ∀ ranges : List (Int × Int),
      ranges.foldlM (fun v r => Op.view.apply [v, .int r.1, .int r.2]) v = .ok w →
        viewable w = true := by
  intro ranges
  induction ranges generalizing v with
  | nil => intro h; cases h; exact hv
  | cons r rs ih =>
    intro h
    simp only [List.foldlM_cons] at h
    cases hu : Op.view.apply [v, .int r.1, .int r.2] with
    | error _ => rw [hu] at h; cases h
    | ok u => rw [hu] at h; exact ih (viewable_view hv hu) h

/-- What a window that holds reads is a string or a list. -/
theorem Holds.viewable_part {sw : List (Option Value)} {si : List Value} {w : Window}
    (h : Holds sw si w) {d : Value} (hd : partIn si w.1 w.2.1 w.2.2 = .ok d) : viewable d = true := by
  obtain ⟨d₀, -, h₂, -, h₄⟩ := h
  rw [partIn_eq_region, h₂] at hd
  exact viewable_slices h₄ _ hd

/-- A value of windows read as an integer is that integer; one that is an integer reads as it. -/
theorem VRel.int {si : List Value} {sw : List (Option Value)} {w v : Value}
    (h : VRel si sw w v) (k : Int) : v = .int k ↔ w = .int k := by
  obtain ⟨hr, hh⟩ := h
  cases w with
  | window l p r =>
    have := (hh _ List.mem_cons_self).viewable_part hr
    constructor
    · rintro rfl; simp [viewable] at this
    · intro h; cases h
  | int k' => simp only [resolveIn, mapWindows] at hr; cases hr; rfl
  | list vs =>
    obtain ⟨_, -, rfl⟩ := mapWindows_list.1 hr
    simp
  | record R fs =>
    obtain ⟨_, -, rfl⟩ := mapWindows_record.1 hr
    simp
  | variant T C vs =>
    obtain ⟨_, -, rfl⟩ := mapWindows_variant.1 hr
    simp
  | _ => simp only [resolveIn, mapWindows] at hr; cases hr; simp

theorem VRel.bool {si : List Value} {sw : List (Option Value)} {w v : Value}
    (h : VRel si sw w v) (b : Bool) : v = .bool b ↔ w = .bool b := by
  obtain ⟨hr, hh⟩ := h
  cases w with
  | window l p r =>
    have := (hh _ List.mem_cons_self).viewable_part hr
    constructor
    · rintro rfl; simp [viewable] at this
    · intro h; cases h
  | bool b' => simp only [resolveIn, mapWindows] at hr; cases hr; rfl
  | list vs =>
    obtain ⟨_, -, rfl⟩ := mapWindows_list.1 hr
    simp
  | record R fs =>
    obtain ⟨_, -, rfl⟩ := mapWindows_record.1 hr
    simp
  | variant T C vs =>
    obtain ⟨_, -, rfl⟩ := mapWindows_variant.1 hr
    simp
  | _ => simp only [resolveIn, mapWindows] at hr; cases hr; simp

/-- An integer read alike. -/
theorem SimP.asInt {Q : IState → WState → Prop} {v w : Value}
    (hQ : ∀ si sw, Q si sw → VRel si.1.store sw.1.store w v) :
    SimP D c pend Q Same (Eval.asInt v) (Eval.asInt w) := by
  intro si sw hp hg hq
  have h := hQ si sw hq
  by_cases hk : ∃ k, v = .int k
  · obtain ⟨k, rfl⟩ := hk
    rw [(h.int k).1 rfl]
    exact ⟨hp, rfl, rfl⟩
  · have hw : ∀ k, w ≠ .int k := fun k hw => hk ⟨k, (h.int k).2 hw⟩
    have h₁ : Eval.asInt (σ := IState) v = Eval.fail .stuck := by
      cases v <;> first | rfl | exact absurd ⟨_, rfl⟩ hk
    have h₂ : Eval.asInt (σ := WState) w = Eval.fail .stuck := by
      cases w <;> first | rfl | exact absurd rfl (hw _)
    rw [h₁, h₂]
    exact CorrG.fault hp _

/-- A Boolean read alike. -/
theorem SimP.asBool {Q : IState → WState → Prop} {v w : Value}
    (hQ : ∀ si sw, Q si sw → VRel si.1.store sw.1.store w v) :
    SimP D c pend Q Same (Eval.asBool v) (Eval.asBool w) := by
  intro si sw hp hg hq
  have h := hQ si sw hq
  by_cases hk : ∃ b, v = .bool b
  · obtain ⟨b, rfl⟩ := hk
    rw [(h.bool b).1 rfl]
    exact ⟨hp, rfl, rfl⟩
  · have hw : ∀ b, w ≠ .bool b := fun b hw => hk ⟨b, (h.bool b).2 hw⟩
    have h₁ : Eval.asBool (σ := IState) v = Eval.fail .stuck := by
      cases v <;> first | rfl | exact absurd ⟨_, rfl⟩ hk
    have h₂ : Eval.asBool (σ := WState) w = Eval.fail .stuck := by
      cases w <;> first | rfl | exact absurd rfl (hw _)
    rw [h₁, h₂]
    exact CorrG.fault hp _

end Windows

end Stilt
