import Stilt.Windows.Read
import Stilt.Windows.Through.Parts
import Stilt.Windows.Scalars

/-!
# Narrowing a view

A value read along a path with no window met before its end reads alike through windows
(`getW_of_get`), and holds only windows of the value (`windowsOf_get`). Narrowing a view by its
offsets (`narrow`) fails as `View.of` of the in-place operands fails, or gives a value read as
that one gives, whose windows read the regions of the view's (`narrow_rel`;
views.making-view).
-/

namespace Stilt

namespace Windows

variable {sw : List (Option Value)} {si : List Value}

/-! ## Reading with no window on the way -/

/-- A path read with no window met before its end reads alike through windows. -/
theorem getW_of_get {z : Value} : ∀ (v : Value) (p : Path), v.get p = .ok z → getW sw v p = .ok z
  | v, [], h => by cases v <;> exact h
  | .record R fs, .field f :: p, h => by
    simp only [Value.get] at h
    simp only [getW]
    cases hl : fs.lookup f with
    | none => simp [hl] at h
    | some v => simp only [hl] at h ⊢; exact getW_of_get v p h
  | .list vs, .index i :: p, h => by
    simp only [Value.get] at h
    simp only [getW]
    cases hl : elemAt? vs i with
    | none => simp [hl] at h
    | some v => simp only [hl] at h ⊢; exact getW_of_get v p h
  | .window .., _ :: _, h | .record _ _, .index _ :: _, h | .list _, .field _ :: _, h
  | .int _, _ :: _, h | .float _, _ :: _, h | .bool _, _ :: _, h | .str _, _ :: _, h
  | .unit, _ :: _, h | .variant .., _ :: _, h | .closure .., _ :: _, h
  | .function .., _ :: _, h | .handle .., _ :: _, h => by simp [Value.get] at h

/-- A part of a value holds only windows of the value. -/
theorem windowsOf_get {z : Value} : ∀ (v : Value) (p : Path), v.get p = .ok z →
    ∀ w ∈ windowsOf z, w ∈ windowsOf v
  | v, [], h => by
    have : v = z := by cases v <;> exact Except.ok.inj h
    subst this
    exact fun _ hw => hw
  | .record R fs, .field f :: p, h => by
    simp only [Value.get] at h
    cases hl : fs.lookup f with
    | none => simp [hl] at h
    | some v =>
      simp only [hl] at h
      exact fun w hw => by
        simp only [windowsOf]; exact windowsOf_lookup hl (windowsOf_get v p h w hw)
  | .list vs, .index i :: p, h => by
    simp only [Value.get] at h
    cases hl : elemAt? vs i with
    | none => simp [hl] at h
    | some v =>
      simp only [hl] at h
      exact fun w hw => by
        simp only [windowsOf]; exact windowsOf_elemAt? hl (windowsOf_get v p h w hw)
  | .window .., _ :: _, h | .record _ _, .index _ :: _, h | .list _, .field _ :: _, h
  | .int _, _ :: _, h | .float _, _ :: _, h | .bool _, _ :: _, h | .str _, _ :: _, h
  | .unit, _ :: _, h | .variant .., _ :: _, h | .closure .., _ :: _, h
  | .function .., _ :: _, h | .handle .., _ :: _, h => by simp [Value.get] at h

/-! ## What a window reads -/

/-- A window holds whatever its ranges: its region is the same. -/
theorem Holds.ranges {l : Nat} {p : Path} {r r' : List (Int × Int)} (h : Holds sw si (l, p, r)) :
    Holds sw si (l, p, r') := by
  obtain ⟨d, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨d, h₁, h₂, h₃, h₄⟩

/-! ## Narrowing -/

theorem narrow_window_other {l : Nat} {p : Path} {r : List (Int × Int)} {ns : List Value}
    (h0 : ns ≠ []) (h2 : ∀ a b, ns ≠ [.int a, .int b]) :
    narrow sw (.window l p r) ns = .error .stuck := by
  rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exact absurd rfl h0
  · cases a <;> rfl
  · cases a <;> cases b <;> first | rfl | exact absurd rfl (h2 _ _)
  · cases a <;> cases b <;> rfl

theorem narrow_other {w : Value} (hw : ∀ l p r, w ≠ .window l p r) (ns : List Value) :
    narrow sw w ns = Op.view.apply (w :: ns) := by
  cases w <;> first | exact absurd rfl (hw _ _ _) | rfl

/-- Offsets read against the in-place store as two integers are those integers, when their
windows hold. -/
theorem ints_of_resolve {ns : List Value} {a b : Int}
    (hns : mapWindowsValues (partIn si) ns = .ok [.int a, .int b])
    (hh : ∀ win ∈ windowsOfValues ns, Holds sw si win) : ns = [.int a, .int b] := by
  have hv : ∀ win ∈ windowsOfValues ns, ∀ d, partIn si win.1 win.2.1 win.2.2 = .ok d →
      viewable d = true := fun win hw _ hd => (hh win hw).viewable_part hd
  obtain ⟨x₀, y₀, rfl⟩ : ∃ x₀ y₀, ns = [x₀, y₀] := by
    have hl := mapWindowsValues_length hns
    match ns, hl with
    | [x₀, y₀], _ => exact ⟨x₀, y₀, rfl⟩
  obtain ⟨x, _, hx, h₁, e₁⟩ := mapWindowsValues_cons.1 hns
  obtain ⟨y, _, hy, h₂, rfl⟩ := mapWindowsValues_cons.1 h₁
  rw [mapWindowsValues_nil h₂] at e₁
  simp only [List.cons.injEq, and_true] at e₁
  obtain ⟨rfl, rfl⟩ := e₁
  rw [int_of_resolveIn hx fun w hw => hv w (by simp [windowsOfValues, hw]),
    int_of_resolveIn hy fun w hw => hv w (by simp [windowsOfValues, hw])]

/-- Offsets for which `View.of` gives a value: none, or two integers, which hold no window. -/
theorem offsets_free {v y : Value} {ns : List Value} (h : Op.view.apply (v :: ns) = .ok y) :
    windowsOfValues ns = [] := by
  by_cases h0 : ns = []
  · subst h0; rfl
  by_cases h2 : ∃ a b, ns = [.int a, .int b]
  · obtain ⟨a, b, rfl⟩ := h2; rfl
  · rw [view_apply_other h0 fun a b e => h2 ⟨a, b, e⟩] at h
    cases h

/-- Narrowing a window by its offsets. -/
theorem narrow_window_rel {l : Nat} {p : Path} {r : List (Int × Int)} {v : Value}
    {ns vs : List Value} (hw : VRel si sw (.window l p r) v)
    (hns : mapWindowsValues (partIn si) ns = .ok vs)
    (hh : ∀ win ∈ windowsOfValues ns, Holds sw si win) :
    (∃ f, Op.view.apply (v :: vs) = .error f ∧ narrow sw (.window l p r) ns = .error f) ∨
      ∃ y' y, Op.view.apply (v :: vs) = .ok y' ∧ narrow sw (.window l p r) ns = .ok y ∧
        VRel si sw y y' ∧
        ∀ win ∈ windowsOf y, ∃ win' ∈ windowsOf (.window l p r), win'.1 = win.1 ∧
          win'.2.1 = win.2.1 := by
  have hv : partIn si l p r = .ok v := hw.1
  have hhold : Holds sw si (l, p, r) := hw.2 _ List.mem_cons_self
  have hpart : part sw l p r = .ok v := hhold.readAlike.1.trans hv
  by_cases h0 : ns = []
  · subst h0
    rw [mapWindowsValues_nil hns]
    exact .inr ⟨v, _, rfl, rfl, hw, fun win h => ⟨win, h, rfl, rfl⟩⟩
  by_cases h2 : ∃ a b, ns = [.int a, .int b]
  · obtain ⟨a, b, rfl⟩ := h2
    obtain ⟨x, _, hx, h₁, rfl⟩ := mapWindowsValues_cons.1 hns
    obtain ⟨y, _, hy, h₂, rfl⟩ := mapWindowsValues_cons.1 h₁
    rw [mapWindowsValues_nil h₂]
    simp only [mapWindows, Except.ok.injEq] at hx hy
    subst hx hy
    have hn : narrow sw (.window l p r) [.int a, .int b] =
        (Op.view.apply [v, .int a, .int b]).bind fun _ => .ok (.window l p (r ++ [(a, b)])) := by
      show (part sw l p (r ++ [(a, b)])).bind _ = _
      rw [part_append, hpart]
      rfl
    cases hz : Op.view.apply [v, .int a, .int b] with
    | error f => exact .inl ⟨f, rfl, by rw [hn, hz]; rfl⟩
    | ok z =>
      refine .inr ⟨z, _, rfl, by rw [hn, hz]; rfl, ⟨?_, fun win h => ?_⟩, fun win h => ?_⟩
      · show partIn si l p (r ++ [(a, b)]) = _
        rw [partIn_append, hv]
        exact hz
      · simp only [windowsOf, List.mem_singleton] at h
        subst h
        exact hhold.ranges
      · simp only [windowsOf, List.mem_singleton] at h
        subst h
        exact ⟨_, List.mem_cons_self, rfl, rfl⟩
  · have hvs : vs ≠ [] := fun e => h0 (List.length_eq_zero_iff.1 (by
      rw [← mapWindowsValues_length hns, e]; rfl))
    exact .inl ⟨.stuck, view_apply_other hvs fun a b e => h2 ⟨a, b, ints_of_resolve (e ▸ hns) hh⟩,
      narrow_window_other h0 fun a b e => h2 ⟨a, b, e⟩⟩

/-- Narrowing a value that is no window: `View.of` of it. -/
theorem narrow_value_rel {w v : Value} {ns vs : List Value} (hwin : ∀ l p r, w ≠ .window l p r)
    (hw : VRel si sw w v) (hns : mapWindowsValues (partIn si) ns = .ok vs)
    (hh : ∀ win ∈ windowsOfValues ns, Holds sw si win) :
    (∃ f, Op.view.apply (v :: vs) = .error f ∧ narrow sw w ns = .error f) ∨
      ∃ y' y, Op.view.apply (v :: vs) = .ok y' ∧ narrow sw w ns = .ok y ∧ VRel si sw y y' ∧
        ∀ win ∈ windowsOf y, ∃ win' ∈ windowsOf w, win'.1 = win.1 ∧ win'.2.1 = win.2.1 := by
  have hall : ∀ win ∈ windowsOfValues (w :: ns), Holds sw si win := by
    intro win h
    simp only [windowsOfValues, List.mem_append] at h
    rcases h with h | h
    · exact hw.2 win h
    · exact hh win h
  rw [narrow_other hwin]
  rcases view_apply_rel (mapWindowsValues_cons.2 ⟨v, vs, hw.1, hns, rfl⟩)
    (fun l p r e => hwin l p r (by simpa using e)) (fun win h d hd => (hall win h).viewable_part hd)
    with ⟨f, h₁, h₂⟩ | ⟨y, y', h₁, h₂, h₃, h₄⟩
  · exact .inl ⟨f, h₂, h₁⟩
  · have hnil := offsets_free h₁
    have h₅ : ∀ win ∈ windowsOf y, win ∈ windowsOf w := fun win h => by
      simpa [windowsOfValues, hnil] using h₄ win h
    exact .inr ⟨y', y, h₂, h₁, ⟨h₃, fun win h => hw.2 win (h₅ win h)⟩,
      fun win h => ⟨win, h₅ win h, rfl, rfl⟩⟩

/-- What narrowing a view reads: the view of windows `w` read as `v`, offsets `ns` read as
`vs`, narrowing fails as `View.of` of the in-place operands, or gives a value read as that one
gives, whose windows read the regions of the view's. -/
theorem narrow_rel {w v : Value} {ns vs : List Value} (hw : VRel si sw w v)
    (hns : mapWindowsValues (partIn si) ns = .ok vs)
    (hh : ∀ win ∈ windowsOfValues ns, Holds sw si win) :
    (∃ f, Op.view.apply (v :: vs) = .error f ∧ narrow sw w ns = .error f) ∨
      ∃ y' y, Op.view.apply (v :: vs) = .ok y' ∧ narrow sw w ns = .ok y ∧ VRel si sw y y' ∧
        ∀ win ∈ windowsOf y, ∃ win' ∈ windowsOf w, win'.1 = win.1 ∧ win'.2.1 = win.2.1 := by
  by_cases hwin : ∃ l p r, w = .window l p r
  · obtain ⟨l, p, r, rfl⟩ := hwin
    exact narrow_window_rel hw hns hh
  · exact narrow_value_rel (fun l p r e => hwin ⟨l, p, r, e⟩) hw hns hh

end Windows

end Stilt
