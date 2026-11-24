import Stilt.Windows.Eval
import Stilt.Windows.Through.Maps

/-!
# The parts of windows, and the windows a value keeps

A window narrowed by a range reads its part sliced by that range (`partIn_append`,
`part_append`; views.making-view). `View.of` of operands read against the in-place store fails
as it fails of the operands, or gives a value read as it gives, when the first operand is no
window and every window among them reads a string or a list (`view_apply_rel`); of offsets
other than none or two integers it is stuck (`view_apply_other`). A value read through its
windows on locations from `n` on keeps what the in-place store reads it as, and only windows
below `n` (`resolveFrom_rel`; views.across-calls), and the values that `resolveAllE` reads are
those read against the in-place store (`resolveAll_eq`).
-/

namespace Stilt

namespace Windows

section Slices

/-- Slicing by ranges and then by one more range is slicing by all of them in turn. -/
theorem foldlM_slices_append (u : Value) (ranges : List (Int × Int)) (a b : Int) :
    (ranges ++ [(a, b)]).foldlM (fun v r => Op.view.apply [v, .int r.1, .int r.2]) u =
      (ranges.foldlM (fun v r => Op.view.apply [v, .int r.1, .int r.2]) u).bind
        fun v => Op.view.apply [v, .int a, .int b] := by
  rw [List.foldlM_append]
  cases ranges.foldlM (fun v r => Op.view.apply [v, .int r.1, .int r.2]) u with
  | error _ => rfl
  | ok w =>
    show Op.view.apply [w, .int a, .int b] >>= pure = _
    rw [bind_pure]
    rfl

/-- The part of the in-place store that a window narrowed by a range reads is the window's
part sliced by the range. -/
theorem partIn_append (st : List Value) (loc : Nat) (path : Path) (ranges : List (Int × Int))
    (a b : Int) : partIn st loc path (ranges ++ [(a, b)]) =
      (partIn st loc path ranges).bind fun v => Op.view.apply [v, .int a, .int b] := by
  have e := partIn_eq_deref st (loc, path, ranges ++ [(a, b)])
  have e' := partIn_eq_deref st (loc, path, ranges)
  simp only [Window.ref] at e e'
  rw [e, e']
  cases InPlace.deref ⟨[], st⟩ ⟨loc, path⟩ [] with
  | error _ => rfl
  | ok u => simpa only [Except.bind] using foldlM_slices_append u ranges a b

/-- The part of the store of windows that a window narrowed by a range reads is the window's
part sliced by the range. -/
theorem part_append (st : List (Option Value)) (loc : Nat) (path : Path)
    (ranges : List (Int × Int)) (a b : Int) : part st loc path (ranges ++ [(a, b)]) =
      (part st loc path ranges).bind fun v => Op.view.apply [v, .int a, .int b] := by
  have e : ∀ rs : List (Int × Int), part st loc path rs =
      (cell st loc).bind fun v => (v.get path).bind fun v =>
        rs.foldlM (fun v r => Op.view.apply [v, .int r.1, .int r.2]) v := fun _ => rfl
  rw [e, e]
  cases cell st loc with
  | error _ => rfl
  | ok v =>
    cases hg : v.get path with
    | error _ => simp only [Except.bind, hg]
    | ok u => simpa only [Except.bind, hg] using foldlM_slices_append u ranges a b

end Slices

section Views

theorem view_apply_two (v a : Value) : Op.view.apply [v, a] = .error .stuck := by
  cases v <;> rfl

theorem view_apply_four (v a b c : Value) (rest : List Value) :
    Op.view.apply (v :: a :: b :: c :: rest) = .error .stuck := by
  cases v <;> rfl

/-- `View.of` of offsets that are not two integers is stuck. -/
theorem view_apply_nonint {v a b : Value} (h : ∀ m n, a = .int m → b = .int n → False) :
    Op.view.apply [v, a, b] = .error .stuck := by
  cases v <;> cases a <;> cases b <;> first | rfl | exact absurd (h _ _ rfl rfl) id

/-- `View.of` with offsets other than none or two integers is stuck. -/
theorem view_apply_other {v : Value} {ns : List Value} (h0 : ns ≠ [])
    (h2 : ∀ a b, ns ≠ [.int a, .int b]) : Op.view.apply (v :: ns) = .error .stuck := by
  rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exact absurd rfl h0
  · exact view_apply_two v a
  · exact view_apply_nonint fun m n ha hb => h2 m n (by rw [ha, hb])
  · exact view_apply_four v a b c rest

variable {si : List Value}

/-- An operand that the in-place store reads as an integer is that integer, when each of its
windows reads a string or a list. -/
theorem int_of_resolveIn {a : Value} {m : Int} (h : resolveIn si a = .ok (.int m))
    (hview : ∀ w ∈ windowsOf a, ∀ d, partIn si w.1 w.2.1 w.2.2 = .ok d → viewable d = true) :
    a = .int m := by
  cases a with
  | window l p r =>
    have := hview (l, p, r) List.mem_cons_self _ h
    simp [viewable] at this
  | list vs => obtain ⟨_, -, h⟩ := mapWindows_list.1 h; cases h
  | record R fs => obtain ⟨_, -, h⟩ := mapWindows_record.1 h; cases h
  | variant T C vs => obtain ⟨_, -, h⟩ := mapWindows_variant.1 h; cases h
  | int _ | float _ | bool _ | str _ | unit | closure _ _ _ _ _ | function _ _ _ | handle _ _ =>
    simp [resolveIn, mapWindows] at h
    try rw [h]

/-- `View.of` of a list and two integers, and of the list read against the in-place store. -/
theorem view_apply_list_rel {vs ws : List Value} (h : mapWindowsValues (partIn si) vs = .ok ws)
    (m n : Int) :
    (∃ f, Op.view.apply [.list vs, .int m, .int n] = .error f ∧
        Op.view.apply [.list ws, .int m, .int n] = .error f) ∨
      ∃ y y', Op.view.apply [.list vs, .int m, .int n] = .ok y ∧
        Op.view.apply [.list ws, .int m, .int n] = .ok y' ∧ resolveIn si y = .ok y' ∧
        ∀ w ∈ windowsOf y, w ∈ windowsOfValues vs := by
  have hl := mapWindowsValues_length h
  simp only [Op.apply, ListOp.apply, onList, Value.list?, hl]
  split
  · refine .inr ⟨_, _, rfl, rfl,
      mapWindows_list.2 ⟨_, mapWindowsValues_take (mapWindowsValues_drop h _) _, rfl⟩,
      fun w hw => ?_⟩
    obtain ⟨v, hv, hw⟩ := mem_windowsOfValues.1 hw
    exact mem_windowsOfValues.2 ⟨v, List.mem_of_mem_drop (List.mem_of_mem_take hv), hw⟩
  · exact .inl ⟨_, rfl, rfl⟩

/-- `View.of` of a value that holds no window and two integers gives a value that holds none. -/
theorem view_apply_free_rel {x : Value} (hx : Free x) (m n : Int) :
    (∃ f, Op.view.apply [x, .int m, .int n] = .error f ∧
        Op.view.apply [x, .int m, .int n] = .error f) ∨
      ∃ y y', Op.view.apply [x, .int m, .int n] = .ok y ∧
        Op.view.apply [x, .int m, .int n] = .ok y' ∧ resolveIn si y = .ok y' ∧
        ∀ w ∈ windowsOf y, w ∈ windowsOf x := by
  cases hy : Op.view.apply [x, .int m, .int n] with
  | error f => exact .inl ⟨f, rfl, rfl⟩
  | ok y =>
    have hfree : windowsOf y = [] := free_view hx hy
    exact .inr ⟨y, y, rfl, rfl, resolveIn_free si hfree, by simp [hfree]⟩

/-- `View.of` of a value that is no window and two integers, and of the value read against
the in-place store. -/
theorem view_apply_ints_rel {x u : Value} (h : resolveIn si x = .ok u)
    (hx : ∀ l p r, x ≠ .window l p r) (m n : Int) :
    (∃ f, Op.view.apply [x, .int m, .int n] = .error f ∧
        Op.view.apply [u, .int m, .int n] = .error f) ∨
      ∃ y y', Op.view.apply [x, .int m, .int n] = .ok y ∧
        Op.view.apply [u, .int m, .int n] = .ok y' ∧ resolveIn si y = .ok y' ∧
        ∀ w ∈ windowsOf y, w ∈ windowsOf x := by
  cases x with
  | window l p r => exact absurd rfl (hx l p r)
  | list vs =>
    obtain ⟨ws, hws, rfl⟩ := mapWindows_list.1 h
    exact view_apply_list_rel hws m n
  | record R fs =>
    obtain ⟨gs, -, rfl⟩ := mapWindows_record.1 h
    exact .inl ⟨.stuck, rfl, rfl⟩
  | variant T C vs =>
    obtain ⟨ws, -, rfl⟩ := mapWindows_variant.1 h
    exact .inl ⟨.stuck, rfl, rfl⟩
  | int _ | float _ | bool _ | str _ | unit | closure _ _ _ _ _ | function _ _ _ | handle _ _ =>
    simp only [resolveIn, mapWindows, Except.ok.injEq] at h
    subst h
    refine view_apply_free_rel ?_ m n
    exact rfl

/-- `View.of` of operands read against the in-place store, the first no window, the parts of
the windows strings or lists: fails alike, or gives related values. -/
theorem view_apply_rel {xs us : List Value}
    (h : mapWindowsValues (partIn si) xs = .ok us)
    (hhead : ∀ l p r, xs.head? ≠ some (.window l p r))
    (hview : ∀ w ∈ windowsOfValues xs, ∀ d, partIn si w.1 w.2.1 w.2.2 = .ok d → viewable d = true) :
    (∃ f, Op.view.apply xs = .error f ∧ Op.view.apply us = .error f) ∨
      ∃ y y', Op.view.apply xs = .ok y ∧ Op.view.apply us = .ok y' ∧ resolveIn si y = .ok y' ∧
        ∀ w ∈ windowsOf y, w ∈ windowsOfValues xs := by
  rcases xs with _ | ⟨x, _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩⟩
  · rw [mapWindowsValues_nil h]
    exact .inl ⟨.stuck, rfl, rfl⟩
  · obtain ⟨u, _, hu, h₁, rfl⟩ := mapWindowsValues_cons.1 h
    rw [mapWindowsValues_nil h₁]
    exact .inr ⟨x, u, rfl, rfl, hu, fun w hw => by simpa [windowsOfValues] using hw⟩
  · obtain ⟨u, _, -, h₁, rfl⟩ := mapWindowsValues_cons.1 h
    obtain ⟨a', _, -, h₂, rfl⟩ := mapWindowsValues_cons.1 h₁
    rw [mapWindowsValues_nil h₂]
    exact .inl ⟨.stuck, view_apply_two x a, view_apply_two u a'⟩
  · obtain ⟨u, _, hu, h₁, rfl⟩ := mapWindowsValues_cons.1 h
    obtain ⟨a', _, ha, h₂, rfl⟩ := mapWindowsValues_cons.1 h₁
    obtain ⟨b', _, hb, h₃, rfl⟩ := mapWindowsValues_cons.1 h₂
    rw [mapWindowsValues_nil h₃]
    have hv : ∀ w ∈ windowsOf a ++ windowsOf b, ∀ d, partIn si w.1 w.2.1 w.2.2 = .ok d →
        viewable d = true := fun w hw =>
      hview w (by
        simp only [windowsOfValues, List.mem_append] at hw ⊢
        rcases hw with hw | hw <;> simp [hw])
    by_cases hab : ∃ m n, a' = .int m ∧ b' = .int n
    · obtain ⟨m, n, rfl, rfl⟩ := hab
      rw [int_of_resolveIn ha fun w hw => hv w (List.mem_append_left _ hw),
        int_of_resolveIn hb fun w hw => hv w (List.mem_append_right _ hw)]
      refine (view_apply_ints_rel hu (fun l p r e => hhead l p r (by simp [e])) m n).imp_right ?_
      rintro ⟨y, y', h₁, h₂, h₃, h₄⟩
      refine ⟨y, y', h₁, h₂, h₃, fun w hw => ?_⟩
      simp only [windowsOfValues, List.mem_append]
      exact .inl (h₄ w hw)
    · refine .inl ⟨.stuck, view_apply_nonint fun m n hm hn => hab ⟨m, n, ?_, ?_⟩,
        view_apply_nonint fun m n hm hn => hab ⟨m, n, hm, hn⟩⟩
      · subst hm; simpa [resolveIn, mapWindows] using ha.symm
      · subst hn; simpa [resolveIn, mapWindows] using hb.symm
  · obtain ⟨u, _, -, h₁, rfl⟩ := mapWindowsValues_cons.1 h
    obtain ⟨a', _, -, h₂, rfl⟩ := mapWindowsValues_cons.1 h₁
    obtain ⟨b', _, -, h₃, rfl⟩ := mapWindowsValues_cons.1 h₂
    obtain ⟨c', _, -, -, rfl⟩ := mapWindowsValues_cons.1 h₃
    exact .inl ⟨.stuck, view_apply_four x a b c rest, view_apply_four u a' b' c' _⟩

end Views

section Partly

variable {f g : Nat → Path → List (Int × Int) → Except Fault Value} {P : Window → Prop}

/-- A window that `g` keeps, when `P` holds of it, or replaces as `f` does, by a part that
holds no window. -/
def KeepsOrReads (f g : Nat → Path → List (Int × Int) → Except Fault Value)
    (P : Window → Prop) (w : Window) : Prop :=
  (g w.1 w.2.1 w.2.2 = .ok (.window w.1 w.2.1 w.2.2) ∧ P w) ∨
    (g w.1 w.2.1 w.2.2 = f w.1 w.2.1 w.2.2 ∧ ∀ d, f w.1 w.2.1 w.2.2 = .ok d → Free d)

mutual

/-- A value whose windows `g` keeps or replaces as `f` does: `g` gives a value that `f`
replaces as it replaces the first, holding only the windows `g` keeps. -/
theorem mapWindows_partly : ∀ (v : Value) {u : Value}, mapWindows f v = .ok u →
    (∀ w ∈ windowsOf v, KeepsOrReads f g P w) →
    ∃ v', mapWindows g v = .ok v' ∧ mapWindows f v' = .ok u ∧
      ∀ w ∈ windowsOf v', w ∈ windowsOf v ∧ P w
  | .window l p r, u, h, hk => by
    rcases hk (l, p, r) List.mem_cons_self with ⟨hg, hp⟩ | ⟨hg, hfree⟩
    · exact ⟨.window l p r, hg, h, fun w hw => by
        simp only [windowsOf, List.mem_singleton] at hw
        subst hw
        exact ⟨List.mem_cons_self, hp⟩⟩
    · have hu : Free u := hfree u h
      exact ⟨u, hg.trans h, mapWindows_free f u hu, fun w hw => by
        rw [show windowsOf u = [] from hu] at hw
        cases hw⟩
  | .list vs, _, h, hk => by
    obtain ⟨_, hws, rfl⟩ := mapWindows_list.1 h
    obtain ⟨vs', h₁, h₂, h₃⟩ := mapWindowsValues_partly vs hws hk
    exact ⟨.list vs', mapWindows_list.2 ⟨vs', h₁, rfl⟩, mapWindows_list.2 ⟨_, h₂, rfl⟩, h₃⟩
  | .record R fs, _, h, hk => by
    obtain ⟨_, hgs, rfl⟩ := mapWindows_record.1 h
    obtain ⟨fs', h₁, h₂, h₃⟩ := mapWindowsFields_partly fs hgs hk
    exact ⟨.record R fs', mapWindows_record.2 ⟨fs', h₁, rfl⟩, mapWindows_record.2 ⟨_, h₂, rfl⟩,
      h₃⟩
  | .variant T C vs, _, h, hk => by
    obtain ⟨_, hws, rfl⟩ := mapWindows_variant.1 h
    obtain ⟨vs', h₁, h₂, h₃⟩ := mapWindowsValues_partly vs hws hk
    exact ⟨.variant T C vs', mapWindows_variant.2 ⟨vs', h₁, rfl⟩,
      mapWindows_variant.2 ⟨_, h₂, rfl⟩, h₃⟩
  | .int _, _, h, _ | .float _, _, h, _ | .bool _, _, h, _ | .str _, _, h, _ | .unit, _, h, _
  | .closure .., _, h, _ | .function .., _, h, _ | .handle .., _, h, _ =>
    ⟨_, rfl, h, fun _ hw => nomatch hw⟩

theorem mapWindowsValues_partly : ∀ (vs : List Value) {us : List Value},
    mapWindowsValues f vs = .ok us → (∀ w ∈ windowsOfValues vs, KeepsOrReads f g P w) →
    ∃ vs', mapWindowsValues g vs = .ok vs' ∧ mapWindowsValues f vs' = .ok us ∧
      ∀ w ∈ windowsOfValues vs', w ∈ windowsOfValues vs ∧ P w
  | [], _, h, _ => ⟨[], rfl, h, fun _ hw => nomatch hw⟩
  | v :: vs, _, h, hk => by
    obtain ⟨_, _, h₁, h₂, rfl⟩ := mapWindowsValues_cons.1 h
    obtain ⟨v', g₁, f₁, k₁⟩ :=
      mapWindows_partly v h₁ fun w hw => hk w (List.mem_append_left _ hw)
    obtain ⟨vs', g₂, f₂, k₂⟩ :=
      mapWindowsValues_partly vs h₂ fun w hw => hk w (List.mem_append_right _ hw)
    refine ⟨v' :: vs', mapWindowsValues_cons.2 ⟨v', vs', g₁, g₂, rfl⟩,
      mapWindowsValues_cons.2 ⟨_, _, f₁, f₂, rfl⟩, fun w hw => ?_⟩
    rcases List.mem_append.1 hw with hw | hw
    · exact (k₁ w hw).imp_left (List.mem_append_left _)
    · exact (k₂ w hw).imp_left (List.mem_append_right _)

theorem mapWindowsFields_partly : ∀ (fs : List (Name × Value)) {gs : List (Name × Value)},
    mapWindowsFields f fs = .ok gs → (∀ w ∈ windowsOfFields fs, KeepsOrReads f g P w) →
    ∃ fs', mapWindowsFields g fs = .ok fs' ∧ mapWindowsFields f fs' = .ok gs ∧
      ∀ w ∈ windowsOfFields fs', w ∈ windowsOfFields fs ∧ P w
  | [], _, h, _ => ⟨[], rfl, h, fun _ hw => nomatch hw⟩
  | (x, v) :: fs, _, h, hk => by
    obtain ⟨_, _, h₁, h₂, rfl⟩ := mapWindowsFields_cons.1 h
    obtain ⟨v', g₁, f₁, k₁⟩ :=
      mapWindows_partly v h₁ fun w hw => hk w (List.mem_append_left _ hw)
    obtain ⟨fs', g₂, f₂, k₂⟩ :=
      mapWindowsFields_partly fs h₂ fun w hw => hk w (List.mem_append_right _ hw)
    refine ⟨(x, v') :: fs', mapWindowsFields_cons.2 ⟨v', fs', g₁, g₂, rfl⟩,
      mapWindowsFields_cons.2 ⟨_, _, f₁, f₂, rfl⟩, fun w hw => ?_⟩
    rcases List.mem_append.1 hw with hw | hw
    · exact (k₁ w hw).imp_left (List.mem_append_left _)
    · exact (k₂ w hw).imp_left (List.mem_append_right _)

end

end Partly

section Calls

variable {sw : List (Option Value)} {si : List Value}

/-- A value that holds no window is itself read through windows. -/
theorem resolve_free {d : Value} (hd : Free d) : resolve sw d = .ok d := by
  simp only [resolve, resolveAt]
  exact mapWindows_free _ d hd

/-- A window that both stores read alike, read through the store of windows: its part, which
holds no window. -/
theorem part_resolve_eq {w : Window} (hr : ReadAlike sw si w) :
    (do resolve sw (← part sw w.1 w.2.1 w.2.2)) = partIn si w.1 w.2.1 w.2.2 := by
  obtain ⟨heq, hfree⟩ := hr
  rw [heq]
  cases hp : partIn si w.1 w.2.1 w.2.2 with
  | error _ => rfl
  | ok d => exact resolve_free (hfree d hp)

/-- Reading through windows on locations from `n` on, when both stores read every window
alike, keeps what the value reads, and leaves only windows below `n`. -/
theorem resolveFrom_rel {n : Nat} {v u : Value}
    (hv : resolveIn si v = .ok u) (hr : ∀ w ∈ windowsOf v, ReadAlike sw si w) :
    ∃ v', resolveFrom sw n v = .ok v' ∧ resolveIn si v' = .ok u ∧
      ∀ w ∈ windowsOf v', w ∈ windowsOf v ∧ w.1 < n := by
  refine mapWindows_partly v hv fun w hw => ?_
  by_cases hn : n ≤ w.1
  · refine .inr ⟨?_, fun d hd => (hr w hw).2 d hd⟩
    simp only [hn, ite_true]
    exact part_resolve_eq (hr w hw)
  · exact .inl ⟨by simp [hn], by omega⟩

/-- What `resolveAllE` computes, against the in-place store. -/
theorem resolveAll_eq {vs : List Value} (hr : ∀ w ∈ windowsOfValues vs, ReadAlike sw si w) :
    mapWindowsValues (fun loc path ranges => do resolve sw (← part sw loc path ranges)) vs =
      mapWindowsValues (partIn si) vs :=
  mapWindowsValues_congr vs fun w hw => part_resolve_eq (hr w hw)

end Calls

end Windows

end Stilt
