import Stilt.Windows.Resolve

/-!
# The windows of a value, element by element

What `mapWindows` gives of a list, a record and a variant, element by element: the same
elements at the same indexes and names, each with its windows replaced, which writes at an
index or a name keep; where the windows of an element, of a list's set element and of a
record's set field are among a value's; and the test by which `windowAt` tells a value that
holds no window, a map of every window to `stuck` (`mapWindows_stuck_isOk`).
-/

namespace Stilt

namespace Windows

section Maps

variable {f : Nat → Path → List (Int × Int) → Except Fault Value}

theorem mapWindowsValues_cons {v : Value} {vs ws : List Value} :
    mapWindowsValues f (v :: vs) = .ok ws ↔
      ∃ w ws', mapWindows f v = .ok w ∧ mapWindowsValues f vs = .ok ws' ∧ ws = w :: ws' := by
  simp only [mapWindowsValues]
  cases h₁ : mapWindows f v <;> cases h₂ : mapWindowsValues f vs <;>
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, eq_comm]

theorem mapWindowsFields_cons {x : Name} {v : Value} {fs gs : List (Name × Value)} :
    mapWindowsFields f ((x, v) :: fs) = .ok gs ↔
      ∃ w gs', mapWindows f v = .ok w ∧ mapWindowsFields f fs = .ok gs' ∧ gs = (x, w) :: gs' := by
  simp only [mapWindowsFields]
  cases h₁ : mapWindows f v <;> cases h₂ : mapWindowsFields f fs <;>
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, eq_comm]

theorem mapWindowsValues_nil {ws : List Value} (h : mapWindowsValues f [] = .ok ws) : ws = [] := by
  simp only [mapWindowsValues, Except.ok.injEq] at h
  exact h.symm

theorem mapWindowsFields_nil {gs : List (Name × Value)} (h : mapWindowsFields f [] = .ok gs) :
    gs = [] := by
  simp only [mapWindowsFields, Except.ok.injEq] at h
  exact h.symm

theorem mapWindows_list {vs : List Value} {u : Value} :
    mapWindows f (.list vs) = .ok u ↔ ∃ ws, mapWindowsValues f vs = .ok ws ∧ u = .list ws := by
  simp only [mapWindows]
  cases mapWindowsValues f vs <;> simp [Functor.map, Except.map, eq_comm]

theorem mapWindows_record {R : Name} {fs : List (Name × Value)} {u : Value} :
    mapWindows f (.record R fs) = .ok u ↔
      ∃ gs, mapWindowsFields f fs = .ok gs ∧ u = .record R gs := by
  simp only [mapWindows]
  cases mapWindowsFields f fs <;> simp [Functor.map, Except.map, eq_comm]

theorem mapWindows_variant {T C : Name} {vs : List Value} {u : Value} :
    mapWindows f (.variant T C vs) = .ok u ↔
      ∃ ws, mapWindowsValues f vs = .ok ws ∧ u = .variant T C ws := by
  simp only [mapWindows]
  cases mapWindowsValues f vs <;> simp [Functor.map, Except.map, eq_comm]

theorem mapWindowsValues_length :
    ∀ {vs ws : List Value}, mapWindowsValues f vs = .ok ws → ws.length = vs.length
  | [], _, h => by rw [mapWindowsValues_nil h]
  | _ :: _, _, h => by
    obtain ⟨_, _, -, h₂, rfl⟩ := mapWindowsValues_cons.1 h
    simp [mapWindowsValues_length h₂]

theorem mapWindowsValues_getElem? : ∀ {vs ws : List Value}, mapWindowsValues f vs = .ok ws →
    ∀ {i : Nat} {v : Value}, vs[i]? = some v → ∃ w, ws[i]? = some w ∧ mapWindows f v = .ok w
  | [], _, _, _, _, hv => by simp at hv
  | _ :: _, _, h, i, _, hv => by
    obtain ⟨w, _, h₁, h₂, rfl⟩ := mapWindowsValues_cons.1 h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hv
      subst hv
      exact ⟨w, rfl, h₁⟩
    | succ i => exact mapWindowsValues_getElem? h₂ (by simpa using hv)

/-- Values whose windows are replaced have their elements at the same indexes. -/
theorem mapWindowsValues_elemAt? {vs ws : List Value} (h : mapWindowsValues f vs = .ok ws)
    (i : Int) : (elemAt? vs i = none ∧ elemAt? ws i = none) ∨
      ∃ v w, elemAt? vs i = some v ∧ elemAt? ws i = some w ∧ mapWindows f v = .ok w := by
  unfold elemAt?
  split
  · cases hv : vs[i.toNat]? with
    | none =>
      refine .inl ⟨rfl, ?_⟩
      rw [List.getElem?_eq_none_iff] at hv ⊢
      rw [mapWindowsValues_length h]
      exact hv
    | some v =>
      obtain ⟨w, hw, hf⟩ := mapWindowsValues_getElem? h hv
      exact .inr ⟨v, w, rfl, hw, hf⟩
  · exact .inl ⟨rfl, rfl⟩

theorem mapWindowsValues_set : ∀ {vs ws : List Value}, mapWindowsValues f vs = .ok ws →
    ∀ {v w : Value}, mapWindows f v = .ok w →
      ∀ i : Nat, mapWindowsValues f (vs.set i v) = .ok (ws.set i w)
  | [], _, h, _, _, _, _ => by rw [mapWindowsValues_nil h]; rfl
  | _ :: _, _, h, _, w, hvw, i => by
    obtain ⟨x, ws', h₁, h₂, rfl⟩ := mapWindowsValues_cons.1 h
    cases i with
    | zero => exact mapWindowsValues_cons.2 ⟨w, ws', hvw, h₂, rfl⟩
    | succ i => exact mapWindowsValues_cons.2 ⟨x, _, h₁, mapWindowsValues_set h₂ hvw i, rfl⟩

theorem mapWindowsValues_drop : ∀ {vs ws : List Value}, mapWindowsValues f vs = .ok ws →
    ∀ n : Nat, mapWindowsValues f (vs.drop n) = .ok (ws.drop n)
  | [], _, h, _ => by simp [mapWindowsValues_nil h, mapWindowsValues]
  | _ :: _, _, h, n => by
    obtain ⟨_, _, _, h₂, rfl⟩ := mapWindowsValues_cons.1 h
    cases n with
    | zero => exact h
    | succ n => exact mapWindowsValues_drop h₂ n

theorem mapWindowsValues_take : ∀ {vs ws : List Value}, mapWindowsValues f vs = .ok ws →
    ∀ n : Nat, mapWindowsValues f (vs.take n) = .ok (ws.take n)
  | [], _, h, _ => by simp [mapWindowsValues_nil h, mapWindowsValues]
  | _ :: _, _, h, n => by
    obtain ⟨w, _, h₁, h₂, rfl⟩ := mapWindowsValues_cons.1 h
    cases n with
    | zero => rfl
    | succ n => exact mapWindowsValues_cons.2 ⟨w, _, h₁, mapWindowsValues_take h₂ n, rfl⟩

/-- Named values whose windows are replaced have their values at the same names. -/
theorem mapWindowsFields_lookup : ∀ {fs gs : List (Name × Value)},
    mapWindowsFields f fs = .ok gs → ∀ k : Name, (fs.lookup k = none ∧ gs.lookup k = none) ∨
      ∃ v w, fs.lookup k = some v ∧ gs.lookup k = some w ∧ mapWindows f v = .ok w
  | [], _, h, _ => by rw [mapWindowsFields_nil h]; exact .inl ⟨rfl, rfl⟩
  | (x, v) :: _, _, h, k => by
    obtain ⟨w, _, h₁, h₂, rfl⟩ := mapWindowsFields_cons.1 h
    by_cases hk : k = x
    · subst hk
      exact .inr ⟨v, w, by simp, by simp, h₁⟩
    · rw [lookup_cons_ne hk, lookup_cons_ne hk]
      exact mapWindowsFields_lookup h₂ k

theorem mapWindowsFields_assocSet : ∀ {fs gs : List (Name × Value)},
    mapWindowsFields f fs = .ok gs → ∀ {v w : Value}, mapWindows f v = .ok w →
      ∀ k : Name, mapWindowsFields f (assocSet fs k v) = .ok (assocSet gs k w)
  | [], _, h, _, _, _, _ => by rw [mapWindowsFields_nil h]; rfl
  | (x, _) :: _, _, h, _, w, hvw, k => by
    obtain ⟨u', gs', h₁, h₂, rfl⟩ := mapWindowsFields_cons.1 h
    unfold assocSet
    by_cases hk : k = x
    · rw [ite_eq_left hk, ite_eq_left hk]
      exact mapWindowsFields_cons.2 ⟨w, gs', hvw, h₂, rfl⟩
    · rw [ite_eq_right hk, ite_eq_right hk]
      exact mapWindowsFields_cons.2 ⟨u', _, h₁, mapWindowsFields_assocSet h₂ hvw k, rfl⟩

end Maps

section Members

theorem mem_windowsOfValues {w : Window} :
    ∀ {vs : List Value}, w ∈ windowsOfValues vs ↔ ∃ v ∈ vs, w ∈ windowsOf v
  | [] => by simp [windowsOfValues]
  | _ :: _ => by simp [windowsOfValues, mem_windowsOfValues]

theorem mem_windowsOfFields {w : Window} :
    ∀ {fs : List (Name × Value)}, w ∈ windowsOfFields fs ↔ ∃ p ∈ fs, w ∈ windowsOf p.2
  | [] => by simp [windowsOfFields]
  | (_, _) :: _ => by simp [windowsOfFields, mem_windowsOfFields]

theorem mem_assocSet {β : Type} {k : Name} {b : β} :
    ∀ {fs : List (Name × β)} {p : Name × β}, p ∈ assocSet fs k b → p ∈ fs ∨ p.2 = b
  | [], _, h => by simp [assocSet] at h
  | (k', _) :: _, _, h => by
    unfold assocSet at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inr rfl
      · exact .inl (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inl List.mem_cons_self
      · rcases mem_assocSet h with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h

theorem windowsOf_lookup {fs : List (Name × Value)} {k : Name} {v : Value}
    (h : fs.lookup k = some v) {w : Window} (hw : w ∈ windowsOf v) : w ∈ windowsOfFields fs :=
  mem_windowsOfFields.2 ⟨(k, v), mem_of_lookup h, hw⟩

theorem windowsOf_elemAt? {vs : List Value} {i : Int} {v : Value} (h : elemAt? vs i = some v)
    {w : Window} (hw : w ∈ windowsOf v) : w ∈ windowsOfValues vs := by
  unfold elemAt? at h
  split at h
  · exact mem_windowsOfValues.2 ⟨v, List.mem_of_getElem? h, hw⟩
  · cases h

theorem windowsOfFields_assocSet {fs : List (Name × Value)} {k : Name} {v : Value} {w : Window}
    (h : w ∈ windowsOfFields (assocSet fs k v)) : w ∈ windowsOfFields fs ∨ w ∈ windowsOf v := by
  obtain ⟨p, hp, hw⟩ := mem_windowsOfFields.1 h
  rcases mem_assocSet hp with hp | rfl
  · exact .inl (mem_windowsOfFields.2 ⟨p, hp, hw⟩)
  · exact .inr hw

theorem windowsOfValues_set {vs : List Value} {i : Nat} {v : Value} {w : Window}
    (h : w ∈ windowsOfValues (vs.set i v)) : w ∈ windowsOfValues vs ∨ w ∈ windowsOf v := by
  obtain ⟨u, hu, hw⟩ := mem_windowsOfValues.1 h
  rcases List.mem_or_eq_of_mem_set hu with hu | rfl
  · exact .inl (mem_windowsOfValues.2 ⟨u, hu, hw⟩)
  · exact .inr hw

end Members

section Stuck

mutual

theorem free_of_stuck : ∀ (v : Value) {w : Value},
    mapWindows (fun _ _ _ => .error .stuck) v = .ok w → Free v
  | .window .., _, h => by simp [mapWindows] at h
  | .list vs, _, h => by
    obtain ⟨_, h, -⟩ := mapWindows_list.1 h
    exact free_of_stuck_values vs h
  | .record _ fs, _, h => by
    obtain ⟨_, h, -⟩ := mapWindows_record.1 h
    exact free_of_stuck_fields fs h
  | .variant _ _ vs, _, h => by
    obtain ⟨_, h, -⟩ := mapWindows_variant.1 h
    exact free_of_stuck_values vs h
  | .int _, _, _ | .float _, _, _ | .bool _, _, _ | .str _, _, _ | .unit, _, _
  | .closure .., _, _ | .function .., _, _ | .handle .., _, _ => rfl

theorem free_of_stuck_values : ∀ (vs : List Value) {ws : List Value},
    mapWindowsValues (fun _ _ _ => .error .stuck) vs = .ok ws → windowsOfValues vs = []
  | [], _, _ => rfl
  | v :: vs, _, h => by
    obtain ⟨_, _, h₁, h₂, -⟩ := mapWindowsValues_cons.1 h
    have h₁' : windowsOf v = [] := free_of_stuck v h₁
    simp only [windowsOfValues, h₁', free_of_stuck_values vs h₂, List.append_nil]

theorem free_of_stuck_fields : ∀ (fs : List (Name × Value)) {gs : List (Name × Value)},
    mapWindowsFields (fun _ _ _ => .error .stuck) fs = .ok gs → windowsOfFields fs = []
  | [], _, _ => rfl
  | (_, v) :: fs, _, h => by
    obtain ⟨_, _, h₁, h₂, -⟩ := mapWindowsFields_cons.1 h
    have h₁' : windowsOf v = [] := free_of_stuck v h₁
    simp only [windowsOfFields, h₁', free_of_stuck_fields fs h₂, List.append_nil]

end

/-- The test of `windowAt`: a value that holds no window is one whose every window is stuck. -/
theorem mapWindows_stuck_isOk {v : Value} :
    (mapWindows (fun _ _ _ => .error .stuck) v).isOk = true ↔ Free v := by
  constructor
  · intro h
    cases hm : mapWindows (fun _ _ _ => .error .stuck) v with
    | error _ => simp [hm, Except.isOk, Except.toBool] at h
    | ok _ => exact free_of_stuck v hm
  · intro h
    rw [mapWindows_free _ v h]
    rfl

end Stuck

end Windows

end Stilt
