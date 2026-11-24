import Stilt.Windows.Eval
import Stilt.Windows.Through.Maps

/-!
# Reading and writing through windows, against the in-place store

A view's part is what its window reads (views.what-view-is). A path read through windows
(`getW`) from a value whose windows the store of windows and the in-place store read alike
fails as the same path read from the value read against the in-place store (`resolveIn`)
fails, or gives a value read as that one gives (`getW_rel`); a write through windows (`setW`)
likewise (`setW_rel`); and a write through windows at a path disjoint from one the value reads
with no window on the way keeps the part there (`get_setW_disjoint`).
-/

namespace Stilt

namespace Windows

section Get

variable {sw : List (Option Value)} {si : List Value}

/-- A window that both stores read alike, read against the in-place store: the part there,
which holds no window. -/
theorem part_of_resolveIn {loc : Nat} {path : Path} {ranges : List (Int × Int)} {u : Value}
    (hx : resolveIn si (.window loc path ranges) = .ok u)
    (hr : ∀ w ∈ windowsOf (.window loc path ranges), ReadAlike sw si w) :
    part sw loc path ranges = .ok u ∧ Free u := by
  have hp : partIn si loc path ranges = .ok u := hx
  obtain ⟨heq, hfree⟩ := hr _ List.mem_cons_self
  exact ⟨heq.trans hp, hfree u hp⟩

theorem getW_rel_window {loc : Nat} {path : Path} {ranges : List (Int × Int)} {u : Value}
    (hx : resolveIn si (.window loc path ranges) = .ok u)
    (hr : ∀ w ∈ windowsOf (.window loc path ranges), ReadAlike sw si w) (s : Step) (p : Path) :
    (∃ f, getW sw (.window loc path ranges) (s :: p) = .error f ∧ u.get (s :: p) = .error f) ∨
      ∃ y y', getW sw (.window loc path ranges) (s :: p) = .ok y ∧ u.get (s :: p) = .ok y' ∧
        resolveIn si y = .ok y' ∧ ∀ w ∈ windowsOf y, w ∈ windowsOf (.window loc path ranges) := by
  obtain ⟨hp, hu⟩ := part_of_resolveIn hx hr
  have hg : getW sw (.window loc path ranges) (s :: p) = u.get (s :: p) := by
    simp only [getW, hp]
    rfl
  rw [hg]
  cases hy : u.get (s :: p) with
  | error e => exact .inl ⟨e, rfl, rfl⟩
  | ok y =>
    have hfree : windowsOf y = [] := free_get u _ hu hy
    exact .inr ⟨y, y, rfl, rfl, resolveIn_free si hfree, by simp [hfree]⟩

/-- Reading a path through windows from a value whose windows both stores read alike fails as
reading it from the value read against the in-place store fails, or gives a value read as
that one gives, holding windows of the value only. -/
theorem getW_rel {x u : Value}
    (hx : resolveIn si x = .ok u) (hr : ∀ w ∈ windowsOf x, ReadAlike sw si w) (P : Path) :
    (∃ f, getW sw x P = .error f ∧ u.get P = .error f) ∨
      ∃ y y', getW sw x P = .ok y ∧ u.get P = .ok y' ∧ resolveIn si y = .ok y' ∧
        ∀ w ∈ windowsOf y, w ∈ windowsOf x := by
  induction P generalizing x u with
  | nil => exact .inr ⟨x, u, by cases x <;> rfl, rfl, hx, fun _ h => h⟩
  | cons s p ih =>
    cases x with
    | window loc path ranges => exact getW_rel_window hx hr s p
    | record R fs =>
      obtain ⟨gs, hgs, rfl⟩ := mapWindows_record.1 hx
      cases s with
      | index i => exact .inl ⟨.stuck, rfl, rfl⟩
      | field k =>
        rcases mapWindowsFields_lookup hgs k with ⟨h₁, h₂⟩ | ⟨v, w, h₁, h₂, h₃⟩
        · exact .inl ⟨.stuck, by simp [getW, h₁], by simp [Value.get, h₂]⟩
        · simp only [getW, Value.get, h₁, h₂]
          rcases ih h₃ fun win hw => hr win (windowsOf_lookup h₁ hw) with h | ⟨y, y', h⟩
          · exact .inl h
          · exact .inr ⟨y, y', h.1, h.2.1, h.2.2.1,
              fun win hw => windowsOf_lookup h₁ (h.2.2.2 win hw)⟩
    | list vs =>
      obtain ⟨ws, hws, rfl⟩ := mapWindows_list.1 hx
      cases s with
      | field k => exact .inl ⟨.stuck, rfl, rfl⟩
      | index i =>
        rcases mapWindowsValues_elemAt? hws i with ⟨h₁, h₂⟩ | ⟨v, w, h₁, h₂, h₃⟩
        · exact .inl ⟨.panic .bounds, by simp [getW, h₁], by simp [Value.get, h₂]⟩
        · simp only [getW, Value.get, h₁, h₂]
          rcases ih h₃ fun win hw => hr win (windowsOf_elemAt? h₁ hw) with h | ⟨y, y', h⟩
          · exact .inl h
          · exact .inr ⟨y, y', h.1, h.2.1, h.2.2.1,
              fun win hw => windowsOf_elemAt? h₁ (h.2.2.2 win hw)⟩
    | variant T C vs =>
      obtain ⟨ws, -, rfl⟩ := mapWindows_variant.1 hx
      exact .inl ⟨.stuck, by cases s <;> rfl, by cases s <;> rfl⟩
    | int _ | float _ | bool _ | str _ | unit | closure _ _ _ _ _ | function _ _ _ | handle _ _ =>
      simp only [resolveIn, mapWindows, Except.ok.injEq] at hx
      subst hx
      exact .inl ⟨.stuck, by cases s <;> rfl, by cases s <;> rfl⟩

end Get

section Set

variable {sw : List (Option Value)} {si : List Value}

/-- Writing at a path of a value that holds no window fails as the same write of the value
read fails, or gives a value read as that one gives, holding windows of what was written
only. -/
theorem set_rel_free {w v : Value} (hw : resolveIn si w = .ok v) :
    ∀ (P : Path) {x : Value}, Free x →
      (∃ f, x.set P w = .error f ∧ x.set P v = .error f) ∨
        ∃ x' u', x.set P w = .ok x' ∧ x.set P v = .ok u' ∧ resolveIn si x' = .ok u' ∧
          ∀ win ∈ windowsOf x', win ∈ windowsOf w
  | [], x, _ => .inr ⟨w, v, by cases x <;> rfl, by cases x <;> rfl, hw, fun _ h => h⟩
  | s :: p, x, hx => by
    cases x with
    | record R fs =>
      cases s with
      | index i => exact .inl ⟨.stuck, rfl, rfl⟩
      | field k =>
        cases h₁ : fs.lookup k with
        | none => exact .inl ⟨.stuck, by simp [Value.set, h₁], by simp [Value.set, h₁]⟩
        | some c =>
          simp only [Value.set, h₁]
          rcases set_rel_free hw p (free_of_mem_fields hx k c (mem_of_lookup h₁)) with
            ⟨e, he, he'⟩ | ⟨c', c'', h₂, h₃, h₄, h₅⟩
          · exact .inl ⟨e, by simp [he, Functor.map, Except.map],
              by simp [he', Functor.map, Except.map]⟩
          · refine .inr ⟨.record R (assocSet fs k c'), .record R (assocSet fs k c''),
              by simp [h₂, Functor.map, Except.map], by simp [h₃, Functor.map, Except.map],
              mapWindows_record.2 ⟨_, mapWindowsFields_assocSet
                (mapWindowsFields_free _ fs hx) h₄ k, rfl⟩, fun win hwin => ?_⟩
            rcases windowsOfFields_assocSet hwin with h | h
            · exact absurd h (by simp [show windowsOfFields fs = [] from hx])
            · exact h₅ win h
    | list vs =>
      cases s with
      | field k => exact .inl ⟨.stuck, rfl, rfl⟩
      | index i =>
        cases h₁ : elemAt? vs i with
        | none => exact .inl ⟨.panic .bounds, by simp [Value.set, h₁], by simp [Value.set, h₁]⟩
        | some c =>
          simp only [Value.set, h₁]
          have hc : Free c := by
            unfold elemAt? at h₁
            split at h₁
            · exact free_of_mem_values hx c (List.mem_of_getElem? h₁)
            · cases h₁
          rcases set_rel_free hw p hc with ⟨e, he, he'⟩ | ⟨c', c'', h₂, h₃, h₄, h₅⟩
          · exact .inl ⟨e, by simp [he, Functor.map, Except.map],
              by simp [he', Functor.map, Except.map]⟩
          · refine .inr ⟨.list (vs.set i.toNat c'), .list (vs.set i.toNat c''),
              by simp [h₂, Functor.map, Except.map], by simp [h₃, Functor.map, Except.map],
              mapWindows_list.2 ⟨_, mapWindowsValues_set
                (mapWindowsValues_free _ vs hx) h₄ _, rfl⟩, fun win hwin => ?_⟩
            rcases windowsOfValues_set hwin with h | h
            · exact absurd h (by simp [show windowsOfValues vs = [] from hx])
            · exact h₅ win h
    | window _ _ _ | variant _ _ _ | int _ | float _ | bool _ | str _ | unit
    | closure _ _ _ _ _ | function _ _ _ | handle _ _ =>
      exact .inl ⟨.stuck, by cases s <;> rfl, by cases s <;> rfl⟩

/-- A write at `P` of `w` through the windows of `x`, against the write of `v` at `P` in `u`:
both fail alike, or give values that the in-place store reads alike, the first holding
windows of `x` and `w` only. -/
def SetsAlike (sw : List (Option Value)) (si : List Value) (x u w v : Value) (P : Path) : Prop :=
  (∃ f, setW sw x P w = .error f ∧ u.set P v = .error f) ∨
    ∃ x' u', setW sw x P w = .ok x' ∧ u.set P v = .ok u' ∧ resolveIn si x' = .ok u' ∧
      ∀ win ∈ windowsOf x', win ∈ windowsOf x ∨ win ∈ windowsOf w

theorem setsAlike_record {R k : Name} {fs gs : List (Name × Value)} {w v : Value} {p : Path}
    (hgs : mapWindowsFields (partIn si) fs = .ok gs)
    (hr : ∀ win ∈ windowsOfFields fs, ReadAlike sw si win)
    (ih : ∀ {x u : Value}, resolveIn si x = .ok u → (∀ win ∈ windowsOf x, ReadAlike sw si win) →
      SetsAlike sw si x u w v p) :
    SetsAlike sw si (.record R fs) (.record R gs) w v (.field k :: p) := by
  rcases mapWindowsFields_lookup hgs k with ⟨h₁, h₂⟩ | ⟨c, cu, h₁, h₂, h₃⟩
  · exact .inl ⟨.stuck, by simp [setW, h₁], by simp [Value.set, h₂]⟩
  rcases ih h₃ (fun win hw => hr win (windowsOf_lookup h₁ hw)) with
    ⟨e, he, he'⟩ | ⟨c', cu', h₄, h₅, h₆, h₇⟩
  · exact .inl ⟨e, by simp [setW, h₁, he, Functor.map, Except.map],
      by simp [Value.set, h₂, he', Functor.map, Except.map]⟩
  refine .inr ⟨.record R (assocSet fs k c'), .record R (assocSet gs k cu'),
    by simp [setW, h₁, h₄, Functor.map, Except.map],
    by simp [Value.set, h₂, h₅, Functor.map, Except.map],
    mapWindows_record.2 ⟨_, mapWindowsFields_assocSet hgs h₆ k, rfl⟩, fun win hwin => ?_⟩
  rcases windowsOfFields_assocSet hwin with h | h
  · exact .inl h
  · exact (h₇ win h).imp_left (windowsOf_lookup h₁)

theorem setsAlike_list {i : Int} {vs ws : List Value} {w v : Value} {p : Path}
    (hws : mapWindowsValues (partIn si) vs = .ok ws)
    (hr : ∀ win ∈ windowsOfValues vs, ReadAlike sw si win)
    (ih : ∀ {x u : Value}, resolveIn si x = .ok u → (∀ win ∈ windowsOf x, ReadAlike sw si win) →
      SetsAlike sw si x u w v p) :
    SetsAlike sw si (.list vs) (.list ws) w v (.index i :: p) := by
  rcases mapWindowsValues_elemAt? hws i with ⟨h₁, h₂⟩ | ⟨c, cu, h₁, h₂, h₃⟩
  · exact .inl ⟨.panic .bounds, by simp [setW, h₁], by simp [Value.set, h₂]⟩
  rcases ih h₃ (fun win hw => hr win (windowsOf_elemAt? h₁ hw)) with
    ⟨e, he, he'⟩ | ⟨c', cu', h₄, h₅, h₆, h₇⟩
  · exact .inl ⟨e, by simp [setW, h₁, he, Functor.map, Except.map],
      by simp [Value.set, h₂, he', Functor.map, Except.map]⟩
  refine .inr ⟨.list (vs.set i.toNat c'), .list (ws.set i.toNat cu'),
    by simp [setW, h₁, h₄, Functor.map, Except.map],
    by simp [Value.set, h₂, h₅, Functor.map, Except.map],
    mapWindows_list.2 ⟨_, mapWindowsValues_set hws h₆ _, rfl⟩, fun win hwin => ?_⟩
  rcases windowsOfValues_set hwin with h | h
  · exact .inl h
  · exact (h₇ win h).imp_left (windowsOf_elemAt? h₁)

/-- Writing a path through windows into a value whose windows both stores read alike fails as
writing it into the value read against the in-place store fails, or gives a value read as
that one gives, holding windows of the value and of what was written only. -/
theorem setW_rel {x u w v : Value}
    (hx : resolveIn si x = .ok u) (hr : ∀ win ∈ windowsOf x, ReadAlike sw si win)
    (hw : resolveIn si w = .ok v) (P : Path) :
    (∃ f, setW sw x P w = .error f ∧ u.set P v = .error f) ∨
      ∃ x' u', setW sw x P w = .ok x' ∧ u.set P v = .ok u' ∧ resolveIn si x' = .ok u' ∧
        ∀ win ∈ windowsOf x', win ∈ windowsOf x ∨ win ∈ windowsOf w := by
  show SetsAlike sw si x u w v P
  induction P generalizing x u with
  | nil => exact .inr ⟨w, v, by cases x <;> rfl, by cases u <;> rfl, hw, fun _ h => .inr h⟩
  | cons s p ih =>
    cases x with
    | window loc path ranges =>
      obtain ⟨hp, hu⟩ := part_of_resolveIn hx hr
      have hg : setW sw (.window loc path ranges) (s :: p) w = u.set (s :: p) w := by
        simp only [setW, hp]
        rfl
      rcases set_rel_free hw (s :: p) hu with h | ⟨x', u', h₁, h₂, h₃, h₄⟩
      · exact .inl (by rw [hg]; exact h)
      · exact .inr ⟨x', u', hg.trans h₁, h₂, h₃, fun win hwin => .inr (h₄ win hwin)⟩
    | record R fs =>
      obtain ⟨gs, hgs, rfl⟩ := mapWindows_record.1 hx
      cases s with
      | index i => exact .inl ⟨.stuck, rfl, rfl⟩
      | field k => exact setsAlike_record hgs hr ih
    | list vs =>
      obtain ⟨ws, hws, rfl⟩ := mapWindows_list.1 hx
      cases s with
      | field k => exact .inl ⟨.stuck, rfl, rfl⟩
      | index i => exact setsAlike_list hws hr ih
    | variant T C vs =>
      obtain ⟨ws, -, rfl⟩ := mapWindows_variant.1 hx
      exact .inl ⟨.stuck, by cases s <;> rfl, by cases s <;> rfl⟩
    | int _ | float _ | bool _ | str _ | unit | closure _ _ _ _ _ | function _ _ _ | handle _ _ =>
      simp only [resolveIn, mapWindows, Except.ok.injEq] at hx
      subst hx
      exact .inl ⟨.stuck, by cases s <;> rfl, by cases s <;> rfl⟩

/-- A write through windows at a path disjoint from `q` keeps the part at `q`, when the
value reads `q` with no window on the way. -/
theorem get_setW_disjoint {x x' w d : Value} {P q : Path}
    (hd : P.Disjoint q) (h : setW sw x P w = .ok x') (hq : x.get q = .ok d) : x'.get q = .ok d := by
  induction P generalizing x x' q d with
  | nil => cases q <;> simp [Path.Disjoint] at hd
  | cons s p ih =>
    cases q with
    | nil => simp [Path.Disjoint] at hd
    | cons t q =>
      cases x with
      | record R fs =>
        cases s with
        | index i => simp [setW] at h
        | field k =>
          simp only [setW] at h
          split at h
          · rename_i c hc
            cases h₁ : setW sw c p w with
            | error e => simp [h₁, Functor.map, Except.map] at h
            | ok c' =>
              simp only [h₁, Functor.map, Except.map, Except.ok.injEq] at h
              subst h
              cases t with
              | index j => simp [Value.get] at hq
              | field g =>
                by_cases hkg : k = g
                · subst hkg
                  have hsome : (fs.lookup k).isSome = true := by simp [hc]
                  simp only [Value.get, hc] at hq
                  simp only [Value.get, lookup_assocSet_self _ _ _ hsome]
                  exact ih (by simpa [Path.Disjoint] using hd) h₁ hq
                · simpa [Value.get, lookup_assocSet_ne _ _ (Ne.symm hkg)] using hq
          · cases h
      | list vs =>
        cases s with
        | field k => simp [setW] at h
        | index i =>
          simp only [setW] at h
          split at h
          · rename_i c hc
            cases h₁ : setW sw c p w with
            | error e => simp [h₁, Functor.map, Except.map] at h
            | ok c' =>
              simp only [h₁, Functor.map, Except.map, Except.ok.injEq] at h
              subst h
              cases t with
              | field g => simp [Value.get] at hq
              | index j =>
                by_cases hij : i = j
                · subst hij
                  simp only [Value.get, hc] at hq
                  simp only [Value.get, elemAt?_set_self hc]
                  exact ih (by simpa [Path.Disjoint] using hd) h₁ hq
                · simpa [Value.get, elemAt?_set_ne _ (nonneg_of_elemAt? hc) hij] using hq
          · cases h
      | window _ _ _ => simp [Value.get] at hq
      | variant _ _ _ | int _ | float _ | bool _ | str _ | unit | closure _ _ _ _ _
      | function _ _ _ | handle _ _ => cases s <;> simp [setW] at h

end Set

end Windows

end Stilt
