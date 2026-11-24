import Stilt.Windows.Memory
import Stilt.Maps
import Stilt.Generics
import Stilt.InPlace.Store

/-!
# Windows read against the in-place store

What the agreement of windows with in-place mutation reads a value of the model of windows as:
each of its windows replaced by the part that the in-place store holds there (`resolveIn`). The
windows a value holds are `windowsOf`'s, those `mapWindows` replaces; a value that holds none,
as every source does (views.view-types), is the same read through any store, and so is each
of its parts and the parts that `View.of` takes of it. Two stores that give a value's windows
the same parts, each holding no window, read it alike (`resolveAt_eq_resolveIn`).
-/

namespace Stilt

namespace Windows

/-- The part of the in-place store that a window reads: its source's part at its path, sliced
by each of its ranges in turn, as `part` reads the store of windows. -/
def partIn (st : List Value) (loc : Nat) (path : Path) (ranges : List (Int × Int)) :
    Except Fault Value := do
  let v ← match st[loc]? with
    | some v => .ok v
    | none => .error .stuck
  let v ← v.get path
  ranges.foldlM (fun v r => Op.view.apply [v, .int r.1, .int r.2]) v

/-- A value of the model of windows read against the in-place store. -/
def resolveIn (st : List Value) (v : Value) : Except Fault Value := mapWindows (partIn st) v

/-- A window: its location, its path and its ranges. -/
abbrev Window := Nat × Path × List (Int × Int)

mutual

/-- The windows a value holds, those `mapWindows` replaces. -/
def windowsOf : Value → List Window
  | .window loc path ranges => [(loc, path, ranges)]
  | .list vs => windowsOfValues vs
  | .record _ fields => windowsOfFields fields
  | .variant _ _ vs => windowsOfValues vs
  | _ => []

/-- The windows that values hold. -/
def windowsOfValues : List Value → List Window
  | [] => []
  | v :: vs => windowsOf v ++ windowsOfValues vs

/-- The windows that named values hold. -/
def windowsOfFields : List (Name × Value) → List Window
  | [] => []
  | (_, v) :: fields => windowsOf v ++ windowsOfFields fields

end

/-- A value that holds no window. -/
def Free (v : Value) : Prop := windowsOf v = []

mutual

/-- Two maps that agree on the windows of a value replace them alike. -/
theorem mapWindows_congr {f g : Nat → Path → List (Int × Int) → Except Fault Value} :
    ∀ v : Value, (∀ w ∈ windowsOf v, f w.1 w.2.1 w.2.2 = g w.1 w.2.1 w.2.2) →
      mapWindows f v = mapWindows g v
  | .window loc path ranges, h => by simpa [mapWindows, windowsOf] using h
  | .list vs, h => by
    simp only [mapWindows]
    rw [mapWindowsValues_congr vs (by simpa [windowsOf] using h)]
  | .record R fields, h => by
    simp only [mapWindows]
    rw [mapWindowsFields_congr fields (by simpa [windowsOf] using h)]
  | .variant T C vs, h => by
    simp only [mapWindows]
    rw [mapWindowsValues_congr vs (by simpa [windowsOf] using h)]
  | .int _, _ | .float _, _ | .bool _, _ | .str _, _ | .unit, _ | .closure .., _
  | .function .., _ | .handle .., _ => rfl

theorem mapWindowsValues_congr {f g : Nat → Path → List (Int × Int) → Except Fault Value} :
    ∀ vs : List Value, (∀ w ∈ windowsOfValues vs, f w.1 w.2.1 w.2.2 = g w.1 w.2.1 w.2.2) →
      mapWindowsValues f vs = mapWindowsValues g vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [windowsOfValues, List.mem_append] at h
    simp only [mapWindowsValues]
    rw [mapWindows_congr v fun w hw => h w (.inl hw),
      mapWindowsValues_congr vs fun w hw => h w (.inr hw)]

theorem mapWindowsFields_congr {f g : Nat → Path → List (Int × Int) → Except Fault Value} :
    ∀ fields : List (Name × Value),
      (∀ w ∈ windowsOfFields fields, f w.1 w.2.1 w.2.2 = g w.1 w.2.1 w.2.2) →
      mapWindowsFields f fields = mapWindowsFields g fields
  | [], _ => rfl
  | (x, v) :: fields, h => by
    simp only [windowsOfFields, List.mem_append] at h
    simp only [mapWindowsFields]
    rw [mapWindows_congr v fun w hw => h w (.inl hw),
      mapWindowsFields_congr fields fun w hw => h w (.inr hw)]

end

mutual

/-- A value that holds no window is what any map of its windows gives. -/
theorem mapWindows_free (f : Nat → Path → List (Int × Int) → Except Fault Value) :
    ∀ v : Value, windowsOf v = [] → mapWindows f v = .ok v
  | .window .., h => by simp [windowsOf] at h
  | .list vs, h => by
    simp only [mapWindows, mapWindowsValues_free f vs (by simpa [windowsOf] using h)]
    rfl
  | .record R fields, h => by
    simp only [mapWindows, mapWindowsFields_free f fields (by simpa [windowsOf] using h)]
    rfl
  | .variant T C vs, h => by
    simp only [mapWindows, mapWindowsValues_free f vs (by simpa [windowsOf] using h)]
    rfl
  | .int _, _ | .float _, _ | .bool _, _ | .str _, _ | .unit, _ | .closure .., _
  | .function .., _ | .handle .., _ => rfl

theorem mapWindowsValues_free (f : Nat → Path → List (Int × Int) → Except Fault Value) :
    ∀ vs : List Value, windowsOfValues vs = [] → mapWindowsValues f vs = .ok vs
  | [], _ => rfl
  | v :: vs, h => by
    simp only [windowsOfValues, List.append_eq_nil_iff] at h
    simp only [mapWindowsValues, mapWindows_free f v h.1, mapWindowsValues_free f vs h.2]
    rfl

theorem mapWindowsFields_free (f : Nat → Path → List (Int × Int) → Except Fault Value) :
    ∀ fields : List (Name × Value), windowsOfFields fields = [] →
      mapWindowsFields f fields = .ok fields
  | [], _ => rfl
  | (x, v) :: fields, h => by
    simp only [windowsOfFields, List.append_eq_nil_iff] at h
    simp only [mapWindowsFields, mapWindows_free f v h.1, mapWindowsFields_free f fields h.2]
    rfl

end

theorem free_of_mem_values {vs : List Value} (h : windowsOfValues vs = []) :
    ∀ v ∈ vs, Free v := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [windowsOfValues, List.append_eq_nil_iff] at h
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact h.1
    · exact ih h.2 w hw

theorem free_of_mem_fields {fields : List (Name × Value)} (h : windowsOfFields fields = []) :
    ∀ x v, (x, v) ∈ fields → Free v := by
  induction fields with
  | nil => simp
  | cons xv fields ih =>
    obtain ⟨y, u⟩ := xv
    simp only [windowsOfFields, List.append_eq_nil_iff] at h
    intro x v hv
    rcases List.mem_cons.1 hv with he | hv
    · cases he
      exact h.1
    · exact ih h.2 x v hv

theorem windowsOfValues_nil_of_forall {vs : List Value} (h : ∀ v ∈ vs, Free v) :
    windowsOfValues vs = [] := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [windowsOfValues, List.append_eq_nil_iff]
    exact ⟨h v (List.mem_cons_self ..), ih fun w hw => h w (List.mem_cons_of_mem _ hw)⟩

/-- A part of a value that holds no window holds none. -/
theorem free_get : ∀ (v : Value) (p : Path) {w : Value}, Free v → v.get p = .ok w → Free w
  | v, [], _, hv, h => by
    simp only [Value.get, Except.ok.injEq] at h
    exact h ▸ hv
  | .record R fields, .field f :: p, w, hv, h => by
    simp only [Value.get] at h
    split at h
    · rename_i u hu
      exact free_get u p (free_of_mem_fields hv f u (mem_of_lookup hu)) h
    · cases h
  | .list vs, .index i :: p, w, hv, h => by
    simp only [Value.get] at h
    split at h
    · rename_i u hu
      unfold elemAt? at hu
      split at hu
      · exact free_get u p (free_of_mem_values hv u (List.mem_of_getElem? hu)) h
      · cases hu
    · cases h
  | .int _, _ :: _, _, _, h | .float _, _ :: _, _, _, h | .bool _, _ :: _, _, _, h
  | .str _, _ :: _, _, _, h | .unit, _ :: _, _, _, h | .closure .., _ :: _, _, _, h
  | .function .., _ :: _, _, _, h | .handle .., _ :: _, _, _, h | .window .., _ :: _, _, _, h
  | .record .., .index _ :: _, _, _, h | .list _, .field _ :: _, _, _, h
  | .variant .., _ :: _, _, _, h => by simp [Value.get] at h

/-- The part `View.of` takes of a value that holds no window holds none. -/
theorem free_view {v w : Value} {a b : Int} (hv : Free v)
    (h : Op.view.apply [v, .int a, .int b] = .ok w) : Free w := by
  cases v with
  | str s =>
    simp only [Op.apply, Op.applyScalars] at h
    split at h
    · revert h
      cases Op.slice.compute _ with
      | error _ => intro h; cases h
      | ok x => intro h; cases h; cases x <;> rfl
    · cases h
  | list xs =>
    simp only [Op.apply, ListOp.apply, onList, Value.list?] at h
    split at h
    · cases h
      exact windowsOfValues_nil_of_forall fun u hu =>
        free_of_mem_values hv u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
    · cases h
  | _ => simp [Op.apply, ListOp.apply, onList, Value.list?] at h

/-- The parts of a value that holds no window, sliced in turn, hold none. -/
theorem free_slices {v w : Value} (hv : Free v) :
    ∀ ranges : List (Int × Int),
      ranges.foldlM (fun v r => Op.view.apply [v, .int r.1, .int r.2]) v = .ok w → Free w := by
  intro ranges
  induction ranges generalizing v with
  | nil =>
    intro h
    cases h
    exact hv
  | cons r rs ih =>
    intro h
    simp only [List.foldlM_cons] at h
    cases hu : Op.view.apply [v, .int r.1, .int r.2] with
    | error _ => rw [hu] at h; cases h
    | ok u =>
      rw [hu] at h
      exact ih (free_view hv hu) h

/-- A window that the store of windows and the in-place store read alike, as a part that holds
no window. -/
def ReadAlike (sw : List (Option Value)) (si : List Value) (w : Window) : Prop :=
  part sw w.1 w.2.1 w.2.2 = partIn si w.1 w.2.1 w.2.2 ∧
    ∀ u, partIn si w.1 w.2.1 w.2.2 = .ok u → Free u

/-- A location that holds the same value in both stores is read alike at every path and
ranges. -/
theorem part_eq_partIn {sw : List (Option Value)} {si : List Value} {loc : Nat} {u : Value}
    (hw : sw[loc]? = some (some u)) (hi : si[loc]? = some u) (path : Path)
    (ranges : List (Int × Int)) : part sw loc path ranges = partIn si loc path ranges := by
  simp [part, partIn, cell, hw, hi]

/-- A value whose windows both stores read alike reads through the store of windows, at any
depth past the first, as it reads against the in-place store. -/
theorem resolveAt_eq_resolveIn {sw : List (Option Value)} {si : List Value} {v : Value}
    (h : ∀ w ∈ windowsOf v, ReadAlike sw si w) (n : Nat) :
    resolveAt sw (n + 1) v = resolveIn si v := by
  unfold resolveIn
  simp only [resolveAt]
  refine mapWindows_congr v fun w hw => ?_
  obtain ⟨heq, hfree⟩ := h w hw
  rw [heq]
  cases hp : partIn si w.1 w.2.1 w.2.2 with
  | error _ => rfl
  | ok u =>
    have hu := hfree u hp
    cases n <;> exact mapWindows_free _ u hu

/-- So a value read through its windows, as `resolve` reads it, is the value read against the
in-place store. -/
theorem resolve_eq_resolveIn {sw : List (Option Value)} {si : List Value} {v : Value}
    (h : ∀ w ∈ windowsOf v, ReadAlike sw si w) : resolve sw v = resolveIn si v :=
  resolveAt_eq_resolveIn h sw.length

/-- A value that holds no window is itself read against any store. -/
theorem resolveIn_free (si : List Value) {v : Value} (h : Free v) : resolveIn si v = .ok v :=
  mapWindows_free _ v h

/-- The reference of the part a window reads, before its ranges. -/
def Window.ref (w : Window) : InPlace.Ref := ⟨w.1, w.2.1⟩

/-- A window's part is the part of the in-place store at its reference, sliced. -/
theorem partIn_eq_deref (st : List Value) (w : Window) :
    partIn st w.1 w.2.1 w.2.2 = (InPlace.deref ⟨[], st⟩ w.ref []).bind fun v =>
      w.2.2.foldlM (fun v r => Op.view.apply [v, .int r.1, .int r.2]) v := by
  simp only [partIn, InPlace.deref, Window.ref, List.append_nil]
  cases st[w.1]? <;> rfl

/-- Writes in turn at paths disjoint from a part leave it as it was. -/
theorem get_setSeq_disjoint {q : Path} :
    ∀ {W : List (Path × Value)} {v v' : Value}, (∀ pw ∈ W, pw.1.Disjoint q) →
      v.setSeq W = .ok v' → v'.get q = v.get q
  | [], _, _, _, h => by cases h; rfl
  | (p, w) :: W, v, v', hd, h => by
    simp only [Value.setSeq] at h
    cases h₁ : v.set p w with
    | error e => simp [h₁, Except.bind] at h
    | ok v₁ =>
      simp only [h₁, Except.bind] at h
      rw [get_setSeq_disjoint (fun pw hpw => hd pw (List.mem_cons_of_mem _ hpw)) h,
        Value.get_of_set_disjoint (hd (p, w) List.mem_cons_self) h₁]

/-- Writes to the in-place store at paths disjoint from a window's reference, and locations
added past its end, leave the part the window reads as it was. -/
theorem partIn_setSeq {st st₁ : List Value} {W : List (Path × Value)} {w : Window}
    (h : (Value.list st).setSeq W = .ok (.list st₁))
    (hd : ∀ pw ∈ W, pw.1.Disjoint w.ref.toPath) (hl : w.1 < st.length)
    (hl₁ : w.1 < st₁.length) (extra : List Value) :
    partIn (st₁ ++ extra) w.1 w.2.1 w.2.2 = partIn st w.1 w.2.1 w.2.2 := by
  rw [partIn_eq_deref, partIn_eq_deref, InPlace.deref_store_append hl₁,
    InPlace.deref_eq_get hl₁, InPlace.deref_eq_get hl, List.append_nil, get_setSeq_disjoint hd h]

end Windows

end Stilt
