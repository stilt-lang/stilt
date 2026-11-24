import Stilt.Windows.Watched

/-!
# What a write leaves

A write at a path of a value, through windows or not, leaves what is read along a disjoint path
(`getW_setW_disjoint`), and what is read along a prefix of the path is the part there with the
rest written (`getW_setW_prefix`). Several variables can share a location of the callers, each
an `inout` parameter on a part of its own: a write through one leaves the others' parts.
-/

namespace Stilt

namespace Windows

variable {sw : List (Option Value)}

theorem getW_nil (v : Value) : getW sw v [] = .ok v := by
  cases v <;> rfl

/-- A value with no window is read through windows as it is read. -/
theorem getW_of_free : ∀ (v : Value) (q : Path), Free v → getW sw v q = v.get q
  | _, [], _ => by rw [getW_nil]; rfl
  | .window _ _ _, _ :: _, h => by simp [Free, windowsOf] at h
  | .record R fs, .field f :: q, h => by
    cases hc : fs.lookup f with
    | none => simp [getW, Value.get, hc]
    | some c =>
      simp only [getW, Value.get, hc]
      refine getW_of_free c q ?_
      have : ∀ w ∈ windowsOf c, w ∈ windowsOfFields fs := fun w hw => windowsOf_lookup hc hw
      simp only [Free, windowsOf] at h
      rw [h] at this
      exact List.eq_nil_iff_forall_not_mem.2 fun w hw => by simpa using this w hw
  | .list vs, .index i :: q, h => by
    cases hc : elemAt? vs i with
    | none => simp [getW, Value.get, hc]
    | some c =>
      simp only [getW, Value.get, hc]
      refine getW_of_free c q ?_
      have : ∀ w ∈ windowsOf c, w ∈ windowsOfValues vs := fun w hw => windowsOf_elemAt? hc hw
      simp only [Free, windowsOf] at h
      rw [h] at this
      exact List.eq_nil_iff_forall_not_mem.2 fun w hw => by simpa using this w hw
  | .record _ _, .index _ :: _, _ | .list _, .field _ :: _, _ => rfl
  | .int _, _ :: _, _ | .float _, _ :: _, _ | .bool _, _ :: _, _ | .str _, _ :: _, _ | .unit, _ :: _, _
  | .variant .., _ :: _, _ | .closure .., _ :: _, _ | .function .., _ :: _, _
  | .handle .., _ :: _, _ => by cases ‹Step› <;> rfl

/-- A write leaves what is read through windows along a disjoint path. -/
theorem getW_set_disjoint {v w v' : Value} {P q : Path} (hd : P.Disjoint q)
    (h : v.set P w = .ok v') : getW sw v' q = getW sw v q := by
  induction P generalizing v v' q with
  | nil => cases q <;> simp [Path.Disjoint] at hd
  | cons s p ih =>
    cases q with
    | nil => simp [Path.Disjoint] at hd
    | cons t q =>
      cases v with
      | record R fs =>
        cases s with
        | index i => simp [Value.set] at h
        | field k =>
          simp only [Value.set] at h
          split at h
          · rename_i c hc
            cases h₁ : c.set p w with
            | error e => simp [h₁, Functor.map, Except.map] at h
            | ok c' =>
              simp only [h₁, Functor.map, Except.map, Except.ok.injEq] at h
              subst h
              cases t with
              | index j => rfl
              | field g =>
                by_cases hkg : k = g
                · subst hkg
                  have hsome : (fs.lookup k).isSome = true := by simp [hc]
                  simp only [getW, hc, lookup_assocSet_self _ _ _ hsome]
                  exact ih (by simpa [Path.Disjoint] using hd) h₁
                · simp only [getW, lookup_assocSet_ne _ _ (Ne.symm hkg)]
          · cases h
      | list vs =>
        cases s with
        | field k => simp [Value.set] at h
        | index i =>
          simp only [Value.set] at h
          split at h
          · rename_i c hc
            cases h₁ : c.set p w with
            | error e => simp [h₁, Functor.map, Except.map] at h
            | ok c' =>
              simp only [h₁, Functor.map, Except.map, Except.ok.injEq] at h
              subst h
              cases t with
              | field g => rfl
              | index j =>
                by_cases hij : i = j
                · subst hij
                  simp only [getW, hc, elemAt?_set_self hc]
                  exact ih (by simpa [Path.Disjoint] using hd) h₁
                · simp only [getW, elemAt?_set_ne _ (nonneg_of_elemAt? hc) hij]
          · cases h
      | _ => cases s <;> simp [Value.set] at h

/-- Each window of a value reads, where it reads, a part with no window. -/
def PartsFree (sw : List (Option Value)) (y : Value) : Prop :=
  ∀ win ∈ windowsOf y, ∀ d, part sw win.1 win.2.1 win.2.2 = .ok d → Free d

theorem PartsFree.lookup {R : Name} {fs : List (Name × Value)} {k : Name} {c : Value}
    (h : PartsFree sw (.record R fs)) (hc : fs.lookup k = some c) : PartsFree sw c :=
  fun win hw => h win (windowsOf_lookup hc hw)

theorem PartsFree.elemAt {vs : List Value} {i : Int} {c : Value} (h : PartsFree sw (.list vs))
    (hc : elemAt? vs i = some c) : PartsFree sw c :=
  fun win hw => h win (windowsOf_elemAt? hc hw)

theorem PartsFree.window {loc : Nat} {path : Path} {ranges : List (Int × Int)} {d : Value}
    (h : PartsFree sw (.window loc path ranges)) (hp : part sw loc path ranges = .ok d) : Free d :=
  h (loc, path, ranges) (by simp [windowsOf]) d hp

theorem setW_window {loc : Nat} {path : Path} {ranges : List (Int × Int)} {d w : Value}
    (hp : part sw loc path ranges = .ok d) (s : Step) (p : Path) :
    setW sw (.window loc path ranges) (s :: p) w = d.set (s :: p) w := by
  simp only [setW, hp]
  rfl

theorem getW_window {loc : Nat} {path : Path} {ranges : List (Int × Int)} {d : Value}
    (hp : part sw loc path ranges = .ok d) (s : Step) (p : Path) :
    getW sw (.window loc path ranges) (s :: p) = d.get (s :: p) := by
  simp only [getW, hp]
  rfl

theorem part_ok_of_setW {loc : Nat} {path : Path} {ranges : List (Int × Int)} {w y' : Value}
    {s : Step} {p : Path} (h : setW sw (.window loc path ranges) (s :: p) w = .ok y') :
    ∃ d, part sw loc path ranges = .ok d := by
  cases hp : part sw loc path ranges with
  | error e => simp [setW, hp] at h; cases h
  | ok d => exact ⟨d, rfl⟩

/-- A write through windows leaves what is read through windows along a disjoint path. -/
theorem getW_setW_disjoint {y y' w : Value} {P q : Path} (hf : PartsFree sw y)
    (hd : P.Disjoint q) (h : setW sw y P w = .ok y') : getW sw y' q = getW sw y q := by
  induction P generalizing y y' q with
  | nil => cases q <;> simp [Path.Disjoint] at hd
  | cons s p ih =>
    cases q with
    | nil => simp [Path.Disjoint] at hd
    | cons t q =>
      cases y with
      | window loc path ranges =>
        obtain ⟨d, hp⟩ := part_ok_of_setW h
        rw [setW_window hp] at h
        rw [getW_set_disjoint hd h, getW_of_free d _ (hf.window hp), getW_window hp]
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
              | index j => rfl
              | field g =>
                by_cases hkg : k = g
                · subst hkg
                  have hsome : (fs.lookup k).isSome = true := by simp [hc]
                  simp only [getW, hc, lookup_assocSet_self _ _ _ hsome]
                  exact ih (hf.lookup hc) (by simpa [Path.Disjoint] using hd) h₁
                · simp only [getW, lookup_assocSet_ne _ _ (Ne.symm hkg)]
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
              | field g => rfl
              | index j =>
                by_cases hij : i = j
                · subst hij
                  simp only [getW, hc, elemAt?_set_self hc]
                  exact ih (hf.elemAt hc) (by simpa [Path.Disjoint] using hd) h₁
                · simp only [getW, elemAt?_set_ne _ (nonneg_of_elemAt? hc) hij]
          · cases h
      | _ => cases s <;> simp [setW] at h

theorem free_lookup {R : Name} {fs : List (Name × Value)} {k : Name} {c : Value}
    (h : Free (.record R fs)) (hc : fs.lookup k = some c) : Free c :=
  free_get (.record R fs) [.field k] (w := c) h (by simp [Value.get, hc])

theorem free_elemAt {vs : List Value} {i : Int} {c : Value} (h : Free (.list vs))
    (hc : elemAt? vs i = some c) : Free c :=
  free_get (.list vs) [.index i] (w := c) h (by simp [Value.get, hc])

/-- A write through windows into a value with no window is a write. -/
theorem setW_free {w : Value} : ∀ {z : Value} (p : Path), Free z → setW sw z p w = z.set p w
  | z, [], _ => by cases z <;> rfl
  | .window _ _ _, _ :: _, h => by simp [Free, windowsOf] at h
  | .record R fs, .field k :: p, h => by
    cases hc : fs.lookup k with
    | none => simp [setW, Value.set, hc]
    | some c => simp only [setW, Value.set, hc, setW_free p (free_lookup h hc)]
  | .list vs, .index i :: p, h => by
    cases hc : elemAt? vs i with
    | none => simp [setW, Value.set, hc]
    | some c => simp only [setW, Value.set, hc, setW_free p (free_elemAt h hc)]
  | .record _ _, .index _ :: _, _ | .list _, .field _ :: _, _ => rfl
  | .int _, _ :: _, _ | .float _, _ :: _, _ | .bool _, _ :: _, _ | .str _, _ :: _, _
  | .unit, _ :: _, _ | .variant .., _ :: _, _ | .closure .., _ :: _, _ | .function .., _ :: _, _
  | .handle .., _ :: _, _ => by cases ‹Step› <;> rfl

/-- Writing below a prefix of a value with no window, then reading the prefix through windows,
reads the part there with the rest written. -/
theorem getW_set_prefix {w : Value} : ∀ {d y' : Value} {q p : Path}, Free d →
    d.set (q ++ p) w = .ok y' → getW sw y' q = d.get q >>= fun z => z.set p w
  | d, y', [], p, _, h => by
    rw [getW_nil]
    cases d <;> exact h.symm
  | .record R fs, y', .field k :: q, p, hd, h => by
    simp only [List.cons_append, Value.set] at h
    split at h
    · rename_i c hc
      cases h₁ : c.set (q ++ p) w with
      | error e => simp [h₁, Functor.map, Except.map] at h
      | ok c' =>
        simp only [h₁, Functor.map, Except.map, Except.ok.injEq] at h
        subst h
        have hsome : (fs.lookup k).isSome = true := by simp [hc]
        simp only [getW, Value.get, hc, lookup_assocSet_self _ _ _ hsome]
        exact getW_set_prefix (free_lookup hd hc) h₁
    · cases h
  | .list vs, y', .index i :: q, p, hd, h => by
    simp only [List.cons_append, Value.set] at h
    split at h
    · rename_i c hc
      cases h₁ : c.set (q ++ p) w with
      | error e => simp [h₁, Functor.map, Except.map] at h
      | ok c' =>
        simp only [h₁, Functor.map, Except.map, Except.ok.injEq] at h
        subst h
        simp only [getW, Value.get, hc, elemAt?_set_self hc]
        exact getW_set_prefix (free_elemAt hd hc) h₁
    · cases h
  | .window _ _ _, _, _ :: _, _, hd, _ => by simp [Free, windowsOf] at hd
  | .record _ _, _, .index _ :: _, _, _, h | .list _, _, .field _ :: _, _, _, h => by
    simp [Value.set] at h
  | .int _, _, _ :: _, _, _, h | .float _, _, _ :: _, _, _, h | .bool _, _, _ :: _, _, _, h
  | .str _, _, _ :: _, _, _, h | .unit, _, _ :: _, _, _, h | .variant .., _, _ :: _, _, _, h
  | .closure .., _, _ :: _, _, _, h | .function .., _, _ :: _, _, _, h
  | .handle .., _, _ :: _, _, _, h => by cases ‹Step› <;> simp [Value.set] at h

/-- Writing through windows below a prefix of a value, then reading the prefix through windows,
reads the part there written through windows with the rest. -/
theorem getW_setW_prefix {w : Value} : ∀ {y y' : Value} {q p : Path}, PartsFree sw y →
    setW sw y (q ++ p) w = .ok y' → getW sw y' q = getW sw y q >>= fun z => setW sw z p w
  | y, y', [], p, _, h => by
    rw [getW_nil, getW_nil]
    exact h.symm
  | .window loc path ranges, y', t :: q, p, hf, h => by
    simp only [List.cons_append] at h
    obtain ⟨d, hp⟩ := part_ok_of_setW h
    rw [setW_window hp] at h
    have hd := hf.window hp
    rw [getW_set_prefix hd (q := t :: q) h, getW_window hp]
    cases hg : d.get (t :: q) with
    | error e => rfl
    | ok z => exact (setW_free p (free_get d _ hd hg)).symm
  | .record R fs, y', .field k :: q, p, hf, h => by
    simp only [List.cons_append, setW] at h
    split at h
    · rename_i c hc
      cases h₁ : setW sw c (q ++ p) w with
      | error e => simp [h₁, Functor.map, Except.map] at h
      | ok c' =>
        simp only [h₁, Functor.map, Except.map, Except.ok.injEq] at h
        subst h
        have hsome : (fs.lookup k).isSome = true := by simp [hc]
        simp only [getW, hc, lookup_assocSet_self _ _ _ hsome]
        exact getW_setW_prefix (hf.lookup hc) h₁
    · cases h
  | .list vs, y', .index i :: q, p, hf, h => by
    simp only [List.cons_append, setW] at h
    split at h
    · rename_i c hc
      cases h₁ : setW sw c (q ++ p) w with
      | error e => simp [h₁, Functor.map, Except.map] at h
      | ok c' =>
        simp only [h₁, Functor.map, Except.map, Except.ok.injEq] at h
        subst h
        simp only [getW, hc, elemAt?_set_self hc]
        exact getW_setW_prefix (hf.elemAt hc) h₁
    · cases h
  | .record _ _, _, .index _ :: _, _, _, h | .list _, _, .field _ :: _, _, _, h => by
    simp [setW] at h
  | .int _, _, _ :: _, _, _, h | .float _, _, _ :: _, _, _, h | .bool _, _, _ :: _, _, _, h
  | .str _, _, _ :: _, _, _, h | .unit, _, _ :: _, _, _, h | .variant .., _, _ :: _, _, _, h
  | .closure .., _, _ :: _, _, _, h | .function .., _, _ :: _, _, _, h
  | .handle .., _, _ :: _, _, _, h => by cases ‹Step› <;> simp [setW] at h

/-! ## Regions a write misses -/

/-- A write at `p` below the reference `r` misses a window's region: it is on another location,
or at a path disjoint from the write's. -/
def Misses (r : InPlace.Ref) (p : Path) (win : Window) : Prop :=
  win.1 = r.loc → (r.path ++ p).Disjoint win.2.1

theorem misses_of_disjoint {r : InPlace.Ref} {p : Path} {win : Window}
    (h : (r.toPath ++ p).Disjoint win.ref.toPath) : Misses r p win := by
  intro hl
  simpa [InPlace.Ref.toPath, Window.ref, Path.Disjoint, hl] using h

theorem misses_of_lt {r : InPlace.Ref} {p : Path} {win : Window} (h : win.1 < r.loc) :
    Misses r p win :=
  fun hl => absurd hl (by omega)

theorem regionW_write {r : InPlace.Ref} {p : Path} {y y' w : Value}
    (hy : sw[r.loc]? = some (some y)) (h : setW sw y (r.path ++ p) w = .ok y') {win : Window}
    (hm : Misses r p win) {d : Value} (hd : regionW sw win = .ok d) :
    regionW (sw.set r.loc (some y')) win = .ok d := by
  by_cases hl : win.1 = r.loc
  · have hlt : r.loc < sw.length := (List.getElem?_eq_some_iff.1 hy).1
    have hg : regionW sw win = y.get win.2.1 := by
      simp only [regionW, cell, hl, hy]
      rfl
    have hg' : regionW (sw.set r.loc (some y')) win = y'.get win.2.1 := by
      simp only [regionW, cell, hl, List.getElem?_set_self hlt]
      rfl
    rw [hg']
    exact get_setW_disjoint (hm hl) h (hg ▸ hd)
  · rw [regionW_set_ne _ (Ne.symm hl)]
    exact hd

theorem regionI_write {si : List Value} {r : InPlace.Ref} {p : Path} {u u' v : Value}
    (hu : si[r.loc]? = some u) (h : u.set (r.path ++ p) v = .ok u') {win : Window}
    (hm : Misses r p win) : regionI (si.set r.loc u') win = regionI si win := by
  by_cases hl : win.1 = r.loc
  · have hlt : r.loc < si.length := (List.getElem?_eq_some_iff.1 hu).1
    simp only [regionI, cellIn, hl, List.getElem?_set_self hlt, hu]
    exact Value.get_of_set_disjoint (hm hl) h
  · exact regionI_set_ne _ (Ne.symm hl)

end Windows

end Stilt
