import Stilt.Holding
import Stilt.Ops

/-!
# Cells

Where the cells of a world come from as `when`s hold them and put values back, and what is
true of every value a world keeps: holding a cell, putting a value back, letting cells go and
making a cell keep a property of every cell's value that the values put in have
(`World.All`). So the values a `when` takes out of a world have it too (shared.when).
-/

namespace Stilt

theorem Cell.mem_modifyOf {u : Ty} {f : Cell → Cell} :
    ∀ {cs : List Cell} {k : Nat} {c' : Cell},
      c' ∈ Cell.modifyOf u f cs k → c' ∈ cs ∨ ∃ c ∈ cs, c.type = u ∧ c' = f c
  | [], _, _, h => nomatch h
  | c :: cs, k, c', h => by
    have tail : c' ∈ Cell.modifyOf u f cs k → c' ∈ c :: cs ∨ ∃ c₀ ∈ c :: cs, c₀.type = u ∧ c' = f c₀ :=
      fun h => (Cell.mem_modifyOf h).elim (fun h => .inl (List.mem_cons_of_mem _ h))
        fun ⟨c₀, hc, hu, he⟩ => .inr ⟨c₀, List.mem_cons_of_mem _ hc, hu, he⟩
    unfold Cell.modifyOf at h
    split at h
    · rename_i hu
      cases k with
      | zero =>
        rcases List.mem_cons.1 h with rfl | h
        · exact .inr ⟨c, List.mem_cons_self, hu, rfl⟩
        · exact .inl (List.mem_cons_of_mem _ h)
      | succ k =>
        rcases List.mem_cons.1 h with rfl | h
        · exact .inl List.mem_cons_self
        · rcases Cell.mem_modifyOf h with h | ⟨c₀, hc, hu', rfl⟩
          · exact .inl (List.mem_cons_of_mem _ h)
          · exact .inr ⟨c₀, List.mem_cons_of_mem _ hc, hu', rfl⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inl List.mem_cons_self
      · exact tail h

theorem Cell.mem_letGo : ∀ {bs cs : List Cell} {c' : Cell}, c' ∈ Cell.letGo bs cs →
    ∃ c ∈ cs, c'.type = c.type ∧ c'.value = c.value
  | _ :: _, [], _, h => nomatch h
  | [], _, _, h => by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
    exact ⟨c, hc, rfl, rfl⟩
  | b :: bs, c :: cs, c', h => by
    rcases List.mem_cons.1 h with rfl | h
    · refine ⟨c, List.mem_cons_self, ?_, ?_⟩ <;> split <;> rfl
    · obtain ⟨c₀, hc, h₁, h₂⟩ := Cell.mem_letGo h
      exact ⟨c₀, List.mem_cons_of_mem _ hc, h₁, h₂⟩

/-- The cell a handle names is a cell of the world, of the handle's type. -/
theorem World.cell?_mem {w : World} {u : Ty} {k : Nat} {c : Cell} (h : w.cell? u k = some c) :
    c ∈ w.cells ∧ c.type = u := by
  have hm := List.mem_of_getElem? h
  simpa [World.cellsOf] using hm

theorem mapM_cells {w : World} : ∀ {hs : List (Ty × Nat)} {cs : List Cell},
    hs.mapM (fun h => w.cell? h.1 h.2) = some cs → Forall₂ (fun h c => w.cell? h.1 h.2 = some c) hs cs
  | [], cs, h => by cases h; exact .nil
  | h :: hs, cs, hm => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hm
    obtain ⟨c, hc, cs', hcs, rfl⟩ := hm
    exact .cons hc (mapM_cells hcs)

/-- The cells that handles name are cells of the world. -/
theorem World.mem_of_cells {w : World} {c : Cell} : ∀ {hs : List (Ty × Nat)} {cs : List Cell},
    c ∈ cs → Forall₂ (fun h c => w.cell? h.1 h.2 = some c) hs cs → c ∈ w.cells
  | _, _, hc, .cons hh hr => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact (World.cell?_mem hh).1
    · exact World.mem_of_cells hc hr

/-- Every cell of a world holds a value of which `P` holds. -/
def World.All (P : Value → Prop) (w : World) : Prop := ∀ c ∈ w.cells, P c.value

namespace World.All

variable {P : Value → Prop} {w : World}

theorem start (input : String) : (World.start input).All P := fun _ h => nomatch h

theorem push (hw : w.All P) {u : Ty} {v : Value} (hv : P v) : (w.push u v).All P := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · exact hw c hc
  · rw [List.mem_singleton.1 hc]
    exact hv

theorem modify (hw : w.All P) {h : Ty × Nat} {f : Cell → Cell} (hf : ∀ c ∈ w.cells, P (f c).value) :
    (w.modify h f).All P := by
  intro c' hc'
  rcases Cell.mem_modifyOf hc' with hc' | ⟨c, hc, -, rfl⟩
  · exact hw c' hc'
  · exact hf c hc

theorem put (hw : w.All P) (h : Ty × Nat) {v : Value} (hv : P v) (held : Bool) :
    (w.put h v held).All P :=
  hw.modify fun _ _ => hv

theorem letGo (hw : w.All P) (before : World) : (before.letGo w).All P := by
  intro c' hc'
  obtain ⟨c, hc, -, h⟩ := Cell.mem_letGo hc'
  rw [h]
  exact hw c hc

theorem holdAll : ∀ (hs : List (Ty × Nat)) {w : World}, w.All P →
    (hs.foldl (fun x h => x.modify h fun c => { c with held := true }) w).All P
  | [], _, hw => hw
  | _ :: hs, _, hw => holdAll hs (hw.modify fun c hc => hw c hc)

/-- An operation on the world leaves its cells, or adds one holding an argument. -/
theorem _root_.Stilt.WorldOp.run_cells {k : WorldOp} {vs : List Value} {v : Value} {w w' : World}
    (h : k.run vs w = .ok (v, w')) : w'.cells = w.cells ∨ ∃ u x, x ∈ vs ∧ w' = w.push u x := by
  unfold WorldOp.run at h
  split at h <;> cases h
  all_goals first | exact .inl rfl | exact .inr ⟨_, _, List.mem_singleton_self _, rfl⟩

/-- An operation keeps a property of every cell's value that its arguments have. -/
theorem run (hw : w.All P) {o : Op} {vs : List Value} {v : Value} {w' : World} (hvs : ∀ v ∈ vs, P v)
    (h : o.run vs w = .ok (v, w')) : w'.All P := by
  cases o
  case world k =>
    rcases WorldOp.run_cells h with hc | ⟨u, x, hx, rfl⟩
    · exact fun c hm => hw c (hc ▸ hm)
    · exact hw.push (hvs x hx)
  all_goals
    simp only [Op.run, Functor.map, Except.map] at h
    split at h <;> cases h
    exact hw

/-- The values a `when` takes out of a world have every property its cells' values have,
and so do the cells of the world it leaves. -/
theorem take (hw : w.All P) {hs : List (Ty × Nat)} {vs : List Value} {w' : World}
    (h : World.take hs w = .ok (vs, w')) : (∀ v ∈ vs, P v) ∧ w'.All P := by
  unfold World.take at h
  split at h
  · rename_i cs hcs
    split at h
    · cases h
      refine ⟨fun v hv => ?_, holdAll hs hw⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
      exact hw c (World.mem_of_cells hc (mapM_cells hcs))
    · cases h
  · cases h

end World.All

end Stilt
