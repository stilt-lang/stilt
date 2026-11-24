import Stilt.Moves.Oblivious
import Stilt.Moves.Maps

/-!
# Holding shared values sees through marks

Erasing a world's cells commutes with what a `when` and a `with` do to them: taking and
holding cells, putting values back and letting cells go (shared.when). So a `when` and a
`with` run alike on erased states (`Eval.Erases.held`, `Eval.Erases.letGo`).
-/

namespace Stilt

theorem Cell.modifyOf_erase {u : Ty} {f g : Cell → Cell} (hfg : ∀ c, f c.erase = (g c).erase) :
    ∀ (cs : List Cell) (k : Nat),
      Cell.modifyOf u f (cs.map Cell.erase) k = (Cell.modifyOf u g cs k).map Cell.erase
  | [], _ => rfl
  | c :: cs, k => by
    show Cell.modifyOf u f (c.erase :: cs.map Cell.erase) k = _
    unfold Cell.modifyOf
    show (if c.type = u then _ else _) = _
    split
    · cases k with
      | zero => simp [hfg]
      | succ k => simp [Cell.modifyOf_erase hfg cs k]
    · simp [Cell.modifyOf_erase hfg cs k]

theorem World.modify_erase {f g : Cell → Cell} (hfg : ∀ c, f c.erase = (g c).erase) (w : World)
    (h : Ty × Nat) : w.erase.modify h f = (w.modify h g).erase := by
  simp only [World.modify, World.erase, Cell.modifyOf_erase hfg]

theorem World.put_erase (w : World) (h : Ty × Nat) (v : Value) (held : Bool) :
    w.erase.put h v.erase held = (w.put h v held).erase :=
  World.modify_erase (f := fun c => { c with value := v.erase, held })
    (g := fun c => { c with value := v, held }) (fun _ => rfl) w h

theorem World.cell?_erase (w : World) (u : Ty) (k : Nat) :
    w.erase.cell? u k = (w.cell? u k).map Cell.erase := by
  simp only [World.cell?, World.cellsOf, World.erase, List.filter_map]
  rw [List.getElem?_map]
  rfl

theorem World.mapM_cell?_erase (w : World) : ∀ hs : List (Ty × Nat),
    hs.mapM (fun h => w.erase.cell? h.1 h.2) =
      (hs.mapM fun h => w.cell? h.1 h.2).map (List.map Cell.erase)
  | [] => rfl
  | h :: hs => by
    rw [List.mapM_cons, List.mapM_cons, World.cell?_erase, World.mapM_cell?_erase w hs]
    cases w.cell? h.1 h.2 <;> cases (hs.mapM fun h => w.cell? h.1 h.2) <;> rfl

theorem World.holdAll_erase : ∀ (hs : List (Ty × Nat)) (w : World),
    hs.foldl (fun x h => x.modify h fun c => { c with held := true }) w.erase =
      (hs.foldl (fun x h => x.modify h fun c => { c with held := true }) w).erase
  | [], _ => rfl
  | h :: hs, w => by
    simp only [List.foldl_cons]
    rw [World.modify_erase (g := fun c => { c with held := true }) (fun _ => rfl), World.holdAll_erase hs]

/-- Taking cells of an erased world takes the erased values. -/
theorem World.take_erase (hs : List (Ty × Nat)) (w : World) :
    World.take hs w.erase = (World.take hs w).map fun p => (p.1.map Value.erase, p.2.erase) := by
  unfold World.take
  rw [World.mapM_cell?_erase]
  cases (hs.mapM fun h => w.cell? h.1 h.2) with
  | none => rfl
  | some cs =>
    simp only [Option.map_some, List.all_map]
    have : ((fun c : Cell => !c.held) ∘ Cell.erase) = fun c => !c.held := rfl
    rw [this]
    split
    · simp [Except.map, World.holdAll_erase, Cell.erase]
    · rfl

theorem Cell.letGo_erase : ∀ bs cs : List Cell,
    Cell.letGo (bs.map Cell.erase) (cs.map Cell.erase) = (Cell.letGo bs cs).map Cell.erase
  | _ :: _, [] => rfl
  | [], cs => by simp [Cell.letGo, Cell.erase]
  | b :: bs, c :: cs => by
    simp only [List.map_cons, Cell.letGo, Cell.letGo_erase bs cs]
    congr 1
    show (if c.held && !b.held then _ else _) = _
    split <;> rfl

theorem World.letGo_erase (before w : World) : before.erase.letGo w.erase = (before.letGo w).erase := by
  simp only [World.letGo, World.erase, Cell.letGo_erase]

/-! ## Runs alike on erased states -/

/-- Putting values back from an erased state puts back the erased values. -/
theorem Copy.putBack_erase (held : Bool) : ∀ (cells : List (Name × Ty × Nat)) (s : Copy.State),
    Copy.memory.putBack held cells (eraseState s) = (Copy.memory.putBack held cells s).map eraseState
  | [], _ => rfl
  | (x, h) :: rest, (fr, w) => by
    have hr := Copy.read_erase fr x []
    show (do let v ← Copy.read (eraseBindings fr) x []
             Copy.memory.putBack held rest (eraseBindings fr, w.erase.put h v held)) =
      (do let v ← Copy.read fr x []; Copy.memory.putBack held rest (fr, w.put h v held)).map eraseState
    rw [hr]
    cases Copy.read fr x [] with
    | error e => rfl
    | ok v =>
      show Copy.memory.putBack held rest (eraseBindings fr, w.erase.put h v.erase held) = _
      rw [World.put_erase]
      exact Copy.putBack_erase held rest (fr, w.put h v held)

variable {α : Type} {f : α → α}

theorem Outcome.Rel.after_erase {held : Bool} {cells : List (Name × Ty × Nat)} {s : Copy.State}
    {o o' : Copy.State → Outcome Copy.State α}
    (h : ∀ s', (o s').Rel (Outcome.erasing f) (o' (eraseState s'))) :
    (Outcome.after (Copy.memory.putBack held cells) s o).Rel (Outcome.erasing f)
      (Outcome.after (Copy.memory.putBack held cells) (eraseState s) o') := by
  unfold Outcome.after
  rw [Copy.putBack_erase]
  cases Copy.memory.putBack held cells s with
  | ok s' => exact h s'
  | error e => exact erasing_fault e s

/-- A `when`'s block and its erasure's, their names' values put back, end alike. -/
theorem Outcome.Rel.release_erase (cells : List (Name × Ty × Nat)) :
    ∀ {o o' : Outcome Copy.State α}, o.Rel (Outcome.erasing f) o' →
      (o.release Copy.memory cells).Rel (Outcome.erasing f) (o'.release Copy.memory cells)
  | .done _ _, .done _ _, ⟨rfl, rfl⟩ | .raised _ _, .raised _ _, ⟨rfl, rfl⟩
  | .jumped _ _, .jumped _ _, ⟨rfl, rfl⟩ | .panicked _ _, .panicked _ _, ⟨rfl, rfl⟩ =>
    Outcome.Rel.after_erase fun _ => ⟨rfl, rfl⟩
  | .performed _ _ _ _, .performed _ _ _ _, ⟨⟨rfl, rfl, rfl⟩, hk⟩ =>
    Outcome.Rel.after_erase fun _ =>
      ⟨⟨rfl, rfl, rfl⟩, fun w x w' x' hw => Outcome.Rel.release_erase cells (hk w x w' x' hw)⟩
  | .outOfFuel, .outOfFuel, _ | .stuck, .stuck, _ => trivial

/-- A `with` and its erasure's, letting go of the same cells, end alike. -/
theorem Outcome.Rel.letGo_erase (before : World) :
    ∀ {o o' : Outcome Copy.State α}, o.Rel (Outcome.erasing f) o' →
      (o.letGo Copy.memory before).Rel (Outcome.erasing f) (o'.letGo Copy.memory before.erase)
  | .done _ (_, _), .done _ _, ⟨rfl, rfl⟩ | .raised _ (_, _), .raised _ _, ⟨rfl, rfl⟩
  | .jumped _ (_, _), .jumped _ _, ⟨rfl, rfl⟩ | .panicked _ (_, _), .panicked _ _, ⟨rfl, rfl⟩ =>
    ⟨rfl, by show (_, before.erase.letGo (World.erase _)) = (_, _); rw [World.letGo_erase]; rfl⟩
  | .performed _ _ _ _, .performed _ _ _ _, ⟨h, hk⟩ =>
    ⟨h, fun w x w' x' hw => Outcome.Rel.letGo_erase before (hk w x w' x' hw)⟩
  | .outOfFuel, .outOfFuel, _ | .stuck, .stuck, _ => trivial

namespace Eval.Erases

theorem letGo {m m' : Eval Copy.State α} (hm : Erases f m m') :
    Erases f (Eval.letGo Copy.memory m) (Eval.letGo Copy.memory m') := fun s =>
  (hm s).letGo_erase s.2

theorem release {m m' : Eval Copy.State α} (cells : List (Name × Ty × Nat)) (hm : Erases f m m') :
    Erases f (Eval.release Copy.memory cells m) (Eval.release Copy.memory cells m') := fun s =>
  (hm s).release_erase cells

theorem _root_.Stilt.Value.cellOf_erase : ∀ v : Value, v.erase.cellOf = v.cellOf
  | .handle .. | .int _ | .float _ | .bool _ | .str _ | .unit | .record .. | .variant .. | .list _
  | .closure .. | .function .. | .window .. => rfl

theorem mapM_cellOf_erase : ∀ vs : List Value, (eraseValues vs).mapM Value.cellOf = vs.mapM Value.cellOf
  | [] => rfl
  | v :: vs => by simp only [eraseValues, List.mapM_cons, Value.cellOf_erase, mapM_cellOf_erase vs]

theorem zip_eraseValues : ∀ (names : List Name) (vs : List Value),
    names.zip (eraseValues vs) = eraseBindings (names.zip vs)
  | [], _ | _ :: _, [] => rfl
  | _ :: names, _ :: vs => by simp [eraseValues, eraseBindings, zip_eraseValues names vs]

/-- A `when` and its erasure's run alike (shared.when). -/
theorem held {m m' : Eval Copy.State Value} (hm : Erases Value.erase m m') (names : List Name)
    (vs : List Value) :
    Erases Value.erase (Eval.held Copy.memory m names vs)
      (Eval.held Copy.memory m' names (eraseValues vs)) := by
  unfold Eval.held
  rw [mapM_cellOf_erase]
  refine bind (f := id) (by simpa using ofExcept id (vs.mapM Value.cellOf)) fun cells => ?_
  simp only [id]
  have hl : ∀ v : Value, Erases eraseValues (Eval.asList v) (Eval.asList v.erase) := fun v => by
    cases v <;> first | exact pure eraseValues _ | exact fail eraseValues .stuck
  refine bind (bind (world fun x => ?_) hl) fun vs' => ?_
  · rw [World.take_erase]
    cases World.take cells x with
    | error e => rfl
    | ok p => simp [Except.map, Value.erase, eraseValues_eq_map]
  · rw [zip_eraseValues, show (eraseValues vs').length = vs'.length by simp [eraseValues_eq_map]]
    split
    · exact withVars (release _ hm) _
    · exact fail _ _

end Eval.Erases

end Stilt
