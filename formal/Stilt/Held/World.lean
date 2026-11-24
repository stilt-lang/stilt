import Stilt.Cells

/-!
# Held cells in a world

What changes a world's cells keep of a held cell: a cell is made and never unmade, each
keeps its type in its place (`World.Extends`), and a held cell stays held (`World.Held`)
while values go in and out of other cells, cells are made, a `when` holds cells that
aren't held, and a `with` lets go of the cells held since it started (shared.when).
-/

namespace Stilt

/-- The cells of the second list are those of the first, each of the same type in the same
place, and maybe more after them. -/
def Cell.Extends : List Cell → List Cell → Prop
  | [], _ => True
  | b :: bs, c :: cs => c.type = b.type ∧ Cell.Extends bs cs
  | _ :: _, [] => False

/-- The world `w` has the cells of `b`, each of the same type in the same place, and maybe
more made after them: a handle of `b` names the same cell in `w`. -/
def World.Extends (b w : World) : Prop := Cell.Extends b.cells w.cells

/-- A `when` holds the cell the handle names (shared.when). -/
def World.Held (w : World) (h : Ty × Nat) : Prop := ∃ c, w.cell? h.1 h.2 = some c ∧ c.held = true

namespace Cell.Extends

theorem refl : ∀ cs : List Cell, Cell.Extends cs cs
  | [] => trivial
  | _ :: cs => ⟨rfl, refl cs⟩

theorem trans : ∀ {as bs cs : List Cell}, Cell.Extends as bs → Cell.Extends bs cs → Cell.Extends as cs
  | [], _, _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h₁, h₂⟩, ⟨h₃, h₄⟩ => ⟨h₃.trans h₁, trans h₂ h₄⟩
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim

/-- Lists of cells with the same types, in order, extend the same lists. -/
theorem of_types : ∀ {bs cs cs' : List Cell}, Cell.Extends bs cs →
    cs'.map Cell.type = cs.map Cell.type → Cell.Extends bs cs'
  | [], _, _, _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h₁, h₂⟩, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact ⟨h.1.trans h₁, of_types h₂ h.2⟩
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => nomatch h

theorem append : ∀ {bs cs : List Cell} (ds : List Cell), Cell.Extends bs cs →
    Cell.Extends bs (cs ++ ds)
  | [], _, _, _ => trivial
  | _ :: _, _ :: _, _, ⟨h₁, h₂⟩ => ⟨h₁, append _ h₂⟩
  | _ :: _, [], _, h => h.elim

end Cell.Extends

theorem Cell.modifyOf_types {u : Ty} {f : Cell → Cell} (hf : ∀ c, (f c).type = c.type) :
    ∀ (cs : List Cell) (k : Nat), (Cell.modifyOf u f cs k).map Cell.type = cs.map Cell.type
  | [], _ => rfl
  | c :: cs, k => by
    unfold Cell.modifyOf
    split
    · cases k with
      | zero => simp [hf]
      | succ k => simp [Cell.modifyOf_types hf cs k]
    · simp [Cell.modifyOf_types hf cs k]

theorem Cell.letGo_types : ∀ bs cs : List Cell, (Cell.letGo bs cs).map Cell.type = cs.map Cell.type
  | _ :: _, [] => rfl
  | [], cs => by simp [Cell.letGo, Function.comp_def]
  | _ :: bs, c :: cs => by
    simp only [Cell.letGo, List.map_cons, Cell.letGo_types bs cs, List.cons.injEq, and_true]
    split <;> rfl

/-- The `j`-th cell of type `u` once `f` changes the `i`-th of type `u'`, keeping its type. -/
theorem Cell.getOf_modifyOf {u' : Ty} {f : Cell → Cell} (hf : ∀ c, (f c).type = c.type) (u : Ty) :
    ∀ (cs : List Cell) (i j : Nat),
      ((Cell.modifyOf u' f cs i).filter fun c => c.type = u)[j]? =
        if u = u' ∧ j = i then ((cs.filter fun c => c.type = u)[j]?).map f
        else (cs.filter fun c => c.type = u)[j]?
  | [], _, _ => by simp [Cell.modifyOf]
  | c :: cs, i, j => by
    have ih := Cell.getOf_modifyOf (u' := u') hf u cs
    unfold Cell.modifyOf
    by_cases hc : c.type = u'
    · simp only [hc, ↓reduceIte]
      cases i with
      | zero =>
        by_cases hu : u = u'
        · subst hu
          cases j <;> simp [hf, hc]
        · simp [hf, hc, Ne.symm hu, hu]
      | succ i =>
        by_cases hu : u = u'
        · subst hu
          cases j <;> simp [hc, ih]
        · simp [hc, Ne.symm hu, hu, ih]
    · simp only [hc, ↓reduceIte]
      by_cases hcu : c.type = u
      · have hu : u ≠ u' := hcu ▸ hc
        cases j <;> simp [hcu, hu, ih]
      · simp [hcu, ih]

namespace World

variable {b w : World}

/-- A change that keeps the cell's type puts the cell a handle names through it, and leaves
every other cell. -/
theorem cell?_modify {h : Ty × Nat} {f : Cell → Cell} (hf : ∀ c, (f c).type = c.type) (u : Ty)
    (j : Nat) : (w.modify h f).cell? u j =
      if (u, j) = h then (w.cell? u j).map f else w.cell? u j := by
  obtain ⟨u', i⟩ := h
  have := Cell.getOf_modifyOf hf u w.cells i j (u' := u')
  simp only [World.cell?, World.cellsOf, World.modify, Prod.mk.injEq] at this ⊢
  exact this

theorem cell?_push {u : Ty} {v : Value} {u' : Ty} {j : Nat} {c : Cell} (h : w.cell? u' j = some c) :
    (w.push u v).cell? u' j = some c := by
  simp only [World.cell?, World.cellsOf, World.push, List.filter_append] at h ⊢
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1, h]

namespace Extends

theorem refl (w : World) : w.Extends w := Cell.Extends.refl _

theorem trans {a : World} (h₁ : a.Extends b) (h₂ : b.Extends w) : a.Extends w :=
  Cell.Extends.trans h₁ h₂

theorem of_cells {w' : World} (h : b.Extends w) (hc : w'.cells.map Cell.type = w.cells.map Cell.type) :
    b.Extends w' :=
  Cell.Extends.of_types h hc

theorem modify (hb : b.Extends w) {h : Ty × Nat} {f : Cell → Cell} (hf : ∀ c, (f c).type = c.type) :
    b.Extends (w.modify h f) :=
  hb.of_cells (Cell.modifyOf_types hf _ _)

theorem put (hb : b.Extends w) (h : Ty × Nat) (v : Value) (held : Bool) : b.Extends (w.put h v held) :=
  hb.modify fun _ => rfl

theorem letGo (hb : b.Extends w) (before : World) : b.Extends (before.letGo w) :=
  hb.of_cells (Cell.letGo_types _ _)

theorem push (hb : b.Extends w) (u : Ty) (v : Value) : b.Extends (w.push u v) :=
  Cell.Extends.append _ hb

end Extends

namespace Held

variable {k : Ty × Nat}

/-- A change keeps a cell held unless it lets go of that very cell. -/
theorem modify (hk : w.Held k) {h : Ty × Nat} {f : Cell → Cell} (hf : ∀ c, (f c).type = c.type)
    (hh : h = k → ∀ c, c.held = true → (f c).held = true) : (w.modify h f).Held k := by
  obtain ⟨c, hc, hheld⟩ := hk
  rw [World.Held, cell?_modify hf]
  by_cases he : (k.1, k.2) = h
  · simp only [he, ↓reduceIte, hc]
    exact ⟨f c, rfl, hh he.symm c hheld⟩
  · simp only [he, ↓reduceIte]
    exact ⟨c, hc, hheld⟩

theorem put (hk : w.Held k) {h : Ty × Nat} (hne : h ≠ k) (v : Value) (held : Bool) :
    (w.put h v held).Held k :=
  hk.modify (fun _ => rfl) fun he => absurd he hne

theorem push (hk : w.Held k) (u : Ty) (v : Value) : (w.push u v).Held k := by
  obtain ⟨c, hc, hheld⟩ := hk
  exact ⟨c, cell?_push hc, hheld⟩

end Held

/-- Cells of the same list are held alike. -/
theorem Held.of_cells {w' : World} {k : Ty × Nat} (hc : w'.cells = w.cells) (hk : w.Held k) :
    w'.Held k := by
  simpa [World.Held, World.cell?, World.cellsOf, hc] using hk

/-- An operation on the world keeps its cells, each in its place and held as it was. -/
theorem _root_.Stilt.Op.run_held {o : Op} {vs : List Value} {v : Value} {w' : World}
    (h : o.run vs w = .ok (v, w')) : w.Extends w' ∧ ∀ k, w.Held k → w'.Held k := by
  cases o
  case world k =>
    rcases WorldOp.run_cells h with hc | ⟨u, x, -, rfl⟩
    · exact ⟨(Extends.refl w).of_cells (by rw [hc]), fun _ hk => hk.of_cells hc⟩
    · exact ⟨(Extends.refl w).push u x, fun _ hk => hk.push u x⟩
  all_goals
    simp only [Op.run, Functor.map, Except.map] at h
    split at h <;> cases h
    exact ⟨Extends.refl w, fun _ hk => hk⟩

theorem _root_.Stilt.Forall₂.exists_of_mem {α β : Type} {R : α → β → Prop} {a : α} :
    ∀ {as : List α} {bs : List β}, Forall₂ R as bs → a ∈ as → ∃ b ∈ bs, R a b
  | _, _, .cons hr hs, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨b, hb, hab⟩ := Forall₂.exists_of_mem hs ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem holdAll : ∀ (hs : List (Ty × Nat)) (w : World),
    w.Extends (hs.foldl (fun x h => x.modify h fun c => { c with held := true }) w) ∧
      ∀ k, w.Held k → (hs.foldl (fun x h => x.modify h fun c => { c with held := true }) w).Held k
  | [], w => ⟨Extends.refl w, fun _ hk => hk⟩
  | h :: hs, w => by
    obtain ⟨he, hk⟩ := holdAll hs (w.modify h fun c => { c with held := true })
    exact ⟨((Extends.refl w).modify (h := h) (f := fun c => { c with held := true }) fun _ => rfl).trans he,
      fun k hw => hk k (hw.modify (fun _ => rfl) fun _ _ _ => rfl)⟩

/-- A `when` that holds cells holds none that was held, and keeps every cell held that was
(shared.when-on-value-already-held). -/
theorem take_held {hs : List (Ty × Nat)} {vs : List Value} {w' : World}
    (h : World.take hs w = .ok (vs, w')) :
    w.Extends w' ∧ ∀ k, w.Held k → k ∉ hs ∧ w'.Held k := by
  unfold World.take at h
  split at h
  · rename_i cs hcs
    split at h
    · rename_i hok
      cases h
      obtain ⟨he, hk⟩ := holdAll hs w
      refine ⟨he, fun k hw => ⟨fun hm => ?_, hk k hw⟩⟩
      obtain ⟨c, hc, hkc⟩ := (mapM_cells hcs).exists_of_mem hm
      obtain ⟨c', hc', hheld⟩ := hw
      rw [hc'] at hkc
      cases hkc
      have := List.all_eq_true.1 hok.2 c hc
      simp [hheld] at this
    · cases h
  · cases h

theorem _root_.Stilt.Cell.getOf_letGo (u : Ty) : ∀ (bs cs : List Cell) (j : Nat) {b c : Cell},
    Cell.Extends bs cs → (bs.filter fun c => c.type = u)[j]? = some b → b.held = true →
      (cs.filter fun c => c.type = u)[j]? = some c → c.held = true →
      ((Cell.letGo bs cs).filter fun c => c.type = u)[j]? = some c
  | [], _, _, _, _, _, hb, _, _, _ => by simp at hb
  | _ :: _, [], _, _, _, he, _, _, _, _ => he.elim
  | b₀ :: bs, c₀ :: cs, j, b, c, ⟨ht, he⟩, hb, hbh, hc, hch => by
    have ih := Cell.getOf_letGo u bs cs
    have hl : Cell.letGo (b₀ :: bs) (c₀ :: cs) =
        (if c₀.held && !b₀.held then { c₀ with held := false } else c₀) :: Cell.letGo bs cs := rfl
    rw [hl]
    by_cases hu : b₀.type = u
    · have hcu : c₀.type = u := ht.trans hu
      cases j with
      | zero =>
        simp only [List.filter_cons, hu, hcu, decide_true, ↓reduceIte, List.getElem?_cons_zero,
          Option.some.injEq] at hb hc
        subst hb hc
        simp [hcu, hbh]
      | succ j =>
        simp only [List.filter_cons, hu, hcu, decide_true, ↓reduceIte,
          List.getElem?_cons_succ] at hb hc
        have hcu' : (if c₀.held && !b₀.held then { c₀ with held := false } else c₀).type = u := by
          split <;> exact hcu
        simp only [List.filter_cons, hcu', decide_true, ↓reduceIte, List.getElem?_cons_succ]
        exact ih j he hb hbh hc hch
    · have hcu : ¬c₀.type = u := ht ▸ hu
      have hcu' : ¬(if c₀.held && !b₀.held then { c₀ with held := false } else c₀).type = u := by
        split <;> exact hcu
      simp only [List.filter_cons, hu, hcu, decide_false, Bool.false_eq_true, ↓reduceIte] at hb hc
      simp only [List.filter_cons, hcu', decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih j he hb hbh hc hch

/-- A `with` that lets go of the cells held since it started keeps those held then held. -/
theorem Held.letGo {before : World} {k : Ty × Nat} (he : before.Extends w) (hb : before.Held k)
    (hw : w.Held k) : (before.letGo w).Held k := by
  obtain ⟨b, hb, hbh⟩ := hb
  obtain ⟨c, hc, hch⟩ := hw
  exact ⟨c, Cell.getOf_letGo k.1 before.cells w.cells k.2 he hb hbh hc hch, hch⟩

end World

end Stilt
