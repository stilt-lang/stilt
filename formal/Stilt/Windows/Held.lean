import Stilt.Windows.Match
import Stilt.Windows.Handling

/-!
# A `when`

A `when` on handles read alike holds the same cells in both models: a handle is no window and
reads as itself, and a window's part is a string or a list, which names no cell. Both take the
same values out of the one world, which the checks accept and which hold no window, bind its
names to them, each in a scope of its own with a written type and no sources, and put back the
same values, read through their windows on the windows' side, however its block ends
(shared.when).
-/

namespace Stilt

namespace Windows

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

/-! ## The cells a `when` holds -/

/-- A value of windows and its reading name the same cell, or none. -/
theorem cellOf_rel {si : List Value} {sw : List (Option Value)} {w v : Value}
    (h : resolveIn si w = .ok v) (hh : ∀ win ∈ windowsOf w, Holds sw si win) :
    w.cellOf = v.cellOf := by
  cases w with
  | window l p r =>
    have hv := (hh (l, p, r) List.mem_cons_self).viewable_part (d := v) h
    cases v <;> simp_all [viewable, Value.cellOf]
  | list vs => obtain ⟨_, -, rfl⟩ := mapWindows_list.1 h; rfl
  | record R fs => obtain ⟨_, -, rfl⟩ := mapWindows_record.1 h; rfl
  | variant T C vs => obtain ⟨_, -, rfl⟩ := mapWindows_variant.1 h; rfl
  | int _ | float _ | bool _ | str _ | unit | closure _ _ _ _ _ | function _ _ _ | handle _ _ =>
    simp only [resolveIn, mapWindows, Except.ok.injEq] at h
    subst h
    rfl

/-- Handles read alike name the same cells. -/
theorem cells_rel {si : List Value} {sw : List (Option Value)} :
    ∀ {ws vs : List Value}, mapWindowsValues (partIn si) ws = .ok vs →
      (∀ win ∈ windowsOfValues ws, Holds sw si win) → ws.mapM Value.cellOf = vs.mapM Value.cellOf
  | [], _, h, _ => by rw [mapWindowsValues_nil h]
  | w :: ws, _, h, hh => by
    obtain ⟨v, vs, hv, hvs, rfl⟩ := mapWindowsValues_cons.1 h
    have hw : ∀ win ∈ windowsOf w, Holds sw si win := fun win hm =>
      hh win (by simp only [windowsOfValues, List.mem_append]; exact .inl hm)
    have hws : ∀ win ∈ windowsOfValues ws, Holds sw si win := fun win hm =>
      hh win (by simp only [windowsOfValues, List.mem_append]; exact .inr hm)
    rw [List.mapM_cons, List.mapM_cons, cellOf_rel hv hw, cells_rel hvs hws]

/-- The values a `when` takes out of the one world: the same, which the checks accept. -/
theorem SimP.take {Q : IState → WState → Prop} (cells : List (Ty × Nat)) :
    SimP D c pend Q (fun us us' _ _ => us' = us ∧ ∀ u ∈ us, u.Viewed D)
      (Eval.world InPlace.memory (fun w => (World.take cells w).map fun p => (.list p.1, p.2)) >>=
        Eval.asList)
      (Eval.world memory (fun w => (World.take cells w).map fun p => (.list p.1, p.2)) >>=
        Eval.asList) := by
  intro si sw hp _ _
  obtain ⟨st, w⟩ := si
  obtain ⟨sv, w'⟩ := sw
  have hw : w' = w := hp.agree.world
  subst hw
  show ((Eval.world InPlace.memory _ (st, w')).bind fun a s => Eval.asList a s).Rel _
    ((Eval.world memory _ (sv, w')).bind fun a s => Eval.asList a s)
  cases ht : World.take cells w' with
  | error e =>
    have hf : ((World.take cells w').map fun p => (Value.list p.1, p.2)) = .error e := by
      rw [ht]; rfl
    have e₁ : Eval.world InPlace.memory _ (st, w') = Outcome.fault e (st, w') :=
      Eval.world_error (F := InPlace.frames)
        (f := fun w => (World.take cells w).map fun p => (Value.list p.1, p.2)) hf
    have e₂ : Eval.world memory _ (sv, w') = Outcome.fault e (sv, w') :=
      Eval.world_error (F := Windows.frames)
        (f := fun w => (World.take cells w).map fun p => (Value.list p.1, p.2)) hf
    rw [e₁, e₂]
    cases e
    · exact ⟨hp, rfl, rfl⟩
    · trivial
  | ok p =>
    obtain ⟨us, x⟩ := p
    have hf : ((World.take cells w').map fun p => (Value.list p.1, p.2)) = .ok (.list us, x) := by
      rw [ht]; rfl
    have e₁ : Eval.world InPlace.memory _ (st, w') = Outcome.done (.list us) (st, x) :=
      Eval.world_ok (F := InPlace.frames)
        (f := fun w => (World.take cells w).map fun p => (Value.list p.1, p.2)) hf
    have e₂ : Eval.world memory _ (sv, w') = Outcome.done (.list us) (sv, x) :=
      Eval.world_ok (F := Windows.frames)
        (f := fun w => (World.take cells w).map fun p => (Value.list p.1, p.2)) hf
    rw [e₁, e₂]
    obtain ⟨hus, hx⟩ := hp.agree.cells.take ht
    exact ⟨hp.setWorld hx, rfl, rfl, hus⟩

/-! ## Putting values back -/

/-- Putting the names' values back from states the simulation keeps: the same fault, or the
same world, with frames unchanged. -/
theorem putBack_rel (held : Bool) : ∀ (cells : List (Name × Ty × Nat)) {si : IState}
    {sw : WState}, Pre D c pend si sw →
    (∃ e, InPlace.memory.putBack held cells si = .error e ∧
        memory.putBack held cells sw = .error e) ∨
      ∃ x, InPlace.memory.putBack held cells si = .ok (si.1, x) ∧
        memory.putBack held cells sw = .ok (sw.1, x) ∧ Pre D c pend (si.1, x) (sw.1, x)
  | [], (st, w), (sv, w'), hp => by
    have hw : w' = w := hp.agree.world
    subst hw
    exact .inr ⟨_, rfl, rfl, hp⟩
  | (y, h) :: rest, (st, w), (sv, w'), hp => by
    have hw : w' = w := hp.agree.world
    subst hw
    simp only [Memory.putBack]
    rcases Pre.var hp y with ⟨f, h₁, h₂⟩ | ⟨v, u, h₁, h₂, hg⟩
    · have e₁ : InPlace.memory.read (st, w') y [] = .error f := h₁
      have e₂ : memory.read (sv, w') y [] = .error f := by
        show (readWindows sv y [] >>= resolve sv.store) = _
        rw [h₂]; rfl
      rw [e₁, e₂]
      exact .inl ⟨f, rfl, rfl⟩
    · have e₁ : InPlace.memory.read (st, w') y [] = .ok v := h₁
      have e₂ : memory.read (sv, w') y [] = .ok v := by
        show (readWindows sv y [] >>= resolve sv.store) = _
        rw [h₂]
        exact hg.1.resolve
      have hx : (w'.put h v held).All (Value.Viewed D) := hp.agree.cells.put h hg.2.2 held
      rw [e₁, e₂]
      exact putBack_rel held rest (hp.setWorld hx)

/-- Putting values back after an outcome, from states the simulation keeps. -/
theorem Rel.after {α β : Type} {R : Outcome.Relation IState WState α β} {held : Bool}
    {cells : List (Name × Ty × Nat)} {si : IState} {sw : WState} (hp : Pre D c pend si sw)
    (hfault : ∀ k, R.panicked k si k sw) {o : IState → Outcome IState α}
    {o' : WState → Outcome WState β}
    (ho : ∀ x, Pre D c pend (si.1, x) (sw.1, x) → (o (si.1, x)).Rel R (o' (sw.1, x))) :
    (Outcome.after (InPlace.memory.putBack held cells) si o).Rel R
      (Outcome.after (memory.putBack held cells) sw o') := by
  unfold Outcome.after
  rcases putBack_rel held cells hp with ⟨e, h₁, h₂⟩ | ⟨x, h₁, h₂, hp'⟩
  · rw [h₁, h₂]
    cases e
    · exact hfault _
    · trivial
  · rw [h₁, h₂]
    exact ho x hp'

/-- A `when`'s block in both models, its names' values put back however it ends, when what
the relation `G` says of results reads no world. -/
theorem Rel.release {G : Value → Value → IState → WState → Prop}
    (hG : ∀ a b si sw x, G a b si sw → G a b (si.1, x) (sw.1, x))
    (cells : List (Name × Ty × Nat)) {env : List (Name × InPlace.Ref)} :
    ∀ {o : Outcome IState Value} {o' : Outcome WState Value}, o.Rel (CorrG D c pend G env) o' →
      (o.release InPlace.memory cells).Rel (CorrG D c pend G env) (o'.release memory cells)
  | .done _ _, o', h => by
    cases o' <;> try exact absurd h id
    obtain ⟨hp, he, hg⟩ := h
    exact Rel.after (R := CorrG D c pend G env) hp (fun _ => ⟨hp, he, rfl⟩) fun x hp' =>
      ⟨hp', he, hG _ _ _ _ x hg⟩
  | .raised _ _, o', h => by
    cases o' <;> try exact absurd h id
    obtain ⟨hp, he, hl⟩ := h
    exact Rel.after (R := CorrG D c pend G env) hp (fun _ => ⟨hp, he, rfl⟩) fun _ hp' =>
      ⟨hp', he, hl⟩
  | .jumped _ _, o', h => by
    cases o' <;> try exact absurd h id
    obtain ⟨hp, he, hj⟩ := h
    exact Rel.after (R := CorrG D c pend G env) hp (fun _ => ⟨hp, he, rfl⟩) fun _ hp' =>
      ⟨hp', he, hj⟩
  | .panicked _ _, o', h => by
    cases o' <;> try exact absurd h id
    obtain ⟨hp, he, hk⟩ := h
    exact Rel.after (R := CorrG D c pend G env) hp (fun _ => ⟨hp, he, rfl⟩) fun _ hp' =>
      ⟨hp', he, hk⟩
  | .performed _ _ _ k, o', h => by
    cases o' with
    | performed op' v' t k' =>
      obtain ⟨⟨hp, he, hP⟩, hk⟩ := h
      exact Rel.after (R := CorrG D c pend G env) hp (fun _ => ⟨hp, he, rfl⟩) fun _ hp' =>
        ⟨⟨hp', he, hP⟩, fun w x w' x' hw => Rel.release hG cells (hk w x w' x' hw)⟩
    | _ => exact absurd h id
  | .outOfFuel, o', h => by cases o' <;> first | exact absurd h id | trivial
  | .stuck, o', h => by cases o' <;> first | exact absurd h id | trivial

/-- A `when`'s block, its names' values put back however it ends. -/
theorem SimP.release {S : List Shape} {m : Eval IState Value} {m' : Eval WState Value}
    (cells : List (Name × Ty × Nat)) (hm : Sim D c pend S m m') :
    Sim D c pend S (Eval.release InPlace.memory cells m) (Eval.release memory cells m') :=
  fun si sw hp hg hq => Rel.release (fun _ _ _ _ _ h => h) cells (hm si sw hp hg hq)

/-! ## The names of a `when` -/

/-- A `when`'s names bound in turn to values the checks accept, each in a scope of its own as
`ViewScope.holding` binds it, with a written type and no sources, whose reads hide its name;
the result's parameters `P` name none of them. -/
theorem SimP.holding {Sb : List Shape} {P : List Name} {m : Eval IState Value}
    {m' : Eval WState Value} :
    ∀ (c : Ctx) (ns : List (Name × Ty)) (vs : List Value), ns.length = vs.length →
      (∀ p ∈ ns, p.1 ∉ P) → (∀ y ∈ P, y ∈ c.P) → (ns = [] → P = c.P) →
      (∀ v ∈ vs, v.Viewed D) → (∀ s ∈ Sb, ∀ p ∈ ns, s.root ≠ p.1) →
      Sim D { c with Γ := c.Γ.holding D ns, R := (ns.map Prod.fst).foldl hide c.R, P := P } pend
        Sb m m' →
      Sim D c pend Sb (Eval.withVars InPlace.memory ((ns.map Prod.fst).zip vs) m)
        (Eval.withVars memory ((ns.map Prod.fst).zip vs) m')
  | c, [], [], _, _, _, hP, _, _, hm => by
    obtain rfl := hP rfl
    exact hm
  | c, (x, τ) :: ns, v :: vs, hl, hxP, hPc, _, hv, hS, hm => by
    have hok : ScopeOk c x ⟨some τ, if τ.holdsView D then [] else [], false⟩ (hide c.R x) P :=
      ⟨rfl, fun t ht hx => mem_hide.2 ⟨ht, hx⟩, fun t ht => (mem_hide.1 ht).2,
        fun _ s hs _ => by simp only [ite_self, List.not_mem_nil] at hs, hPc,
        hxP (x, τ) List.mem_cons_self⟩
    have hrest := SimP.holding (c.scope x ⟨some τ, if τ.holdsView D then [] else [], false⟩
      (hide c.R x) P) ns vs (by simpa using hl) (fun p hp => hxP p (List.mem_cons_of_mem _ hp))
      (fun _ h => h) (fun _ => rfl) (fun u hu => hv u (List.mem_cons_of_mem _ hu))
      (fun s hs p hp => hS s hs p (List.mem_cons_of_mem _ hp)) hm
    exact (SimP.scope hok (fun s hs => hS s hs (x, τ) List.mem_cons_self) hrest v v).mono
      (fun si sw _ => bindsAs_viewed (hv v List.mem_cons_self) si sw) fun _ _ _ _ h => h
  | _, [], _ :: _, hl, _, _, _, _, _, _ => by simp at hl
  | _, _ :: _, [], hl, _, _, _, _, _, _ => by simp at hl

/-- After the cells: the values taken out, then the names bound to them around the block,
whose values are put back however it ends. -/
theorem SimP.heldCells {ns : List (Name × Ty)} {Sb : List Shape}
    {m : Eval IState Value} {m' : Eval WState Value} (cells : List (Ty × Nat))
    (hm : Sim D { c with Γ := c.Γ.holding D ns, R := List.foldl hide c.R (ns.map Prod.fst)
                         P := c.P.removeAll (ns.map Prod.fst) } pend Sb m m')
    (hS : ∀ s ∈ Sb, ∀ p ∈ ns, s.root ≠ p.1) :
    Sim D c pend Sb
      (Eval.world InPlace.memory (fun w => (World.take cells w).map fun p => (.list p.1, p.2)) >>=
        Eval.asList >>= fun us =>
          if (ns.map Prod.fst).length = us.length then
            Eval.withVars InPlace.memory ((ns.map Prod.fst).zip us)
              (Eval.release InPlace.memory ((ns.map Prod.fst).zip cells) m)
          else Eval.fail .stuck)
      (Eval.world memory (fun w => (World.take cells w).map fun p => (.list p.1, p.2)) >>=
        Eval.asList >>= fun us =>
          if (ns.map Prod.fst).length = us.length then
            Eval.withVars memory ((ns.map Prod.fst).zip us)
              (Eval.release memory ((ns.map Prod.fst).zip cells) m')
          else Eval.fail .stuck) := by
  refine SimP.bind (SimP.take cells) fun us us' => ?_
  intro si sw hp hg ⟨he, hus⟩
  subst us'
  by_cases hl : (ns.map Prod.fst).length = us.length
  · simp only [hl, ↓reduceIte]
    refine SimP.holding c ns us (by simpa using hl) (fun p hp hP => ?_) (fun y hy => ?_)
      (fun h => by subst h; simp [List.removeAll]) hus hS (SimP.release _ hm) si sw hp hg trivial
    · simp only [List.removeAll, List.mem_filter] at hP
      simp [List.mem_map_of_mem hp] at hP
    · simp only [List.removeAll, List.mem_filter] at hy
      exact hy.1
  · simp only [hl, ↓reduceIte]
    exact CorrG.fault hp .stuck

/-- A `when`: its handles read alike, the same cells held, its names bound to the same values
around its block, which are put back however it ends (shared.when). -/
theorem SimP.held (n : Nat) (hΓ : ScopeKeeps D c.Γ) {ns₀ ns : List (Name × Ty)}
    {hs₀ hs : List Expr} {b₀ b : Expr}
    (hi : Expr.Inst D (.held ns₀ hs₀ b₀) (.held ns hs b))
    (ih : ∀ c' : Ctx, ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e →
      RunsIn D c' (Stilt.eval D InPlace.memory n) (Windows.eval D n) e₀ e)
    (hr : (Expr.held ns₀ hs₀ b₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.held ns₀ hs₀ b₀).contained D c.Γ c.P = true) :
    Sim D c pend ((Expr.held ns₀ hs₀ b₀).sources D c.Γ)
      (Stilt.eval D InPlace.memory (n + 1) (.held ns hs b))
      (Windows.eval D (n + 1) (.held ns hs b)) := by
  cases hi with
  | held hns his hb =>
  simp only [Expr.viewsRead, Bool.and_eq_true] at hr
  simp only [Expr.contained, Bool.and_eq_true, List.all_eq_true] at hc
  show Sim D c pend _
    (Eval.list _ hs >>= fun hv => Eval.held InPlace.memory (Stilt.eval D InPlace.memory n b)
      (ns.map Prod.fst) hv)
    (Eval.list _ hs >>= fun hv => Eval.held memory (Windows.eval D n b) (ns.map Prod.fst) hv)
  rw [hns]
  let cb : Ctx :=
    { c with Γ := c.Γ.holding D ns₀, R := List.foldl hide c.R (ns₀.map Prod.fst)
             P := c.P.removeAll (ns₀.map Prod.fst) }
  have hbody := ih cb (hΓ.holding ns₀) b₀ b hb cb.R pend hr.2 hc.2.1
  have hS : ∀ s ∈ b₀.sources D cb.Γ, ∀ p ∈ ns₀, s.root ≠ p.1 := fun s hs p hp he => by
    have := hc.2.2 s hs
    rw [he] at this
    simp [List.mem_map_of_mem hp] at this
  refine SimP.bind (SimP.list his c pend (fun e₀ e _ hi => ih c hΓ e₀ e hi) hr.1 hc.1)
    fun vs ws => ?_
  refine SimP.bind (G := fun a b _ _ => b = a)
    (SimP.inspect (f := fun _ => vs.mapM Value.cellOf) (f' := fun _ => ws.mapM Value.cellOf)
      fun si sw _ _ h => ?_) fun cells cells' => ?_
  · rw [cells_rel h.1 fun win hw => (h.2.1 win hw).1]
    cases vs.mapM Value.cellOf with
    | error e => exact .inl ⟨e, rfl, rfl⟩
    | ok a => exact .inr ⟨a, a, rfl, rfl, rfl⟩
  · intro si sw hp hg he
    subst cells'
    exact SimP.heldCells cells hbody hS si sw hp hg trivial

end Windows

end Stilt
