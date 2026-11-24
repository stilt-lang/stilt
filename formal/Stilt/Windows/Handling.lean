import Stilt.Windows.Fits
import Stilt.Windows.Handling.Escapes
import Stilt.Handling.Related
import Stilt.Holding

/-!
# Performances and handlers on the relation of windows

A performance of the same value, which holds no window, is resumed alike in both models
(handlers.performing-operation). The clauses of a handler value of windows and of its reading
against the in-place store are called alike: the same closure or function, or two values
neither model can call (`clauses_of_vrel`). A `with` handles alike what its block ends with,
each clause called as the model of windows calls it, and lets the same cells go
(`SimP.withHandler`; handlers.with). Its block's value, raised error and returned value are read
through their windows (`underHandler`), and a clause's raised error is read through its windows
when the call ends, so what a body or a rest ends with reads no store: it relates as well on the
frames of the rest resumed before it, where a handler that takes control ends it
(`CorrH.lifts`; handlers.resuming).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

/-! ## States in another world -/

/-- The simulation keeps two states in one world whose cells hold values the checks accept. -/
theorem Pre.setWorld {si : IState} {sw : WState} (h : Pre D c pend si sw) {x : World}
    (hx : x.All (Value.Viewed D)) : Pre D c pend (si.1, x) (sw.1, x) :=
  ⟨h.agree.setWorld hx, h.fits, h.outer, h.owned, h.pend, h.start, h.alive⟩

/-- A performance of the same value, which holds no window, resumed alike. -/
theorem SimP.perform {Q : IState → WState → Prop}
    {G : Value → Value → IState → WState → Prop}
    (hG : ∀ w si sw, Pre D c pend si sw → Free w → w.Viewed D → G w w si sw)
    {op : Operation} {v : Value} (hv : Free v) (hvv : v.Viewed D) :
    SimP D c pend Q G (Eval.perform InPlace.memory op v) (Eval.perform memory op v) := by
  intro si sw hp _ _
  refine ⟨⟨hp, rfl, rfl, rfl, hv, hvv⟩, ?_⟩
  rintro w x w' x' ⟨rfl, hw, hwv, rfl, hx⟩
  exact ⟨hp.setWorld hx, rfl, hG _ _ _ (hp.setWorld hx) hw hwv⟩

/-! ## Clauses -/

/-- A value no handler's clause reads and no call can call: no record, closure or function. -/
def Plain (v : Value) : Prop := (∀ n, v.clause? n = none) ∧ NotCallable v

theorem plain_view {v w : Value} {a b : Int} (h : Op.view.apply [v, .int a, .int b] = .ok w) :
    Plain w := by
  cases v
  case str s =>
    simp only [Op.apply, Op.applyScalars] at h
    split at h
    · revert h
      cases Op.compute _ _ with
      | error _ => intro h; cases h
      | ok x =>
        intro h; cases h
        cases x <;> exact ⟨fun _ => rfl, fun _ _ _ _ _ => nofun, fun _ _ _ => nofun⟩
    · cases h
  all_goals
    simp only [Op.apply, ListOp.apply, onList] at h
    split at h
    · split at h
      · cases h; exact ⟨fun _ => rfl, fun _ _ _ _ _ => nofun, fun _ _ _ => nofun⟩
      · cases h
    · cases h

theorem plain_slices {d w : Value} (hd : Plain d) :
    ∀ ranges : List (Int × Int), slices ranges d = .ok w → Plain w := by
  intro ranges
  induction ranges generalizing d with
  | nil => intro h; cases h; exact hd
  | cons r rs ih =>
    intro h
    simp only [slices, List.foldlM_cons] at h
    cases hu : Op.view.apply [d, .int r.1, .int r.2] with
    | error _ => rw [hu] at h; cases h
    | ok u => rw [hu] at h; exact ih (plain_view hu) h

theorem Plain.of_viewable {d : Value} (h : viewable d = true) : Plain d := by
  cases d <;> (try cases h) <;> exact ⟨fun _ => rfl, fun _ _ _ _ _ => nofun, fun _ _ _ => nofun⟩

/-- What a window that holds reads in the in-place store is plain. -/
theorem Holds.plain {sw : List (Option Value)} {si : List Value} {w : Window} {u : Value}
    (h : Holds sw si w) (hu : partIn si w.1 w.2.1 w.2.2 = .ok u) : Plain u := by
  obtain ⟨d, -, hi, -, hv⟩ := h
  rw [partIn_eq_region, hi] at hu
  exact plain_slices (Plain.of_viewable hv) _ hu

/-- A value of windows and its reading, whose windows hold, are called alike. -/
theorem callLike_of_resolve {si : List Value} {sw : List (Option Value)} {f' f : Value}
    (hf : resolveIn si f' = .ok f) (hh : ∀ w ∈ windowsOf f', Holds sw si w) (hfv : f.Viewed D) :
    CallLike D f f' := by
  have K : ∀ {v : Value}, Plain v → NotCallable v := fun h => h.2
  cases f' with
  | window l p r =>
    simp only [resolveIn, mapWindows] at hf
    exact .inr ⟨K ((hh _ (List.mem_singleton_self _)).plain hf),
      fun _ _ _ _ _ => nofun, fun _ _ _ => nofun⟩
  | list vs =>
    obtain ⟨ws, -, rfl⟩ := mapWindows_list.1 hf
    exact .inr ⟨⟨fun _ _ _ _ _ => nofun, fun _ _ _ => nofun⟩,
      fun _ _ _ _ _ => nofun, fun _ _ _ => nofun⟩
  | record R fs =>
    obtain ⟨gs, -, rfl⟩ := mapWindows_record.1 hf
    exact .inr ⟨⟨fun _ _ _ _ _ => nofun, fun _ _ _ => nofun⟩,
      fun _ _ _ _ _ => nofun, fun _ _ _ => nofun⟩
  | variant T C vs =>
    obtain ⟨ws, -, rfl⟩ := mapWindows_variant.1 hf
    exact .inr ⟨⟨fun _ _ _ _ _ => nofun, fun _ _ _ => nofun⟩,
      fun _ _ _ _ _ => nofun, fun _ _ _ => nofun⟩
  | closure =>
    simp only [resolveIn, mapWindows, Except.ok.injEq] at hf
    subst hf
    exact .inl ⟨rfl, hfv⟩
  | function =>
    simp only [resolveIn, mapWindows, Except.ok.injEq] at hf
    subst hf
    exact .inl ⟨rfl, hfv⟩
  | _ =>
    simp only [resolveIn, mapWindows, Except.ok.injEq] at hf
    subst hf
    exact .inr ⟨⟨fun _ _ _ _ _ => nofun, fun _ _ _ => nofun⟩,
      fun _ _ _ _ _ => nofun, fun _ _ _ => nofun⟩

/-- The clauses of a handler value and of its reading are called alike. -/
theorem clauses_of_vrel {si : List Value} {sw : List (Option Value)} {hv' hv : Value}
    (h : VRel si sw hv' hv) (hvv : hv.Viewed D) (n : Name) :
    ClauseRel (CallLike D) (hv.clause? n) (hv'.clause? n) := by
  obtain ⟨hres, hh⟩ := h
  cases hv' with
  | record R fs =>
    obtain ⟨gs, hgs, rfl⟩ := mapWindows_record.1 hres
    simp only [Value.clause?]
    rcases mapWindowsFields_lookup hgs n with ⟨h1, h2⟩ | ⟨c', c, h1, h2, hc⟩
    · rw [h1, h2]; trivial
    · rw [h1, h2]
      cases hvv with
      | record hf =>
        exact callLike_of_resolve hc (fun w hw => hh w (windowsOf_lookup h1 hw))
          (hf _ (mem_of_lookup h2))
  | window l p r =>
    simp only [resolveIn, mapWindows] at hres
    rw [((hh _ (List.mem_singleton_self _)).plain hres).1 n]
    trivial
  | list vs => obtain ⟨ws, -, rfl⟩ := mapWindows_list.1 hres; trivial
  | variant T C vs => obtain ⟨ws, -, rfl⟩ := mapWindows_variant.1 hres; trivial
  | _ => simp only [resolveIn, mapWindows, Except.ok.injEq] at hres; subst hres; trivial

/-! ## The relation under a handler -/

/-- What two outcomes of a block under a handler relate: as `CorrG` with the same value on both
sides, one that holds no window, as the result, the raised error and the returned value. These
read no store, so they relate as well on the frames of another rest of the block. -/
def CorrH (D : Decls) (c : Ctx) (pend : List (Window × Value)) (env : List (Name × Ref)) :
    Outcome.Relation IState WState Value Value where
  done a si b sw := Pre D c pend si sw ∧ sw.1.env = env ∧ FreeG D a b si sw
  raised e si e' sw := Pre D c pend si sw ∧ sw.1.env = env ∧ FreeG D e e' si sw
  jumped j si j' sw := Pre D c pend si sw ∧ sw.1.env = env ∧
    match j, j' with
    | .ret v, .ret w => FreeG D v w si sw
    | .brk, .brk | .cont, .cont => True
    | _, _ => False
  panicked k si k' sw := Pre D c pend si sw ∧ sw.1.env = env ∧ k = k'
  performed op v si op' v' sw := Pre D c pend si sw ∧ sw.1.env = env ∧ op = op' ∧ v' = v ∧
    Free v ∧ v.Viewed D
  resume _ w x w' x' := w' = w ∧ Free w ∧ w.Viewed D ∧ x' = x ∧ x.All (Value.Viewed D)

variable {env : List (Name × Ref)}

theorem freeG_of_leaving {si : IState} {sw : WState} {e e' : Value}
    (h : Leaving D c env si sw e e') (hf : Free e') : FreeG D e e' si sw := by
  have he : e' = e := by
    have := h.1.1
    rw [resolveIn_free _ hf] at this
    exact Except.ok.inj this
  subst he
  exact ⟨rfl, hf, h.2.2⟩

theorem leaving_of_freeG {si : IState} {sw : WState} {e e' : Value} (h : FreeG D e e' si sw) :
    Leaving D c env si sw e e' := by
  obtain ⟨rfl, hf, hv⟩ := h
  exact ⟨VRel.free hf, fun w hw => absurd (hf ▸ hw) (List.not_mem_nil), hv⟩

theorem CorrH.sub : (CorrH D c pend env).Sub (CorrG D c pend (FreeG D) env) :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => ⟨h.1, h.2.1, leaving_of_freeG h.2.2⟩,
    fun j _ j' _ h => ⟨h.1, h.2.1, by
      cases j <;> cases j' <;> first | exact h.2.2 | exact leaving_of_freeG h.2.2⟩,
    fun _ _ _ _ h => h, fun _ _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩

/-- Outcomes related by `CorrG` whose escaping values of windows hold no window. -/
theorem Rel.toH {o : Outcome IState Value} {o' : Outcome WState Value}
    (h : o.Rel (CorrG D c pend (FreeG D) env) o') (hf : o'.EscFree) :
    o.Rel (CorrH D c pend env) o' := by
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' t k' =>
      exact ⟨h.1, fun w x w' x' hr => ih w x (h.2 w x w' x' hr) (hf w' x')⟩
    | _ => exact absurd h id
  | raised e s =>
    cases o' <;> first | exact absurd h id | exact ⟨h.1, h.2.1, freeG_of_leaving h.2.2 hf⟩
  | jumped j s =>
    cases o' with
    | jumped j' t =>
      refine ⟨h.1, h.2.1, ?_⟩
      have h₂ := h.2.2
      cases j <;> cases j' <;> first | exact h₂ | exact freeG_of_leaving h₂ hf
    | _ => exact absurd h id
  | _ => cases o' <;> first | exact absurd h id | exact h

/-- A block's outcomes related by `CorrG`, the second read under a handler: its value, its
raised error and its returned value read through their windows. -/
theorem Rel.underHandler {S : List Shape} {o : Outcome IState Value} {o' : Outcome WState Value}
    (h : o.Rel (CorrG D c pend (ValG D c S) env) o') :
    o.Rel (CorrH D c pend env) ((o'.bind fun v s => resolveE v s).readEscapes) := by
  induction o generalizing o' with
  | done a s =>
    cases o' with
    | done b t =>
      obtain ⟨hp, he, hr, -, hv⟩ := h
      show Outcome.Rel _ _ (Outcome.readEscapes (Eval.ofExcept (resolve t.1.store b) t))
      rw [hr.resolve]
      exact ⟨hp, he, rfl, hv.free, hv⟩
    | _ => exact absurd h id
  | raised e s =>
    cases o' with
    | raised e' t =>
      obtain ⟨hp, he, hr, -, hv⟩ := h
      show Outcome.Rel _ _ (match resolve t.1.store e' with
        | .ok w => .raised w t | .error f => .fault f t)
      rw [hr.resolve]
      exact ⟨hp, he, rfl, hv.free, hv⟩
    | _ => exact absurd h id
  | jumped j s =>
    cases o' with
    | jumped j' t =>
      obtain ⟨hp, he, hj⟩ := h
      cases j <;> cases j' <;> first | exact hj.elim | exact ⟨hp, he, trivial⟩ | skip
      rename_i v w
      obtain ⟨hr, -, hv⟩ := hj
      show Outcome.Rel _ _ (match resolve t.1.store w with
        | .ok u => .jumped (.ret u) t | .error f => .fault f t)
      rw [hr.resolve]
      exact ⟨hp, he, rfl, hv.free, hv⟩
    | _ => exact absurd h id
  | performed op v s k ih =>
    cases o' with
    | performed op' v' t k' => exact ⟨h.1, fun w x w' x' hr => ih w x (h.2 w x w' x' hr)⟩
    | _ => exact absurd h id
  | _ => cases o' <;> first | exact absurd h id | exact h

/-- A `with` letting go of the same cells in both models, from one world. -/
theorem Rel.letGo {before before' : World} (hb : before' = before) {o : Outcome IState Value}
    {o' : Outcome WState Value} (h : o.Rel (CorrG D c pend (FreeG D) env) o') :
    (o.letGo InPlace.memory before).Rel (CorrG D c pend (FreeG D) env)
      (o'.letGo memory before') := by
  subst hb
  have hw : ∀ {si : IState} {sw : WState}, Pre D c pend si sw →
      Pre D c pend (si.1, before'.letGo si.2) (sw.1, before'.letGo sw.2) := fun hp => by
    rw [hp.agree.world]
    exact hp.setWorld (hp.agree.cells.letGo before')
  induction o generalizing o' with
  | performed op v s k ih =>
    cases o' with
    | performed op' v' t k' => exact ⟨h.1, fun w x w' x' hr => ih w x (h.2 w x w' x' hr)⟩
    | _ => exact absurd h id
  | done | raised | jumped | panicked =>
    cases o' <;> first | exact absurd h id | exact ⟨hw h.1, h.2.1, h.2.2⟩
  | _ => cases o' <;> first | exact absurd h id | exact h

/-- What a block under a handler and a clause relate, carried to the frames of the states a
rest of the block left. -/
theorem CorrH.lifts {si : IState} {sw : WState} (hp : Pre D c pend si sw) (he : sw.1.env = env) :
    (CorrH D c pend env).Lifts InPlace.memory memory si sw := by
  have hl : ∀ {si' : IState} {sw' : WState}, Pre D c pend si' sw' →
      Pre D c pend (si.1, si'.2) (sw.1, sw'.2) := fun hp' => by
    rw [hp'.agree.world]
    exact hp.setWorld hp'.agree.cells
  exact ⟨fun _ _ _ _ h => ⟨hl h.1, he, h.2.2⟩, fun _ _ _ _ h => ⟨hl h.1, he, h.2.2⟩,
    fun _ _ _ _ h => ⟨hl h.1, he, h.2.2⟩, fun _ _ _ _ h => ⟨hl h.1, he, h.2.2⟩,
    fun _ _ _ _ _ _ h => ⟨hl h.1, he, h.2.2⟩⟩

/-- A call of a value that is no closure and no function is stuck. -/
theorem callAs_notCallable {σ : Type} {f : Value} (hf : NotCallable f) (D : Decls) (M : Memory σ)
    (run : Expr → Eval σ Value) (ctl : Bool) (args : List Passed) (s : σ) :
    Eval.callAs D M run ctl f args s = .stuck := by
  obtain ⟨h₁, h₂⟩ := hf
  unfold Eval.callAs
  cases f <;>
    first | exact absurd rfl (h₁ _ _ _ _ _) | exact absurd rfl (h₂ _ _ _) | (split <;> rfl)

/-- Clauses called alike from a performance the relation under a handler relates. -/
theorem SimP.callH {ctl : Bool} {run : Expr → Eval IState Value}
    {run' : Expr → Eval WState Value}
    (hcall : ∀ f, f.Viewed D → (¬NotCallable f) → ∀ v, Free v → v.Viewed D →
      SimP D c pend (fun _ _ => True) (FreeG D) (Eval.callAs D InPlace.memory run ctl f [.value v])
        (callSettled D run' ctl f [.value v] >>= resolveE))
    (hg : Guards D c pend env) {f f' : Value} {op : Operation} {v v' : Value} {si : IState}
    {sw : WState} (hf : CallLike D f f') (h : (CorrH D c pend env).performed op v si op v' sw) :
    (Eval.callAs D InPlace.memory run ctl f [.value v] si).Rel (CorrH D c pend env)
      ((callSettled D run' ctl f' [.value v'] >>= resolveE) sw) := by
  obtain ⟨hp, he, -, rfl, hvf, hvv⟩ := h
  have hstuck : ∀ {g : Value}, NotCallable g →
      (callSettled D run' ctl g [.value v'] >>= resolveE) sw = .stuck := fun hg' => by
    show ((Eval.callAs D memory run' ctl _ _ sw).settle _).bind _ = _
    rw [callAs_notCallable hg']
    rfl
  rcases hf with ⟨hff, hfv⟩ | ⟨hn, hn'⟩
  · rw [hff]
    by_cases hnc : NotCallable f
    · rw [callAs_notCallable hnc, hstuck hnc]
      trivial
    · have := hcall f hfv hnc v' hvf hvv si sw hp (he ▸ hg) trivial
      rw [he] at this
      exact Rel.toH this (escFree_call _ _ _ _ _ _)
  · rw [callAs_notCallable hn, hstuck hn']
    trivial

/-- A `with`: its block's value read through its windows, each clause called as the model of
windows calls it, the cells its dropped rests hold let go (handlers.with). -/
theorem SimP.withHandler {E : Name} {ctl : Bool} {hv hv' : Value}
    (hcl : ∀ n, ClauseRel (CallLike D) (hv.clause? n) (hv'.clause? n))
    {run : Expr → Eval IState Value} {run' : Expr → Eval WState Value}
    (hcall : ∀ f, f.Viewed D → (¬NotCallable f) → ∀ v, Free v → v.Viewed D →
      SimP D c pend (fun _ _ => True) (FreeG D) (Eval.callAs D InPlace.memory run ctl f [.value v])
        (callSettled D run' ctl f [.value v] >>= resolveE))
    {S : List Shape} {m : Eval IState Value} {m' : Eval WState Value} (hm : Sim D c pend S m m') :
    SimP D c pend (fun _ _ => True) (FreeG D)
      (Eval.letGo InPlace.memory (Eval.handleWith InPlace.memory E ctl hv
        (fun f v => Eval.callAs D InPlace.memory run ctl f [.value v]) m))
      (Eval.letGo memory (Eval.handleWith memory E ctl hv'
        (fun f v => callSettled D run' ctl f [.value v] >>= resolveE) (underHandler m'))) := by
  intro si sw hp hg _
  have hh := Outcome.Rel.handleWith (R := CorrH D c pend sw.1.env)
    (M := InPlace.memory) (M' := memory) (C := CallLike D)
    (effect := E) (control := ctl) (fun _ _ _ _ _ _ h => h.2.2.1.symm) hcl
    (fun _ _ _ _ _ _ _ hf h => SimP.callH hcall hg hf h)
    (fun _ _ _ _ _ h => ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2, h.1.agree.world, h.1.agree.cells⟩)
    (fun _ _ _ _ _ h => ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, h.1.agree.world, h.1.agree.cells⟩)
    (fun _ _ _ _ h => CorrH.lifts h.1 h.2.1) (Rel.underHandler (hm si sw hp hg trivial))
  exact Rel.letGo hp.agree.world (Outcome.Rel.mono hh CorrH.sub)

end Windows

end Stilt
