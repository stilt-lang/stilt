import Stilt.Windows.Guards.Steps
import Stilt.InPlace.Enter

/-!
# Calls that keep guarded regions

In place, a callee's variables are new locations, except that each `inout` parameter
refers to its argument's place in the caller's store (`Entry`). So whatever the callee
writes below its variables, the caller's store changes only below the places of the call's
`inout` arguments, and at the new locations, which the caller forgets (`evolvesBy_leave`). A
call keeps the regions its reads guard when the place of each `inout` argument, and every
part below it, avoids them; the law of exclusivity, as E0423 counts it, gives that
(`Stilt.Windows.Guards.Eval`).

When the places of one call's `inout` arguments are disjoint (modes.overlapping-inout), the
callee's references are pairwise disjoint as the caller's are (`Entry.disjoint`).
-/

namespace Stilt

open InPlace

namespace InPlace

/-- What the start of a call gives, once the parameters `pre` are bound: the callee's store
extends the caller's, its references are valid, each is a new location or the place of an
`inout` argument, and they are pairwise disjoint when the caller's are and the places of the
`inout` arguments are. -/
structure Entry (s : State) (pre : List (Name × Passed)) (sc : State) : Prop where
  store : ∃ F, sc.store = s.store ++ F
  valid : Valid sc
  refs : ∀ xr ∈ sc.env, s.store.length ≤ xr.2.loc ∨
    ∃ y x p r, (y, Passed.place x p) ∈ pre ∧ s.env.lookup x = some r ∧ xr.2 = placeRef r p
  disjoint : s.env.Pairwise (fun a b => a.2.Disjoint b.2) →
    (pre.map Prod.snd).Pairwise Passed.Compat → sc.env.Pairwise fun a b => a.2.Disjoint b.2

theorem entry_base (s : State) :
    ∀ captured : List (Name × Value),
      Entry s [] (captured.foldr (fun xv t => InPlace.bind t xv.1 xv.2) ⟨[], s.store⟩)
  | [] => ⟨⟨[], by simp⟩, by simp [Valid], by simp, fun _ _ => .nil⟩
  | (x, v) :: captured => by
    have ih := entry_base s captured
    obtain ⟨F, hF⟩ := ih.store
    refine ⟨⟨F ++ [v], ?_⟩, valid_bind ih.valid x v, ?_, fun hd hc => ?_⟩
    · show (List.foldr (β := State) _ _ captured).store ++ [v] = _
      rw [hF, List.append_assoc]
    · intro xr hxr
      rcases List.mem_cons.1 hxr with rfl | hxr
      · refine .inl ?_
        show s.store.length ≤ (List.foldr (β := State) _ _ captured).store.length
        rw [hF]
        simp
      · exact ih.refs xr hxr
    · refine List.Pairwise.cons (fun xr hxr => ?_) (ih.disjoint hd hc)
      exact .inl (by simp; have := ih.valid xr hxr; omega)

namespace Entry

variable {s : State} {pre : List (Name × Passed)} {s₀ : State}

theorem value (h : Entry s pre s₀) (y : Name) (a : Passed) (v : Value) :
    Entry s (pre ++ [(y, a)]) (InPlace.bind s₀ y v) := by
  obtain ⟨F, hF⟩ := h.store
  refine ⟨⟨F ++ [v], by simp [InPlace.bind, hF]⟩, valid_bind h.valid y v, ?_, fun hd hc => ?_⟩
  · intro xr hxr
    rcases List.mem_cons.1 hxr with rfl | hxr
    · exact .inl (by simp [hF])
    · rcases h.refs xr hxr with hfresh | ⟨y', x, p, r, hmem, hl, heq⟩
      · exact .inl hfresh
      · exact .inr ⟨y', x, p, r, List.mem_append_left _ hmem, hl, heq⟩
  · have hc' : (pre.map Prod.snd).Pairwise Passed.Compat := by
      simp only [List.map_append, List.pairwise_append] at hc
      exact hc.1
    refine List.Pairwise.cons (fun xr hxr => ?_) (h.disjoint hd hc')
    exact .inl (by simp; have := h.valid xr hxr; omega)

theorem place (h : Entry s pre s₀) (y x : Name) (p : Path) {r : Ref}
    (hl : s.env.lookup x = some r) {u : Value} (hu : deref s r p = .ok u) :
    Entry s (pre ++ [(y, .place x p)]) { s₀ with env := (y, placeRef r p) :: s₀.env } := by
  obtain ⟨F, hF⟩ := h.store
  have hlt := lt_of_deref hu
  refine ⟨h.store, fun xr hxr => ?_, fun xr hxr => ?_, fun hd hc => ?_⟩
  · rcases List.mem_cons.1 hxr with rfl | hxr
    · simp [placeRef, hF]; omega
    · exact h.valid xr hxr
  · rcases List.mem_cons.1 hxr with rfl | hxr
    · exact .inr ⟨y, x, p, r, by simp, hl, rfl⟩
    · rcases h.refs xr hxr with hfresh | ⟨y', x', p', r', hmem, hl', heq⟩
      · exact .inl hfresh
      · exact .inr ⟨y', x', p', r', List.mem_append_left _ hmem, hl', heq⟩
  · simp only [List.map_append, List.map_cons, List.map_nil, List.pairwise_append,
      List.pairwise_cons, List.mem_singleton] at hc
    refine List.Pairwise.cons (fun xr hxr => ?_) (h.disjoint hd hc.1)
    rcases h.refs xr hxr with hfresh | ⟨y', x', p', r', hmem, hl', heq⟩
    · exact .inl (by simp [placeRef]; omega)
    · rw [heq]
      exact (placeRef_disjoint hd hl' hl
        (hc.2.2 _ (List.mem_map.2 ⟨_, hmem, rfl⟩) _ rfl)).symm

end Entry

/-- Binding the parameters `rest`, after `pre`, gives an entry. -/
theorem entry_fold (s : State) :
    ∀ (rest pre : List (Name × Passed)) (s₀ sc : State), Entry s pre s₀ →
      rest.foldlM (enterStep s) s₀ = .ok sc → Entry s (pre ++ rest) sc
  | [], pre, s₀, sc, h, he => by cases he; simpa using h
  | (y, a) :: rest, pre, s₀, sc, h, he => by
    have hassoc : pre ++ (y, a) :: rest = (pre ++ [(y, a)]) ++ rest := by simp
    rw [hassoc]
    simp only [List.foldlM_cons] at he
    cases a with
    | value v => exact entry_fold s rest _ _ _ (h.value y _ v) he
    | moved x v => exact entry_fold s rest _ _ _ (h.value y _ v) he
    | place x p =>
      simp only [enterStep] at he
      cases hl : s.env.lookup x with
      | none => simp [hl] at he; cases he
      | some r =>
        simp only [hl] at he
        cases hu : deref s r p with
        | error f => simp [hu] at he; cases he
        | ok u =>
          simp only [hu] at he
          exact entry_fold s rest _ _ _ (h.place y x p hl hu) he

/-- A call's start, in place, gives an entry. -/
theorem entry_of_enter {s sc : State} {captured : List (Name × Value)}
    {bound : List (Name × Passed)} (he : InPlace.frames.enter s captured bound = .ok sc) :
    Entry s bound sc := by
  rw [enter_eq] at he
  simpa using entry_fold s bound [] _ sc (entry_base s captured) he

/-- The writes a call's end gives the caller: below the places of its `inout` arguments. -/
def InoutWrite (s : State) (bound : List (Name × Passed)) (P : Path) : Prop :=
  ∃ y x p r q, (y, Passed.place x p) ∈ bound ∧ s.env.lookup x = some r ∧ P = r.toPath ++ (p ++ q)

/-- The end of a call: whatever the callee wrote below its variables, the caller's store
changed only below the places of the `inout` arguments, and at new locations. -/
theorem evolvesBy_leave {s sc s' : State} {bound : List (Name × Passed)} (hent : Entry s bound sc)
    {ok : Path → Prop} (hev : EvolvesBy ok sc s') :
    EvolvesBy (InoutWrite s bound) s ⟨s.env, s'.store⟩ := by
  obtain ⟨-, W, st, extra, hs', hW, hseq⟩ := hev
  obtain ⟨F, hF⟩ := hent.store
  rw [hF] at hseq
  obtain ⟨A', B', hR, -, -, hlow, -⟩ := setSeq_append_store
    (fun pw hpw => atLoc_of_under (hW pw hpw).1) hseq
  simp only [Value.list.injEq] at hR
  subst hR
  refine ⟨rfl, _, A', B' ++ extra, by rw [hs', List.append_assoc], fun pw hpw => ?_, hlow⟩
  obtain ⟨hpw, hb⟩ := List.mem_filter.1 hpw
  obtain ⟨⟨P, hP, q, hq⟩, -⟩ := hW pw hpw
  obtain ⟨xr, hxr, rfl⟩ := List.mem_map.1 hP
  rcases hent.refs xr hxr with hfresh | ⟨y, x, p, r, hmem, hl, heq⟩
  · simp [below, hq, Ref.toPath] at hb
    omega
  · have hpath : pw.1 = r.toPath ++ (p ++ q) := by
      rw [hq, heq]
      simp [placeRef, Ref.toPath]
    exact ⟨⟨r.toPath, List.mem_map.2 ⟨(x, r), mem_of_lookup hl, rfl⟩, p ++ q, hpath⟩,
      y, x, p, r, q, hmem, hl, hpath⟩

theorem memory_leave (s s' : State × World) (bound : List (Name × Passed)) :
    InPlace.memory.leave s s' bound = .ok (⟨s.1.env, s'.1.store⟩, s'.2) := rfl

end InPlace

namespace Outcome.Within

/-- The callee's outcome as its call's, from the caller's state: the caller's store changed
only below the places of the `inout` arguments, however the callee ended, and so in each
rest of a performance that leaves the call. -/
theorem leaveCall {s : State × World} {bound : List (Name × Passed)} {sc : State}
    (hent : Entry s.1 bound sc) {ok okc : Path → Prop} (hok : ∀ P, InoutWrite s.1 bound P → ok P) :
    ∀ {o : Outcome (State × World) Value}, o.Within okc (fun _ => True) sc →
      (o.leaveCall InPlace.memory bound s).Within ok (fun _ => True) s.1
  | .done _ _, h => by
    simp only [Outcome.leaveCall, memory_leave]
    exact ⟨trivial, (evolvesBy_leave hent h.2).mono hok⟩
  | .raised _ _, h => by
    simp only [Outcome.leaveCall, memory_leave]
    exact (evolvesBy_leave hent h).mono hok
  | .jumped .brk _, _ | .jumped .cont _, _ => trivial
  | .jumped (.ret _) _, h => by
    simp only [Outcome.leaveCall, memory_leave]
    exact ⟨trivial, (evolvesBy_leave hent h).mono hok⟩
  | .panicked _ _, h => by
    simp only [Outcome.leaveCall, memory_leave]
    exact (evolvesBy_leave hent h).mono hok
  | .performed _ _ _ _, ⟨h, hk⟩ => by
    simp only [Outcome.leaveCall, memory_leave]
    exact ⟨(evolvesBy_leave hent h).mono hok, fun w x => leaveCall hent hok (hk w x)⟩
  | .outOfFuel, _ => trivial
  | .stuck, _ => trivial

end Outcome.Within

namespace Eval.Guards

variable {G : List Path} {R : List Shape}

/-- The places a call passes `inout` avoid the regions, and so does every part below them. -/
def PlacesAvoid (G : List Path) (R : List Shape) (passed : List Passed) : Prop :=
  ∀ (s : State), Regions G R s → ∀ x p r, Passed.place x p ∈ passed →
    s.env.lookup x = some r → ∀ q, Avoids G (r.toPath ++ (p ++ q))

theorem placesAvoid_nil (R : List Shape) (passed : List Passed) : PlacesAvoid [] R passed :=
  fun _ _ _ _ _ _ _ _ => avoids_nil _

/-- A call runs its body from new locations and the caller's places: it keeps the regions
when the places it passes `inout` avoid them. -/
theorem invoke (captured : List (Name × Value)) (params : List Param) {passed : List Passed}
    {body : Eval (State × World) Value} (hb : Eval.Guards [] [] (fun _ => True) body)
    (hp : PlacesAvoid G R passed) :
    Eval.Guards G R (fun _ => True) (Eval.invoke InPlace.memory captured params passed body) := by
  intro s _ hr
  unfold Eval.invoke
  cases hbind : bindArgs params passed with
  | none => trivial
  | some bound =>
    have hsnd := (bindArgs_spec hbind).2
    dsimp only
    rw [InPlace.memory, Frames.withWorld_enter]
    cases he : InPlace.frames.enter s.1 captured bound with
    | error f => exact Outcome.Within.fault (.refl _ s.1) f
    | ok sc =>
      have hent := entry_of_enter he
      refine Outcome.Within.leaveCall hent (fun P ⟨y, x, p, r, q, hmem, hl, hP⟩ => ?_)
        (hb (sc, s.2) hent.valid (regions_nil _ _))
      rw [hP]
      exact hp s.1 hr x p r (hsnd ▸ List.mem_map_of_mem (f := Prod.snd) hmem) hl q

theorem call (D : Decls) {run : Expr → Eval (State × World) Value}
    (hrun : ∀ e, Eval.Guards [] [] (fun _ => True) (run e)) (f : Value) {passed : List Passed}
    (hp : PlacesAvoid G R passed) :
    Eval.Guards G R (fun _ => True) (Eval.call D InPlace.memory run f passed) := by
  cases f with
  | closure captured params result ρ body => exact invoke captured params (hrun body) hp
  | function name types rows =>
    unfold Eval.call
    dsimp only
    cases D.fn? name with
    | none => exact fail _
    | some d => exact invoke [] d.params (hrun _) hp
  | _ => exact fail _

theorem callAs (D : Decls) {run : Expr → Eval (State × World) Value}
    (hrun : ∀ e, Eval.Guards [] [] (fun _ => True) (run e)) (control : Bool) (f : Value)
    {passed : List Passed} (hp : PlacesAvoid G R passed) :
    Eval.Guards G R (fun _ => True) (Eval.callAs D InPlace.memory run control f passed) := by
  unfold Eval.callAs
  split
  · exact fail _
  · exact call D hrun f hp

/-- A clause of a handler is called on a value alone, so it writes no place of the caller. -/
theorem placesAvoid_value (v : Value) : PlacesAvoid G R [.value v] := by
  intro _ _ x p _ hmem
  simp at hmem

/-- A `with` keeps the regions that its block and its handler keep (handlers.with). -/
theorem withHandler (D : Decls) {run : Expr → Eval (State × World) Value}
    (hrun : ∀ e, Eval.Guards [] [] (fun _ => True) (run e)) (effect : Name) (control : Bool)
    (handler : Value) {m : Eval (State × World) Value} (hm : Eval.Guards G R (fun _ => True) m) :
    Eval.Guards G R (fun _ => True) (Eval.letGo InPlace.memory (Eval.handleWith InPlace.memory
      effect control handler (fun f v => Eval.callAs D InPlace.memory run control f [.value v]) m)) :=
  letGo fun s hv hr => Outcome.Within.handleWith (fun c v t ht =>
    (callAs D hrun control c (placesAvoid_value v) t (ht.valid hv) (hr.evolve ht)).base hv ht)
    (hm s hv hr)

end Eval.Guards

end Stilt
