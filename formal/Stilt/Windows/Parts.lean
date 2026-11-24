import Stilt.Windows.Let
import Stilt.Windows.Scalars
import Stilt.Windows.Lists
import Stilt.Windows.Handling.Escapes

/-!
# A field or an element

The model of windows reads a value through its windows before taking a field or an element of
it (views.functions-of-views), so both models take the same part of the same value, which holds
no window.
-/

namespace Stilt

namespace Windows

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

/-- A value read through its windows on the windows' side: the same value on both sides. -/
theorem SimP.readThrough {S : List Shape} {m : Eval IState Value} {m' : Eval WState Value}
    (hm : Sim D c pend S m m') : SimP D c pend (fun _ _ => True) (FreeG D) m (m' >>= resolveE) := by
  have h := SimP.bind (H := FreeG D) (f := fun v => (Pure.pure v : Eval IState Value))
    (f' := resolveE) hm fun v w => by
      intro si sw hp _ hq
      show (Outcome.done v si).Rel _ (Eval.ofExcept (resolve sw.1.store w) sw)
      rw [hq.1.resolve]
      exact ⟨hp, rfl, rfl, hq.1.target_free, hq.2.2⟩
  have he : (m >>= fun v => (Pure.pure v : Eval IState Value)) = m := by
    funext s
    show (m s).bind (fun a s' => Outcome.done a s') = m s
    induction (m s) with
    | performed op v s k ih =>
      simp only [Outcome.bind]
      congr 1
      funext w x
      exact ih w x
    | _ => rfl
  rwa [he] at h

/-- The same step on the same value, giving a value with no window that the checks accept. -/
theorem SimP.same {Q : IState → WState → Prop} (x : Except Fault Value)
    (hx : ∀ v, x = .ok v → Free v ∧ v.Viewed D) :
    SimP D c pend Q (ValG D c []) (Eval.ofExcept x) (Eval.ofExcept x) := by
  intro si sw hp _ _
  cases h : x with
  | error f => exact CorrG.fault hp f
  | ok v =>
    obtain ⟨hf, hv⟩ := hx v h
    exact ⟨hp, rfl, VRel.free hf, fun w hw => (by rw [hf] at hw; cases hw), hv⟩

/-- A part of a value read alike: the same part of the same value. -/
theorem SimP.get {S : List Shape} {m : Eval IState Value} {m' : Eval WState Value}
    (hm : Sim D c pend S m m') (P : Path) :
    Sim D c pend [] (m >>= fun v => Eval.ofExcept (v.get P))
      ((m' >>= resolveE) >>= fun v => Eval.ofExcept (v.get P)) :=
  SimP.bind (SimP.readThrough hm) fun v w => by
    intro si sw hp hg hq
    obtain ⟨rfl, hf, hv⟩ := hq
    exact SimP.same (Q := fun _ _ => True) _ (fun u hu => ⟨free_get _ _ hf hu, hv.get hu⟩)
      si sw hp hg trivial

/-- A field of a value. -/
theorem SimP.field {S : List Shape} {m : Eval IState Value} {m' : Eval WState Value}
    (hm : Sim D c pend S m m') (f : Name) :
    Sim D c pend [] (m >>= fun v => Eval.ofExcept (v.get [.field f]))
      ((m' >>= resolveE) >>= fun v => Eval.ofExcept (v.get [.field f])) :=
  SimP.get hm _

/-- An element of a value: the index read alike while nothing waits, as the value read through
its windows holds none. -/
theorem SimP.index {S X : List Shape} {m mi : Eval IState Value} {m' mi' : Eval WState Value}
    (hm : Sim D c pend S m m') (hi : Sim D c pend X mi mi') :
    Sim D c pend [] (m >>= fun v => (mi >>= Eval.asInt) >>= fun k => Eval.ofExcept (v.get [.index k]))
      ((m' >>= resolveE) >>= fun v => (mi' >>= Eval.asInt) >>= fun k =>
        Eval.ofExcept (v.get [.index k])) := by
  refine SimP.bind (SimP.readThrough hm) fun v w => ?_
  refine SimP.bindEnv (SimP.bind (hi.mono (fun _ _ _ => trivial) fun _ _ _ _ h => h) fun a b =>
    SimP.asInt fun _ _ h => h.1) fun k k' => ?_
  by_cases hk : k = k'
  · subst hk
    intro si sw hp hg hq
    obtain ⟨-, si₀, sw₀, ⟨rfl, hf, hv⟩, -⟩ := hq
    exact SimP.same (Q := fun _ _ => True) _ (fun u hu => ⟨free_get _ _ hf hu, hv.get hu⟩)
      si sw hp hg trivial
  · exact fun _ _ _ _ hq => absurd hq.1 hk

/-- An operation: its operands read through their windows on the windows' side, the same values
as in place, and the same step on the same world. -/
theorem SimP.op {S : List Shape} {m : Eval IState (List Value)} {m' : Eval WState (List Value)}
    (hm : SimP D c pend (fun _ _ => True) (ValsG D c S) m m') (o : Op) :
    Sim D c pend [] (m >>= fun vs => Eval.world InPlace.memory (o.run vs))
      ((m' >>= resolveAllE) >>= fun vs => Eval.world memory (o.run vs)) := by
  rw [Eval.bind_assoc']
  refine SimP.bind hm fun vs ws => ?_
  intro si sw hp hg hq
  have hr : resolveAllE ws sw = .done vs sw := by
    show Eval.ofExcept (mapWindowsValues (fun loc path ranges => do
      resolve sw.1.store (← part sw.1.store loc path ranges)) ws) sw = _
    rw [resolveAll_eq (fun w hw => (hq.2.1 w hw).1.readAlike), hq.1]
    rfl
  show ((Eval.world InPlace.memory (o.run vs)) si).Rel _ ((resolveAllE ws sw).bind fun a s =>
    Eval.world memory (o.run a) s)
  rw [hr]
  obtain ⟨st, wo⟩ := si
  obtain ⟨sv, wv⟩ := sw
  have hw : wv = wo := hp.agree.world
  subst hw
  show (Eval.world InPlace.memory (o.run vs) (st, wv)).Rel _ (Eval.world memory (o.run vs) (sv, wv))
  cases h : o.run vs wv with
  | error e =>
    have e₁ : Eval.world InPlace.memory (o.run vs) (st, wv) = Outcome.fault e (st, wv) :=
      Eval.world_error (F := InPlace.frames) h
    have e₂ : Eval.world memory (o.run vs) (sv, wv) = Outcome.fault e (sv, wv) :=
      Eval.world_error (F := Windows.frames) h
    rw [e₁, e₂]
    exact CorrG.fault hp e
  | ok p =>
    obtain ⟨v, x⟩ := p
    have e₁ : Eval.world InPlace.memory (o.run vs) (st, wv) = Outcome.done v (st, x) :=
      Eval.world_ok (F := InPlace.frames) h
    have e₂ : Eval.world memory (o.run vs) (sv, wv) = Outcome.done v (sv, x) :=
      Eval.world_ok (F := Windows.frames) h
    rw [e₁, e₂]
    have hx : x.All (Value.Viewed D) := hp.agree.cells.run hq.2.2 h
    have hv : v.Viewed D := Op.run_hereditary (Value.Viewed.hereditary D) .unit hq.2.2 h
    have hp' : Pre D c pend (st, x) (sv, x) :=
      ⟨hp.agree.setWorld hx, hp.fits, hp.outer, hp.owned, hp.pend, hp.start, hp.alive⟩
    exact ⟨hp', rfl, VRel.free hv.free, fun w hw => (by rw [hv.free] at hw; cases hw), hv⟩

end Windows

end Stilt
