import Stilt.Windows.Unbind

/-!
# A scope

Running a body with a variable bound, then ending the binding however the body ends
(expressions.scope): both models end alike, the value the scope gives reading no source of
the variable's name, and a value leaving the body none either, as the result's parameters no
longer name it (views.escaping, E0422).
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls} {c : Ctx} {x : Name} {b : ViewBinding} {R : List Shape} {P : List Name}
  {pend : List (Window × Value)} {env : List (Name × Ref)} {n : Nat} {si : IState} {sw : WState}

namespace Ending

theorem unbind_env (h : Ending D c x b R P pend env n si sw) : (memory.unbind sw).1.env = env := by
  show (Windows.unbind sw.1).env = env
  rw [h.unbind_eq]

theorem unbind_store (h : Ending D c x b R P pend env n si sw) :
    (memory.unbind sw).1.store = sw.1.store.set n none := by
  show (Windows.unbind sw.1).store = _
  rw [h.unbind_eq]

theorem unbind_istore : (InPlace.memory.unbind si).1.store = si.1.store := rfl

/-- A value whose windows the scope's sources of other names track keeps its relation. -/
theorem vrel {S : List Shape} (h : Ending D c x b R P pend env n si sw) (hS : ∀ s ∈ S, s.root ≠ x)
    {v w : Value} (hv : VRel si.1.store sw.1.store w v)
    (ht : ∀ win ∈ windowsOf w, Tracked sw.1.env c.In S win) :
    VRel (InPlace.memory.unbind si).1.store (memory.unbind sw).1.store w v ∧
      ∀ win ∈ windowsOf w, Tracked (memory.unbind sw).1.env c.In S win := by
  rw [h.unbind_store, h.unbind_env, unbind_istore]
  refine ⟨hv.region (fun win hw => regionW_set_ne _ (Ne.symm (h.tracked hS (ht win hw)).1))
    fun _ _ => rfl, fun win hw => (h.tracked hS (ht win hw)).2⟩

theorem valG {S : List Shape} (h : Ending D c x b R P pend env n si sw) (hS : ∀ s ∈ S, s.root ≠ x)
    {v w : Value} (hv : ValG D (c.scope x b R P) S v w si sw) :
    ValG D c S v w (InPlace.memory.unbind si) (memory.unbind sw) :=
  ⟨(h.vrel hS hv.1 hv.2.1).1, (h.vrel hS hv.1 hv.2.1).2, hv.2.2⟩

theorem leaving (h : Ending D c x b R P pend env n si sw) (hok : ScopeOk c x b R P)
    {v w : Value} (hv : Leaving D (c.scope x b R P) sw.1.env si sw v w) :
    Leaving D c (memory.unbind sw).1.env (InPlace.memory.unbind si) (memory.unbind sw) v w := by
  have hS : ∀ s ∈ P.map (fun y => (⟨y, []⟩ : Shape)), s.root ≠ x := by
    intro s hs
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
    exact fun he => hok.erased (he ▸ hy)
  obtain ⟨h₁, h₂⟩ := h.vrel hS hv.1 hv.2.1
  refine ⟨h₁, fun win hw => (h₂ win hw).sub fun s hs => ?_, hv.2.2⟩
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
  exact List.mem_map.2 ⟨y, hok.sub y hy, rfl⟩

end Ending

/-- A scope: the body run with the variable bound to related values, then unbound. -/
theorem SimP.scope (hok : ScopeOk c x b R P) {S : List Shape} (hS : ∀ s ∈ S, s.root ≠ x)
    {m : Eval IState Value} {m' : Eval WState Value} (hm : Sim D (c.scope x b R P) pend S m m')
    (v w : Value) :
    SimP D c pend (BindsAs D c b v w) (ValG D c S) (Eval.withVar InPlace.memory x v m)
      (Eval.withVar memory x w m') := by
  intro si sw hp hg hq
  obtain ⟨st, wo⟩ := si
  obtain ⟨sv, wv⟩ := sw
  have hp' := hp.bind (x := x) (R := R) (P := P) hok.param hq
  have hg' := Guards.bind hp hg hok
  have hend : ∀ si₁ sw₁, Pre D (c.scope x b R P) pend si₁ sw₁ →
      sw₁.1.env = (x, ⟨sv.store.length, []⟩) :: sv.env →
      Ending D c x b R P pend sv.env sv.store.length si₁ sw₁ :=
    fun si₁ sw₁ hp₁ he => ⟨hp₁, he, hg', env_lt hp.agree, hp.start⟩
  refine Outcome.Rel.unbind InPlace.memory memory (hm _ _ hp' hg' trivial)
    (fun _ _ _ _ ⟨hp₁, he, hG⟩ => ?_) (fun _ _ _ _ ⟨hp₁, he, hG⟩ => ?_)
    (fun j _ j' _ ⟨hp₁, he, hG⟩ => ?_) (fun _ _ _ _ ⟨hp₁, he, hG⟩ => ?_)
    (fun _ _ _ _ _ _ ⟨hp₁, he, hG⟩ => ?_) fun _ _ _ _ _ h => h
  · have hE := hend _ _ hp₁ he
    exact ⟨hE.unbound hok, hE.unbind_env, hE.valG hS hG⟩
  · have hE := hend _ _ hp₁ he
    have := hE.leaving hok (he ▸ hG)
    rw [hE.unbind_env] at this
    exact ⟨hE.unbound hok, hE.unbind_env, this⟩
  · have hE := hend _ _ hp₁ he
    refine ⟨hE.unbound hok, hE.unbind_env, ?_⟩
    rcases j with _ | _ | v <;> rcases j' with _ | _ | w <;> try exact hG
    have := hE.leaving hok (he ▸ hG)
    rw [hE.unbind_env] at this
    exact this
  · have hE := hend _ _ hp₁ he
    exact ⟨hE.unbound hok, hE.unbind_env, hG⟩
  · have hE := hend _ _ hp₁ he
    exact ⟨hE.unbound hok, hE.unbind_env, hG⟩

end Windows

end Stilt
