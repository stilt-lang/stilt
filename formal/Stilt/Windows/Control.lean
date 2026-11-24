import Stilt.Windows.Let

/-!
# Control

The forms that pass control on, on the relation of windows: a turn of a loop's body, which a
`break` or a `continue` ends (expressions.break-and-continue); a raise (effects.raise) and a
`return` of a value whose windows the result's parameters track (views.escaping); a `catch`,
whose error is read through its windows and bound in the handler's scope (effects.catch,
effects.innermost-catch); and a `for` loop, whose iterable is read through its windows and each
element bound in the body's scope (expressions.for-iterables, views.for-over-view).
-/

namespace Stilt

namespace Windows

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

/-- Related values whose windows some sources track, tracked by more. -/
theorem ValG.sub {S S' : List Shape} (hS : ∀ s ∈ S, s ∈ S') {v w : Value} {si : IState}
    {sw : WState} (h : ValG D c S v w si sw) : ValG D c S' v w si sw :=
  ⟨h.1, fun win hw => (h.2.1 win hw).sub hS, h.2.2⟩

/-- Related values whose sources are the result's parameters leave the body. -/
theorem ValG.leaving {S : List Shape} (hS : ∀ s ∈ S, s ∈ c.P.map (fun y => (⟨y, []⟩ : Shape)))
    {v w : Value} {si : IState} {sw : WState} (h : ValG D c S v w si sw) :
    Leaving D c sw.1.env si sw v w :=
  ⟨h.1, fun win hw => (h.2.1 win hw).sub hS, h.2.2⟩

/-- A turn of a loop's body. -/
theorem SimP.turn {S : List Shape} {m : Eval IState Value} {m' : Eval WState Value}
    (hm : Sim D c pend S m m') :
    SimP D c pend (fun _ _ => True) Same (Eval.turn m) (Eval.turn m') := by
  intro si sw hp hg hq
  refine Outcome.Rel.turn (hm si sw hp hg hq) (fun _ _ _ _ ⟨h₁, h₂, _⟩ => ⟨h₁, h₂, rfl⟩)
    (fun _ _ _ _ h => h) (fun j _ j' _ h => ?_) (fun _ _ _ _ h => h) CorrG.escapes.performs
  obtain ⟨h₁, h₂, h₃⟩ := h
  rcases j with _ | _ | v <;> rcases j' with _ | _ | w <;>
    first | exact ⟨h₁, h₂, rfl⟩ | exact ⟨h₁, h₂, h₃⟩ | exact absurd h₃ id

/-- A raise of a value whose sources are the result's parameters, whole (`leaves`). -/
theorem SimP.throw {S : List Shape} (hS : ∀ s ∈ S, s ∈ c.P.map (fun y => (⟨y, []⟩ : Shape)))
    {G : Value → Value → IState → WState → Prop} {v w : Value} :
    SimP D c pend (ValG D c S v w) G (Eval.throw v) (Eval.throw w) :=
  fun _ _ hp _ hq => ⟨hp, rfl, hq.leaving hS⟩

/-- A `return`, likewise. -/
theorem SimP.jumpRet {S : List Shape} (hS : ∀ s ∈ S, s ∈ c.P.map (fun y => (⟨y, []⟩ : Shape)))
    {G : Value → Value → IState → WState → Prop} {v w : Value} :
    SimP D c pend (ValG D c S v w) G (Eval.jump (.ret v)) (Eval.jump (.ret w)) :=
  fun _ _ hp _ hq => ⟨hp, rfl, hq.leaving hS⟩

/-- The scope of a binding of a written type and no sources, whose reads hide its name and keep
the others. -/
theorem scopeOk_hide {x : Name} {τ : Ty} {R : List Shape} (hR : ∀ t ∈ c.R, t ∈ R) :
    ScopeOk c x ⟨some τ, if τ.holdsView D then [] else [], false⟩ (hide R x) (c.P.filter (· != x)) :=
  ⟨rfl, fun t ht hx => mem_hide.2 ⟨hR t ht, hx⟩, fun t ht => (mem_hide.1 ht).2,
    fun _ s hs _ => by simp only [ite_self, List.not_mem_nil] at hs,
    fun y hy => (List.mem_filter.1 hy).1, fun hx => by simp at hx⟩

/-- A value the checks accept, which holds no window, binds as itself with no sources. -/
theorem bindsAs_viewed {τ : Ty} {v : Value} (hv : v.Viewed D) (si : IState) (sw : WState) :
    BindsAs D c ⟨some τ, if τ.holdsView D then [] else [], false⟩ v v si sw := by
  refine ⟨VRel.free hv.free, hv, ?_⟩
  simp only [Option.isSome_some, ↓reduceIte]
  intro win hw
  rw [hv.free] at hw
  cases hw

/-- A `catch`: the error read through its windows, bound in the handler's scope. -/
theorem SimP.tryCatch {x : Name} {E : Ty} {S₁ S₂ : List Shape} {m mh : Eval IState Value}
    {m' mh' : Eval WState Value} (hm : Sim D c pend S₁ m m')
    (hh : Sim D (c.scope x ⟨some E, if E.holdsView D then [] else [], false⟩ (hide c.R x)
      (c.P.filter (· != x))) pend S₂ mh mh') (hS : ∀ s ∈ S₂, s.root ≠ x) :
    Sim D c pend (S₁ ++ S₂) (Eval.handle m fun err => Eval.withVar InPlace.memory x err mh)
      (Eval.handle m' fun err => resolveE err >>= fun err => Eval.withVar memory x err mh') := by
  intro si sw hp hg hq
  have hsc := SimP.scope (scopeOk_hide (D := D) (τ := E) (fun t ht => ht)) hS hh
  refine Outcome.Rel.handle (hm si sw hp hg hq)
    (fun _ _ _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃.sub fun s hs => List.mem_append_left _ hs⟩)
    (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) CorrG.escapes.performs
    fun e si₁ e' sw₁ ⟨hp₁, he, hl⟩ => ?_
  have hs : SimP D c pend (fun si₂ sw₂ => si₂ = si₁ ∧ sw₂ = sw₁) (ValG D c (S₁ ++ S₂))
      (Eval.withVar InPlace.memory x e mh)
      (resolveE e' >>= fun err => Eval.withVar memory x err mh') :=
    SimP.resolveRight (fun _ _ ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ hl.1)
      ((hsc e e).mono (fun si₂ sw₂ _ => bindsAs_viewed hl.2.2 si₂ sw₂)
        fun _ _ _ _ h => h.sub fun s hs => List.mem_append_right _ hs)
  have := hs si₁ sw₁ hp₁ (he ▸ hg) ⟨rfl, rfl⟩
  rwa [he] at this

/-- A scope whose body ends with the same result on both sides: the body run with the variable
bound to related values, then unbound. -/
theorem SimP.scopeSame {α : Type} {x : Name} {b : ViewBinding} {R : List Shape} {P : List Name}
    (hok : ScopeOk c x b R P) {m : Eval IState α} {m' : Eval WState α}
    (hm : SimP D (c.scope x b R P) pend (fun _ _ => True) Same m m') (v w : Value) :
    SimP D c pend (BindsAs D c b v w) Same (Eval.withVar InPlace.memory x v m)
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
    exact ⟨hE.unbound hok, hE.unbind_env, hG⟩
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

/-- Each element of a list, which the checks accept, bound in turn in the body's scope until a
turn ends the loop. -/
theorem SimP.forEach {x : Name} {b : ViewBinding} {R : List Shape} {P : List Name}
    (hok : ScopeOk c x b R P) (hb : ∀ v, v.Viewed D → ∀ si sw, BindsAs D c b v v si sw)
    {m : Eval IState Bool} {m' : Eval WState Bool}
    (hm : SimP D (c.scope x b R P) pend (fun _ _ => True) Same m m') (vs : List Value)
    (hvs : ∀ v ∈ vs, v.Viewed D) {Q : IState → WState → Prop} :
    SimP D c pend Q Same (Eval.forEach (fun v => Eval.withVar InPlace.memory x v m) vs)
      (Eval.forEach (fun v => Eval.withVar memory x v m') vs) := by
  induction vs generalizing Q with
  | nil =>
    simp only [Eval.forEach]
    exact SimP.pure fun _ _ _ _ => rfl
  | cons v vs ih =>
    simp only [Eval.forEach]
    refine SimP.bind ((SimP.scopeSame hok hm v v).mono
      (fun si sw _ => hb v (hvs v List.mem_cons_self) si sw) fun _ _ _ _ h => h) fun a a' => ?_
    intro si sw hp hg (hq : a = a')
    subst hq
    exact SimP.ite (Q := fun _ _ => True) a (ih fun u hu => hvs u (List.mem_cons_of_mem _ hu))
      (SimP.pure fun _ _ _ _ => rfl) si sw hp hg trivial

/-- The list a value the checks accept holds, on both sides, or stuck on both. -/
theorem SimP.asList {S : List Shape} {β : Type} {v w : Value}
    {f : List Value → Eval IState β} {f' : List Value → Eval WState β}
    {G : β → β → IState → WState → Prop}
    (hf : ∀ vs, (∀ u ∈ vs, u.Viewed D) → SimP D c pend (fun _ _ => True) G (f vs) (f' vs)) :
    SimP D c pend (ValG D c S v w) G (Eval.asList v >>= f) (Eval.asList v >>= f') := by
  intro si sw hp hg hq
  by_cases hk : ∃ vs, v = .list vs
  · obtain ⟨vs, rfl⟩ := hk
    have hvs : ∀ u ∈ vs, u.Viewed D := by
      have h := hq.2.2
      cases h with
      | list h => exact h
    exact hf vs hvs si sw hp hg trivial
  · have h₁ : ∀ {σ : Type}, Eval.asList (σ := σ) v = Eval.fail .stuck := by
      intro σ
      cases v <;> first | rfl | exact absurd ⟨_, rfl⟩ hk
    rw [h₁, h₁]
    trivial

/-- A `for` loop: the iterable read through its windows, each element bound in the body's
scope, whose reads add the iterable's sources (`.for`'s case of `Expr.viewsRead`). -/
theorem SimP.loop {x : Name} {τ : Ty} {X S : List Shape} {mi : Eval IState Value}
    {mi' : Eval WState Value} (hi : Sim D c pend X mi mi') {m : Eval IState Value}
    {m' : Eval WState Value}
    (hm : Sim D (c.scope x ⟨some τ, if τ.holdsView D then [] else [], false⟩
      (hide (X ++ c.R) x) (c.P.filter (· != x))) pend S m m') :
    Sim D c pend [] (do
        let vs ← mi >>= Eval.asList
        Eval.forEach (fun v => Eval.withVar InPlace.memory x v (Eval.turn m)) vs
        Pure.pure .unit)
      (do
        let vs ← mi' >>= resolveE >>= Eval.asList
        Eval.forEach (fun v => Eval.withVar memory x v (Eval.turn m')) vs
        Pure.pure .unit) := by
  intro si sw hp hg hq
  have hok := scopeOk_hide (D := D) (c := c) (x := x) (τ := τ) (R := X ++ c.R)
    (fun t ht => List.mem_append_right X ht)
  have hu : ∀ si sw, ValG D c [] .unit .unit si sw :=
    fun _ _ => ⟨VRel.free rfl, fun _ hw => by simp only [windowsOf, List.not_mem_nil] at hw,
      Value.Viewed.unit⟩
  simp only [Eval.bind_assoc']
  refine (SimP.bind hi fun v w => SimP.resolveRight (fun _ _ hq => hq.1) (SimP.asList fun vs hvs =>
    SimP.bind (SimP.forEach hok (fun v hv => bindsAs_viewed hv) (SimP.turn hm) vs hvs)
      fun _ _ => SimP.pure fun si sw _ _ => hu si sw)) si sw hp hg hq

end Windows

end Stilt
