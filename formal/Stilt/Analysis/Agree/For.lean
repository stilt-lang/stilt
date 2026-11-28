import Stilt.Analysis.Agree.Loops

/-!
# `for` loops

A `for` whose head facts the analysis checked (`forRes`), facts on no term of its variable that
hold after its iterable and that each turn of its body keeps: its release run agrees with the
run that keeps every check, and ends where they hold or a `break`'s facts do (`agree_forHead`),
by induction on the values it runs its body on, each run with the variable bound to one. Over a
range, the body starts with its variable's bounds too (`Facts.forRange`): each value lies within
the bounds the range was evaluated with, whose terms the turns leave no greater for the first
and no less for the second (`agree_rangeIter`).
-/

namespace Stilt

theorem Facts.restrict_idem (F : Facts) (k : Term → Bool) :
    (F.restrict k).restrict k = F.restrict k := by
  cases F
  simp [Facts.restrict, List.filter_filter, Bool.and_self]

/-- Facts on no term of `x` hold alike with `x` bound. -/
theorem Facts.Holds.bindUnbound {J : Facts} {x : Name} {fr : Copy.Frame} {u v : Value}
    {st : List Value} (h : (J.unbind x).Holds (fr.nu st v)) :
    (J.unbind x).Holds (Copy.Frame.nu ((x, u) :: fr) st v) := by
  have := h.restrict (keep := fun t => t.name? != some x) (ν' := Copy.Frame.nu ((x, u) :: fr) st v)
    fun t ht => by
      simp only [bne_iff_ne, ne_eq] at ht
      exact Copy.Frame.nu_bind ht
  unfold Facts.unbind at this ⊢
  rwa [Facts.restrict_idem] at this

/-- A turn of a `for`'s body, its variable then unbound: what it meets, without `x`, and `Q`,
which every frame the turn keeps keeps. -/
theorem Outcome.sat_turnUnbind (w : WriteBack) {x : Name} {v : Value} {fr : Copy.Frame}
    {W L : List Name} {rb : Res} {st : List Value} {B' C' : Copy.State → Prop}
    {Q : Copy.Frame → Prop}
    (hQ : ∀ u rest, Frame.Keeps W L ((x, v) :: fr) ((x, u) :: rest) → Q rest) :
    ∀ {o : Outcome Copy.State Value}, o.Keeps W L (fun _ => True) ((x, v) :: fr) → o.Meets rb st →
      (o.turn.unbind (Copy.memoryWith w)).Sat
        (fun b s => (b = true → ((rb.post.noRes.join rb.cont).unbind x).Holds (s.1.nu st .unit) ∧
          Q s.1) ∧ (b = false → (rb.brk.unbind x).Holds (s.1.nu st .unit))) B' C'
  | .done _ s, ⟨_, k⟩, h => by
    obtain ⟨u, rest, he⟩ := k.cons_inv
    obtain ⟨fr', wd⟩ := s
    simp only at he
    subst he
    exact ⟨fun _ => ⟨(Facts.holds_join (.inl h.1.noRes)).unbind, hQ u rest k⟩, fun e => nomatch e⟩
  | .jumped .brk s, k, h => by
    obtain ⟨u, rest, he⟩ := Frame.Keeps.cons_inv k
    obtain ⟨fr', wd⟩ := s
    simp only at he
    subst he
    exact ⟨fun e => (nomatch e), fun _ => Facts.Holds.unbind h⟩
  | .jumped .cont s, k, h => by
    obtain ⟨u, rest, he⟩ := Frame.Keeps.cons_inv k
    obtain ⟨fr', wd⟩ := s
    simp only at he
    subst he
    exact ⟨fun _ => ⟨(Facts.holds_join (.inr h)).unbind, hQ u rest k⟩, fun e => nomatch e⟩
  | .jumped (.ret _) _, _, _ => trivial
  | .performed _ _ _ _, ⟨_, hk⟩, h => fun w' x' => Outcome.sat_turnUnbind w hQ (hk w' x') (h w' x')
  | .raised _ _, _, _ | .panicked _ _, _, _ | .outOfFuel, _, _ | .stuck, _, _ => trivial

variable {runR run : Expr → Eval Copy.State Value}

/-- A turn of a `for`'s body, with its variable bound to `v`. -/
theorem agree_turnVar (w : WriteBack) (ih : AgreeRun runR run) (hk : KeepsRun run) {L : Bool}
    {d : Nat} {Bf : Facts} {x : Name} {body : Expr} {st : List Value} {s : Copy.State} {v : Value}
    {B' C' : Copy.State → Prop} {Q : Copy.Frame → Prop} (hb : (an L d Bf body).ok = true)
    (hd : st.length = d) (hB : Bf.Holds (Copy.Frame.nu ((x, v) :: s.1) st .unit))
    (hQ : ∀ u rest, Frame.Keeps body.writes body.resizes ((x, v) :: s.1) ((x, u) :: rest) →
      Q rest) :
    Eval.Agree (fun b s =>
        (b = true → (((an L d Bf body).post.noRes.join (an L d Bf body).cont).unbind x).Holds
          (s.1.nu st .unit) ∧ Q s.1) ∧
        (b = false → ((an L d Bf body).brk.unbind x).Holds (s.1.nu st .unit)))
      B' C' (Eval.withVar (Copy.memoryWith w) x v (Eval.turn (runR body)))
      (Eval.withVar (Copy.memoryWith w) x v (Eval.turn (run body))) s := by
  have hbd := ih L d Bf body st ((x, v) :: s.1, s.2) hb hd hB
  refine ⟨?_, ?_⟩
  · show ((runR body ((x, v) :: s.1, s.2)).turn).unbind (Copy.memoryWith w) =
      ((run body ((x, v) :: s.1, s.2)).turn).unbind (Copy.memoryWith w)
    rw [hbd.1]
  · show ((run body ((x, v) :: s.1, s.2)).turn.unbind (Copy.memoryWith w)).Sat _ _ _
    exact Outcome.sat_turnUnbind w hQ
      (hk body _ _ (List.Subset.refl _) (List.Subset.refl _) ((x, v) :: s.1, s.2)) hbd.2

/-- The turns of a `for` over the values `vs`, from where its head facts `I` and `Q` hold, each
value meeting `ok`, its body analysed from `Bf`, which they give it. -/
theorem agree_forEach (w : WriteBack) (ih : AgreeRun runR run) (hk : KeepsRun run) {L : Bool}
    {d : Nat} {I Bf : Facts} {x : Name} {body : Expr} {st : List Value} {B C : Copy.State → Prop}
    {Q : Copy.Frame → Prop} {ok : Value → Prop}
    (hd : st.length = d) (hb : (an L d Bf body).ok = true)
    (hpres : (((an L d Bf body).post.noRes.join (an L d Bf body).cont).unbind x).close.entails I =
      true)
    (hQ : ∀ v u fr rest, Frame.Keeps body.writes body.resizes ((x, v) :: fr) ((x, u) :: rest) →
      Q fr → Q rest)
    (hB : ∀ v fr, ok v → Q fr → I.Holds (fr.nu st .unit) →
      Bf.Holds (Copy.Frame.nu ((x, v) :: fr) st .unit)) :
    ∀ (vs : List Value) (s : Copy.State), (∀ v ∈ vs, ok v) → I.Holds (s.1.nu st .unit) → Q s.1 →
      Eval.Agree (fun _ s => (I.join ((an L d Bf body).brk.unbind x)).Holds (s.1.nu st .unit)) B C
        (Eval.forEach (fun v => Eval.withVar (Copy.memoryWith w) x v (Eval.turn (runR body))) vs)
        (Eval.forEach (fun v => Eval.withVar (Copy.memoryWith w) x v (Eval.turn (run body))) vs) s
  | [], _, _, hI, _ => Eval.Agree.pure (Facts.holds_join (.inl hI))
  | v :: vs, s, hok, hI, hq => by
    simp only [Eval.forEach]
    refine (agree_turnVar (B' := B) (C' := C) (Q := Q) w ih hk hb hd
      (hB v s.1 (hok v List.mem_cons_self) hq hI) fun u rest k => hQ v u s.1 rest k hq).bind
      (fun _ h => h) (fun _ h => h) fun u s₂ hu => ?_
    cases u
    · exact Eval.Agree.pure (Facts.holds_join (.inr (hu.2 rfl)))
    · obtain ⟨h1, h2⟩ := hu.1 rfl
      exact agree_forEach w ih hk hd hb hpres hQ hB vs s₂
        (fun v hv => hok v (List.mem_cons_of_mem _ hv)) ((h1.close rfl).entails rfl hpres) h2

/-- A `for` whose head facts `I` the analysis checked: the iterable, which ends with values each
meeting `ok p` where `G` and `Q p` hold, for some `p`, then the turns. -/
theorem agree_forHead {α : Type} (w : WriteBack) (ih : AgreeRun runR run) (hk : KeepsRun run)
    {L : Bool} {d : Nat} {G I Bf : Facts} {x : Name} {e body : Expr} {st : List Value}
    {s : Copy.State} {Bi Ci : Copy.State → Prop} {Q : α → Copy.Frame → Prop}
    {ok : α → Value → Prop} (hd : st.length = d)
    (hit : Eval.Agree (fun vs s => G.Holds (s.1.nu st .unit) ∧ ∃ p, Q p s.1 ∧ ∀ v ∈ vs, ok p v)
      Bi Ci (runR e >>= Eval.asList) (run e >>= Eval.asList) s)
    (hb : (an L d Bf body).ok = true) (hin : G.close.entails I = true)
    (hpres : (((an L d Bf body).post.noRes.join (an L d Bf body).cont).unbind x).close.entails I =
      true)
    (hQ : ∀ p v u fr rest, Frame.Keeps body.writes body.resizes ((x, v) :: fr) ((x, u) :: rest) →
      Q p fr → Q p rest)
    (hB : ∀ p v fr, ok p v → Q p fr → I.Holds (fr.nu st .unit) →
      Bf.Holds (Copy.Frame.nu ((x, v) :: fr) st .unit)) :
    Eval.Agree (fun v s => v = .unit ∧
        (I.join ((an L d Bf body).brk.unbind x)).Holds (s.1.nu st .unit)) Bi Ci
      (Eval.loop (Copy.memoryWith w) runR x e body) (Eval.loop (Copy.memoryWith w) run x e body) s := by
  unfold Eval.loop
  refine hit.bind (fun _ h => h) (fun _ h => h) fun vs s₁ hG => ?_
  obtain ⟨hG, p, hq, hv⟩ := hG
  exact (agree_forEach w ih hk hd hb hpres (hQ p) (hB p) vs s₁ hv ((hG.close rfl).entails rfl hin)
    hq).bind (fun _ h => h) (fun _ h => h) fun _ s₂ h => Eval.Agree.pure ⟨rfl, h⟩

end Stilt
