import Stilt.Moves.Steps

/-!
# Bindings and their scopes

The steps that bind a variable keep the simulation: an ordinary binding, in a
new location, and the binding of a variable's last use, which ends that
variable and hands its storage over (values.passing-values). Ending the binding
forgets what the body did to its own location.
-/

namespace Stilt.Moving

open InPlace

variable {α : Type} {G : α → Prop} {Lb L X : Live}

theorem withVar_eq {σ : Type} (M : Memory σ) (x : Name) (v : Value) (m : Eval σ α) (s : σ) :
    Eval.withVar M x v m s = (m (M.bind s x v)).unbind M := rfl

theorem withInit_eq {σ : Type} (M : Memory σ) (x : Name) (init : Expr) (v : Value) (m : Eval σ α)
    (s : σ) : Eval.withInit M x init v m s = (m (M.bindInit s x init v)).unbind M := rfl

theorem sel_cons {β : Type} {mk : List Bool} {X : Live} {a : Name × β} {env : List (Name × β)} :
    ∀ e ∈ sel (true :: mk) X (a :: env), e ∈ a :: sel mk X env := by
  intro e he
  simp only [mem_sel, keep, ↓reduceIte, List.mem_cons] at he ⊢
  rcases he with ⟨rfl | he, hx⟩
  · exact .inl rfl
  · exact .inr ⟨he, hx⟩

/-- Writes below the references of a state with a binding that shares one of
its references are writes below its own references. -/
theorem Evolves.unshare {e : List (Name × Ref)} {st : List Value} {y z : Name} {r : Ref}
    {s₁ : State} (hz : (z, r) ∈ e) (h : Evolves ⟨(y, r) :: e, st⟩ s₁) :
    Evolves ⟨e, st⟩ ⟨e, s₁.store⟩ := by
  obtain ⟨-, W, st', extra, hs, hW, hseq⟩ := h
  refine ⟨rfl, W, st', extra, hs, fun pw hpw => ?_, hseq⟩
  obtain ⟨P, hP, q, hq⟩ := hW pw hpw
  simp only [State.paths, List.map_cons, List.mem_cons] at hP
  rcases hP with rfl | hP
  · exact ⟨_, List.mem_map.2 ⟨(z, r), hz, rfl⟩, q, hq⟩
  · exact ⟨P, hP, q, hq⟩

/-- Ending the binding that a body ran with gives corresponding outcomes. -/
theorem MCorr.unbind {X₀ : Live} {mk₀ mk : List Bool} {a₀ : Name × Value} {fr : Copy.Frame}
    {s s₀ : State} (hs₀ : s₀.env.tail = s.env)
    (hev₀ : ∀ st, Evolves ⟨sel mk₀ X₀ s₀.env, s₀.store⟩ ⟨sel mk₀ X₀ s₀.env, st⟩ →
      Evolves ⟨sel mk X s.env, s.store⟩ ⟨sel mk X s.env, st⟩)
    (hk₀ : ∀ c m₁, Kills L X₀ mk₀ (c :: m₁) (keys s₀) → Kills L X mk m₁ (keys s))
    (hag₀ : MAgrees mk₀ (a₀ :: fr) s₀) {o : Outcome Copy.State α} {o' : Outcome (State × World) α}
    (hc : MCorr G L X₀ mk₀ s₀ o o') :
    MCorr G L X mk s (o.unbind Copy.memory) (o'.unbind Moving.memory) := by
  have key : ∀ fr₁ s₁, Post L X₀ mk₀ s₀ fr₁ s₁ →
      Post L X mk s (Copy.memory.unbind fr₁) (Moving.memory.unbind s₁) := by
    intro ⟨fr₁, w⟩ ⟨s₁, w'⟩ ⟨m₁, ⟨hag₁, hw⟩, hk, henv, hev⟩
    dsimp only at hag₁ hw henv hev
    have hn : names fr₁ = keys s₀ := by rw [hag₁.keys_eq, keys, henv]
    match fr₁, m₁, hag₁, hk, hn with
    | b :: fr₁, c :: m₁, hag₁, hk, hn =>
      have hst : (Moving.memory.unbind (s₁, w')).1 = ⟨s.env, s₁.store⟩ := by
        show (⟨s₁.env.tail, s₁.store⟩ : State) = _
        rw [henv, hs₀]
      refine ⟨m₁, ⟨hag₁.unbind, hw⟩, hk₀ c m₁ hk, by rw [hst], ?_⟩
      rw [hst]
      exact hev₀ _ hev
    | [], _, _, _, hn =>
      rw [← hag₀.keys_eq] at hn
      simp [names] at hn
    | _ :: _, [], hag₁, _, _ =>
      have := hag₁.len
      simp at this
  exact Outcome.Rel.unbind Copy.memory Moving.memory hc
    (fun _ _ _ _ h => ⟨h.1, h.2.1, key _ _ h.2.2⟩) (fun _ _ _ _ h => ⟨h.1, h.2.1, key _ _ h.2.2⟩)
    (fun _ _ _ _ h => ⟨h.1, h.2.1, key _ _ h.2.2⟩) (fun _ _ _ _ h => ⟨h.1, key _ _ h.2⟩)
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, key _ _ h.2.2.2⟩) fun _ _ _ _ _ h => h

namespace MSim

/-- An ordinary binding, live for its body, in a new location. -/
theorem withVar (x : Name) {v : Value} (hv : VOk v) {m : Eval Copy.State α}
    {m' : Eval (State × World) α}
    {Lb' X' : Live} (hm : MSim G Lb' L X' m m')
    (hLb : ∀ z, Lb'.mem z = true → z ≠ x → Lb.mem z = true) (hall : Lb'.all = true → Lb.all = true)
    (hX : X'.Sub X) :
    MSim G Lb L X (Eval.withVar Copy.memory x v m) (Eval.withVar Moving.memory x v m') := by
  intro fr s mk hag hinv
  show MCorr G L X mk s.1 (Eval.withVar Copy.memory x v m fr) (Eval.withVar Moving.memory x v m' s)
  rw [withVar_eq, withVar_eq]
  have hag₀ : MAgrees (true :: mk) ((x, v) :: fr.1) (InPlace.bind s.1 x v) :=
    hag.1.bind x hv.1 hv.2
  refine MCorr.unbind rfl (fun st h => ?_) (fun c m₁ hk =>
    (show Kills L X' (true :: mk) (c :: m₁) (x :: keys s.1) from hk).2.2.mono (Live.Sub.refl L) hX)
    hag₀ (hm (Copy.memory.bind fr x v) (Moving.memory.bind s x v) _ ⟨hag₀, hag.2⟩
      (Inv.cons hinv hLb hall))
  have h₁ := Evolves.unbind (s := ⟨sel mk X' s.1.env, s.1.store⟩) (x := x) (v := v)
    (Evolves.of_sub sel_cons h)
  exact Evolves.of_sub (fun e he => by
    rw [mem_sel] at he ⊢
    exact ⟨he.1, hX.2 _ he.2⟩) h₁

theorem read_lookup {fr : Copy.Frame} {x : Name} {v : Value} (h : Copy.read fr x [] = .ok v) :
    fr.lookup x = some v := by
  unfold Copy.read at h
  split at h
  · rename_i w hw
    cases h
    exact hw
  · cases h

theorem bind_inspect {σ β : Type} (f : σ → Except Fault α) (k : α → Eval σ β) (s : σ) :
    (Eval.inspect f >>= k) s = match f s with | .ok a => k a s | .error e => Outcome.fault e s := by
  show Eval.bind _ _ s = _
  unfold Eval.bind Outcome.bind Eval.inspect Eval.ofExcept
  cases f s with
  | ok => rfl
  | error e => cases e <;> rfl

/-- The binding of the last use of `x`, which ends `x` and hands its storage
over to `y` (values.passing-values). Nothing after it mentions `x`, but as `y`. -/
theorem withMove (x y : Name) {m : Eval Copy.State α} {m' : Eval (State × World) α}
    {Lb' X' : Live}
    (hm : MSim G Lb' L X' m m') (hx : Lb.mem x = true) (hxL : L.mem x = false)
    (hX : X.mem x = true) (hX' : X'.Sub X)
    (hLb : ∀ z, Lb'.mem z = true → z ≠ y → z ≠ x ∧ Lb.mem z = true) (hall : Lb'.all = false) :
    MSim G Lb L X
      (Eval.inspect (fun fr => Copy.memory.read fr x []) >>= fun v =>
        Eval.withInit Copy.memory y (.move x) v m)
      (Eval.inspect (fun s => Moving.memory.read s x []) >>= fun v =>
        Eval.withInit Moving.memory y (.move x) v m') := by
  intro ⟨fr, w⟩ ⟨s, w'⟩ mk ⟨hag, hw⟩ hinv
  dsimp only at hag hw hinv ⊢
  have hlx : LiveAt x mk (names fr) := hag.keys_eq ▸ hinv.live x hx
  rw [bind_inspect, bind_inspect, show Copy.memory.read (fr, w) x [] = Copy.read fr x [] from rfl,
    show Moving.memory.read (s, w') x [] = Copy.read fr x [] from (hag.read hlx []).symm]
  cases hc : Copy.read fr x [] with
  | error f => exact MCorr.fault (s := (s, w')) ⟨hag, hw⟩ f
  | ok v =>
    dsimp only
    have hv := read_lookup hc
    obtain ⟨r, hr⟩ := hag.lookup_ref hlx hv
    rw [withInit_eq, withInit_eq]
    have hag₀ := hag.bindMoved hlx y hv
    have hb : Moving.bindMoved s y x v = ⟨(y, r) :: s.env, s.store⟩ := by
      simp [Moving.bindMoved, hr]
    have hlen : mk.length = (keys s).length := by simp [hag.len_env]
    have hkill := Kills.kill hxL hX mk (keys s) hlen
    rw [hag.keys_eq] at hag₀
    have hinv₀ : Inv Lb' (true :: kill x mk (keys s)) (y :: keys s) := by
      refine ⟨fun z hz => ?_, fun h => absurd h (by simp [hall])⟩
      by_cases hzy : z = y
      · subst hzy
        exact LiveAt.cons_self z _ _
      · obtain ⟨hzx, hz'⟩ := hLb z hz hzy
        exact ((hinv.live z hz').kill hzx).cons hzy
    have hxr : (x, r) ∈ sel mk X s.env := by
      rw [mem_sel]
      refine ⟨mem_of_lookup (by rw [hag.lookup_env hlx]; exact hr), hX⟩
    refine MCorr.unbind (by rw [hb]; rfl) (fun st h => ?_)
      (fun c m₁ hk => hkill.trans
        ((show Kills L X' (true :: kill x mk (keys s)) (c :: m₁) (y :: keys s) by
          rw [keys, hb] at hk; exact hk).2.2.mono
          (Live.Sub.refl L) hX') (Live.Sub.refl L)) hag₀
      (hm ((y, v) :: fr, w) (Moving.bindMoved s y x v, w') _ ⟨hag₀, hw⟩
        (by show Inv Lb' _ (keys (Moving.bindMoved s y x v)); rw [hb]; exact hinv₀))
    rw [hb] at h
    refine Evolves.unshare (y := y) (s₁ := ⟨(y, r) :: sel mk X s.env, st⟩) hxr
      (Evolves.of_sub (fun e he => ?_) h)
    rcases List.mem_cons.1 (sel_cons e he) with rfl | he
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (sel_sub hkill hX' e he)

end MSim

end Stilt.Moving
