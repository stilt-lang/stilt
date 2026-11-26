import Stilt.Related
import Stilt.Moves.Operations
import Stilt.Moves.Kills

/-!
# Steps

The simulation of copy-in, copy-out by `Moving`, and the steps of the
evaluator that keep it.

`MSim G Lb L X m m'` says that `m`, run on a state of copy-in, copy-out, and
`m'`, run on a `Moving` state that agrees with it under a mask that keeps the
variables of `Lb` live, in the same world, end the same way. When they return
or raise, the value is the same, and `Post` holds: the two states agree, in
one world, under a mask that ended only newest bindings of variables that `X`
holds and `L` doesn't, the state has the same variables, and its store changed
only below the references of the newest live bindings of variables that `X`
holds, and in new locations. `Lb`, `L` and `X` come from
`Expr.movesOk`: the variables mentioned from the start of `m` on, after it,
and by it. A raise skips what follows it up to its handler, which `L` holds
too, and so does a jump, which skips what follows it up to its loop or the end
of its body.
-/

namespace Stilt.Moving

open InPlace

variable {α β : Type}

/-- A value that a run may hold: safe and justified. -/
def VOk (v : Value) : Prop := v.Safe ∧ v.Justified

/-- The names of a state's variables, the newest first. -/
abbrev keys (s : State) : List Name := s.env.map Prod.fst

/-- A jump that a run may hold: a `return`'s value is one that the run may hold. -/
def JOk : Jump → Prop
  | .ret v => VOk v
  | _ => True

/-- What holds when a step ends, from the frames `s` and the mask `mk`. -/
def Post (L X : Live) (mk : List Bool) (s : State) (fr : Copy.State) (s' : State × World) :
    Prop :=
  ∃ m, MAgreesIn m fr s' ∧ Kills L X mk m (keys s) ∧ s'.1.env = s.env ∧
    Evolves ⟨sel mk X s.env, s.store⟩ ⟨sel mk X s.env, s'.1.store⟩

/-- What the two runs from a state and one whose frames `s` agree with it under
the mask `mk` relate: the same value, which `G` holds of with the frame it
ends with, or the same raise, jump, panic or performance, each that a run may
hold, and with each `Post`; and a performance resumed with the same value in
both, one that a run may hold, in the same world. -/
def MCorr.relationF (G : α → Copy.Frame → Prop) (L X : Live) (mk : List Bool) (s : State) :
    Outcome.Relation Copy.State (State × World) α α where
  done a fr a' s' := a = a' ∧ G a fr.1 ∧ Post L X mk s fr s'
  raised e fr e' s' := e = e' ∧ VOk e ∧ Post L X mk s fr s'
  jumped j fr j' s' := j = j' ∧ JOk j ∧ Post L X mk s fr s'
  panicked k fr k' s' := k = k' ∧ Post L X mk s fr s'
  performed op v fr op' v' s' := op = op' ∧ v = v' ∧ VOk v ∧ Post L X mk s fr s'
  resume _ w x w' x' := w = w' ∧ VOk w ∧ x = x' ∧ x.All VOk

/-- What the two runs relate when what `G` holds of is the value alone. -/
abbrev MCorr.relation (G : α → Prop) (L X : Live) (mk : List Bool) (s : State) :
    Outcome.Relation Copy.State (State × World) α α :=
  MCorr.relationF (fun a _ => G a) L X mk s

/-- The outcomes of the two runs from a state and one whose frames `s` agree
with it under the mask `mk` correspond. -/
def MCorr (G : α → Prop) (L X : Live) (mk : List Bool) (s : State) :
    Outcome Copy.State α → Outcome (State × World) α → Prop :=
  Outcome.Rel (MCorr.relation G L X mk s)

/-- `m` and `m'` end the same way from every two states that agree under a
mask that keeps the variables of `Lb` live. -/
def MSim (G : α → Prop) (Lb L X : Live) (m : Eval Copy.State α) (m' : Eval (State × World) α) :
    Prop :=
  ∀ fr s mk, MAgreesIn mk fr s → Inv Lb mk (keys s.1) → MCorr G L X mk s.1 (m fr) (m' s)

variable {G : α → Prop} {H : β → Prop} {Lb L X L₁ X' : Live}

/-- What relates a raise, a jump, a panic and a performance, each with its
`Post`, relates them with any `Post` that it implies. -/
theorem MCorr.escapes {G : α → Copy.Frame → Prop} {H : β → Copy.Frame → Prop} {L' X' : Live}
    {mk mk' : List Bool} {s s' : State}
    (f : ∀ fr s₁, Post L X mk s fr s₁ → Post L' X' mk' s' fr s₁) :
    (MCorr.relationF G L X mk s).Escapes (MCorr.relationF H L' X' mk' s') :=
  ⟨fun _ _ _ _ h => ⟨h.1, h.2.1, f _ _ h.2.2⟩, fun _ _ _ _ h => ⟨h.1, h.2.1, f _ _ h.2.2⟩,
    fun _ _ _ _ h => ⟨h.1, f _ _ h.2⟩,
    fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, f _ _ h.2.2.2⟩, fun _ _ _ _ _ h => h⟩

/-- What relates outcomes with each `Post` relates them with any `Post` that it
implies, and with any property of values that `G` implies. -/
theorem MCorr.subF {G G' : α → Copy.Frame → Prop} {L' X' : Live} {mk mk' : List Bool}
    {s s' : State} (hG : ∀ a fr, G a fr → G' a fr)
    (f : ∀ fr s₁, Post L X mk s fr s₁ → Post L' X' mk' s' fr s₁) :
    (MCorr.relationF G L X mk s).Sub (MCorr.relationF G' L' X' mk' s') :=
  ⟨fun _ _ _ _ h => ⟨h.1, hG _ _ h.2.1, f _ _ h.2.2⟩, MCorr.escapes f⟩

/-- What relates outcomes with each `Post` relates them with any `Post` that it
implies. -/
theorem MCorr.sub {L' X' : Live} {mk mk' : List Bool} {s s' : State}
    (f : ∀ fr s₁, Post L X mk s fr s₁ → Post L' X' mk' s' fr s₁) :
    (MCorr.relation G L X mk s).Sub (MCorr.relation G L' X' mk' s') :=
  MCorr.subF (fun _ _ h => h) f

theorem MAgrees.keys_eq {m : List Bool} {fr : Copy.Frame} {s : State} (h : MAgrees m fr s) :
    names fr = keys s := h.align

theorem MAgrees.liveAt_env {m : List Bool} {fr : Copy.Frame} {s : State} (h : MAgrees m fr s)
    {x : Name} (hx : LiveAt x m (names fr)) : LiveAt x m (s.env.map Prod.fst) :=
  h.align ▸ hx

theorem MAgrees.valid_sel {m mk : List Bool} {fr : Copy.Frame} {s : State} (h : MAgrees m fr s)
    (X : Live) : Valid ⟨sel mk X s.env, s.store⟩ := fun xr hxr =>
  h.valid xr ((sublist_keep mk s.env).subset (sel_mem hxr).1)

namespace Post

theorem refl {mk : List Bool} {fr : Copy.State} {s : State × World} (h : MAgreesIn mk fr s) :
    Post L X mk s.1 fr s :=
  ⟨mk, h, Kills.refl L X mk _ (by rw [← h.1.keys_eq]; simp [h.1.len]), rfl, Evolves.refl _⟩

theorem trans {mk : List Bool} {fr : Copy.Frame} {fr₂ : Copy.State} {s : State}
    {s₂ : State × World} (hag : MAgrees mk fr s) {m₁ : List Bool} {s₁ : State}
    (hk : Kills L₁ X mk m₁ (keys s)) (henv : s₁.env = s.env)
    (hev : Evolves ⟨sel mk X s.env, s.store⟩ ⟨sel mk X s.env, s₁.store⟩)
    (h : Post L X m₁ s₁ fr₂ s₂) (hL : L.Sub L₁) : Post L X mk s fr₂ s₂ := by
  obtain ⟨m₂, hag₂, hk₂, henv₂, hev₂⟩ := h
  rw [keys, henv] at hk₂
  rw [henv] at hev₂
  refine ⟨m₂, hag₂, hk.trans hk₂ hL, henv₂.trans henv, ?_⟩
  exact hev.trans (hag.valid_sel X) (Evolves.of_sub (sel_sub hk (Live.Sub.refl X)) hev₂)

theorem mono {mk : List Bool} {fr : Copy.State} {s : State} {s' : State × World}
    (h : Post L X mk s fr s')
    {L' X' : Live} (hL : L'.Sub L) (hX : X.Sub X') : Post L' X' mk s fr s' := by
  obtain ⟨m, hag, hk, henv, hev⟩ := h
  exact ⟨m, hag, hk.mono hL hX, henv, Evolves.of_sub (sel_mono hX) hev⟩

/-- The two states a step ends with are in one world. -/
theorem world {mk : List Bool} {s : State} {fr : Copy.State} {s' : State × World}
    (h : Post L X mk s fr s') : fr.2 = s'.2 := by
  obtain ⟨_, ⟨_, hw, _⟩, _⟩ := h
  exact hw

/-- The cells of the world a step ends in hold values that a run may hold. -/
theorem safe {mk : List Bool} {s : State} {fr : Copy.State} {s' : State × World}
    (h : Post L X mk s fr s') : fr.2.All VOk := by
  obtain ⟨_, ⟨_, _, hx⟩, _⟩ := h
  exact hx

/-- What holds when a step ends holds of its frames in any one world. -/
theorem reworld {mk : List Bool} {s : State} {fr : Copy.State} {s' : State × World}
    (h : Post L X mk s fr s') {w w' : World} (hw : w = w') (hx : w.All VOk) :
    Post L X mk s (fr.1, w) (s'.1, w') := by
  obtain ⟨m, ⟨hag, -⟩, hk, henv, hev⟩ := h
  exact ⟨m, ⟨hag, hw, hx⟩, hk, henv, hev⟩

end Post

/-- The ways two corresponding outcomes can be. A raise and a jump each carry
what goes on with them and a `Post`; `Escape` groups them, as every step but
those that catch them passes both on alike. -/
def Escape (L X : Live) (mk : List Bool) (s : State) (o : Outcome Copy.State α)
    (o' : Outcome (State × World) α) : Prop :=
  (∃ e fr s', o = .raised e fr ∧ o' = .raised e s' ∧ VOk e ∧ Post L X mk s fr s') ∨
    (∃ j fr s', o = .jumped j fr ∧ o' = .jumped j s' ∧ JOk j ∧ Post L X mk s fr s')

theorem MCorr.cases {mk : List Bool} {s : State} {o : Outcome Copy.State α}
    {o' : Outcome (State × World) α} (h : MCorr G L X mk s o o') :
    (∃ a fr s', o = .done a fr ∧ o' = .done a s' ∧ G a ∧ Post L X mk s fr s') ∨
      Escape L X mk s o o' ∨
      (∃ k fr s', o = .panicked k fr ∧ o' = .panicked k s' ∧ Post L X mk s fr s') ∨
      (∃ op v fr s' k k', o = .performed op v fr k ∧ o' = .performed op v s' k' ∧ VOk v ∧
        Post L X mk s fr s' ∧ ∀ w x, VOk w → x.All VOk → MCorr G L X mk s (k w x) (k' w x)) ∨
      (o = .outOfFuel ∧ o' = .outOfFuel) ∨
      (o = .stuck ∧ o' = .stuck) := by
  cases o <;> cases o' <;> (try exact absurd h id)
  · obtain ⟨rfl, hG, hp⟩ := h
    exact .inl ⟨_, _, _, rfl, rfl, hG, hp⟩
  · obtain ⟨rfl, he, hp⟩ := h
    exact .inr (.inl (.inl ⟨_, _, _, rfl, rfl, he, hp⟩))
  · obtain ⟨rfl, hj, hp⟩ := h
    exact .inr (.inl (.inr ⟨_, _, _, rfl, rfl, hj, hp⟩))
  · obtain ⟨rfl, hp⟩ := h
    exact .inr (.inr (.inl ⟨_, _, _, rfl, rfl, hp⟩))
  · obtain ⟨⟨rfl, rfl, hv, hp⟩, hk⟩ := h
    exact .inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, rfl, rfl, hv, hp, fun w x hw hx => hk w x w x ⟨rfl, hw, rfl, hx⟩⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩))))
  · exact .inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩))))

/-- An escape with its `Post` changed, as `f` changes it. -/
theorem Escape.post {mk mk' : List Bool} {s s₀ : State} {L' X' : Live}
    {o : Outcome Copy.State α} {o' : Outcome (State × World) α} (h : Escape L X mk s o o')
    (f : ∀ fr s', Post L X mk s fr s' → Post L' X' mk' s₀ fr s') : MCorr G L' X' mk' s₀ o o' := by
  rcases h with ⟨e, fr, s', rfl, rfl, he, hp⟩ | ⟨j, fr, s', rfl, rfl, hj, hp⟩
  · exact ⟨rfl, he, f fr s' hp⟩
  · exact ⟨rfl, hj, f fr s' hp⟩

theorem MCorr.fault {mk : List Bool} {fr : Copy.State} {s : State × World}
    (hag : MAgreesIn mk fr s) (f : Fault) :
    MCorr G L X mk s.1 (Outcome.fault f fr) (Outcome.fault f s) := by
  cases f
  · exact ⟨rfl, Post.refl hag⟩
  · trivial

/-- What came before an outcome: a step that ended no binding `L₁` holds. -/
theorem MCorr.prefix {mk m₁ : List Bool} {fr : Copy.Frame} {s s₁ : State}
    (hag : MAgrees mk fr s) (hk : Kills L₁ X mk m₁ (keys s))
    (henv : s₁.env = s.env) (hev : Evolves ⟨sel mk X s.env, s.store⟩ ⟨sel mk X s.env, s₁.store⟩)
    (hL : L.Sub L₁) {o : Outcome Copy.State α} {o' : Outcome (State × World) α}
    (hc : MCorr G L X m₁ s₁ o o') : MCorr G L X mk s o o' :=
  Outcome.Rel.mono hc (MCorr.sub fun _ _ hp => Post.trans hag hk henv hev hp hL)

namespace MSim

theorem pure {a : α} (h : G a) : MSim G Lb L X (Pure.pure a) (Pure.pure a) :=
  fun _ _ _ hag _ => ⟨rfl, h, Post.refl hag⟩

theorem fail (f : Fault) : MSim G Lb L X (Eval.fail f) (Eval.fail f) :=
  fun _ _ _ hag _ => MCorr.fault hag f

theorem outOfFuel : MSim G Lb L X Eval.outOfFuel Eval.outOfFuel :=
  fun _ _ _ _ _ => trivial

theorem throw {e : Value} (he : VOk e) : MSim G Lb L X (Eval.throw e) (Eval.throw e) :=
  fun _ _ _ hag _ => ⟨rfl, he, Post.refl hag⟩

theorem jump {j : Jump} (hj : JOk j) : MSim G Lb L X (Eval.jump j) (Eval.jump j) :=
  fun _ _ _ hag _ => ⟨rfl, hj, Post.refl hag⟩

/-- A turn of a loop's body: a `break` or a `continue` ends it as a step does
(expressions.break-and-continue). -/
theorem turn {m : Eval Copy.State Value} {m' : Eval (State × World) Value}
    (hm : MSim VOk Lb L X m m') :
    MSim (fun _ => True) Lb L X (Eval.turn m) (Eval.turn m') := by
  intro fr s mk hag hinv
  refine Outcome.Rel.turn (hm fr s mk hag hinv) (fun _ _ _ _ hc => ⟨rfl, trivial, hc.2.2⟩)
    (fun _ _ _ _ hc => hc) ?_ (fun _ _ _ _ hc => hc) ⟨fun _ _ _ _ _ _ h => h, fun _ _ _ _ _ h => h⟩
  rintro j fr₁ j' s₁ ⟨rfl, hj, hp⟩
  cases j with
  | brk => exact ⟨rfl, trivial, hp⟩
  | cont => exact ⟨rfl, trivial, hp⟩
  | ret v => exact ⟨rfl, hj, hp⟩

theorem ofExcept (x : Except Fault α) (h : ∀ a, x = .ok a → G a) :
    MSim G Lb L X (Eval.ofExcept x) (Eval.ofExcept x) := by
  intro fr s mk hag _
  cases x with
  | error f => exact MCorr.fault hag f
  | ok a => exact ⟨rfl, h a rfl, Post.refl hag⟩

/-- Reading and writing the world alike: both models are in one world. -/
theorem world {R : Value → Prop} (f : World → Except Fault (Value × World))
    (h : ∀ x v x', x.All VOk → f x = .ok (v, x') → R v ∧ x'.All VOk) :
    MSim R Lb L X (Eval.world Copy.memory f) (Eval.world Moving.memory f) := by
  rintro ⟨fr, x⟩ ⟨s, y⟩ mk ⟨hm, hx, hsafe⟩ _
  cases hx
  cases hf : f x with
  | ok p =>
    rw [show Eval.world Copy.memory f (fr, x) = .done p.1 (fr, p.2) from Eval.world_ok hf,
      show Eval.world Moving.memory f (s, x) = .done p.1 (s, p.2) from Eval.world_ok hf]
    obtain ⟨hv, hx'⟩ := h x p.1 p.2 hsafe hf
    exact ⟨rfl, hv, Post.refl (⟨hm, rfl, hx'⟩ : MAgreesIn mk (fr, p.2) (s, p.2))⟩
  | error e =>
    rw [show Eval.world Copy.memory f (fr, x) = .fault e (fr, x) from Eval.world_error hf,
      show Eval.world Moving.memory f (s, x) = .fault e (s, x) from Eval.world_error hf]
    exact MCorr.fault ⟨hm, rfl, hsafe⟩ e

/-- Reading the state alike. -/
theorem inspect {f : Copy.State → Except Fault α} {f' : State × World → Except Fault α}
    (h : ∀ fr s mk, MAgreesIn mk fr s → Inv Lb mk (keys s.1) →
      f fr = f' s ∧ ∀ a, f fr = .ok a → G a) :
    MSim G Lb L X (Eval.inspect f) (Eval.inspect f') := by
  intro fr s mk hag hinv
  obtain ⟨heq, hG⟩ := h fr s mk hag hinv
  show MCorr G L X mk s.1 (Eval.ofExcept (f fr) fr) (Eval.ofExcept (f' s) s)
  rw [← heq]
  cases hf : f fr with
  | error e => exact MCorr.fault hag e
  | ok a => exact ⟨rfl, hG a hf, Post.refl hag⟩

theorem bind {m : Eval Copy.State α} {m' : Eval (State × World) α} {f : α → Eval Copy.State β}
    {f' : α → Eval (State × World) β} (hm : MSim G Lb L₁ X m m')
    (hf : ∀ a, G a → MSim H L₁ L X (f a) (f' a)) (hLb : L₁.Sub Lb) (hL : L.Sub L₁) :
    MSim H Lb L X (m >>= f) (m' >>= f') := by
  intro fr s mk hag hinv
  show MCorr H L X mk s.1 ((m fr).bind fun a fr' => f a fr') ((m' s).bind fun a s' => f' a s')
  refine Outcome.Rel.bind (hm fr s mk hag hinv)
    (MCorr.escapes fun _ _ hp => hp.mono hL (Live.Sub.refl X)) ?_
  rintro a fr₁ a' s₁ ⟨rfl, hG, m₁, hag₁, hk, henv, hev⟩
  have hinv₁ : Inv L₁ m₁ (keys s₁.1) := by
    rw [keys, henv]
    exact hinv.of_kills hLb hk
  exact (hf a hG fr₁ s₁ m₁ hag₁ hinv₁).prefix hag.1 hk henv hev hL

theorem ite (b : Bool) {m₁ m₂ : Eval Copy.State α} {m₁' m₂' : Eval (State × World) α}
    (h₁ : MSim G Lb L X m₁ m₁') (h₂ : MSim G Lb L X m₂ m₂') :
    MSim G Lb L X (if b then m₁ else m₂) (if b then m₁' else m₂') := by
  cases b
  · exact h₂
  · exact h₁

/-- Weakens what an expression needs live, what follows it, and what it may
end or write. -/
theorem mono {m : Eval Copy.State α} {m' : Eval (State × World) α} {Lb' L' : Live}
    (h : MSim G Lb L X m m') (hLb : Lb.Sub Lb') (hL : L'.Sub L) (hX : X.Sub X') :
    MSim G Lb' L' X' m m' := by
  intro fr s mk hag hinv
  exact Outcome.Rel.mono (h fr s mk hag (hinv.mono hLb)) (MCorr.sub fun _ _ hp => hp.mono hL hX)

/-- Both models read a variable that is live. -/
theorem read (x : Name) (hx : Lb.mem x = true) :
    MSim VOk Lb L X (Eval.inspect fun fr => Copy.memory.read fr x [])
      (Eval.inspect fun s => Moving.memory.read s x []) :=
  inspect fun _ _ _ hag hinv => by
    have hl : LiveAt x _ (names _) := hag.1.keys_eq ▸ hinv.live x hx
    exact ⟨hag.1.read hl [], fun _ ha => hag.1.read_ok hl ha⟩

end MSim

end Stilt.Moving
