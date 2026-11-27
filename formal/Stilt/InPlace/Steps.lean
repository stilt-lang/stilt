import Stilt.Related
import Stilt.InPlace.Evolves
import Stilt.Cells
import Stilt.Selection

/-!
# Steps

The simulation between the two models of memory, and the steps of the
evaluator that keep it.

`Sim G m m'` says that `m`, run on a copy frame, and `m'`, run on an in-place
state that agrees with it, end the same way: with the same value, which `G`
holds of, or the same raise, jump, panic or performance, from a frame and a
state that still agree, the state having evolved only by writes below its
variables, a performance's rests ending the same way once resumed with the same
safe value in one world whose cells hold safe values; or out of fuel, or stuck. Each combinator of `Stilt.Semantics` keeps it,
as each keeps `Eval.Below` in `Stilt.Fuel`. Calls are in
`Stilt.InPlace.Call`.
-/

namespace Stilt.InPlace

variable {α β : Type}

/-- A jump that a run may carry: a `return`'s value is safe. -/
def _root_.Stilt.Jump.Safe : Jump → Prop
  | .ret v => v.Safe
  | _ => True

/-- A state of each model that agree: frames that agree, in one world, whose cells hold safe
values. -/
def AgreesIn (fr : Copy.State) (s : State × World) : Prop :=
  Agrees fr.1 s.1 ∧ fr.2 = s.2 ∧ fr.2.All Value.Safe

/-- What the two runs from a frame and the state `s` that agrees with it
relate: the same value, which `G` holds of, or the same raise, jump, panic or
performance of a safe value, each with a frame and a state that agree, the
state having evolved from `s`; and a performance resumed with the same safe
value in both, in one world whose cells hold safe values. -/
def Corr.relation (G : α → Prop) (s : State) :
    Outcome.Relation Copy.State (State × World) α α where
  done a fr a' s' := a = a' ∧ G a ∧ AgreesIn fr s' ∧ Evolves s s'.1
  raised e fr e' s' := e = e' ∧ e.Safe ∧ AgreesIn fr s' ∧ Evolves s s'.1
  jumped j fr j' s' := j = j' ∧ j.Safe ∧ AgreesIn fr s' ∧ Evolves s s'.1
  panicked k fr k' s' := k = k' ∧ AgreesIn fr s' ∧ Evolves s s'.1
  performed op v fr op' v' s' := op = op' ∧ v = v' ∧ v.Safe ∧ AgreesIn fr s' ∧ Evolves s s'.1
  resume _ w x w' x' := w = w' ∧ w.Safe ∧ x = x' ∧ x.All Value.Safe

/-- The outcomes of the two runs from a frame and the state `s` that agrees
with it correspond. -/
def Corr (G : α → Prop) (s : State) :
    Outcome Copy.State α → Outcome (State × World) α → Prop :=
  Outcome.Rel (Corr.relation G s)

/-- A step after a value leaves a raise, a jump, a panic and a performance as
they are. -/
theorem Corr.escapes {G : α → Prop} {H : β → Prop} (s : State) :
    (Corr.relation G s).Escapes (Corr.relation H s) :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ _ _ h => h,
    fun _ _ _ _ _ h => h⟩

/-- `m` and `m'` end the same way from every frame and state that agree. -/
def Sim (G : α → Prop) (m : Eval Copy.State α) (m' : Eval (State × World) α) : Prop :=
  ∀ fr s, AgreesIn fr s → Corr G s.1 (m fr) (m' s)

/-- Evaluating a safe expression keeps the simulation. -/
def SimRun (run : Expr → Eval Copy.State Value) (run' : Expr → Eval (State × World) Value) :
    Prop :=
  ∀ e, e.Safe → Sim Value.Safe (run e) (run' e)

/-- What relates outcomes from a state that evolved from `s` relates them from `s`. -/
theorem Corr.sub {G : α → Prop} {s s₁ : State} (hv : Valid s) (h : Evolves s s₁) :
    (Corr.relation G s₁).Sub (Corr.relation G s) :=
  ⟨fun _ _ _ _ hc => ⟨hc.1, hc.2.1, hc.2.2.1, h.trans hv hc.2.2.2⟩,
    fun _ _ _ _ hc => ⟨hc.1, hc.2.1, hc.2.2.1, h.trans hv hc.2.2.2⟩,
    fun _ _ _ _ hc => ⟨hc.1, hc.2.1, hc.2.2.1, h.trans hv hc.2.2.2⟩,
    fun _ _ _ _ hc => ⟨hc.1, hc.2.1, h.trans hv hc.2.2⟩,
    fun _ _ _ _ _ _ hc => ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, h.trans hv hc.2.2.2.2⟩,
    fun _ _ _ _ _ hc => hc⟩

theorem Corr.evolve {G : α → Prop} {s s₁ : State} (hv : Valid s) (h : Evolves s s₁)
    {o : Outcome Copy.State α} {o' : Outcome (State × World) α} (hc : Corr G s₁ o o') :
    Corr G s o o' :=
  Outcome.Rel.mono hc (Corr.sub hv h)

/-- The seven ways two corresponding outcomes can be. -/
theorem Corr.cases {G : α → Prop} {s : State} {o : Outcome Copy.State α}
    {o' : Outcome (State × World) α} (h : Corr G s o o') :
    (∃ a fr s', o = .done a fr ∧ o' = .done a s' ∧ G a ∧ AgreesIn fr s' ∧ Evolves s s'.1) ∨
      (∃ e fr s', o = .raised e fr ∧ o' = .raised e s' ∧ e.Safe ∧ AgreesIn fr s' ∧
        Evolves s s'.1) ∨
      (∃ j fr s', o = .jumped j fr ∧ o' = .jumped j s' ∧ j.Safe ∧ AgreesIn fr s' ∧
        Evolves s s'.1) ∨
      (∃ k fr s', o = .panicked k fr ∧ o' = .panicked k s' ∧ AgreesIn fr s' ∧ Evolves s s'.1) ∨
      (∃ op v fr s' k k', o = .performed op v fr k ∧ o' = .performed op v s' k' ∧ v.Safe ∧
        AgreesIn fr s' ∧ Evolves s s'.1 ∧ ∀ w x, w.Safe → x.All Value.Safe → Corr G s (k w x) (k' w x)) ∨
      (o = .outOfFuel ∧ o' = .outOfFuel) ∨
      (o = .stuck ∧ o' = .stuck) := by
  cases o <;> cases o' <;> (try exact absurd h id)
  · obtain ⟨rfl, hG, hag, hev⟩ := h
    exact .inl ⟨_, _, _, rfl, rfl, hG, hag, hev⟩
  · obtain ⟨rfl, he, hag, hev⟩ := h
    exact .inr (.inl ⟨_, _, _, rfl, rfl, he, hag, hev⟩)
  · obtain ⟨rfl, hj, hag, hev⟩ := h
    exact .inr (.inr (.inl ⟨_, _, _, rfl, rfl, hj, hag, hev⟩))
  · obtain ⟨rfl, hag, hev⟩ := h
    exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl, rfl, hag, hev⟩)))
  · obtain ⟨⟨rfl, rfl, hv, hag, hev⟩, hk⟩ := h
    exact .inr (.inr (.inr (.inr (.inl
      ⟨_, _, _, _, _, _, rfl, rfl, hv, hag, hev, fun w x hw hx => hk w x w x ⟨rfl, hw, rfl, hx⟩⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, rfl⟩)))))

theorem Corr.fault {G : α → Prop} {fr : Copy.State} {s : State × World} (hs : AgreesIn fr s)
    (f : Fault) : Corr G s.1 (Outcome.fault f fr) (Outcome.fault f s) := by
  cases f
  · exact ⟨rfl, hs, Evolves.refl s.1⟩
  · trivial

namespace Sim

theorem pure {G : α → Prop} {a : α} (h : G a) : Sim G (pure a) (pure a) :=
  fun _ s hs => ⟨rfl, h, hs, Evolves.refl s.1⟩

theorem fail {G : α → Prop} (f : Fault) : Sim G (Eval.fail f) (Eval.fail f) :=
  fun _ _ hs => Corr.fault hs f

theorem outOfFuel {G : α → Prop} : Sim G Eval.outOfFuel Eval.outOfFuel :=
  fun _ _ _ => trivial

theorem throw {G : α → Prop} {e : Value} (he : e.Safe) : Sim G (Eval.throw e) (Eval.throw e) :=
  fun _ s hs => ⟨rfl, he, hs, Evolves.refl s.1⟩

theorem jump {G : α → Prop} {j : Jump} (hj : j.Safe) : Sim G (Eval.jump j) (Eval.jump j) :=
  fun _ s hs => ⟨rfl, hj, hs, Evolves.refl s.1⟩

theorem ofExcept {G : α → Prop} (x : Except Fault α) (h : ∀ a, x = .ok a → G a) :
    Sim G (Eval.ofExcept x) (Eval.ofExcept x) := by
  intro fr s hs
  cases x with
  | error f => exact Corr.fault hs f
  | ok a => exact ⟨rfl, h a rfl, hs, Evolves.refl s.1⟩

/-- Reading and writing the world alike: both models are in one world. -/
theorem world (f : World → Except Fault (Value × World))
    (h : ∀ x v x', x.All Value.Safe → f x = .ok (v, x') → v.Safe ∧ x'.All Value.Safe) :
    Sim Value.Safe (Eval.world Copy.memory f) (Eval.world InPlace.memory f) := by
  rintro ⟨fr, x⟩ ⟨s, y⟩ ⟨hag, hx, hsafe⟩
  cases hx
  cases hf : f x with
  | ok p =>
    rw [show Eval.world Copy.memory f (fr, x) = .done p.1 (fr, p.2) from Eval.world_ok hf,
      show Eval.world InPlace.memory f (s, x) = .done p.1 (s, p.2) from Eval.world_ok hf]
    obtain ⟨hv, hx'⟩ := h x p.1 p.2 hsafe hf
    exact ⟨rfl, hv, ⟨hag, rfl, hx'⟩, Evolves.refl s⟩
  | error e =>
    rw [show Eval.world Copy.memory f (fr, x) = .fault e (fr, x) from Eval.world_error hf,
      show Eval.world InPlace.memory f (s, x) = .fault e (s, x) from Eval.world_error hf]
    exact Corr.fault ⟨hag, rfl, hsafe⟩ e

/-- Reading the state alike. -/
theorem inspect {G : α → Prop} {f : Copy.State → Except Fault α}
    {f' : State × World → Except Fault α}
    (h : ∀ fr s, AgreesIn fr s → f fr = f' s ∧ ∀ a, f fr = .ok a → G a) :
    Sim G (Eval.inspect f) (Eval.inspect f') := by
  intro fr s hs
  obtain ⟨heq, hG⟩ := h fr s hs
  show Corr G s.1 (Eval.ofExcept (f fr) fr) (Eval.ofExcept (f' s) s)
  rw [← heq]
  cases hf : f fr with
  | error e => exact Corr.fault hs e
  | ok a => exact ⟨rfl, hG a hf, hs, Evolves.refl s.1⟩

theorem bind {G : α → Prop} {H : β → Prop} {m : Eval Copy.State α} {m' : Eval (State × World) α}
    {f : α → Eval Copy.State β} {f' : α → Eval (State × World) β} (hm : Sim G m m')
    (hf : ∀ a, G a → Sim H (f a) (f' a)) : Sim H (m >>= f) (m' >>= f') := by
  intro fr s hs
  show Corr H s.1 ((m fr).bind fun a fr' => f a fr') ((m' s).bind fun a s' => f' a s')
  refine Outcome.Rel.bind (hm fr s hs) (Corr.escapes s.1) ?_
  rintro a fr₁ a' s₁ ⟨rfl, hG, hag, hev⟩
  exact (hf a hG fr₁ s₁ hag).evolve hs.1.valid hev

theorem ite {G : α → Prop} (b : Bool) {m₁ m₂ : Eval Copy.State α} {m₁' m₂' : Eval (State × World) α}
    (h₁ : Sim G m₁ m₁') (h₂ : Sim G m₂ m₂') :
    Sim G (if b then m₁ else m₂) (if b then m₁' else m₂') := by
  cases b
  · exact h₂
  · exact h₁

theorem withVar {G : α → Prop} (x : Name) {v : Value} (hv : v.Safe) {m : Eval Copy.State α}
    {m' : Eval (State × World) α} (hm : Sim G m m') :
    Sim G (Eval.withVar Copy.memory x v m) (Eval.withVar InPlace.memory x v m') := by
  intro fr s hs
  have key : ∀ fr₁ s₁, AgreesIn fr₁ s₁ → Evolves (InPlace.bind s.1 x v) s₁.1 →
      AgreesIn (Copy.memory.unbind fr₁) (InPlace.memory.unbind s₁) ∧
        Evolves s.1 (InPlace.memory.unbind s₁).1 := by
    intro fr₁ s₁ hag hev
    have henv : s₁.1.env.tail = s.1.env := by rw [hev.1]; rfl
    refine ⟨⟨hag.1.unbind, hag.2⟩, ?_⟩
    show Evolves s.1 ⟨s₁.1.env.tail, s₁.1.store⟩
    rw [henv]
    exact hev.unbind
  exact Outcome.Rel.unbind Copy.memory InPlace.memory (hm _ _ ⟨hs.1.bind x hv, hs.2⟩)
    (fun _ _ _ _ ⟨h₁, h₂, hag, hev⟩ => ⟨h₁, h₂, key _ _ hag hev⟩)
    (fun _ _ _ _ ⟨h₁, h₂, hag, hev⟩ => ⟨h₁, h₂, key _ _ hag hev⟩)
    (fun _ _ _ _ ⟨h₁, h₂, hag, hev⟩ => ⟨h₁, h₂, key _ _ hag hev⟩)
    (fun _ _ _ _ ⟨h₁, hag, hev⟩ => ⟨h₁, key _ _ hag hev⟩)
    (fun _ _ _ _ _ _ ⟨h₁, h₂, h₃, hag, hev⟩ => ⟨h₁, h₂, h₃, key _ _ hag hev⟩) fun _ _ _ _ _ h => h

/-- Both models copy an initializer's value, the last use of a variable
included (values.independent-copies and values.let-and-var). -/
theorem withInit {G : α → Prop} (x : Name) (init : Expr) {v : Value} (hv : v.Safe)
    {m : Eval Copy.State α} {m' : Eval (State × World) α} (hm : Sim G m m') :
    Sim G (Eval.withInit Copy.memory x init v m) (Eval.withInit InPlace.memory x init v m') := by
  have h₁ : Eval.withInit Copy.memory x init v m = Eval.withVar Copy.memory x v m := by
    cases init <;> rfl
  have h₂ : Eval.withInit InPlace.memory x init v m' = Eval.withVar InPlace.memory x v m' := by
    cases init <;> rfl
  rw [h₁, h₂]
  exact withVar x hv hm

theorem withVars {G : α → Prop} {m : Eval Copy.State α} {m' : Eval (State × World) α} (hm : Sim G m m') :
    ∀ bindings : List (Name × Value), (∀ xv ∈ bindings, xv.2.Safe) →
      Sim G (Eval.withVars Copy.memory bindings m) (Eval.withVars InPlace.memory bindings m')
  | [], _ => hm
  | (x, v) :: bindings, h =>
    withVar x (h (x, v) List.mem_cons_self)
      (withVars hm bindings fun xv hxv => h xv (List.mem_cons_of_mem _ hxv))

theorem handle {G : α → Prop} {m : Eval Copy.State α} {m' : Eval (State × World) α}
    {h : Value → Eval Copy.State α} {h' : Value → Eval (State × World) α} (hm : Sim G m m')
    (hh : ∀ e, e.Safe → Sim G (h e) (h' e)) : Sim G (Eval.handle m h) (Eval.handle m' h') := by
  intro fr s hs
  show Corr G s.1 ((m fr).handle fun e fr' => h e fr') ((m' s).handle fun e s' => h' e s')
  refine Outcome.Rel.handle (hm fr s hs) (fun _ _ _ _ hc => hc) (fun _ _ _ _ hc => hc)
    (fun _ _ _ _ hc => hc) (Corr.escapes s.1).performs ?_
  rintro e fr₁ e' s₁ ⟨rfl, he, hag, hev⟩
  exact (hh e he fr₁ s₁ hag).evolve hs.1.valid hev

/-- A turn of a loop's body: a `break` or a `continue` ends it as a step does
(expressions.break-and-continue). -/
theorem turn {m : Eval Copy.State Value} {m' : Eval (State × World) Value} (hm : Sim Value.Safe m m') :
    Sim (fun _ => True) (Eval.turn m) (Eval.turn m') := by
  intro fr s hs
  refine Outcome.Rel.turn (hm fr s hs) (fun _ _ _ _ hc => ⟨rfl, trivial, hc.2.2⟩)
    (fun _ _ _ _ hc => hc) ?_ (fun _ _ _ _ hc => hc) (Corr.escapes s.1).performs
  rintro j fr₁ j' s₁ ⟨rfl, hj, hag, hev⟩
  cases j with
  | brk => exact ⟨rfl, trivial, hag, hev⟩
  | cont => exact ⟨rfl, trivial, hag, hev⟩
  | ret v => exact ⟨rfl, hj, hag, hev⟩

theorem forEach {body : Value → Eval Copy.State Bool} {body' : Value → Eval (State × World) Bool}
    (h : ∀ v, v.Safe → Sim (fun _ => True) (body v) (body' v)) :
    ∀ vs : List Value, (∀ v ∈ vs, v.Safe) →
      Sim (fun _ => True) (Eval.forEach body vs) (Eval.forEach body' vs)
  | [], _ => pure trivial
  | v :: vs, hvs =>
    bind (h v (hvs v List.mem_cons_self)) fun g _ =>
      ite g (forEach h vs fun u hu => hvs u (List.mem_cons_of_mem _ hu)) (pure trivial)

/-! ## Reading, writing and capturing -/

theorem read (x : Name) :
    Sim Value.Safe (Eval.inspect fun fr => Copy.memory.read fr x [])
      (Eval.inspect fun s => InPlace.memory.read s x []) :=
  inspect fun _ _ hs => ⟨hs.1.read x [], fun _ ha => hs.1.read_safe ha⟩

theorem capture (keep : Name → Bool) :
    Sim (fun captured : List (Name × Value) => ∀ xv ∈ captured, xv.2.Safe)
      (Eval.inspect (Copy.memory.capture · keep)) (Eval.inspect (InPlace.memory.capture · keep)) :=
  inspect fun _ _ hs => ⟨(hs.1.capture keep).symm, fun _ ha => by
    cases ha; exact fun xv h => hs.1.safe xv (mem_of_mem_newestOf h)⟩

theorem update (x : Name) (p : Path) {w : Value} (hw : w.Safe) :
    Sim (fun _ => True) (Eval.update fun fr => Copy.memory.write fr x p w)
      (Eval.update fun s => InPlace.memory.write s x p w) := by
  intro fr s hs
  unfold Eval.update
  rcases hs.1.write hw x p with ⟨f, h₁, h₂⟩ | ⟨fr', s', h₁, h₂, hag, hev⟩
  · simp only [Copy.memory, InPlace.memory, Frames.withWorld, Copy.frames, InPlace.frames, h₁, h₂]
    exact Corr.fault hs f
  · simp only [Copy.memory, InPlace.memory, Frames.withWorld, Copy.frames, InPlace.frames, h₁, h₂]
    exact ⟨rfl, trivial, ⟨hag, hs.2⟩, hev⟩

/-! ## Conversions -/

theorem asInt {v : Value} : Sim (fun _ => True) (Eval.asInt v) (Eval.asInt v) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem asBool {v : Value} : Sim (fun _ => True) (Eval.asBool v) (Eval.asBool v) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem asList {v : Value} (hv : v.Safe) :
    Sim (fun vs : List Value => ∀ u ∈ vs, u.Safe) (Eval.asList v) (Eval.asList v) := by
  cases v <;> first | exact fail _ | skip
  cases hv with
  | list h => exact pure h

end Sim

end Stilt.InPlace

namespace Stilt.InPlace.Sim

theorem mapM_mem {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {out : List β}, l.mapM g = some out → ∀ b ∈ out, ∃ a ∈ l, g a = some b
  | [], out, h, b, hb => by
    have : out = [] := by simpa [eq_comm] using h
    subst this
    simp at hb
  | a :: l, out, h, b, hb => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨b', hb', out', hout', hout⟩ := h
    have : out = b' :: out' := by simpa [eq_comm] using hout
    subst this
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hb'⟩
    · obtain ⟨a', ha', hg⟩ := mapM_mem hout' b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', hg⟩

theorem declare (D : Decls) (R : Name) {written : List (Name × Value)}
    (hw : ∀ fv ∈ written, fv.2.Safe) :
    Sim Value.Safe (Eval.declare D R written) (Eval.declare D R written) := by
  unfold Eval.declare
  split
  · split
    · rename_i fields hfields
      refine pure (.record fun fv hfv => ?_)
      obtain ⟨⟨f, τ⟩, _, ha⟩ := mapM_mem hfields fv hfv
      simp only [Option.map_eq_some_iff] at ha
      obtain ⟨v, hv, rfl⟩ := ha
      exact hw _ (mem_of_lookup hv)
    · exact fail _
  · exact fail _

section Runs

variable {run : Expr → Eval Copy.State Value} {run' : Expr → Eval (State × World) Value}

theorem list (h : SimRun run run') : ∀ es : List Expr, (∀ e ∈ es, e.Safe) →
    Sim (fun vs : List Value => ∀ v ∈ vs, v.Safe) (Eval.list run es) (Eval.list run' es)
  | [], _ => pure (by simp)
  | e :: es, hes =>
    bind (h e (hes e List.mem_cons_self)) fun v hv =>
      bind (list h es fun e' he' => hes e' (List.mem_cons_of_mem _ he')) fun vs hvs =>
        pure fun u hu => by
          rcases List.mem_cons.1 hu with rfl | hu
          · exact hv
          · exact hvs u hu

theorem fields (h : SimRun run run') : ∀ fs : List (Name × Expr), (∀ fe ∈ fs, fe.2.Safe) →
    Sim (fun ws : List (Name × Value) => ∀ fv ∈ ws, fv.2.Safe) (Eval.fields run fs)
      (Eval.fields run' fs)
  | [], _ => pure (by simp)
  | (f, e) :: fs, hfs =>
    bind (h e (hfs (f, e) List.mem_cons_self)) fun v hv =>
      bind (fields h fs fun fe hfe => hfs fe (List.mem_cons_of_mem _ hfe)) fun ws hws =>
        pure fun fv hfv => by
          rcases List.mem_cons.1 hfv with rfl | hfv
          · exact hv
          · exact hws fv hfv

/-- Evaluating the indexes of a place gives a path that resolves it. -/
theorem path (h : SimRun run run') : ∀ ps : List Projection, PathSafe ps →
    Sim (fun p : Path => p.Resolves ps) (Eval.path run ps) (Eval.path run' ps)
  | [], _ => pure trivial
  | .field _ :: ps, hps =>
    bind (path h ps fun i hi => hps i (List.mem_cons_of_mem _ hi)) fun _ hp => pure ⟨rfl, hp⟩
  | .index i :: ps, hps =>
    bind (bind (h i (hps i List.mem_cons_self)) fun _ _ => asInt) fun _ _ =>
      bind (path h ps fun j hj => hps j (List.mem_cons_of_mem _ hj)) fun _ hp => pure hp

/-- The values a call passes are safe. -/
def PassedSafe (passed : List Passed) : Prop := ∀ q ∈ passed, ∀ v, q.value? = some v → v.Safe

/-- Each passed argument is what its argument evaluated to: a value, or the
place it names with its indexes evaluated. -/
def ArgsResolved : List Arg → List Passed → Prop
  | [], [] => True
  | .value _ :: as, .value _ :: qs => ArgsResolved as qs
  | .value _ :: as, .moved _ _ :: qs => ArgsResolved as qs
  | .inout ⟨x, ps⟩ :: as, .place y p :: qs => x = y ∧ p.Resolves ps ∧ ArgsResolved as qs
  | _, _ => False

theorem value?_ofArg (e : Expr) (v : Value) : (Passed.ofArg e v).value? = some v := by
  cases e <;> rfl

theorem resolved_ofArg (e : Expr) (v : Value) {as : List Arg} {qs : List Passed}
    (h : ArgsResolved as qs) : ArgsResolved (.value e :: as) (Passed.ofArg e v :: qs) := by
  cases e <;> exact h

/-- Evaluating a call's arguments gives safe values and the places the
arguments name. -/
theorem args (h : SimRun run run') : ∀ as : List Arg, ArgsSafe as →
    Sim (fun passed => PassedSafe passed ∧ ArgsResolved as passed) (Eval.args run as)
      (Eval.args run' as)
  | [], _ => pure ⟨by simp [PassedSafe], trivial⟩
  | .value e :: as, has =>
    bind (h e (has.1 e List.mem_cons_self)) fun v hv =>
      bind (args h as has.tail) fun ps hps =>
        pure ⟨fun q hq u hu => by
          rcases List.mem_cons.1 hq with rfl | hq
          · rw [value?_ofArg] at hu
            cases hu
            exact hv
          · exact hps.1 q hq u hu, resolved_ofArg e v hps.2⟩
  | .inout ⟨x, projections⟩ :: as, has =>
    bind (path h projections (has.2 x projections List.mem_cons_self)) fun _ hp =>
      bind (args h as has.tail) fun ps hps =>
        pure ⟨fun q hq u hu => by
          rcases List.mem_cons.1 hq with rfl | hq
          · cases hu
          · exact hps.1 q hq u hu, rfl, hp, hps.2⟩

theorem select (h : SimRun run run') {arms : List Arm}
    (harms : ∀ arm ∈ arms, arm.body.Safe ∧ ∀ g, arm.guard = some g → g.Safe)
    {v : Value} (hv : v.Safe) :
    Sim Value.Safe (Eval.select Copy.memory run arms v)
      (Eval.select InPlace.memory run' arms v) := by
  refine Eval.select_rel (Sim Value.Safe) (fail _) (fun arm ha _ us hm _ => ?_)
    fun arm ha g hg us hu _ m m' hmm => ?_
  · exact withVars (h _ (harms arm ha).1) _ fun xv hxv =>
      arm.pattern.matchOn_parts Value.Safe.passesToParts hv hm xv.2 (List.of_mem_zip hxv).2
  · obtain ⟨q, -, hq⟩ := Pattern.mem_ways hu
    have hparts : ∀ xv ∈ arm.binders.zip us, xv.2.Safe := fun xv hxv =>
      q.matchOn_parts Value.Safe.passesToParts hv hq xv.2 (List.of_mem_zip hxv).2
    exact bind (withVars (bind (h g ((harms arm ha).2 g hg)) fun _ _ => asBool) _ hparts)
      fun b _ => ite b (withVars (h _ (harms arm ha).1) _ hparts) hmm

theorem assign (h : SimRun run run') (x : Name) {ps : List Projection} (hps : PathSafe ps)
    {value : Expr} (hv : value.Safe) :
    Sim Value.Safe (Eval.assign Copy.memory run x ps value)
      (Eval.assign InPlace.memory run' x ps value) :=
  bind (path h ps hps) fun p _ =>
    bind (h value hv) fun _ hw => bind (update x p hw) fun _ _ => pure .unit

theorem loop (h : SimRun run run') (x : Name) {e body : Expr} (he : e.Safe) (hb : body.Safe) :
    Sim Value.Safe (Eval.loop Copy.memory run x e body) (Eval.loop InPlace.memory run' x e body) :=
  bind (bind (h e he) fun _ hv => asList hv) fun vs hvs =>
    bind (forEach (fun _ hv => withVar x hv (turn (h body hb))) vs hvs)
      fun _ _ => pure .unit

end Runs

end Stilt.InPlace.Sim
