import Stilt.Related
import Stilt.Cells
import Stilt.InPlace.Steps
import Stilt.Sharing.Evolves
import Stilt.Sharing.Kept
import Stilt.Sharing.Relation
import Stilt.Sharing.Eval

/-!
# Steps

The simulation of copy-in, copy-out by sharing when every binding is shared, and the steps of
the evaluator that keep it, as `Stilt.InPlace.Steps` gives them for in-place mutation.

`Sim G m m'` says that `m`, run on a copy frame, and `m'`, run on a state of sharing that agrees
with it on every binding, every binding shared, end the same way: with the same value, which `G`
holds of, or the same raise, jump, panic or performance, from a frame and a state that still
agree, the state having followed from the first (`Follows`): written only below the homes and
parts of its bindings and grown, its bindings referring, at the locations the first store has,
only below what the first state's did. A performance's rests end the same way once resumed with
the same safe value in one world whose cells hold safe values; or both runs are out of fuel, or
stuck.
-/

namespace Stilt.Sharing

open InPlace (Ref)

variable {α β : Type}

/-! ## Following -/

/-- The bindings of a state as the evaluator of sharing makes them when every binding is shared:
each modification of each copies first, and each home is a location of its own but an `inout`
parameter's, which is its argument's place and the part the parameter refers to. -/
structure AllShared (s : State) : Prop where
  shared : ∀ ye ∈ s.env, ye.2.unique = false
  homes : ∀ ye ∈ s.env, ye.2.home.path = [] ∨ ye.2.alias = none ∧ ye.2.inout = true
  inout : ∀ ye ∈ s.env, ye.2.inout = true → ye.2.alias = none

/-- The bindings of `s'` refer, at the locations of `s`'s store, only below the homes and parts
of `s`'s bindings. -/
def Within (s s' : State) : Prop :=
  ∀ P ∈ s'.paths, ∀ i q, P = .index i :: q → i < s.store.size → P.Under s.paths

/-- `s'` grew from `s`: it evolved from `s`, and its bindings refer, at the locations of `s`'s
store, only below `s`'s. -/
def Grown (s s' : State) : Prop := Evolves s s' ∧ Within s s'

/-- `s'` follows from `s`: it grew from `s`, with `s`'s bindings' names in order and its `inout`
bindings in their places. -/
def Follows (s s' : State) : Prop := Evolves s s' ∧ Within s s' ∧ Kept s s'

theorem Evolves.size_le {s s' : State} (h : Evolves s s') : s.store.size ≤ s'.store.size := by
  obtain ⟨W, st, extra, hs, hW, hseq⟩ := h
  have hlen := length_of_setSeq hW hseq
  rw [← Array.length_toList (xs := s'.store), hs, List.length_append, hlen]
  omega

theorem Follows.refl (s : State) : Follows s s :=
  ⟨Evolves.refl s, fun P hP _ _ _ _ => ⟨P, hP, [], by rw [List.append_nil]⟩, Kept.refl s⟩

theorem Grown.trans {s s₁ s₂ : State} (h₁ : Grown s s₁) (h₂ : Grown s₁ s₂) :
    Grown s s₂ := by
  refine ⟨h₁.1.trans h₂.1 h₁.2, fun P hP i q hq hi => ?_⟩
  have hle : (s.store.size : Int) ≤ s₁.store.size := by exact_mod_cast h₁.1.size_le
  obtain ⟨Q, hQ, r, rfl⟩ := h₂.2 P hP i q hq (Int.lt_of_lt_of_le hi hle)
  obtain ⟨j, q', rfl⟩ := atLoc_of_mem hQ
  have hj : (j : Int) = i := by
    simp only [List.cons_append, List.cons.injEq, Step.index.injEq] at hq
    exact hq.1
  subst hj
  obtain ⟨P₀, hP₀, r₀, hr₀⟩ := h₁.2 _ hQ j q' rfl hi
  exact ⟨P₀, hP₀, r₀ ++ r, by rw [hr₀, List.append_assoc]⟩

theorem Follows.grown {s s' : State} (h : Follows s s') : Grown s s' := ⟨h.1, h.2.1⟩

theorem Follows.trans {s s₁ s₂ : State} (h₁ : Follows s s₁) (h₂ : Follows s₁ s₂) :
    Follows s s₂ :=
  have h := h₁.grown.trans h₂.grown
  ⟨h.1, h.2, h₁.2.2.trans h₂.2.2⟩

/-! ## The simulation -/

/-- A copy frame and a state of sharing that agree on every binding. -/
abbrev AgreesAll (fr : Copy.Frame) (s : State) : Prop := Agrees (fr.map fun _ => true) fr s

/-- Every binding is live under the all-true mask. -/
theorem liveAt_all (x : Name) : ∀ l : List (Name × Value),
    Moving.LiveAt x (l.map fun _ => true) (l.map Prod.fst)
  | [] => trivial
  | (y, _) :: l => by
    simp only [List.map_cons, Moving.LiveAt]
    split
    · trivial
    · exact liveAt_all x l

/-- Both models read a variable of frames that agree on every binding alike. -/
theorem AgreesAll.read {fr : Copy.Frame} {s : State} (h : AgreesAll fr s) (x : Name) (p : Path) :
    Copy.read fr x p = Sharing.read s x p :=
  Agrees.read h (liveAt_all x fr) p

/-- What a frame of copies reads is safe. -/
theorem AgreesAll.read_safe {fr : Copy.Frame} {s : State} (h : AgreesAll fr s) {x : Name}
    {p : Path} {v : Value} (hv : Copy.read fr x p = .ok v) : v.Safe := by
  unfold Copy.read at hv
  split at hv
  · rename_i w hw
    exact Value.Safe.get (h.safe (x, w) (mem_of_lookup hw)) hv
  · cases hv

/-- A state of each model that agree: frames that agree on every binding, every binding of
sharing shared, in one world, whose cells hold safe values. -/
def AgreesIn (fr : Copy.State) (s : State × World) : Prop :=
  AgreesAll fr.1 s.1 ∧ AllShared s.1 ∧ fr.2 = s.2 ∧ fr.2.All Value.Safe

/-- What the two runs from a frame and the state `s` that agrees with it relate: the same
value, which `G` holds of, or the same raise, jump, panic or performance of a safe value, each
with a frame and a state that agree, the state following from `s`; and a performance resumed
with the same safe value in both, in one world whose cells hold safe values. -/
def Corr.relation (G : α → Prop) (s : State) :
    Outcome.Relation Copy.State (State × World) α α where
  done a fr a' s' := a = a' ∧ G a ∧ AgreesIn fr s' ∧ Follows s s'.1
  raised e fr e' s' := e = e' ∧ e.Safe ∧ AgreesIn fr s' ∧ Follows s s'.1
  jumped j fr j' s' := j = j' ∧ j.Safe ∧ AgreesIn fr s' ∧ Follows s s'.1
  panicked k fr k' s' := k = k' ∧ AgreesIn fr s' ∧ Follows s s'.1
  performed op v fr op' v' s' := op = op' ∧ v = v' ∧ v.Safe ∧ AgreesIn fr s' ∧ Follows s s'.1
  resume _ w x w' x' := w = w' ∧ w.Safe ∧ x = x' ∧ x.All Value.Safe

/-- The outcomes of the two runs from a frame and the state `s` that agrees with it
correspond. -/
def Corr (G : α → Prop) (s : State) :
    Outcome Copy.State α → Outcome (State × World) α → Prop :=
  Outcome.Rel (Corr.relation G s)

/-- A step after a value leaves a raise, a jump, a panic and a performance as they are. -/
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

/-- What relates outcomes from a state that follows from `s` relates them from `s`. -/
theorem Corr.sub {G : α → Prop} {s s₁ : State} (h : Follows s s₁) :
    (Corr.relation G s₁).Sub (Corr.relation G s) :=
  ⟨fun _ _ _ _ hc => ⟨hc.1, hc.2.1, hc.2.2.1, h.trans hc.2.2.2⟩,
    fun _ _ _ _ hc => ⟨hc.1, hc.2.1, hc.2.2.1, h.trans hc.2.2.2⟩,
    fun _ _ _ _ hc => ⟨hc.1, hc.2.1, hc.2.2.1, h.trans hc.2.2.2⟩,
    fun _ _ _ _ hc => ⟨hc.1, hc.2.1, h.trans hc.2.2⟩,
    fun _ _ _ _ _ _ hc => ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, h.trans hc.2.2.2.2⟩,
    fun _ _ _ _ _ hc => hc⟩

theorem Corr.follow {G : α → Prop} {s s₁ : State} (h : Follows s s₁)
    {o : Outcome Copy.State α} {o' : Outcome (State × World) α} (hc : Corr G s₁ o o') :
    Corr G s o o' :=
  Outcome.Rel.mono hc (Corr.sub h)

/-- The seven ways two corresponding outcomes can be. -/
theorem Corr.cases {G : α → Prop} {s : State} {o : Outcome Copy.State α}
    {o' : Outcome (State × World) α} (h : Corr G s o o') :
    (∃ a fr s', o = .done a fr ∧ o' = .done a s' ∧ G a ∧ AgreesIn fr s' ∧ Follows s s'.1) ∨
      (∃ e fr s', o = .raised e fr ∧ o' = .raised e s' ∧ e.Safe ∧ AgreesIn fr s' ∧
        Follows s s'.1) ∨
      (∃ j fr s', o = .jumped j fr ∧ o' = .jumped j s' ∧ j.Safe ∧ AgreesIn fr s' ∧
        Follows s s'.1) ∨
      (∃ k fr s', o = .panicked k fr ∧ o' = .panicked k s' ∧ AgreesIn fr s' ∧ Follows s s'.1) ∨
      (∃ op v fr s' k k', o = .performed op v fr k ∧ o' = .performed op v s' k' ∧ v.Safe ∧
        AgreesIn fr s' ∧ Follows s s'.1 ∧
          ∀ w x, w.Safe → x.All Value.Safe → Corr G s (k w x) (k' w x)) ∨
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
  · exact ⟨rfl, hs, Follows.refl s.1⟩
  · trivial

namespace Sim

theorem pure {G : α → Prop} {a : α} (h : G a) : Sim G (pure a) (pure a) :=
  fun _ s hs => ⟨rfl, h, hs, Follows.refl s.1⟩

theorem fail {G : α → Prop} (f : Fault) : Sim G (Eval.fail f) (Eval.fail f) :=
  fun _ _ hs => Corr.fault hs f

theorem outOfFuel {G : α → Prop} : Sim G Eval.outOfFuel Eval.outOfFuel :=
  fun _ _ _ => trivial

theorem throw {G : α → Prop} {e : Value} (he : e.Safe) : Sim G (Eval.throw e) (Eval.throw e) :=
  fun _ s hs => ⟨rfl, he, hs, Follows.refl s.1⟩

theorem jump {G : α → Prop} {j : Jump} (hj : j.Safe) : Sim G (Eval.jump j) (Eval.jump j) :=
  fun _ s hs => ⟨rfl, hj, hs, Follows.refl s.1⟩

theorem ofExcept {G : α → Prop} (x : Except Fault α) (h : ∀ a, x = .ok a → G a) :
    Sim G (Eval.ofExcept x) (Eval.ofExcept x) := by
  intro fr s hs
  cases x with
  | error f => exact Corr.fault hs f
  | ok a => exact ⟨rfl, h a rfl, hs, Follows.refl s.1⟩

/-- Reading and writing the world alike: both models are in one world. -/
theorem world (shared : Name → Bool) (f : World → Except Fault (Value × World))
    (h : ∀ x v x', x.All Value.Safe → f x = .ok (v, x') → v.Safe ∧ x'.All Value.Safe) :
    Sim Value.Safe (Eval.world Copy.memory f) (Eval.world (memory shared) f) := by
  rintro ⟨fr, x⟩ ⟨s, y⟩ ⟨hag, hsh, hx, hsafe⟩
  cases hx
  cases hf : f x with
  | ok p =>
    rw [show Eval.world Copy.memory f (fr, x) = .done p.1 (fr, p.2) from Eval.world_ok hf,
      show Eval.world (memory shared) f (s, x) = .done p.1 (s, p.2) from Eval.world_ok hf]
    obtain ⟨hv, hx'⟩ := h x p.1 p.2 hsafe hf
    exact ⟨rfl, hv, ⟨hag, hsh, rfl, hx'⟩, Follows.refl s⟩
  | error e =>
    rw [show Eval.world Copy.memory f (fr, x) = .fault e (fr, x) from Eval.world_error hf,
      show Eval.world (memory shared) f (s, x) = .fault e (s, x) from Eval.world_error hf]
    exact Corr.fault ⟨hag, hsh, rfl, hsafe⟩ e

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
  | ok a => exact ⟨rfl, hG a hf, hs, Follows.refl s.1⟩

theorem bind {G : α → Prop} {H : β → Prop} {m : Eval Copy.State α} {m' : Eval (State × World) α}
    {f : α → Eval Copy.State β} {f' : α → Eval (State × World) β} (hm : Sim G m m')
    (hf : ∀ a, G a → Sim H (f a) (f' a)) : Sim H (m >>= f) (m' >>= f') := by
  intro fr s hs
  show Corr H s.1 ((m fr).bind fun a fr' => f a fr') ((m' s).bind fun a s' => f' a s')
  refine Outcome.Rel.bind (hm fr s hs) (Corr.escapes s.1) ?_
  rintro a fr₁ a' s₁ ⟨rfl, hG, hag, hev⟩
  exact (hf a hG fr₁ s₁ hag).follow hev

theorem ite {G : α → Prop} (b : Bool) {m₁ m₂ : Eval Copy.State α}
    {m₁' m₂' : Eval (State × World) α} (h₁ : Sim G m₁ m₁') (h₂ : Sim G m₂ m₂') :
    Sim G (if b then m₁ else m₂) (if b then m₁' else m₂') := by
  cases b
  · exact h₂
  · exact h₁

theorem handle {G : α → Prop} {m : Eval Copy.State α} {m' : Eval (State × World) α}
    {h : Value → Eval Copy.State α} {h' : Value → Eval (State × World) α} (hm : Sim G m m')
    (hh : ∀ e, e.Safe → Sim G (h e) (h' e)) : Sim G (Eval.handle m h) (Eval.handle m' h') := by
  intro fr s hs
  show Corr G s.1 ((m fr).handle fun e fr' => h e fr') ((m' s).handle fun e s' => h' e s')
  refine Outcome.Rel.handle (hm fr s hs) (fun _ _ _ _ hc => hc) (fun _ _ _ _ hc => hc)
    (fun _ _ _ _ hc => hc) (Corr.escapes s.1).performs ?_
  rintro e fr₁ e' s₁ ⟨rfl, he, hag, hev⟩
  exact (hh e he fr₁ s₁ hag).follow hev

/-- A turn of a loop's body: a `break` or a `continue` ends it as a step does
(expressions.break-and-continue). -/
theorem turn {m : Eval Copy.State Value} {m' : Eval (State × World) Value}
    (hm : Sim Value.Safe m m') : Sim (fun _ => True) (Eval.turn m) (Eval.turn m') := by
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

theorem declare (D : Decls) (R : Name) {written : List (Name × Value)}
    (hw : ∀ fv ∈ written, fv.2.Safe) :
    Sim Value.Safe (Eval.declare D R written) (Eval.declare D R written) := by
  unfold Eval.declare
  split
  · split
    · rename_i fields hfields
      refine pure (.record fun fv hfv => ?_)
      obtain ⟨⟨f, τ⟩, _, ha⟩ := InPlace.Sim.mapM_mem hfields fv hfv
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

/-- Evaluating a call's arguments gives safe values and the places the arguments name. -/
theorem args (h : SimRun run run') : ∀ as : List Arg, ArgsSafe as →
    Sim (fun passed => InPlace.Sim.PassedSafe passed ∧ InPlace.Sim.ArgsResolved as passed)
      (Eval.args run as) (Eval.args run' as)
  | [], _ => pure ⟨by simp [InPlace.Sim.PassedSafe], trivial⟩
  | .value e :: as, has =>
    bind (h e (has.1 e List.mem_cons_self)) fun v hv =>
      bind (args h as has.tail) fun ps hps =>
        pure ⟨fun q hq u hu => by
          rcases List.mem_cons.1 hq with rfl | hq
          · rw [InPlace.Sim.value?_ofArg] at hu
            cases hu
            exact hv
          · exact hps.1 q hq u hu, InPlace.Sim.resolved_ofArg e v hps.2⟩
  | .inout ⟨x, projections⟩ :: as, has =>
    bind (path h projections (has.2 x projections List.mem_cons_self)) fun _ hp =>
      bind (args h as has.tail) fun ps hps =>
        pure ⟨fun q hq u hu => by
          rcases List.mem_cons.1 hq with rfl | hq
          · cases hu
          · exact hps.1 q hq u hu, rfl, hp, hps.2⟩

end Runs

end Sim

end Stilt.Sharing
