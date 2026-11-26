import Stilt.Panics.Values
import Stilt.Panics.Kept
import Stilt.Panics.Reaches

/-!
# Steps without panics

`Eval.PanicFree lim G P m`: run on a panic-free state, whose frame and whose world's cells
hold panic-free values, and whose variables of `G` hold integers other than zero, `m`
ends with a value that `P` holds of, a panic-free raise or jump, each in a panic-free
state; with a panic of the kind `overflow` or `deadlock`, which `without panic` doesn't
rule out (effects.without-overflow and shared.when-on-value-already-held); with a
performance of a panic-free value, from a panic-free state, whose rest ends so again
once resumed with a panic-free value in a world whose cells hold panic-free values;
or out of fuel, or stuck. Each combinator of `Stilt.Semantics` keeps it in copy-in, copy-out,
whatever its order of write-back, and a step that keeps the variables outside
`W` keeps the facts about `G` but those of `W` (`Frame.Meets.keep`) at every
value it reaches (`Outcome.Reaches`).
-/

namespace Stilt

/-- A jump whose `return` carries a panic-free value. -/
def Jump.PanicFree (lim : Limited) : Jump → Prop
  | .ret v => v.PanicFree lim
  | _ => True

/-- How an evaluation that keeps to panic-free code may end. A performance
passes a panic-free argument, and its rest, resumed with a panic-free value in
a world whose cells hold panic-free values, ends so again: performing an operation adds no `panic` of its own, since it is
a call through a stored function value, the handler's clause, whose body is
code of the function that wrote it (handlers.implicit-effects-and-capabilities). -/
def Outcome.PanicFree (lim : Limited) {α : Type} (P : α → Prop) : Outcome Copy.State α → Prop
  | .done a s => P a ∧ State.PanicFree lim s
  | .raised e s => e.PanicFree lim ∧ State.PanicFree lim s
  | .jumped j s => j.PanicFree lim ∧ State.PanicFree lim s
  | .panicked k s => ((k = .overflow ∧ lim.overflows = true) ∨ k = .deadlock) ∧ State.PanicFree lim s
  | .performed _ v s k =>
    v.PanicFree lim ∧ State.PanicFree lim s ∧
      ∀ w x, w.PanicFree lim → x.All (Value.PanicFree lim) → Outcome.PanicFree lim P (k w x)
  | .outOfFuel | .stuck => True

/-- From a state whose frame is panic-free and meets the facts `G`, `m` ends as
panic-free code may. -/
def Eval.PanicFree (lim : Limited) {α : Type} (G : List Known) (P : α → Prop) (m : Eval Copy.State α) : Prop :=
  ∀ s : Copy.State, State.PanicFree lim s → Frame.Meets G s.1 → Outcome.PanicFree lim P (m s)

namespace Outcome.PanicFree

variable {lim : Limited} {α β : Type} {P : α → Prop} {Q : β → Prop}

/-- What follows each value a panic-free outcome reaches, when it is panic-free
from there, keeps it panic-free. -/
theorem bind {f : α → Copy.State → Outcome Copy.State β} :
    ∀ {o : Outcome Copy.State α}, o.PanicFree lim P →
      (∀ a s, o.Reaches a s → P a → State.PanicFree lim s → (f a s).PanicFree lim Q) →
        (o.bind f).PanicFree lim Q
  | .done a s, h, hf => hf a s .done h.1 h.2
  | .performed _ _ _ _, ⟨hv, hs, hk⟩, hf =>
    ⟨hv, hs, fun w x hw hx => bind (hk w x hw hx) fun a s hr => hf a s (.rest w x hr)⟩
  | .raised _ _, h, _ | .jumped _ _, h, _ | .panicked _ _, h, _ | .outOfFuel, h, _ | .stuck, h, _ => h

/-- A raise handed to a panic-free handler, from a frame that keeps what the
outcome keeps from `s₀`. -/
theorem handle {W L : List Name} {R : α → Prop} {s₀ : Copy.Frame}
    {h : Value → Copy.State → Outcome Copy.State α}
    (hh : ∀ e s, e.PanicFree lim → State.PanicFree lim s → Frame.Keeps W L s₀ s.1 → (h e s).PanicFree lim P) :
    ∀ {o : Outcome Copy.State α}, o.PanicFree lim P → o.Keeps W L R s₀ → (o.handle h).PanicFree lim P
  | .raised e s, h', k => hh e s h'.1 h'.2 k
  | .performed _ _ _ _, ⟨hv, hs, hk⟩, ⟨_, k⟩ =>
    ⟨hv, hs, fun w x hw hx => handle hh (hk w x hw hx) (k w x)⟩
  | .done _ _, h', _ | .jumped _ _, h', _ | .panicked _ _, h', _ | .outOfFuel, h', _
  | .stuck, h', _ => h'

theorem map {Q : α → Prop} (hPQ : ∀ a, P a → Q a) :
    ∀ {o : Outcome Copy.State α}, o.PanicFree lim P → o.PanicFree lim Q
  | .done _ _, h => ⟨hPQ _ h.1, h.2⟩
  | .performed _ _ _ _, ⟨hv, hs, hk⟩ => ⟨hv, hs, fun w x hw hx => map hPQ (hk w x hw hx)⟩
  | .raised _ _, h | .jumped _ _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

/-- A property of every value an outcome reaches. -/
theorem withReached {R : α → Prop} :
    ∀ {o : Outcome Copy.State α}, o.PanicFree lim P → (∀ a s, o.Reaches a s → R a) →
      o.PanicFree lim (fun a => P a ∧ R a)
  | .done _ _, h, hR => ⟨⟨h.1, hR _ _ .done⟩, h.2⟩
  | .performed _ _ _ _, ⟨hv, hs, hk⟩, hR =>
    ⟨hv, hs, fun w x hw hx => withReached (hk w x hw hx) fun a s hr => hR a s (.rest w x hr)⟩
  | .raised _ _, h, _ | .jumped _ _, h, _ | .panicked _ _, h, _ | .outOfFuel, h, _ | .stuck, h, _ => h

theorem both {R : α → Prop} :
    ∀ {o : Outcome Copy.State α}, o.PanicFree lim P → o.PanicFree lim R → o.PanicFree lim (fun a => P a ∧ R a)
  | .done _ _, h, h' => ⟨⟨h.1, h'.1⟩, h.2⟩
  | .performed _ _ _ _, ⟨hv, hs, hk⟩, ⟨_, _, hk'⟩ =>
    ⟨hv, hs, fun w x hw hx => both (hk w x hw hx) (hk' w x hw hx)⟩
  | .raised _ _, h, _ | .jumped _ _, h, _ | .panicked _ _, h, _ | .outOfFuel, h, _ | .stuck, h, _ => h

theorem turn {R : Value → Prop} :
    ∀ {o : Outcome Copy.State Value}, o.PanicFree lim R → o.turn.PanicFree lim (fun _ => True)
  | .done _ _, h => ⟨trivial, h.2⟩
  | .jumped .brk _, h => ⟨trivial, h.2⟩
  | .jumped .cont _, h => ⟨trivial, h.2⟩
  | .jumped (.ret _) _, h => h
  | .performed _ _ _ _, ⟨hv, hs, hk⟩ => ⟨hv, hs, fun w x hw hx => turn (hk w x hw hx)⟩
  | .raised _ _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

/-- A scope's end, which drops its binding from every frame. -/
theorem unbind (w : WriteBack) :
    ∀ {o : Outcome Copy.State α}, o.PanicFree lim P → (o.unbind (Copy.memoryWith w)).PanicFree lim P
  | .done _ _, h => ⟨h.1, h.2.1.tail, h.2.2⟩
  | .raised _ _, h => ⟨h.1, h.2.1.tail, h.2.2⟩
  | .jumped _ _, h => ⟨h.1, h.2.1.tail, h.2.2⟩
  | .panicked _ _, h => ⟨h.1, h.2.1.tail, h.2.2⟩
  | .performed _ _ _ _, ⟨hv, hs, hk⟩ =>
    ⟨hv, ⟨hs.1.tail, hs.2⟩, fun w' x hw hx => unbind w (hk w' x hw hx)⟩
  | .outOfFuel, h | .stuck, h => h

/-- Letting cells go changes no frame and no cell's value (shared.when). -/
theorem letGo (w : WriteBack) (before : World) :
    ∀ {o : Outcome Copy.State α}, o.PanicFree lim P → (o.letGo (Copy.memoryWith w) before).PanicFree lim P
  | .done _ (_, _), h | .raised _ (_, _), h | .jumped _ (_, _), h | .panicked _ (_, _), h =>
    ⟨h.1, h.2.1, h.2.2.letGo before⟩
  | .performed _ _ _ _, ⟨hv, hs, hk⟩ =>
    ⟨hv, hs, fun w' x hw hx => letGo w before (hk w' x hw hx)⟩
  | .outOfFuel, h | .stuck, h => h

end Outcome.PanicFree

namespace Eval.PanicFree

variable {lim : Limited} {α β : Type} {P : α → Prop} {Q : β → Prop}

theorem fault {γ : Type} {f : Fault} (hf : Calm (Except.error f : Except Fault γ) lim.overflows) {s : Copy.State}
    (hs : State.PanicFree lim s) : Outcome.PanicFree lim P (Outcome.fault f s) := by
  cases f with
  | panic k => exact ⟨.inl (hf k rfl), hs⟩
  | stuck => trivial

variable {G : List Known} {L : List Name}

theorem weaken {G' : List Known} {m : Eval Copy.State α} (hm : Eval.PanicFree lim G' P m) (hG : G' ⊆ G) :
    Eval.PanicFree lim G P m := fun s hs hz => hm s hs (hz.mono hG)

theorem pure {a : α} (h : P a) : Eval.PanicFree lim G P (Pure.pure a) := fun _ hs _ => ⟨h, hs⟩

/-- A step, then `f` from each value `a` it reaches, in a frame that meets `H a`
whenever the step started from one that meets `G`. -/
theorem bindReached {H : α → List Known} {m : Eval Copy.State α} {f : α → Eval Copy.State β}
    (hm : Eval.PanicFree lim G P m)
    (hH : ∀ s a s', Frame.Meets G s.1 → (m s).Reaches a s' → Frame.Meets (H a) s'.1)
    (hf : ∀ a, P a → Eval.PanicFree lim (H a) Q (f a)) : Eval.PanicFree lim G Q (m >>= f) := fun s hs hz =>
  Outcome.PanicFree.bind (hm s hs hz) fun a s' hr ha hs' => hf a ha s' hs' (hH s a s' hz hr)

/-- A step `m` that keeps the variables outside `W`, then `f`, which may count on the
facts of `G` that read none of `W`. -/
theorem bind {W : List Name} {R : α → Prop} {m : Eval Copy.State α} {f : α → Eval Copy.State β}
    (hm : Eval.PanicFree lim G P m) (hk : Eval.Keeps W L R m)
    (hf : ∀ a, P a → Eval.PanicFree lim (withoutNames G W) Q (f a)) :
    Eval.PanicFree lim G Q (m >>= f) :=
  bindReached hm (fun s _ _ hz hr => hz.keep (hr.keeps (hk s)).2) hf

/-- A step `m` that keeps the variables outside `W` and the lengths of the lists
outside `L`, then `f`, which may count on the facts of `G` that read the value of
none of `W` and the length of none of `L`. -/
theorem bindLen {W : List Name} {R : α → Prop} {m : Eval Copy.State α} {f : α → Eval Copy.State β}
    (hm : Eval.PanicFree lim G P m) (hk : Eval.Keeps W L R m)
    (hf : ∀ a, P a → Eval.PanicFree lim (withoutWrites G W L) Q (f a)) :
    Eval.PanicFree lim G Q (m >>= f) :=
  bindReached hm (fun s _ _ hz hr => hz.keepLen (hr.keeps (hk s)).2) hf

/-- A step after which the facts `F a` hold at every value `a` it reaches, then `f`,
which may count on them. -/
theorem bindAfter {W : List Name} {F : α → List Known} {R : α → Prop} {m : Eval Copy.State α}
    {f : α → Eval Copy.State β} (hm : Eval.PanicFree lim G P m) (hk : Eval.Keeps W L R m)
    (hF : ∀ s a s', (m s).Reaches a s' → Frame.Meets (F a) s'.1)
    (hf : ∀ a, P a → Eval.PanicFree lim (withoutNames G W ++ F a) Q (f a)) :
    Eval.PanicFree lim G Q (m >>= f) :=
  bindReached hm (fun s a s' hz hr => (hz.keep (hr.keeps (hk s)).2).append (hF s a s' hr)) hf

/-- `bindAfter` for code whose continuation keeps the facts that read the value of none
of `W` and the length of none of `L`. -/
theorem bindAfterLen {W : List Name} {F : α → List Known} {R : α → Prop} {m : Eval Copy.State α}
    {f : α → Eval Copy.State β} (hm : Eval.PanicFree lim G P m) (hk : Eval.Keeps W L R m)
    (hF : ∀ s a s', (m s).Reaches a s' → Frame.Meets (F a) s'.1)
    (hf : ∀ a, P a → Eval.PanicFree lim (withoutWrites G W L ++ F a) Q (f a)) :
    Eval.PanicFree lim G Q (m >>= f) :=
  bindReached hm (fun s a s' hz hr => (hz.keepLen (hr.keeps (hk s)).2).append (hF s a s' hr)) hf

/-- A step whose values, at every value it reaches from a frame that meets `G`, meet `R`. -/
theorem withDone {R : α → Prop} {m : Eval Copy.State α} (hm : Eval.PanicFree lim G P m)
    (hR : ∀ s a s', Frame.Meets G s.1 → (m s).Reaches a s' → R a) :
    Eval.PanicFree lim G (fun a => P a ∧ R a) m := fun s hs hz =>
  (hm s hs hz).withReached fun a s' hr => hR s a s' hz hr

theorem stuck : Eval.PanicFree lim G P (Eval.fail .stuck : Eval Copy.State α) := fun _ _ _ => trivial

theorem outOfFuel : Eval.PanicFree lim G P (Eval.outOfFuel : Eval Copy.State α) := fun _ _ _ => trivial

theorem ofExcept {x : Except Fault α} (h : CalmTo P x) : Eval.PanicFree lim G P (Eval.ofExcept x) := by
  intro s hs _
  cases x with
  | ok a => exact ⟨h.2 a rfl, hs⟩
  | error f => exact fault h.1.weaken hs

theorem inspect {f : Copy.State → Except Fault α} (h : ∀ s : Copy.State, Frame.PanicFree lim s.1 → CalmTo P (f s)) :
    Eval.PanicFree lim G P (Eval.inspect f) := fun s hs hz => ofExcept (h s hs.1) s hs hz

theorem update {f : Copy.State → Except Fault Copy.State}
    (h : ∀ s : Copy.State, State.PanicFree lim s → CalmTo (State.PanicFree lim) (f s)) :
    Eval.PanicFree lim G (fun _ => True) (Eval.update f) := by
  intro s hs _
  have h1 := h s hs
  unfold Eval.update
  cases hf : f s with
  | ok s' => exact ⟨trivial, h1.2 s' hf⟩
  | error e => rw [hf] at h1; exact fault h1.1.weaken hs

theorem throw {e : Value} (he : e.PanicFree lim) : Eval.PanicFree lim G P (Eval.throw e) :=
  fun _ hs _ => ⟨he, hs⟩

theorem jump {j : Jump} (hj : j.PanicFree lim) : Eval.PanicFree lim G P (Eval.jump j) :=
  fun _ hs _ => ⟨hj, hs⟩

theorem handle {W : List Name} {R : α → Prop} {m : Eval Copy.State α} {h : Value → Eval Copy.State α}
    (hm : Eval.PanicFree lim G P m) (hk : Eval.Keeps W L R m)
    (hh : ∀ e, e.PanicFree lim → Eval.PanicFree lim (withoutNames G W) P (h e)) :
    Eval.PanicFree lim G P (Eval.handle m h) := fun s hs hz =>
  Outcome.PanicFree.handle (fun e s' he hs' k => hh e he s' hs' (hz.keep k)) (hm s hs hz) (hk s)

theorem turn {R : Value → Prop} {m : Eval Copy.State Value} (hm : Eval.PanicFree lim G R m) :
    Eval.PanicFree lim G (fun _ => True) (Eval.turn m) := fun s hs hz => (hm s hs hz).turn

theorem ite (b : Bool) {m₁ m₂ : Eval Copy.State α} (h₁ : Eval.PanicFree lim G P m₁)
    (h₂ : Eval.PanicFree lim G P m₂) : Eval.PanicFree lim G P (if b then m₁ else m₂) := by
  cases b
  · exact h₂
  · exact h₁

theorem map {Q : α → Prop} {m : Eval Copy.State α} (hp : Eval.PanicFree lim G P m) (h : ∀ a, P a → Q a) :
    Eval.PanicFree lim G Q m := fun s hs hz => (hp s hs hz).map h

/-- Two properties of one step's value. -/
theorem both {Q : α → Prop} {m : Eval Copy.State α} (hp : Eval.PanicFree lim G P m)
    (hq : Eval.PanicFree lim G Q m) : Eval.PanicFree lim G (fun a => P a ∧ Q a) m := fun s hs hz =>
  (hp s hs hz).both (hq s hs hz)

/-- The facts that read no variable a turn writes hold at every turn, and each turn
may count on what its element meets. -/
theorem forEach {W : List Name} {Q : Value → Prop} {body : Value → Eval Copy.State Bool}
    (hG : ∀ f ∈ G, (∀ x ∈ f.valReads, x ∉ W) ∧ ∀ x ∈ f.lenReads, x ∉ L)
    (hb : ∀ v, v.PanicFree lim → Q v → Eval.PanicFree lim G (fun _ => True) (body v))
    (hk : ∀ v, Eval.Keeps W L (fun _ => True) (body v)) :
    ∀ vs : List Value, (∀ v ∈ vs, v.PanicFree lim ∧ Q v) →
      Eval.PanicFree lim G (fun _ => True) (Eval.forEach body vs)
  | [], _ => pure trivial
  | v :: vs, h => by
    unfold Eval.forEach
    have hv := h v List.mem_cons_self
    refine bindLen (hb v hv.1 hv.2) (hk v) fun b _ => weaken ?_ fun f hf =>
      mem_withoutWrites.2 ⟨hf, hG f hf⟩
    cases b
    · exact pure trivial
    · exact forEach hG hb hk vs fun u hu => h u (List.mem_cons_of_mem _ hu)

section

variable (w : WriteBack)

/-- An operation in the world, which panics only as its value does, and only by overflow,
gives a value of `P` in the frame it started from, and a cell it makes holds one of its
panic-free operands. -/
theorem run {R : Value → Prop} {o : Op} {vs : List Value} (hc : Calm (o.apply vs) lim.overflows)
    (hvs : ∀ v ∈ vs, v.PanicFree lim) (hP : ∀ x v x', o.run vs x = .ok (v, x') → R v) :
    Eval.PanicFree lim G R (Eval.world (Copy.memoryWith w) (o.run vs)) := by
  rintro ⟨fr, x⟩ hs _
  cases hf : o.run vs x with
  | ok p =>
    rw [show Eval.world (Copy.memoryWith w) (o.run vs) (fr, x) = .done p.1 (fr, p.2) from
      Eval.world_ok hf]
    exact ⟨hP x p.1 p.2 hf, hs.1, hs.2.run hvs hf⟩
  | error e =>
    rw [show Eval.world (Copy.memoryWith w) (o.run vs) (fr, x) = .fault e (fr, x) from
      Eval.world_error hf]
    refine fault (γ := Value) (fun k hk => ?_) hs
    rcases Op.run_error hf with rfl | ha
    · cases hk
    · exact hc k (ha.trans (by rw [hk]))

theorem withVar {x : Name} {v : Value} {m : Eval Copy.State α} (hv : v.PanicFree lim)
    (hm : Eval.PanicFree lim (withoutNames G [x]) P m) :
    Eval.PanicFree lim G P (Eval.withVar (Copy.memoryWith w) x v m) := by
  intro s hs hz
  exact (hm ((Copy.memoryWith w).bind s x v) ⟨hs.1.cons (x := x) hv, hs.2⟩ (hz.bind x v)).unbind w

/-- A binding that, from every frame that meets `G`, makes the facts `F` hold. -/
theorem withVarFacts {x : Name} {v : Value} {F : List Known} {m : Eval Copy.State α} (hv : v.PanicFree lim)
    (hF : ∀ s : Copy.Frame, Frame.Meets G s → Frame.Meets F ((x, v) :: s))
    (hm : Eval.PanicFree lim (withoutNames G [x] ++ F) P m) :
    Eval.PanicFree lim G P (Eval.withVar (Copy.memoryWith w) x v m) := by
  intro s hs hz
  exact (hm ((Copy.memoryWith w).bind s x v) ⟨hs.1.cons (x := x) hv, hs.2⟩ ((hz.bind x v).append (hF s.1 hz))).unbind w

theorem withInit {x : Name} {init : Expr} {v : Value} {m : Eval Copy.State α} (hv : v.PanicFree lim)
    (hm : Eval.PanicFree lim (withoutNames G [x]) P m) :
    Eval.PanicFree lim G P (Eval.withInit (Copy.memoryWith w) x init v m) := by
  have : Eval.withInit (Copy.memoryWith w) x init v m = Eval.withVar (Copy.memoryWith w) x v m := by
    funext s
    unfold Eval.withInit Eval.withVar Memory.bindInit
    cases init <;> rfl
  rw [this]
  exact withVar w hv hm

theorem withVars {m : Eval Copy.State α} :
    ∀ {H : List Known} (bs : List (Name × Value)), (∀ xv ∈ bs, xv.2.PanicFree lim) →
      Eval.PanicFree lim (withoutNames H (bs.map Prod.fst)) P m →
      Eval.PanicFree lim H P (Eval.withVars (Copy.memoryWith w) bs m)
  | _, [], _, hm => weaken hm fun x hx => (mem_withoutNames.1 hx).1
  | H, (x, v) :: bs, h, hm =>
    withVar w (h (x, v) List.mem_cons_self)
      (withVars (H := withoutNames H [x]) bs (fun xv hx => h xv (List.mem_cons_of_mem _ hx))
        (weaken hm fun f hf => by
          obtain ⟨hf, hn⟩ := mem_withoutNames.1 hf
          simp only [List.map_cons, List.mem_cons, not_or] at hn
          exact mem_withoutNames.2 ⟨mem_withoutNames.2 ⟨hf, fun y hy => by simpa using (hn y hy).1⟩,
            fun y hy => (hn y hy).2⟩))

end

end Eval.PanicFree

end Stilt
