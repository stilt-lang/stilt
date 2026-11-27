import Stilt.Sharing.Bind
import Stilt.Selection

/-!
# Scopes with sharing

A body run with one more binding, which ends however the body ends (expressions.scope), runs
alike with copies and with sharing: a `catch`'s, a `for`'s and an arm's binders, each with a new
home, and a `let`'s or a `var`'s, which shares the place its initializer names
(modes.copies). Reading a variable reads alike.
-/

namespace Stilt.Sharing

open InPlace (Ref)

variable {α : Type}

/-- A frame of copies and a state of sharing that agree on every binding keep agreeing once
each ends its newest binding. -/
theorem AgreesAll.tail {fr : Copy.Frame} {s : State} (h : AgreesAll fr s) :
    AgreesAll fr.tail ⟨s.env.tail, s.store⟩ := by
  match fr, s, h with
  | [], ⟨[], st⟩, h => exact ⟨rfl, rfl, trivial, by simp, .nil, by simp⟩
  | (x, v) :: fr, s, h => exact Agrees.unbind (b := true) (x := x) (v := v) h
  | [], ⟨_ :: _, _⟩, h => exact absurd h.align (by simp)

/-- The body `m`, run from a state with one more binding than `s` that follows from it, ends
alike in both models once each ends that binding. -/
theorem Corr.scoped {G : α → Prop} (shared : Name → Bool) {x : Name} {v : Value}
    {m : Eval Copy.State α} {m' : Eval (State × World) α} (hm : Sim G m m') {fr : Copy.State}
    {s : State × World} {s₀ : State} (h₀ : AgreesIn ((x, v) :: fr.1, fr.2) (s₀, s.2))
    (hf : Grown s.1 s₀) {a : Name × Entry} (henv : s₀.env = a :: s.1.env) :
    Corr G s.1 ((m ((x, v) :: fr.1, fr.2)).unbind Copy.memory)
      ((m' (s₀, s.2)).unbind (memory shared)) := by
  have key : ∀ fr₁ s₁, AgreesIn fr₁ s₁ → Follows s₀ s₁.1 →
      AgreesIn (Copy.memory.unbind fr₁) ((memory shared).unbind s₁) ∧
        Follows s.1 ((memory shared).unbind s₁).1 := fun fr₁ s₁ hag hev =>
    ⟨⟨hag.1.tail, hag.2.1.tail _, hag.2.2⟩, Follows.unbind hf henv hev⟩
  exact Outcome.Rel.unbind Copy.memory (memory shared) (hm _ _ h₀)
    (fun _ _ _ _ ⟨h₁, h₂, hag, hev⟩ => ⟨h₁, h₂, key _ _ hag hev⟩)
    (fun _ _ _ _ ⟨h₁, h₂, hag, hev⟩ => ⟨h₁, h₂, key _ _ hag hev⟩)
    (fun _ _ _ _ ⟨h₁, h₂, hag, hev⟩ => ⟨h₁, h₂, key _ _ hag hev⟩)
    (fun _ _ _ _ ⟨h₁, hag, hev⟩ => ⟨h₁, key _ _ hag hev⟩)
    (fun _ _ _ _ _ _ ⟨h₁, h₂, h₃, hag, hev⟩ => ⟨h₁, h₂, h₃, key _ _ hag hev⟩) fun _ _ _ _ _ h => h

namespace Sim

theorem withVar {G : α → Prop} (shared : Name → Bool) (x : Name) {v : Value} (hv : v.Safe)
    {m : Eval Copy.State α} {m' : Eval (State × World) α} (hm : Sim G m m') :
    Sim G (Eval.withVar Copy.memory x v m) (Eval.withVar (memory shared) x v m') :=
  fun _ s hs => Corr.scoped shared hm (s₀ := bindWith s.1 x v false false)
    ⟨hs.1.bindWith x hv false false, hs.2.1.cons rfl rfl rfl rfl, hs.2.2⟩
    (Grown.bindWith s.1 x v false false) rfl

theorem withVars {G : α → Prop} (shared : Name → Bool) {m : Eval Copy.State α}
    {m' : Eval (State × World) α} (hm : Sim G m m') :
    ∀ bindings : List (Name × Value), (∀ xv ∈ bindings, xv.2.Safe) →
      Sim G (Eval.withVars Copy.memory bindings m) (Eval.withVars (memory shared) bindings m')
  | [], _ => hm
  | (x, v) :: bindings, h =>
    withVar shared x (h (x, v) List.mem_cons_self)
      (withVars shared hm bindings fun xv hxv => h xv (List.mem_cons_of_mem _ hxv))

theorem read (shared : Name → Bool) (x : Name) :
    Sim Value.Safe (Eval.inspect fun fr => Copy.memory.read fr x [])
      (Eval.inspect fun s => (memory shared).read s x []) :=
  inspect fun _ _ hs => ⟨hs.1.read x [], fun _ ha => hs.1.read_safe ha⟩

section Runs

variable {run : Expr → Eval Copy.State Value} {run' : Expr → Eval (State × World) Value}

theorem select (shared : Name → Bool) (h : SimRun run run') {arms : List Arm}
    (harms : ∀ arm ∈ arms, arm.body.Safe ∧ ∀ g, arm.guard = some g → g.Safe) {v : Value}
    (hv : v.Safe) :
    Sim Value.Safe (Eval.select Copy.memory run arms v)
      (Eval.select (memory shared) run' arms v) := by
  refine Eval.select_rel (Sim Value.Safe) (fail _) (fun arm ha _ us hm _ => ?_)
    fun arm ha g hg us hu _ m m' hmm => ?_
  · exact withVars shared (h _ (harms arm ha).1) _ fun xv hxv =>
      arm.pattern.matchOn_parts Value.Safe.passesToParts hv hm xv.2 (List.of_mem_zip hxv).2
  · obtain ⟨q, -, hq⟩ := Pattern.mem_ways hu
    have hparts : ∀ xv ∈ arm.binders.zip us, xv.2.Safe := fun xv hxv =>
      q.matchOn_parts Value.Safe.passesToParts hv hq xv.2 (List.of_mem_zip hxv).2
    exact bind (withVars shared (bind (h g ((harms arm ha).2 g hg)) fun _ _ => asBool) _ hparts)
      fun b _ => ite b (withVars shared (h _ (harms arm ha).1) _ hparts) hmm

theorem loop (shared : Name → Bool) (h : SimRun run run') (x : Name) {e body : Expr}
    (he : e.Safe) (hb : body.Safe) :
    Sim Value.Safe (Eval.loop Copy.memory run x e body)
      (Eval.loop (memory shared) run' x e body) :=
  bind (bind (h e he) fun _ hv => asList hv) fun vs hvs =>
    bind (forEach (fun _ hv => withVar shared x hv (turn (h body hb))) vs hvs)
      fun _ _ => pure .unit

end Runs

end Sim

end Stilt.Sharing
