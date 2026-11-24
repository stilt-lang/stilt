import Stilt.Held.Eval
import Stilt.Held.PutBack

/-!
# No code but a `when` reaches the cell it holds

`eval_keepsHeld`: evaluating any expression, with any fuel, from a state whose world holds
a cell, keeps the cell held in every state the outcome carries, and in every state of every
rest of a performance resumed in a world that holds it; and every cell stays in its place.
By induction on the fuel, case by case on the expression. A `when` panics with `deadlock`
before it holds a cell already held (shared.when-on-value-already-held), so the cells it
holds are others, and putting their values back leaves a held cell held; a `with` lets go
only of cells held since it started (shared.when). So a cell held by a `when` is neither
read nor written while it is held but through the names of that `when`, which put back
exactly their values when it ends (`release_puts_back`).
-/

namespace Stilt

namespace Eval.KeepsHeld

variable {τ : Type} (F : Frames τ) {k : Ty × Nat}

/-- A `when` keeps every cell held that was held when it started: it holds none of them,
so putting values back leaves them. -/
theorem held {block : Eval (τ × World) Value} (hb : Eval.KeepsHeld k block) (names : List Name)
    (handles : List Value) : Eval.KeepsHeld k (Eval.held F.withWorld block names handles) := by
  refine bind (ofExcept _) fun cells => ?_
  rintro ⟨fr, w⟩ hk
  show ((((Eval.world F.withWorld (fun w => (World.take cells w).map fun p => (Value.list p.1, p.2))
    (fr, w)).bind fun a s => Eval.asList a s).bind fun vs s =>
      (if names.length = vs.length then
        Eval.withVars F.withWorld (names.zip vs) (Eval.release F.withWorld (names.zip cells) block)
      else Eval.fail .stuck) s)).KeepsHeld k w
  cases ht : World.take cells w with
  | error e =>
    rw [Eval.world_error (by rw [ht]; rfl)]
    cases e
    · exact ⟨World.Extends.refl w, hk⟩
    · trivial
  | ok p =>
    obtain ⟨vs, w'⟩ := p
    rw [Eval.world_ok (by rw [ht]; rfl)]
    obtain ⟨he, hk'⟩ := World.take_held ht
    obtain ⟨hnot, hw'⟩ := hk' k hk
    refine Outcome.KeepsHeld.base he ?_
    show ((if names.length = vs.length then
        Eval.withVars F.withWorld (names.zip vs) (Eval.release F.withWorld (names.zip cells) block)
      else Eval.fail .stuck) (fr, w')).KeepsHeld k w'
    split
    · refine withVars F (fun s hs => Outcome.KeepsHeld.release F _ ?_ (hb s hs)) _ (fr, w') hw'
      intro x c hm he'
      exact hnot (he' ▸ (List.of_mem_zip hm).2)
    · exact fail _ (fr, w') hw'

end Eval.KeepsHeld

open Eval.KeepsHeld in
/-- **No code but a `when` reaches the cell it holds**, with any fuel: from a state whose
world holds a cell, every state the evaluation reaches holds it, in every rest too. -/
theorem eval_keepsHeld (D : Decls) {τ : Type} (F : Frames τ) (k : Ty × Nat) :
    ∀ n e, Eval.KeepsHeld k (eval D F.withWorld n e)
  | 0, _ => fun _ _ => trivial
  | n + 1, e => by
    have ih := eval_keepsHeld D F k n
    cases e
    case var x => exact inspect _
    case move x => exact inspect _
    case int => exact pure _
    case bool => exact pure _
    case unit => exact pure _
    case record R fs => exact bind (fields ih fs) fun _ => declare D R _
    case variant T C es => exact bind (list ih es) fun _ => pure _
    case list τ es => exact bind (list ih es) fun _ => pure _
    case op o es => exact bind (list ih es) fun vs => run F o vs
    case view es => exact bind (list ih es) fun _ => ofExcept _
    case field e f => exact bind (ih e) fun _ => ofExcept _
    case index e i => exact bind (ih e) fun _ => bind (bind (ih i) asInt) fun _ => ofExcept _
    case fnRef => exact pure _
    case method t m ty => exact method D t m ty
    case closure => exact bind (inspect _) fun _ => pure _
    case call callee as _ =>
      exact bind (ih callee) fun f => bind (args ih as) fun ps => callAs F ih D false f ps
    case letIn x ty init body => exact bind (ih init) fun v => withInit F x init v (ih body)
    case varIn x ty init body => exact bind (ih init) fun v => withInit F x init v (ih body)
    case assign p value =>
      obtain ⟨x, ps⟩ := p
      exact assign F ih x ps value
    case seq a b => exact bind (ih a) fun _ => ih b
    case «if» c ty a b => exact bind (bind (ih c) asBool) fun v => ite v (ih a) (ih b)
    case «match» e ty arms => exact bind (ih e) fun v => select F ih arms v
    case «for» x ty e body => exact loop F ih x e body
    case raise e => exact bind (ih e) fun v => throw v
    case «try» e => exact ih e
    case tryCatch e E x h ty => exact handle (ih e) fun err => withVar F x err (ih h)
    case «while» c body =>
      have hloop := ih (.while c body)
      exact bind (bind (ih c) asBool) fun v =>
        ite v (bind (turn (ih body)) fun g => ite g hloop (pure _)) (pure _)
    case «loop» body =>
      have hloop := ih (.loop body)
      exact bind (turn (ih body)) fun g => ite g hloop (pure _)
    case «break» => exact jump _
    case «continue» => exact jump _
    case «return» e => exact bind (ih e) fun v => jump _
    case perform op e => exact bind (ih e) fun v => perform F op v
    case withH E c h b =>
      exact bind (ih h) fun hv => withH F E c hv (fun f v => callAs F ih D c f [.value v]) (ih b)
    case held ns hs b => exact bind (list ih hs) fun vs => held F (ih b) _ vs

/-- A `when` that holds cells names each by one handle (shared.when-on-value-already-held). -/
theorem World.take_nodup {hs : List (Ty × Nat)} {w w' : World} {vs : List Value}
    (h : World.take hs w = .ok (vs, w')) : hs.Nodup := by
  unfold World.take at h
  split at h
  · split at h
    · rename_i hok
      exact hok.1
    · cases h
  · cases h

/-- Every evaluation of a program's reference run keeps each held cell held, and each
`when` puts back its names' values (shared.when). -/
theorem Program.keepsHeld (p : Program) :
    (∀ (n : Nat) (e : Expr) (s : Copy.State) (k : Ty × Nat), s.2.Held k →
      (eval p.decls Copy.memory n e s).KeepsHeld k s.2) ∧
    ∀ (cells : List (Name × Ty × Nat)) (o : Outcome Copy.State Value) (s s' : Copy.State),
      (cells.map Prod.snd).Nodup → o.ending? = some s →
      (∀ x h, (x, h) ∈ cells → ∃ v, Copy.read s.1 x [] = .ok v) →
      (o.release Copy.memory cells).ending? = some s' → Memory.PutBack Copy.frames false cells s s' :=
  ⟨fun n e s k hk => eval_keepsHeld p.decls Copy.frames k n e s hk,
    fun _ _ _ _ hn hs hr hs' => Outcome.release_puts_back Copy.frames hn hs hr hs'⟩

end Stilt
