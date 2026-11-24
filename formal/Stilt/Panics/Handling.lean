import Stilt.Panics.Calls

/-!
# Handlers without panics

A `with` whose handler is a panic-free value, a record of closures with
panic-free bodies, handles a panic-free block's performances without a panic of
its own: each clause it calls is panic-free, on a panic-free argument, from the
frame the performance left, and resuming the rest of the block or ending the
`with` with the clause's value adds nothing (handlers.with, handlers.resuming
and handlers.implicit-effects-and-capabilities).
-/

namespace Stilt

/-- The clause of a panic-free handler is panic-free. -/
theorem Value.PanicFree.clause {handler c : Value} {op : Name} (hh : handler.PanicFree)
    (hc : handler.clause? op = some c) : c.PanicFree := by
  cases handler <;> simp only [Value.clause?, reduceCtorEq] at hc
  cases hh with
  | record hfs => exact hfs _ (mem_of_lookup hc)

namespace Outcome.PanicFree

variable {α : Type} {P : α → Prop} (w : WriteBack)

/-- A clause's outcome as the `with`'s, on a panic-free frame, in the world the clause
left. -/
theorem lift {s : Copy.State} (hs : Frame.PanicFree s.1) :
    ∀ {o : Outcome Copy.State α}, o.PanicFree P → (o.lift (Copy.memoryWith w) s).PanicFree P
  | .done _ _, h => ⟨h.1, hs, h.2.2⟩
  | .raised _ _, h => ⟨h.1, hs, h.2.2⟩
  | .jumped _ _, h => ⟨h.1, hs, h.2.2⟩
  | .panicked _ _, h => ⟨h.1, hs, h.2.2⟩
  | .performed _ _ _ _, ⟨hv, hs', hk⟩ => ⟨hv, ⟨hs, hs'.2⟩, fun u x hu hx => lift hs (hk u x hu hx)⟩
  | .outOfFuel, h | .stuck, h => h

/-- The body of a clause that takes control, each `resume` running a panic-free rest. -/
theorem runBody {resume : Value → World → Outcome Copy.State Value}
    (hr : ∀ u x, u.PanicFree → x.All Value.PanicFree → (resume u x).PanicFree Value.PanicFree) :
    ∀ {o : Outcome Copy.State Value}, o.PanicFree Value.PanicFree →
      (o.runBody (Copy.memoryWith w) resume).PanicFree Value.PanicFree
  | .performed op u s k, ⟨hu, hs, hk⟩ => by
    unfold Outcome.runBody
    split
    · exact bind (hr u _ hu hs.2) fun r s' _ hr' hs' => lift w hs'.1 (runBody hr (hk r _ hr' hs'.2))
    · exact ⟨hu, hs, fun u' x hu' hx => runBody hr (hk u' x hu' hx)⟩
  | .done _ _, h | .raised _ _, h | .jumped _ _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

/-- A `with` of a panic-free handler, whose clauses' calls on panic-free arguments
are panic-free, keeps a panic-free block's outcome panic-free. -/
theorem handleWith {effect : Name} {control : Bool} {handler : Value}
    {call : Value → Value → Copy.State → Outcome Copy.State Value} (hh : handler.PanicFree)
    (hcall : ∀ c v s, c.PanicFree → v.PanicFree → State.PanicFree s →
      (call c v s).PanicFree Value.PanicFree) :
    ∀ {o : Outcome Copy.State Value}, o.PanicFree Value.PanicFree →
      (o.handleWith (Copy.memoryWith w) effect control handler call).PanicFree Value.PanicFree
  | .performed op v s k, ⟨hv, hs, hk⟩ => by
    unfold Outcome.handleWith
    split
    · split
      · trivial
      · rename_i c hc
        have hcv := hcall c v s (hh.clause hc) hv hs
        split
        · exact runBody w (fun u x hu hx => handleWith hh hcall (hk u x hu hx)) hcv
        · exact bind hcv fun u _ _ hu hs' => handleWith hh hcall (hk u _ hu hs'.2)
    · exact ⟨hv, hs, fun u x hu hx => handleWith hh hcall (hk u x hu hx)⟩
  | .done _ _, h | .raised _ _, h | .jumped _ _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

end Outcome.PanicFree

end Stilt
