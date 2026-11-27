import Stilt.Quiet.Calls

/-!
# The world's cells, `when` and handlers keep the world's output and input

An operation other than a read or a write of the world leaves its output, standard error and
input as they were: `Shared.new` makes a cell, and the others leave the world alone. A
`when` takes, puts back and lets go of cells alone, and so does a `with` that lets go of the
cells its dropped rests hold. A handler's clause that keeps the world, resuming a rest that
keeps it, keeps it: each rest resumes in the world the clause leaves, with a value of the
type its operation gives, the only one the operation may give (`Decls.operation?`).
-/

namespace Stilt

variable {D : Decls} {α : Type} {Γ : Ctx} {η : REnv} {X : Exits}

/-- An operation that neither reads nor writes the world's output or input leaves them. -/
theorem Op.run_io {o : Op} (ho : o.io = false) {vs : List Value} {w w' : World} {v : Value}
    (h : o.run vs w = .ok (v, w')) : w'.io = w.io := by
  cases o
  case world k =>
    cases k with
    | sharedNew u =>
      simp only [Op.run, WorldOp.run] at h
      split at h <;> simp_all [World.io, World.push]
      obtain ⟨-, rfl⟩ := h
      exact ⟨rfl, rfl, rfl⟩
    | _ => exact absurd ho (by simp [Op.io, WorldOp.io])
  all_goals exact congrArg World.io (Op.run_world (fun _ h => Op.noConfusion h) h).1

/-- A step on the world that leaves its output, standard error and input keeps them. -/
theorem Outcome.KeepsIo.world {f : World → Except Fault (Value × World)}
    (h : ∀ x v x', f x = .ok (v, x') → x'.io = x.io) (γ : Copy.State) :
    (Eval.world Copy.memory f γ).KeepsIo D X γ.2.io := by
  obtain ⟨fr, x⟩ := γ
  cases hf : f x with
  | ok p =>
    obtain ⟨v, x'⟩ := p
    rw [show Eval.world Copy.memory f (fr, x) = .done v (fr, x') from Eval.world_ok hf]
    exact h x v x' hf
  | error e =>
    rw [show Eval.world Copy.memory f (fr, x) = .fault e (fr, x) from Eval.world_error hf]
    exact Outcome.KeepsIo.fault rfl

/-- Changing cells keeps the output, standard error and input. -/
theorem World.io_modify (w : World) (h : Ty × Nat) (f : Cell → Cell) : (w.modify h f).io = w.io :=
  rfl

theorem World.io_foldl_modify (f : Ty × Nat → Cell → Cell) :
    ∀ (hs : List (Ty × Nat)) (w : World),
      (hs.foldl (fun x h => x.modify h (f h)) w).io = w.io
  | [], _ => rfl
  | h :: hs, w => (World.io_foldl_modify f hs (w.modify h (f h))).trans (World.io_modify w h _)

/-- Taking cells keeps the output, standard error and input. -/
theorem World.take_io {hs : List (Ty × Nat)} {w w' : World} {vs : List Value}
    (h : World.take hs w = .ok (vs, w')) : w'.io = w.io := by
  unfold World.take at h
  split at h
  · split at h
    · cases h
      exact World.io_foldl_modify (fun _ c => { c with held := true }) hs w
    · cases h
  · cases h

/-- Putting values back changes the cells alone. -/
theorem Copy.putBack_io (held : Bool) :
    ∀ (cells : List (Name × Ty × Nat)) {s s' : Copy.State},
      Copy.memory.putBack held cells s = .ok s' → s'.2.io = s.2.io
  | [], _, _, h => by cases h; rfl
  | (x, c) :: rest, (fr, w), s', h => by
    simp only [Memory.putBack] at h
    cases hr : Copy.memory.read (fr, w) x [] with
    | error e => rw [hr] at h; cases h
    | ok v =>
      rw [hr] at h
      exact Copy.putBack_io held rest (s := (fr, w.put c v held)) h

theorem Outcome.KeepsIo.after {f : Copy.State → Except Fault Copy.State} {s : Copy.State}
    {o : Copy.State → Outcome Copy.State α} {c} (hc : s.2.io = c)
    (hf : ∀ s', f s = .ok s' → s'.2.io = s.2.io) (ho : ∀ s', s'.2.io = c → (o s').KeepsIo D X c) :
    (Outcome.after f s o).KeepsIo D X c := by
  unfold Outcome.after
  cases h : f s with
  | ok s' => exact ho s' ((hf s' h).trans hc)
  | error e => exact Outcome.KeepsIo.fault hc

/-- A `when`'s block, its names' values put back however it ends, keeps what it kept. -/
theorem Outcome.KeepsIo.release {cells : List (Name × Ty × Nat)} :
    ∀ {o : Outcome Copy.State α} {c}, o.KeepsIo D X c → (o.release Copy.memory cells).KeepsIo D X c
  | .done _ _, _, h | .raised _ _, _, h | .jumped _ _, _, h | .panicked _ _, _, h =>
    Outcome.KeepsIo.after h (fun _ h' => Copy.putBack_io false cells h') fun _ h' => h'
  | .performed _ _ _ _, _, ⟨hc, hk⟩ =>
    Outcome.KeepsIo.after hc (fun _ h' => Copy.putBack_io true cells h') fun _ h' =>
      ⟨h', fun w x hx hw => Outcome.KeepsIo.release (hk w x hx hw)⟩
  | .outOfFuel, _, h | .stuck, _, h => h

/-- A `with`, letting go of the cells its dropped rests hold, keeps what its block kept. -/
theorem Outcome.KeepsIo.letGo (before : World) :
    ∀ {o : Outcome Copy.State α} {c}, o.KeepsIo D X c → (o.letGo Copy.memory before).KeepsIo D X c
  | .done _ (_, _), _, h | .raised _ (_, _), _, h | .jumped _ (_, _), _, h
  | .panicked _ (_, _), _, h => h
  | .performed _ _ _ _, _, ⟨hc, hk⟩ => ⟨hc, fun w x hx hw => Outcome.KeepsIo.letGo before (hk w x hx hw)⟩
  | .outOfFuel, _, h | .stuck, _, h => h

/-- A handler's body's outcome on the frames of a state keeps the worlds it had. -/
theorem Outcome.KeepsIo.lift {γ : Copy.State} :
    ∀ {o : Outcome Copy.State Value} {c}, o.KeepsIo D X c → (o.lift Copy.memory γ).KeepsIo D X c
  | .done _ (_, _), _, h | .raised _ (_, _), _, h | .jumped _ (_, _), _, h
  | .panicked _ (_, _), _, h => by obtain ⟨_, _⟩ := γ; exact h
  | .performed _ _ (_, _) _, _, ⟨hc, hk⟩ => by
    obtain ⟨_, _⟩ := γ
    exact ⟨hc, fun w x hx hw => Outcome.KeepsIo.lift (hk w x hx hw)⟩
  | .outOfFuel, _, h | .stuck, _, h => h

/-- The body of a handler that takes control keeps the world when it does, and each rest it
resumes does from the world it resumes it in. -/
theorem Outcome.KeepsIo.runBody {Xr : Exits} {R ρ : STy}
    {resume : Value → World → Outcome Copy.State Value}
    (hO : ∀ op τ ρ, op ≠ .resume → Xr.performs op τ ρ → X.performs op τ ρ)
    (hres : Xr.Resumes D ρ R)
    (hr : ∀ u x, Value.Typed D u ρ → World.Typed D x →
      (resume u x).Ok D Γ η X (fun v => Value.Typed D v R))
    (hrk : ∀ u x, Value.Typed D u ρ → World.Typed D x → (resume u x).KeepsIo D X x.io) :
    ∀ {o : Outcome Copy.State Value} {c}, o.Ok D Γ η Xr (fun v => Value.Typed D v R) →
      o.KeepsIo D Xr c → (o.runBody Copy.memory resume).KeepsIo D X c
  | .done _ _, _, _, h | .raised _ _, _, _, h | .jumped _ _, _, _, h | .panicked _ _, _, _, h => h
  | .performed op u γ k, c, ⟨⟨τ, ρ', hop, hu, hok⟩, hγ⟩, ⟨hc, hk⟩ => by
    unfold Outcome.runBody
    split
    · rename_i h
      subst h
      obtain ⟨hu', _⟩ := hres τ ρ' hop
      refine (hr u _ (hu' u hu) hγ.2).keeps_bind (fun r γ₃ hrt hγ₃ => ?_)
        (hc ▸ hrk u _ (hu' u hu) hγ.2)
      refine Outcome.KeepsIo.lift (Outcome.KeepsIo.runBody hO hres hr hrk
        (hok r _ ((hres τ ρ' hop).2 r hrt) hγ₃.2) (hk r _ hγ₃.2 fun τ'' ρ'' h _ => ?_))
      exact (hres τ'' ρ'' h).2 r hrt
    · rename_i h
      exact ⟨hc, fun w x hx hw => Outcome.KeepsIo.runBody hO hres hr hrk
        (hok w x (hw τ ρ' (hO op _ _ h hop) hu) hx)
        (hk w x hx fun τ'' ρ'' h' hv => hw τ'' ρ'' (hO op _ _ h h') hv)⟩
  | .outOfFuel, _, _, h | .stuck, _, _, h => h

end Stilt
