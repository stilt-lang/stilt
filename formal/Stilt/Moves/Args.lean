import Stilt.Moves.Runs
import Stilt.Moves.Frame

/-!
# The arguments of a call

Evaluating a call's arguments keeps the simulation, and more: each argument
that is the last use of a variable passes the value that the variable still
holds, live, when the call starts (values.passing-values and values.inout-argument-order). Nothing after the
last use mentions the variable, so nothing writes it: the step that evaluates
the later arguments writes only live variables it mentions (`Post`).
-/

namespace Stilt.Moving

open InPlace

/-- The variable an argument passes at its last use, if it is one. -/
def _root_.Stilt.Arg.moved? : Arg → Option Name
  | .value (.move x) => some x
  | _ => none

/-- The variables a call's arguments pass at their last uses (values.passing-values). -/
def movedRoots : List Arg → List Name
  | [] => []
  | a :: as =>
    match a.moved? with
    | some x => x :: movedRoots as
    | none => movedRoots as

theorem eq_of_moved? : ∀ {a : Arg} {x : Name}, a.moved? = some x → a = .value (.move x)
  | .value (.move _), _, h => by cases h; rfl
  | .value (.var _), _, h | .value (.int _), _, h | .value (.bool _), _, h | .value .unit, _, h
  | .value (.record ..), _, h | .value (.variant ..), _, h | .value (.list ..), _, h
  | .value (.field ..), _, h | .value (.index ..), _, h | .value (.fnRef ..), _, h
  | .value (.method ..), _, h
  | .value (.closure ..), _, h | .value (.call ..), _, h | .value (.letIn ..), _, h
  | .value (.varIn ..), _, h | .value (.assign ..), _, h | .value (.seq ..), _, h
  | .value (.if ..), _, h | .value (.match ..), _, h | .value (.for ..), _, h
  | .value (.raise _), _, h | .value (.try _), _, h | .value (.tryCatch ..), _, h
  | .inout _, _, h => by cases h

theorem argsMentions_sub_cons (a : Arg) (as : List Arg) :
    (argsMentions as).Sub (argsMentions (a :: as)) := by
  rcases a with e | ⟨x, ps⟩ <;> simp only [argsMentions] <;> live_sub

/-- The variable a passed argument hands over, if it is a last use. -/
def _root_.Stilt.Passed.moved? : Passed → Option Name
  | .moved x _ => some x
  | _ => none

/-- The variables that the passed arguments hand over, in order. -/
def movedOf (passed : List Passed) : List Name := passed.filterMap Passed.moved?

/-- The values a call passes may be held by a run. -/
def PassedOk (passed : List Passed) : Prop := ∀ q ∈ passed, ∀ v, q.value? = some v → VOk v

/-- Each last use that a call passes is the value its variable holds. -/
def MovedHeld (passed : List Passed) (fr : Copy.Frame) : Prop :=
  ∀ x v, Passed.moved x v ∈ passed → fr.lookup x = some v

/-- What evaluating a call's arguments promises: what `MSim` does, and that
each last use passed is still the value of its variable in the frame the
evaluation ends with. -/
def ASim (G : List Passed → Prop) (Lb L X : Live) (m : Eval Copy.State (List Passed))
    (m' : Eval (State × World) (List Passed)) : Prop :=
  ∀ fr s mk, MAgreesIn mk fr s → Inv Lb mk (keys s.1) →
    (m fr).Rel (MCorr.relationF (fun ps fr' => G ps ∧ MovedHeld ps fr') L X mk s.1) (m' s)

/-- Evaluating a last use reads its variable, or runs out of fuel. -/
def MoveReads (run : Expr → Eval Copy.State Value) (run' : Expr → Eval (State × World) Value) :
    Prop :=
  ∀ x, (run (.move x) = Eval.inspect (fun fr => Copy.memory.read fr x []) ∧
      run' (.move x) = Eval.inspect (fun s => Moving.memory.read s x [])) ∨
    (run (.move x) = Eval.outOfFuel ∧ run' (.move x) = Eval.outOfFuel)

theorem movedRoots_sub : ∀ (as : List Arg) (x : Name), x ∈ movedRoots as →
    (argsMentions as).mem x = true
  | [], _, h => by simp [movedRoots] at h
  | a :: as, x, h => by
    simp only [movedRoots] at h
    split at h
    · rename_i y hy
      rcases List.mem_cons.1 h with rfl | h
      · rw [eq_of_moved? hy]
        simp [argsMentions, Expr.mentions]
      · exact (argsMentions_sub_cons a as) x (movedRoots_sub as x h)
    · exact (argsMentions_sub_cons a as) x (movedRoots_sub as x h)

theorem Kills.union_unmentioned {L X M : Live} (hM : ∀ z, X.mem z = true → M.mem z = false) :
    ∀ {mk m : List Bool} {ns : List Name}, Kills L X mk m ns → Kills (L.union M) X mk m ns :=
  fun k => k.weaken (fun z hz h => by simpa [hM z hz] using h) (Live.Sub.refl X)

/-- A step that ends and writes no binding of `x` leaves its value, live. -/
theorem MAgrees.held {mk m : List Bool} {fr fr' : Copy.Frame} {s s' : State} {x : Name}
    {v : Value} {L X : Live} (hag : MAgrees mk fr s) (hlx : LiveAt x mk (keys s))
    (hv : fr.lookup x = some v) (hag' : MAgrees m fr' s') (hk : Kills L X mk m (keys s))
    (hX : X.mem x = false) (henv : s'.env = s.env)
    (hev : Evolves ⟨sel mk X s.env, s.store⟩ ⟨sel mk X s.env, s'.store⟩) :
    fr'.lookup x = some v ∧ LiveAt x m (keys s') := by
  have hlx' : LiveAt x m (keys s') := by rw [keys, henv]; exact hlx.of_kills (.inr hX) hk
  have hl₀ : LiveAt x mk (names fr) := hag.keys_eq ▸ hlx
  have hl₁ : LiveAt x m (names fr') := hag'.keys_eq ▸ hlx'
  obtain ⟨r, hr⟩ := hag.lookup_ref hl₀ hv
  have hd : deref ⟨[], s.store⟩ r [] = .ok v := by
    rcases hag.agrees.holds.lookup x with ⟨h₁, -⟩ | ⟨v', r', h₁, h₂, hd⟩
    · rw [hag.lookup_frame hl₀, hv] at h₁; cases h₁
    · rw [hag.lookup_frame hl₀, hv] at h₁
      rw [hag.lookup_env hl₀, hr] at h₂
      cases h₁; cases h₂; exact hd
  have hsame : deref ⟨[], s'.store⟩ r [] = deref ⟨[], s.store⟩ r [] := by
    refine hev.deref_disjoint (hag.valid (x, r) (mem_of_lookup hr)) fun e he => ?_
    replace he := sel_mem he
    refine disjoint_of_lookup hag.agrees.disjoint (by rw [hag.lookup_env hl₀]; exact hr) e he.1 ?_
    rintro rfl
    rw [hX] at he
    exact absurd he.2 (by simp)
  refine ⟨?_, hlx'⟩
  rcases hag'.agrees.holds.lookup x with ⟨-, h₂⟩ | ⟨v', r', h₁, h₂, hd'⟩
  · rw [hag'.lookup_env hl₁, henv, hr] at h₂; cases h₂
  · rw [hag'.lookup_frame hl₁] at h₁
    rw [hag'.lookup_env hl₁, henv, hr] at h₂
    cases h₂
    rw [h₁]
    have : deref ⟨[], s'.store⟩ r [] = .ok v' := hd'
    rw [hsame, hd] at this
    cases this
    rfl

end Stilt.Moving

namespace Stilt.Moving

open InPlace

variable {Lb L X : Live}

/-- What the arguments of a call pass: values a run may hold, the places they
name, and last uses of the variables `movedRoots` lists. -/
def ArgsOk (as : List Arg) (passed : List Passed) : Prop :=
  PassedOk passed ∧ InPlace.Sim.ArgsResolved as passed ∧ movedOf passed = movedRoots as

namespace ASim

variable {G H : List Passed → Prop} {m : Eval Copy.State (List Passed)}
  {m' : Eval (State × World) (List Passed)}

theorem mono (h : ASim G Lb L X m m') {Lb' L' X' : Live} (hLb : Lb.Sub Lb') (hL : L'.Sub L)
    (hX : X.Sub X') (hG : ∀ ps, G ps → H ps) : ASim H Lb' L' X' m m' := fun fr s mk hag hinv =>
  Outcome.Rel.mono (h fr s mk hag (hinv.mono hLb))
    (MCorr.subF (fun ps _ hp => ⟨hG ps hp.1, hp.2⟩) fun _ _ hp => hp.mono hL hX)

/-- What evaluating the arguments promises, without the values their last uses hold. -/
theorem msim (h : ASim G Lb L X m m') : MSim G Lb L X m m' := fun fr s mk hag hinv =>
  Outcome.Rel.mono (h fr s mk hag hinv) (MCorr.subF (fun _ _ hp => hp.1) fun _ _ hp => hp)

theorem bind {α : Type} {G₀ : α → Prop} {L₁ : Live} {m₀ : Eval Copy.State α}
    {m₀' : Eval (State × World) α}
    {f : α → Eval Copy.State (List Passed)} {f' : α → Eval (State × World) (List Passed)}
    (hm : MSim G₀ Lb L₁ X m₀ m₀') (hf : ∀ a, G₀ a → ASim H L₁ L X (f a) (f' a)) (hLb : L₁.Sub Lb)
    (hL : L.Sub L₁) : ASim H Lb L X (m₀ >>= f) (m₀' >>= f') := by
  intro fr s mk hag hinv
  show ((m₀ fr).bind fun a fr' => f a fr').Rel _ ((m₀' s).bind fun a s' => f' a s')
  refine Outcome.Rel.bind (hm fr s mk hag hinv)
    (MCorr.escapes fun _ _ hp => hp.mono hL (Live.Sub.refl X)) ?_
  rintro a fr₁ a' s₁ ⟨rfl, hG, m₁, hag₁, hk, henv, hev⟩
  have hinv₁ : Inv L₁ m₁ (keys s₁.1) := by
    rw [keys, henv]
    exact hinv.of_kills hLb hk
  exact Outcome.Rel.mono (hf a hG fr₁ s₁ m₁ hag₁ hinv₁)
    (MCorr.subF (fun _ _ hp => hp) fun _ _ hp => Post.trans hag.1 hk henv hev hp hL)

/-- Passing one more argument in front, which is no last use. -/
theorem cons (q : Passed) (hm : ASim G Lb L X m m') (hG : ∀ ps, G ps → H (q :: ps))
    (hq : ∀ x v, q ≠ .moved x v) :
    ASim H Lb L X (m >>= fun vs => Pure.pure (q :: vs)) (m' >>= fun vs => Pure.pure (q :: vs)) := by
  intro fr s mk hag hinv
  show ((m fr).bind fun a fr' => (Pure.pure (q :: a) : Eval Copy.State _) fr').Rel _
    ((m' s).bind fun a s' => (Pure.pure (q :: a) : Eval (State × World) _) s')
  refine Outcome.Rel.bind (hm fr s mk hag hinv) (MCorr.escapes fun _ _ hp => hp) ?_
  rintro a fr₁ a' s₁ ⟨rfl, ⟨hg, hheld⟩, hp⟩
  refine ⟨rfl, ⟨hG a hg, fun x v hx => ?_⟩, hp⟩
  rcases List.mem_cons.1 hx with hx | hx
  · exact absurd hx.symm (hq x v)
  · exact hheld x v hx

end ASim

theorem moved?_of_ne {e : Expr} (h : ∀ x, e ≠ .move x) : (Arg.value e).moved? = none := by
  cases e <;> first | rfl | exact absurd rfl (h _)

theorem ofArg_of_ne {e : Expr} (h : ∀ x, e ≠ .move x) (v : Value) : Passed.ofArg e v = .value v := by
  cases e <;> first | rfl | exact absurd rfl (h _)

theorem movedRoots_sub' (A : Live) (as : List Arg) :
    (A.union (Live.ofList (movedRoots as))).Sub (A.union (argsMentions as)) :=
  fun z hz => by
    simp only [Live.mem_union, Bool.or_eq_true, Live.mem_ofList] at hz ⊢
    exact hz.imp id (movedRoots_sub as z)

end Stilt.Moving
