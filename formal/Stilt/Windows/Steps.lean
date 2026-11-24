import Stilt.Windows.Store

/-!
# Steps that keep the relation

The simulation of the in-place model by the model of windows, and the steps of the evaluator
that keep it. `SimP D c pend Q G m m'`: from two states the simulation keeps (`Pre`), whose
variables the context guards (`Guards`), and of which `Q` holds, `m` and `m'` end alike: with
results that `G` relates, or the same raise, return, panic or performance of related values,
from states the simulation keeps, with the same variables. `Sim` is the case of values, whose
windows a value's sources track.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

/-- An in-place state and a world. -/
abbrev IState := InPlace.State × World

/-- A state of windows and a world. -/
abbrev WState := State × World

variable {α β γ δ : Type}

/-- What a raise or a return of the body carries: related values, the windows of the second
tracked by the result's parameters, the first a value the checks accept. -/
def Leaving (D : Decls) (c : Ctx) (env : List (Name × Ref)) (si : IState) (sw : WState)
    (v w : Value) : Prop :=
  VRel si.1.store sw.1.store w v ∧ (∀ win ∈ windowsOf w, Tracked env c.In (c.P.map (⟨·, []⟩)) win) ∧
    v.Viewed D

/-- What two outcomes of a body running in the context `c` relate, from variables `env`: states
the simulation keeps, the same variables; results that `G` relates; a raise or a return
`Leaving` the body; a performance of the same value, which holds no window, resumed alike. -/
def CorrG (D : Decls) (c : Ctx) (pend : List (Window × Value)) (G : α → β → IState → WState → Prop)
    (env : List (Name × Ref)) : Outcome.Relation IState WState α β where
  done a si b sw := Pre D c pend si sw ∧ sw.1.env = env ∧ G a b si sw
  raised e si e' sw := Pre D c pend si sw ∧ sw.1.env = env ∧ Leaving D c env si sw e e'
  jumped j si j' sw := Pre D c pend si sw ∧ sw.1.env = env ∧
    match j, j' with
    | .ret v, .ret w => Leaving D c env si sw v w
    | .brk, .brk | .cont, .cont => True
    | _, _ => False
  panicked k si k' sw := Pre D c pend si sw ∧ sw.1.env = env ∧ k = k'
  performed op v si op' v' sw := Pre D c pend si sw ∧ sw.1.env = env ∧ op = op' ∧ v' = v ∧
    Free v ∧ v.Viewed D
  resume _ w x w' x' := w' = w ∧ Free w ∧ w.Viewed D ∧ x' = x ∧ x.All (Value.Viewed D)

/-- From states the simulation keeps, whose variables the context guards, and of which `Q`
holds, `m` and `m'` end alike, their results related by `G`. -/
def SimP (D : Decls) (c : Ctx) (pend : List (Window × Value)) (Q : IState → WState → Prop)
    (G : α → β → IState → WState → Prop) (m : Eval IState α) (m' : Eval WState β) : Prop :=
  ∀ si sw, Pre D c pend si sw → Guards D c pend sw.1.env → Q si sw →
    (m si).Rel (CorrG D c pend G sw.1.env) (m' sw)

/-- Related values: the second read against the in-place store is the first, its windows hold
and the sources `S` track them, and the first is a value the checks accept. -/
def ValG (D : Decls) (c : Ctx) (S : List Shape) (v w : Value) (si : IState) (sw : WState) : Prop :=
  VRel si.1.store sw.1.store w v ∧ (∀ win ∈ windowsOf w, Tracked sw.1.env c.In S win) ∧ v.Viewed D

/-- Two runs of an expression whose sources are `S`. -/
def Sim (D : Decls) (c : Ctx) (pend : List (Window × Value)) (S : List Shape)
    (m : Eval IState Value) (m' : Eval WState Value) : Prop :=
  SimP D c pend (fun _ _ => True) (ValG D c S) m m'

/-- The same value on both sides, one that holds no window and that the checks accept: what
both models give where the model of windows reads a value through its windows. -/
def FreeG (D : Decls) (v w : Value) (_ : IState) (_ : WState) : Prop :=
  w = v ∧ Free v ∧ v.Viewed D

/-- A value that is no closure and no function: calling it is stuck. -/
def NotCallable (v : Value) : Prop :=
  (∀ captured ps result ρ body, v ≠ .closure captured ps result ρ body) ∧
    ∀ f types rows, v ≠ .function f types rows

/-- Values called alike: the same closure or function, which the checks accept, or two values
neither of which can be called. -/
def CallLike (D : Decls) (f f' : Value) : Prop :=
  (f' = f ∧ f.Viewed D) ∨ (NotCallable f ∧ NotCallable f')

/-- The same result on both sides. -/
def Same (a b : α) (_ : IState) (_ : WState) : Prop := a = b

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)} {env : List (Name × Ref)}

theorem CorrG.escapes {G : α → β → IState → WState → Prop} {H : γ → δ → IState → WState → Prop} :
    (CorrG D c pend G env).Escapes (CorrG D c pend H env) :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ _ _ _ h => h,
    fun _ _ _ _ _ h => h⟩

theorem CorrG.fault {G : α → β → IState → WState → Prop} {si : IState} {sw : WState}
    (hp : Pre D c pend si sw) (f : Fault) :
    (Outcome.fault f si : Outcome IState α).Rel (CorrG D c pend G sw.1.env) (Outcome.fault f sw) :=
  Outcome.Rel.fault (R := CorrG D c pend G sw.1.env) (fun _ => ⟨hp, rfl, rfl⟩) f

namespace SimP

variable {Q Q' : IState → WState → Prop} {G G' : α → β → IState → WState → Prop}
  {H : γ → δ → IState → WState → Prop}

theorem mono {m : Eval IState α} {m' : Eval WState β} (h : SimP D c pend Q G m m')
    (hQ : ∀ si sw, Q' si sw → Q si sw) (hG : ∀ a b si sw, G a b si sw → G' a b si sw) :
    SimP D c pend Q' G' m m' := fun si sw hp hg hq =>
  Outcome.Rel.mono (h si sw hp hg (hQ si sw hq))
    ⟨fun _ _ _ _ ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, hG _ _ _ _ h₃⟩, CorrG.escapes⟩

theorem pure {a : α} {b : β} (h : ∀ si sw, Pre D c pend si sw → Q si sw → G a b si sw) :
    SimP D c pend Q G (Pure.pure a) (Pure.pure b) :=
  fun si sw hp _ hq => ⟨hp, rfl, h si sw hp hq⟩

theorem fail (f : Fault) : SimP D c pend Q G (Eval.fail f) (Eval.fail f) :=
  fun _ _ hp _ _ => CorrG.fault hp f

theorem outOfFuel : SimP D c pend Q G Eval.outOfFuel Eval.outOfFuel :=
  fun _ _ _ _ _ => trivial

/-- Reading the states alike: failing alike, or giving related results. -/
theorem inspect {f : IState → Except Fault α} {f' : WState → Except Fault β}
    (h : ∀ si sw, Pre D c pend si sw → Guards D c pend sw.1.env → Q si sw →
      (∃ e, f si = .error e ∧ f' sw = .error e) ∨ ∃ a b, f si = .ok a ∧ f' sw = .ok b ∧ G a b si sw) :
    SimP D c pend Q G (Eval.inspect f) (Eval.inspect f') := by
  intro si sw hp hg hq
  show (Eval.ofExcept (f si) si).Rel _ (Eval.ofExcept (f' sw) sw)
  rcases h si sw hp hg hq with ⟨e, h₁, h₂⟩ | ⟨a, b, h₁, h₂, h₃⟩
  · rw [h₁, h₂]
    exact CorrG.fault hp e
  · rw [h₁, h₂]
    exact ⟨hp, rfl, h₃⟩

theorem bind {m : Eval IState α} {m' : Eval WState β} {f : α → Eval IState γ}
    {f' : β → Eval WState δ} (hm : SimP D c pend Q G m m')
    (hf : ∀ a b, SimP D c pend (G a b) H (f a) (f' b)) :
    SimP D c pend Q H (m >>= f) (m' >>= f') := by
  intro si sw hp hg hq
  show ((m si).bind fun a s => f a s).Rel _ ((m' sw).bind fun b s => f' b s)
  refine Outcome.Rel.bind (hm si sw hp hg hq) CorrG.escapes ?_
  rintro a si₁ b sw₁ ⟨hp₁, he, hG⟩
  have := hf a b si₁ sw₁ hp₁ (he ▸ hg) hG
  rwa [he] at this

/-- A step after another, which learns the state the first started from had the same
variables. -/
theorem bindEnv {m : Eval IState α} {m' : Eval WState β} {f : α → Eval IState γ}
    {f' : β → Eval WState δ} (hm : SimP D c pend Q G m m')
    (hf : ∀ a b, SimP D c pend (fun si₁ sw₁ => G a b si₁ sw₁ ∧
      ∃ si₀ sw₀, Q si₀ sw₀ ∧ sw₁.1.env = sw₀.1.env) H (f a) (f' b)) :
    SimP D c pend Q H (m >>= f) (m' >>= f') := by
  intro si sw hp hg hq
  show ((m si).bind fun a s => f a s).Rel _ ((m' sw).bind fun b s => f' b s)
  refine Outcome.Rel.bind (hm si sw hp hg hq) CorrG.escapes ?_
  rintro a si₁ b sw₁ ⟨hp₁, he, hG⟩
  have := hf a b si₁ sw₁ hp₁ (he ▸ hg) ⟨hG, si, sw, hq, he⟩
  rwa [he] at this

theorem ite (b : Bool) {m₁ m₂ : Eval IState α} {m₁' m₂' : Eval WState β}
    (h₁ : SimP D c pend Q G m₁ m₁') (h₂ : SimP D c pend Q G m₂ m₂') :
    SimP D c pend Q G (if b then m₁ else m₂) (if b then m₁' else m₂') := by
  cases b
  · exact h₂
  · exact h₁

/-- What `Q` holds of, the simulation holds of from it. -/
theorem assume {m : Eval IState α} {m' : Eval WState β}
    (h : ∀ si sw, Pre D c pend si sw → Q si sw → SimP D c pend (fun si' sw' => si' = si ∧ sw' = sw) G m m') :
    SimP D c pend Q G m m' :=
  fun si sw hp hg hq => h si sw hp hq si sw hp hg ⟨rfl, rfl⟩

end SimP

end Windows

end Stilt
