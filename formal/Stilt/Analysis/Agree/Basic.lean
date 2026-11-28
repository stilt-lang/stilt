import Stilt.Analysis.Release

/-!
# Runs that agree

`Eval.Agree P B C m' m s`: from `s`, the release step `m'` ends as `m` does, and `m`'s outcome
satisfies `P` where it ends with a value, `B` at a `break` and `C` at a `continue`. Steps that
agree compose (`Eval.Agree.bind`), and steps run by functions equal on their parts are equal
(`Eval.list_congr` and the others).
-/

namespace Stilt

/-- From `s`, `m'` ends as `m` does, which satisfies `P`, `B` and `C`. -/
def Eval.Agree {α : Type} (P : α → Copy.State → Prop) (B C : Copy.State → Prop)
    (m' m : Eval Copy.State α) (s : Copy.State) : Prop :=
  m' s = m s ∧ (m s).Sat P B C

namespace Outcome

variable {α β : Type} {P : α → Copy.State → Prop} {Q : β → Copy.State → Prop}
  {B C B' C' : Copy.State → Prop}

theorem Sat.mono {P' : α → Copy.State → Prop} (hP : ∀ a s, P a s → P' a s) (hB : ∀ s, B s → B' s)
    (hC : ∀ s, C s → C' s) : ∀ {o : Outcome Copy.State α}, o.Sat P B C → o.Sat P' B' C'
  | .done a s, h => hP a s h
  | .jumped .brk s, h => hB s h
  | .jumped .cont s, h => hC s h
  | .jumped (.ret _) _, _ => trivial
  | .performed _ _ _ _, h => fun w x => Sat.mono hP hB hC (h w x)
  | .raised _ _, _ | .panicked _ _, _ | .outOfFuel, _ | .stuck, _ => trivial

/-- What follows each value of an outcome, agreeing from there, agrees after the outcome. -/
theorem agree_bind {f' f : α → Copy.State → Outcome Copy.State β} (hB : ∀ s, B s → B' s)
    (hC : ∀ s, C s → C' s) (hf : ∀ a s, P a s → f' a s = f a s ∧ (f a s).Sat Q B' C') :
    ∀ {o : Outcome Copy.State α}, o.Sat P B C → o.bind f' = o.bind f ∧ (o.bind f).Sat Q B' C'
  | .done a s, h => hf a s h
  | .jumped .brk s, h => ⟨rfl, hB s h⟩
  | .jumped .cont s, h => ⟨rfl, hC s h⟩
  | .jumped (.ret _) _, _ => ⟨rfl, trivial⟩
  | .performed op v s k, h => by
    have ih := fun w x => agree_bind hB hC hf (h w x)
    refine ⟨?_, fun w x => (ih w x).2⟩
    simp only [Outcome.bind]
    congr
    funext w x
    exact (ih w x).1
  | .raised _ _, _ | .panicked _ _, _ | .outOfFuel, _ | .stuck, _ => ⟨rfl, trivial⟩

end Outcome

namespace Eval.Agree

variable {α β : Type} {P : α → Copy.State → Prop} {Q : β → Copy.State → Prop}
  {B C B' C' : Copy.State → Prop} {m' m : Eval Copy.State α} {s : Copy.State}

theorem bind {f' f : α → Eval Copy.State β} (h : Eval.Agree P B C m' m s) (hB : ∀ s, B s → B' s)
    (hC : ∀ s, C s → C' s) (hf : ∀ a s, P a s → Eval.Agree Q B' C' (f' a) (f a) s) :
    Eval.Agree Q B' C' (m' >>= f') (m >>= f) s := by
  show (m' s).bind (fun a s => f' a s) = (m s).bind (fun a s => f a s) ∧ _
  rw [h.1]
  exact Outcome.agree_bind hB hC hf h.2

theorem mono {P' : α → Copy.State → Prop} (h : Eval.Agree P B C m' m s) (hP : ∀ a s, P a s → P' a s)
    (hB : ∀ s, B s → B' s) (hC : ∀ s, C s → C' s) : Eval.Agree P' B' C' m' m s :=
  ⟨h.1, h.2.mono hP hB hC⟩

theorem pure {a : α} (h : P a s) : Eval.Agree P B C (Pure.pure a) (Pure.pure a) s := ⟨rfl, h⟩

theorem ofExcept {x : Except Fault α} (h : ∀ a, x = .ok a → P a s) :
    Eval.Agree P B C (Eval.ofExcept x) (Eval.ofExcept x) s := by
  refine ⟨rfl, ?_⟩
  cases x with
  | ok a => exact h a rfl
  | error f => cases f <;> trivial

theorem same (h : (m s).Sat P B C) : Eval.Agree P B C m m s := ⟨rfl, h⟩

end Eval.Agree

/-! ## Steps run by functions equal on their parts -/

namespace Eval

variable {σ : Type} {r₁ r₂ : Expr → Eval σ Value}

theorem list_congr : ∀ {es : List Expr}, (∀ e ∈ es, r₁ e = r₂ e) → Eval.list r₁ es = Eval.list r₂ es
  | [], _ => rfl
  | e :: es, h => by
    simp only [Eval.list]
    rw [h e List.mem_cons_self, list_congr fun e' he' => h e' (List.mem_cons_of_mem _ he')]

theorem fields_congr : ∀ {fs : List (Name × Expr)}, (∀ fe ∈ fs, r₁ fe.2 = r₂ fe.2) →
    Eval.fields r₁ fs = Eval.fields r₂ fs
  | [], _ => rfl
  | (f, e) :: fs, h => by
    simp only [Eval.fields]
    rw [h (f, e) List.mem_cons_self, fields_congr fun fe hfe => h fe (List.mem_cons_of_mem _ hfe)]

theorem path_congr : ∀ {ps : List Projection}, (∀ i, Projection.index i ∈ ps → r₁ i = r₂ i) →
    Eval.path r₁ ps = Eval.path r₂ ps
  | [], _ => rfl
  | .field f :: ps, h => by
    simp only [Eval.path]
    rw [path_congr fun i hi => h i (List.mem_cons_of_mem _ hi)]
  | .index i :: ps, h => by
    simp only [Eval.path]
    rw [h i List.mem_cons_self, path_congr fun i hi => h i (List.mem_cons_of_mem _ hi)]

end Eval

end Stilt
