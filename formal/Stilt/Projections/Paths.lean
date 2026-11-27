import Stilt.Projections.Check
import Stilt.Panics.Kept

/-!
# Runs of a projection's body, counted

`Outcome.Yielding res N r P o`: on each path through `o`, an outcome of code of a projection's
body whose kept values are in `res`, the frame keeps its variables `N` in order, and `res`
holds as many values as the path has run `yield`s: the number `r` gives when the path ends
normally, with a value that `P` holds of; one when it ends with a `return`; at most one when it
raises or reaches a performance, whose rest, resumed with any value in any world, again ends so;
and the path ends with no `break` or `continue`. A panic ends the run. `Eval.Yielding` is the
same of every run from a frame whose `res` holds `n` values.

Code that runs no `yield` (`Expr.keeps`) keeps every variable it doesn't write
(`eval_keeps`), `res` among them, and ends with no jump but a `return` once a `yield` has run
(`eval_exits`), so its runs yield as its paths do (`keeps_yielding`).
-/

namespace Stilt

/-- A frame whose variables are `N`, in order, and whose newest `res` holds `m` values. -/
def Frame.Kept (res : Name) (N : List Name) (m : Nat) (fr : Copy.Frame) : Prop :=
  fr.map Prod.fst = N ∧ ∃ l, fr.lookup res = some (.list l) ∧ l.length = m

/-- On each path through an outcome, as many values kept in `res` as the path has run
`yield`s: `r`'s number at its end, one at a `return`, at most one at a raise or a performance,
and no `break` or `continue` (projections.once-on-every-path). -/
def Outcome.Yielding {α : Type} (res : Name) (N : List Name) (r : Yields) (P : α → Prop) :
    Outcome Copy.State α → Prop
  | .done a s => P a ∧ ∃ m, m ≤ 1 ∧ r = some (some m) ∧ Frame.Kept res N m s.1
  | .jumped (.ret _) s => Frame.Kept res N 1 s.1
  | .jumped .brk _ | .jumped .cont _ => False
  | .raised _ s => ∃ m, m ≤ 1 ∧ Frame.Kept res N m s.1
  | .performed _ _ s k =>
    (∃ m, m ≤ 1 ∧ Frame.Kept res N m s.1) ∧ ∀ w x, Outcome.Yielding res N r P (k w x)
  | .panicked _ _ | .outOfFuel | .stuck => True

/-- From every frame whose `res` holds `n` values, `m`'s paths yield as `r` says. -/
def Eval.Yielding {α : Type} (res : Name) (N : List Name) (n : Nat) (r : Yields) (P : α → Prop)
    (m : Eval Copy.State α) : Prop :=
  ∀ s, Frame.Kept res N n s.1 → (m s).Yielding res N r P

/-! ## Frames -/

namespace Frame

theorem Keeps.names {W L : List Name} :
    ∀ {fr fr' : Copy.Frame}, Frame.Keeps W L fr fr' → fr'.map Prod.fst = fr.map Prod.fst
  | _, _, .nil => rfl
  | _, _, .cons _ _ h => by simp [h.names]

theorem Kept.of_keeps {W L : List Name} {res : Name} {N : List Name} {m : Nat} {fr fr' : Copy.Frame}
    (hres : res ∉ W) (h : Frame.Keeps W L fr fr') (hk : Frame.Kept res N m fr) : Frame.Kept res N m fr' :=
  ⟨by rw [h.names]; exact hk.1, by rw [h.lookup hres]; exact hk.2⟩

theorem Kept.bind {res : Name} {N : List Name} {m : Nat} {fr : Copy.Frame} {x : Name} (v : Value)
    (hx : x ≠ res) (hk : Frame.Kept res N m fr) : Frame.Kept res (x :: N) m ((x, v) :: fr) := by
  have hb : (res == x) = false := by simpa using Ne.symm hx
  exact ⟨by simp [hk.1], by simpa only [List.lookup, hb] using hk.2⟩

theorem Kept.tail {res : Name} {N : List Name} {m : Nat} {fr : Copy.Frame} {x : Name}
    (hx : x ≠ res) (hk : Frame.Kept res (x :: N) m fr) : Frame.Kept res N m fr.tail := by
  obtain ⟨hn, l, hl, hm⟩ := hk
  cases fr with
  | nil => simp at hn
  | cons p fr =>
    obtain ⟨y, v⟩ := p
    simp only [List.map_cons, List.cons.injEq] at hn
    obtain ⟨rfl, hn⟩ := hn
    have hb : (res == y) = false := by simpa using Ne.symm hx
    simp only [List.lookup, hb] at hl
    exact ⟨hn, l, hl, hm⟩

end Frame

/-! ## Outcomes -/

namespace Outcome.Yielding

variable {α β : Type} {res : Name} {N : List Name} {r r' : Yields} {P Q' : α → Prop} {Q : β → Prop}

theorem fault (f : Fault) (s : Copy.State) : (Outcome.fault f s : Outcome Copy.State α).Yielding res N r P := by
  cases f <;> trivial

theorem mono (hP : ∀ a, P a → Q' a) (hr : ∀ m, r = some (some m) → r' = some (some m)) :
    ∀ {o : Outcome Copy.State α}, o.Yielding res N r P → o.Yielding res N r' Q'
  | .done _ _, ⟨ha, m, h1, hm, hk⟩ => ⟨hP _ ha, m, h1, hr m hm, hk⟩
  | .performed _ _ _ _, ⟨h, hk⟩ => ⟨h, fun w x => mono hP hr (hk w x)⟩
  | .jumped (.ret _) _, h | .jumped .brk _, h | .jumped .cont _, h | .raised _ _, h
  | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

theorem bind {f : α → Copy.State → Outcome Copy.State β}
    (hf : ∀ a s m, P a → m ≤ 1 → r = some (some m) → Frame.Kept res N m s.1 →
      (f a s).Yielding res N r' Q) :
    ∀ {o : Outcome Copy.State α}, o.Yielding res N r P → (o.bind f).Yielding res N r' Q
  | .done a s, ⟨ha, m, h1, hm, hk⟩ => hf a s m ha h1 hm hk
  | .performed _ _ _ _, ⟨h, hk⟩ => ⟨h, fun w x => bind hf (hk w x)⟩
  | .jumped (.ret _) _, h | .jumped .brk _, h | .jumped .cont _, h | .raised _ _, h
  | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

/-- A scope's end drops its binding, which isn't `res`. -/
theorem unbind {x : Name} (hx : x ≠ res) :
    ∀ {o : Outcome Copy.State α}, o.Yielding res (x :: N) r P → (o.unbind Copy.memory).Yielding res N r P
  | .done _ _, ⟨ha, m, h1, hm, hk⟩ => ⟨ha, m, h1, hm, hk.tail hx⟩
  | .raised _ _, ⟨m, hm, hk⟩ => ⟨m, hm, hk.tail hx⟩
  | .jumped (.ret _) _, h => h.tail hx
  | .performed _ _ _ _, ⟨⟨m, hm, hk⟩, hr⟩ => ⟨⟨m, hm, hk.tail hx⟩, fun w x => unbind hx (hr w x)⟩
  | .jumped .brk _, h | .jumped .cont _, h | .panicked _ _, h | .outOfFuel, h | .stuck, h => h

/-- Code that keeps every variable it doesn't write, `res` among them, and ends with no jump but
a `return` once a `yield` has run, yields as it started. -/
theorem of_keeps {W L : List Name} {fr : Copy.Frame} {n : Nat} (hres : res ∉ W) (hn : n ≤ 1)
    (hfr : Frame.Kept res N n fr) :
    ∀ {o : Outcome Copy.State α}, o.Keeps W L P fr → o.Exits false (n == 1) →
      o.Yielding res N (some (some n)) P
  | .done _ _, ⟨ha, hk⟩, _ => ⟨ha, n, hn, rfl, hfr.of_keeps hres hk⟩
  | .raised _ _, hk, _ => ⟨n, hn, hfr.of_keeps hres hk⟩
  | .jumped (.ret _) _, hk, he => by
    have h1 : n = 1 := by simpa [Outcome.Exits, Jump.Allowed] using he
    subst h1
    exact hfr.of_keeps hres hk
  | .jumped .brk _, _, he | .jumped .cont _, _, he => by simp [Outcome.Exits, Jump.Allowed] at he
  | .performed _ _ _ _, ⟨hk, hr⟩, he =>
    ⟨⟨n, hn, hfr.of_keeps hres hk⟩, fun w x => of_keeps hres hn hfr (hr w x) (he w x)⟩
  | .panicked _ _, _, _ | .outOfFuel, _, _ | .stuck, _, _ => trivial

/-- A `catch` around code that runs no `yield`: its handler runs from as many values kept. -/
theorem handle_of_keeps {W L : List Name} {fr : Copy.Frame} {n : Nat} {h : Value → Copy.State → Outcome Copy.State α}
    (hres : res ∉ W) (hn : n ≤ 1) (hfr : Frame.Kept res N n fr) (hr : r = some (some n))
    (hh : ∀ e s, Frame.Kept res N n s.1 → (h e s).Yielding res N r P) :
    ∀ {o : Outcome Copy.State α}, o.Keeps W L P fr → o.Exits false (n == 1) → (o.handle h).Yielding res N r P
  | .done _ _, ⟨ha, hk⟩, _ => ⟨ha, n, hn, hr, hfr.of_keeps hres hk⟩
  | .raised e s, hk, _ => hh e s (hfr.of_keeps hres hk)
  | .jumped (.ret _) _, hk, he => by
    have h1 : n = 1 := by simpa [Outcome.Exits, Jump.Allowed] using he
    subst h1
    exact hfr.of_keeps hres hk
  | .jumped .brk _, _, he | .jumped .cont _, _, he => by simp [Outcome.Exits, Jump.Allowed] at he
  | .performed _ _ _ _, ⟨hk, hr'⟩, he =>
    ⟨⟨n, hn, hfr.of_keeps hres hk⟩, fun w x => handle_of_keeps hres hn hfr hr hh (hr' w x) (he w x)⟩
  | .panicked _ _, _, _ | .outOfFuel, _, _ | .stuck, _, _ => trivial

end Outcome.Yielding

/-- An outcome that never ends with a value, nor a performance whose rest may. -/
def Outcome.NoDone {σ α : Type} : Outcome σ α → Prop
  | .done _ _ => False
  | .performed _ _ _ k => ∀ w x, Outcome.NoDone (k w x)
  | _ => True

theorem Outcome.NoDone.bind {σ α β : Type} {f : α → σ → Outcome σ β} (hf : ∀ a s, (f a s).NoDone) :
    ∀ {o : Outcome σ α}, (o.bind f).NoDone
  | .done a s => hf a s
  | .performed _ _ _ k => fun w x => bind hf (o := k w x)
  | .raised _ _ | .jumped _ _ | .panicked _ _ | .outOfFuel | .stuck => trivial

/-- Paths that end no way normally end as any count of `yield`s says. -/
theorem Outcome.Yielding.of_noDone {α : Type} {res : Name} {N : List Name} {r r' : Yields}
    {P Q : α → Prop} : ∀ {o : Outcome Copy.State α}, o.NoDone → o.Yielding res N r P → o.Yielding res N r' Q
  | .done _ _, h, _ => h.elim
  | .performed _ _ _ _, hd, ⟨h, hk⟩ => ⟨h, fun w x => of_noDone (hd w x) (hk w x)⟩
  | .jumped (.ret _) _, _, h | .jumped .brk _, _, h | .jumped .cont _, _, h | .raised _ _, _, h
  | .panicked _ _, _, h | .outOfFuel, _, h | .stuck, _, h => h

/-! ## Steps -/

namespace Eval.Yielding

variable {α β : Type} {res : Name} {N : List Name} {n : Nat} {r r' : Yields} {P : α → Prop}
  {Q : β → Prop}

theorem pure (a : α) (hP : P a) (hn : n ≤ 1) : Eval.Yielding res N n (some (some n)) P (Pure.pure a) :=
  fun _ hs => ⟨hP, n, hn, rfl, hs⟩

theorem bind {m : Eval Copy.State α} {f : α → Eval Copy.State β} (hm : Eval.Yielding res N n r P m)
    (hf : ∀ a k, P a → k ≤ 1 → r = some (some k) → Eval.Yielding res N k r' Q (f a)) :
    Eval.Yielding res N n r' Q (m >>= f) := fun s hs =>
  Outcome.Yielding.bind (fun a s' k ha h1 hk hs' => hf a k ha h1 hk s' hs') (hm s hs)

theorem mono {Q' : α → Prop} {m : Eval Copy.State α} (hP : ∀ a, P a → Q' a)
    (hr : ∀ k, r = some (some k) → r' = some (some k)) (hm : Eval.Yielding res N n r P m) :
    Eval.Yielding res N n r' Q' m := fun s hs => Outcome.Yielding.mono hP hr (hm s hs)

theorem withVar {x : Name} (hx : x ≠ res) (v : Value) {m : Eval Copy.State α}
    (hm : Eval.Yielding res (x :: N) n r P m) : Eval.Yielding res N n r P (Eval.withVar Copy.memory x v m) :=
  fun s hs => Outcome.Yielding.unbind hx (hm ((x, v) :: s.1, s.2) (hs.bind v hx))

theorem withInit {x : Name} (hx : x ≠ res) (init : Expr) (v : Value) {m : Eval Copy.State α}
    (hm : Eval.Yielding res (x :: N) n r P m) :
    Eval.Yielding res N n r P (Eval.withInit Copy.memory x init v m) := by
  intro s hs
  unfold Eval.withInit Memory.bindInit
  cases init
  case move y => exact Outcome.Yielding.unbind hx (hm ((x, v) :: s.1, s.2) (hs.bind v hx))
  all_goals exact Outcome.Yielding.unbind hx (hm ((x, v) :: s.1, s.2) (hs.bind v hx))

theorem withVars {m : Eval Copy.State α} :
    ∀ {N : List Name} (bs : List (Name × Value)), (∀ p ∈ bs, p.1 ≠ res) →
      Eval.Yielding res ((bs.map Prod.fst).reverse ++ N) n r P m →
      Eval.Yielding res N n r P (Eval.withVars Copy.memory bs m)
  | _, [], _, hm => hm
  | N, (x, v) :: bs, hbs, hm => by
    refine withVar (hbs (x, v) List.mem_cons_self) v (withVars (N := x :: N) bs
      (fun p hp => hbs p (List.mem_cons_of_mem _ hp)) ?_)
    simpa using hm

theorem asBool (v : Value) (hn : n ≤ 1) : Eval.Yielding res N n (some (some n)) (fun _ => True)
    (Eval.asBool v : Eval Copy.State Bool) := by
  cases v <;> first | exact pure _ trivial hn | exact fun s _ => Outcome.Yielding.fault .stuck s

end Eval.Yielding

end Stilt
