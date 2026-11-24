import Stilt.Declarations
import Stilt.Memory

/-!
# What code writes

The variables that code may change: those it assigns, and those it passes
`inout`, which a call writes back when it ends (values.inout-arguments). A
closure literal's body writes its own copies of what it captures
(expressions.capture), so nothing it writes counts. Running code keeps the value of
every other variable of the frame (`Frame.Keeps`).
-/

namespace Stilt

mutual

/-- The variables that `e` may change. -/
def Expr.writes : Expr → List Name
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ | .closure _ _ _ _ => []
  | .record _ fields => fieldsWrites fields
  | .variant _ _ es => exprsWrites es
  | .list _ es => exprsWrites es
  | .op _ es | .view es => exprsWrites es
  | .field e _ => e.writes
  | .index e i => e.writes ++ i.writes
  | .call callee args _ => callee.writes ++ argsWrites args
  | .letIn _ _ init body => init.writes ++ body.writes
  | .held _ hs body => exprsWrites hs ++ body.writes
  | .varIn _ _ init body => init.writes ++ body.writes
  | .assign ⟨x, path⟩ value => x :: (pathWrites path ++ value.writes)
  | .seq a b => a.writes ++ b.writes
  | .if c _ a b => c.writes ++ (a.writes ++ b.writes)
  | .match e _ arms => e.writes ++ armsWrites arms
  | .for _ _ e body => e.writes ++ body.writes
  | .raise e => e.writes
  | .try e => e.writes
  | .tryCatch e _ _ handler _ => e.writes ++ handler.writes
  | .while c body => c.writes ++ body.writes
  | .loop body => body.writes
  | .return e => e.writes
  | .perform _ e => e.writes
  | .withH _ _ h b => h.writes ++ b.writes

def exprsWrites : List Expr → List Name
  | [] => []
  | e :: es => e.writes ++ exprsWrites es

def fieldsWrites : List (Name × Expr) → List Name
  | [] => []
  | (_, e) :: fields => e.writes ++ fieldsWrites fields

def argsWrites : List Arg → List Name
  | [] => []
  | .value e :: args => e.writes ++ argsWrites args
  | .inout ⟨x, path⟩ :: args => x :: (pathWrites path ++ argsWrites args)

def pathWrites : List Projection → List Name
  | [] => []
  | .field _ :: path => pathWrites path
  | .index i :: path => i.writes ++ pathWrites path

def armsWrites : List Arm → List Name
  | [] => []
  | ⟨_, _, body⟩ :: arms => body.writes ++ armsWrites arms

end

mutual

/-- The variables whose lists `e` may change the length of: those it stores whole,
and those it passes `inout` whole. A store or an `inout` argument below a
variable, `xs[i] = v` or `f(inout xs[i])`, keeps its list's length (`Value.set_sameLen`). -/
def Expr.resizes : Expr → List Name
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ | .closure _ _ _ _ => []
  | .record _ fields => fieldsResizes fields
  | .variant _ _ es => exprsResizes es
  | .list _ es => exprsResizes es
  | .op _ es | .view es => exprsResizes es
  | .field e _ => e.resizes
  | .index e i => e.resizes ++ i.resizes
  | .call callee args _ => callee.resizes ++ argsResizes args
  | .letIn _ _ init body => init.resizes ++ body.resizes
  | .held _ hs body => exprsResizes hs ++ body.resizes
  | .varIn _ _ init body => init.resizes ++ body.resizes
  | .assign ⟨x, path⟩ value => (if path.isEmpty then [x] else []) ++ (pathResizes path ++ value.resizes)
  | .seq a b => a.resizes ++ b.resizes
  | .if c _ a b => c.resizes ++ (a.resizes ++ b.resizes)
  | .match e _ arms => e.resizes ++ armsResizes arms
  | .for _ _ e body => e.resizes ++ body.resizes
  | .raise e => e.resizes
  | .try e => e.resizes
  | .tryCatch e _ _ handler _ => e.resizes ++ handler.resizes
  | .while c body => c.resizes ++ body.resizes
  | .loop body => body.resizes
  | .return e => e.resizes
  | .perform _ e => e.resizes
  | .withH _ _ h b => h.resizes ++ b.resizes

def exprsResizes : List Expr → List Name
  | [] => []
  | e :: es => e.resizes ++ exprsResizes es

def fieldsResizes : List (Name × Expr) → List Name
  | [] => []
  | (_, e) :: fields => e.resizes ++ fieldsResizes fields

def argsResizes : List Arg → List Name
  | [] => []
  | .value e :: args => e.resizes ++ argsResizes args
  | .inout ⟨x, path⟩ :: args => (if path.isEmpty then [x] else []) ++ (pathResizes path ++ argsResizes args)

def pathResizes : List Projection → List Name
  | [] => []
  | .field _ :: path => pathResizes path
  | .index i :: path => i.resizes ++ pathResizes path

def armsResizes : List Arm → List Name
  | [] => []
  | ⟨_, _, body⟩ :: arms => body.resizes ++ armsResizes arms

end

theorem append_subset_append {α : Type} {a b c d : List α} (h₁ : a ⊆ c) (h₂ : b ⊆ d) :
    a ++ b ⊆ c ++ d := fun _ h => (List.mem_append.1 h).elim
  (fun h => List.mem_append.2 (.inl (h₁ h))) (fun h => List.mem_append.2 (.inr (h₂ h)))

theorem if_isEmpty_subset {x : Name} {ps : List Projection} :
    (if ps.isEmpty then [x] else []) ⊆ [x] := by
  split
  · exact List.Subset.refl _
  · intro _ h; cases h

mutual

/-- What code resizes it writes. -/
theorem Expr.resizes_subset : ∀ e : Expr, e.resizes ⊆ e.writes
  | .var _ | .move _ | .int _ | .bool _ | .unit | .break | .continue | .fnRef _ _ _
  | .method _ _ _ | .closure _ _ _ _ => List.Subset.refl _
  | .record _ fields => fieldsResizes_subset fields
  | .variant _ _ es | .list _ es | .op _ es | .view es => exprsResizes_subset es
  | .field e _ | .raise e | .perform _ e | .try e | .return e | .loop e => Expr.resizes_subset e
  | .index e i => append_subset_append (Expr.resizes_subset e) (Expr.resizes_subset i)
  | .call c args _ => append_subset_append (Expr.resizes_subset c) (argsResizes_subset args)
  | .letIn _ _ a b | .varIn _ _ a b | .seq a b | .withH _ _ a b | .for _ _ a b | .while a b =>
    append_subset_append (Expr.resizes_subset a) (Expr.resizes_subset b)
  | .tryCatch a _ _ b _ => append_subset_append (Expr.resizes_subset a) (Expr.resizes_subset b)
  | .held _ hs b => append_subset_append (exprsResizes_subset hs) (Expr.resizes_subset b)
  | .assign ⟨_, path⟩ value => fun y hy => by
    simp only [Expr.resizes, List.mem_append] at hy
    simp only [Expr.writes, List.mem_cons, List.mem_append]
    rcases hy with hy | hy | hy
    · exact .inl (List.mem_singleton.1 (if_isEmpty_subset hy))
    · exact .inr (.inl (pathResizes_subset path hy))
    · exact .inr (.inr (Expr.resizes_subset value hy))
  | .if c _ a b => append_subset_append (Expr.resizes_subset c)
      (append_subset_append (Expr.resizes_subset a) (Expr.resizes_subset b))
  | .match e _ arms => append_subset_append (Expr.resizes_subset e) (armsResizes_subset arms)

theorem exprsResizes_subset : ∀ es : List Expr, exprsResizes es ⊆ exprsWrites es
  | [] => List.Subset.refl _
  | e :: es => append_subset_append (Expr.resizes_subset e) (exprsResizes_subset es)

theorem fieldsResizes_subset : ∀ fs : List (Name × Expr), fieldsResizes fs ⊆ fieldsWrites fs
  | [] => List.Subset.refl _
  | (_, e) :: fs => append_subset_append (Expr.resizes_subset e) (fieldsResizes_subset fs)

theorem argsResizes_subset : ∀ as : List Arg, argsResizes as ⊆ argsWrites as
  | [] => List.Subset.refl _
  | .value e :: as => append_subset_append (Expr.resizes_subset e) (argsResizes_subset as)
  | .inout ⟨_, path⟩ :: as => fun y hy => by
    simp only [argsResizes, List.mem_append] at hy
    simp only [argsWrites, List.mem_cons, List.mem_append]
    rcases hy with hy | hy | hy
    · exact .inl (List.mem_singleton.1 (if_isEmpty_subset hy))
    · exact .inr (.inl (pathResizes_subset path hy))
    · exact .inr (.inr (argsResizes_subset as hy))

theorem pathResizes_subset : ∀ ps : List Projection, pathResizes ps ⊆ pathWrites ps
  | [] => List.Subset.refl _
  | .field _ :: ps => pathResizes_subset ps
  | .index i :: ps => append_subset_append (Expr.resizes_subset i) (pathResizes_subset ps)

theorem armsResizes_subset : ∀ arms : List Arm, armsResizes arms ⊆ armsWrites arms
  | [] => List.Subset.refl _
  | ⟨_, _, body⟩ :: arms =>
    append_subset_append (Expr.resizes_subset body) (armsResizes_subset arms)

end

/-- A value whose list, if it is one, the other has, with as many elements. -/
def Value.SameLen (v v' : Value) : Prop :=
  ∀ vs, v = .list vs → ∃ vs', v' = .list vs' ∧ vs'.length = vs.length

theorem Value.SameLen.refl (v : Value) : v.SameLen v := fun vs h => ⟨vs, h, rfl⟩

theorem Value.SameLen.trans {u v w : Value} (h₁ : u.SameLen v) (h₂ : v.SameLen w) : u.SameLen w :=
  fun us hu =>
    let ⟨vs, hv, hl⟩ := h₁ us hu
    let ⟨ws, hw, hl'⟩ := h₂ vs hv
    ⟨ws, hw, hl'.trans hl⟩

/-- A store below a value keeps its list's length. -/
theorem Value.set_sameLen {v w v' : Value} {p : Step} {ps : Path} (h : v.set (p :: ps) w = .ok v') :
    v.SameLen v' := by
  intro vs hv
  subst hv
  cases p with
  | field f => simp [Value.set] at h
  | index i =>
    simp only [Value.set] at h
    split at h
    · rename_i u _
      cases hs : u.set ps w with
      | error e => rw [hs] at h; cases h
      | ok u' => rw [hs] at h; cases h; exact ⟨_, rfl, List.length_set⟩
    · cases h

/-- `s'` has the variables of `s`, in order, each with its value unless `W` holds
its name, and with a list of the same length unless `L` holds it. -/
inductive Frame.Keeps (W L : List Name) : Copy.Frame → Copy.Frame → Prop
  | nil : Frame.Keeps W L [] []
  | cons {x : Name} {v v' : Value} {s s' : Copy.Frame} :
      (x ∉ W → v' = v) → (x ∉ L → v.SameLen v') → Frame.Keeps W L s s' →
        Frame.Keeps W L ((x, v) :: s) ((x, v') :: s')

namespace Frame.Keeps

variable {W W' L L' : List Name}

theorem refl : ∀ s : Copy.Frame, Frame.Keeps W L s s
  | [] => .nil
  | (_, v) :: s => .cons (fun _ => rfl) (fun _ => Value.SameLen.refl v) (refl s)

theorem trans : ∀ {s₁ s₂ s₃ : Copy.Frame}, Frame.Keeps W L s₁ s₂ → Frame.Keeps W L s₂ s₃ →
    Frame.Keeps W L s₁ s₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h₁ l₁ k₁, .cons h₂ l₂ k₂ =>
    .cons (fun hx => (h₂ hx).trans (h₁ hx)) (fun hx => (l₁ hx).trans (l₂ hx)) (trans k₁ k₂)

theorem mono (hW : W ⊆ W') (hL : L ⊆ L') :
    ∀ {s s' : Copy.Frame}, Frame.Keeps W L s s' → Frame.Keeps W' L' s s'
  | _, _, .nil => .nil
  | _, _, .cons h l k =>
    .cons (fun hx => h fun hw => hx (hW hw)) (fun hx => l fun hl => hx (hL hl)) (mono hW hL k)

/-- Ending the scope of the newest binding keeps the rest. -/
theorem tail {x : Name} {v : Value} {s s' : Copy.Frame} (h : Frame.Keeps W L ((x, v) :: s) s') :
    Frame.Keeps W L s s'.tail := by
  cases h with
  | cons _ _ k => exact k

theorem lookup : ∀ {s s' : Copy.Frame}, Frame.Keeps W L s s' → ∀ {x : Name}, x ∉ W →
    s'.lookup x = s.lookup x
  | _, _, .nil, _, _ => rfl
  | _, _, .cons (x := y) h _ k, x, hx => by
    simp only [List.lookup_cons]
    by_cases hxy : x = y
    · subst hxy; simp [h hx]
    · have : (x == y) = false := by simpa using hxy
      simp only [this]
      exact lookup k hx

/-- A variable that `L` doesn't hold keeps its list's length. -/
theorem lookup_list : ∀ {s s' : Copy.Frame}, Frame.Keeps W L s s' → ∀ {x : Name}, x ∉ L →
    ∀ {vs}, s.lookup x = some (.list vs) → ∃ vs', s'.lookup x = some (.list vs') ∧ vs'.length = vs.length
  | _, _, .nil, _, _, _, h => by simp at h
  | _, _, .cons (x := y) _ l k, x, hx, vs, h => by
    simp only [List.lookup_cons] at h ⊢
    by_cases hxy : x = y
    · subst hxy
      simp only [beq_self_eq_true, Option.some.injEq] at h ⊢
      exact l hx vs h
    · have : (x == y) = false := by simpa using hxy
      simp only [this] at h ⊢
      exact lookup_list k hx h

/-- Storing `b` at `x`, which `W` holds, keeps the frame, when `L` holds `x` too or
`b` has the length of the list `x` held. -/
theorem assocSet {x : Name} (hx : x ∈ W) {b : Value} :
    ∀ s : Copy.Frame, (x ∈ L ∨ ∀ v, s.lookup x = some v → v.SameLen b) →
      Frame.Keeps W L s (Stilt.assocSet s x b)
  | [], _ => .nil
  | (y, v) :: s, hb => by
    unfold Stilt.assocSet
    split
    · rename_i h; subst h
      exact .cons (fun h' => absurd hx h')
        (fun hl => hb.resolve_left hl v (by simp)) (refl s)
    · rename_i h
      have hne : (x == y) = false := by simpa using h
      refine .cons (fun _ => rfl) (fun _ => Value.SameLen.refl v) (assocSet hx s ?_)
      exact hb.imp id fun f u hu => f u (by simpa [List.lookup_cons, hne] using hu)

/-- A write of `x`, which `W` holds, keeps the frame, when it is below `x` or `L`
holds `x` too. -/
theorem write {fr fr' : Copy.Frame} {x : Name} {p : Path} {w : Value} (hx : x ∈ W)
    (hl : p = [] → x ∈ L) (h : Copy.write fr x p w = .ok fr') : Frame.Keeps W L fr fr' := by
  unfold Copy.write at h
  split at h
  · rename_i v hv
    cases hs : v.set p w with
    | error e => rw [hs] at h; cases h
    | ok v' =>
      rw [hs] at h
      cases h
      refine assocSet hx fr ?_
      cases p with
      | nil => exact .inl (hl rfl)
      | cons q ps =>
        refine .inr fun u hu => ?_
        rw [hv] at hu
        cases hu
        exact Value.set_sameLen hs
  · cases h

end Frame.Keeps

end Stilt
