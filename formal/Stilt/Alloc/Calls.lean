import Stilt.Alloc.Steps
import Stilt.Alloc.Instances
import Stilt.InPlace.Enter

/-!
# Calls that count no allocation

The steps of a run that read and write the frame, evaluate the parts of an expression in
order, and call a function value, kept by `Eval.Counts`: the counting model reads, writes,
binds and calls as copy-in, copy-out does, with the count beside its frame, and a call of a
function value that allocates nothing when called runs a body that makes no value needing
storage, a closure's own or that of a function the set covers (`Decls.MakesCover`), its type
parameters and row variables replaced (`Stilt.Alloc.Instances`).
-/

namespace Stilt

variable {D : Decls} {lim : Limited}

/-- `run'` counts as `run` does on code that makes no value needing storage. -/
def CountsRun (D : Decls) (lim : Limited) (run' : Expr → Eval Count.State Value)
    (run : Expr → Eval Copy.State Value) : Prop :=
  ∀ e, e.allocFreeIn D lim = true → Eval.Counts D lim (Value.AllocFree D lim) (run' e) (run e)

/-- The functions that `lim` covers make no value needing storage, and each impl's method `m`
of a trait `t` is covered when `t.m` is. -/
structure Decls.MakesCover (D : Decls) (lim : Limited) : Prop where
  fns : ∀ d ∈ D.fns, lim.fn d.name = true → d.body.allocFreeIn D lim = true
  methods : ∀ t m h i, lim.method t m = true → D.traitImpl? t h = some i →
    lim.fn (implName t h m) = true

namespace Count

theorem read_lift (c : Nat) (s : Copy.State) (x : Name) (p : Path) :
    memory.read (lift c s) x p = Copy.memory.read s x p := by
  obtain ⟨fr, w⟩ := s; rfl

theorem write_lift (c : Nat) (s : Copy.State) (x : Name) (p : Path) (v : Value) :
    memory.write (lift c s) x p v = lift c <$> Copy.memory.write s x p v := by
  obtain ⟨fr, w⟩ := s
  show (·, w) <$> ((·, c) <$> Copy.write fr x p v) = lift c <$> ((·, w) <$> Copy.write fr x p v)
  cases Copy.write fr x p v <;> rfl

theorem enter_lift (c : Nat) (s : Copy.State) (captured : List (Name × Value))
    (params : List (Name × Passed)) :
    memory.enter (lift c s) captured params = lift c <$> Copy.memory.enter s captured params := by
  obtain ⟨fr, w⟩ := s
  show (·, w) <$> ((·, c) <$> Copy.enter fr captured params) =
    lift c <$> ((·, w) <$> Copy.enter fr captured params)
  cases Copy.enter fr captured params <;> rfl

theorem leave_lift (c : Nat) (s s' : Copy.State) (params : List (Name × Passed)) :
    memory.leave (lift c s) (lift c s') params = lift c <$> Copy.memory.leave s s' params := by
  obtain ⟨fr, w⟩ := s
  obtain ⟨fr', w'⟩ := s'
  show (·, w') <$> ((·, c) <$> Copy.leave fr fr' params) =
    lift c <$> ((·, w') <$> Copy.leave fr fr' params)
  cases Copy.leave fr fr' params <;> rfl

theorem setWorld_lift (c : Nat) (s : Copy.State) (w : World) :
    memory.setWorld (lift c s) w = lift c (Copy.memory.setWorld s w) := by
  obtain ⟨fr, w⟩ := s; rfl

theorem world_lift' (c : Nat) (s : Copy.State) : memory.world (lift c s) = Copy.memory.world s := by
  obtain ⟨fr, w⟩ := s; rfl

end Count

theorem Outcome.atCount_fault {α : Type} (c : Nat) (f : Fault) (s : Copy.State) :
    (Outcome.fault f s : Outcome Copy.State α).atCount c = Outcome.fault f (Count.lift c s) := by
  cases f <;> rfl

theorem Outcome.good_fault {α : Type} {P : α → Prop} (f : Fault) (s : Copy.State) :
    (Outcome.fault f s : Outcome Copy.State α).Good D lim P := by
  cases f <;> trivial

namespace Eval.Counts

variable {α : Type} {P : α → Prop}

theorem read (x : Name) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.inspect fun s => Count.memory.read s x [])
      (Eval.inspect fun s => Copy.memory.read s x []) :=
  inspect (fun c s => Count.read_lift c s x []) fun s _ hs h => by
    obtain ⟨fr, w⟩ := s
    exact hs.1.read h

theorem asInt (v : Value) : Eval.Counts D lim (fun _ => True) (Eval.asInt v) (Eval.asInt v) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem asBool (v : Value) : Eval.Counts D lim (fun _ => True) (Eval.asBool v) (Eval.asBool v) := by
  cases v <;> first | exact pure trivial | exact fail _

theorem asList {v : Value} (hv : v.AllocFree D lim) :
    Eval.Counts D lim (fun vs => ∀ u ∈ vs, u.AllocFree D lim) (Eval.asList v) (Eval.asList v) := by
  cases v <;> first | exact fail _ | skip
  exact pure fun u hu => by cases hv with | list h => exact h u hu

theorem declare (R : Name) {written : List (Name × Value)}
    (hw : ∀ fv ∈ written, fv.2.AllocFree D lim) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.declare D R written) (Eval.declare D R written) := by
  unfold Eval.declare
  split
  · split
    · rename_i fields hfields
      refine pure (.record fun fv hfv => ?_)
      obtain ⟨⟨f, τ⟩, _, ha⟩ := InPlace.Sim.mapM_mem hfields fv hfv
      simp only [Option.map_eq_some_iff] at ha
      obtain ⟨v, hv, rfl⟩ := ha
      exact hw _ (mem_of_lookup hv)
    · exact fail _
  · exact fail _

section Runs

variable {run' : Expr → Eval Count.State Value} {run : Expr → Eval Copy.State Value}
  (h : CountsRun D lim run' run)
include h

theorem list : ∀ es : List Expr, exprsAllocFree D lim es = true →
    Eval.Counts D lim (fun vs : List Value => ∀ v ∈ vs, v.AllocFree D lim) (Eval.list run' es)
      (Eval.list run es)
  | [], _ => pure (by simp)
  | e :: es, hes => by
    simp only [exprsAllocFree, Bool.and_eq_true] at hes
    exact bind (h e hes.1) fun v hv => bind (list es hes.2) fun vs hvs => pure fun u hu => by
      rcases List.mem_cons.1 hu with rfl | hu
      · exact hv
      · exact hvs u hu

theorem fields : ∀ fs : List (Name × Expr), fieldsAllocFree D lim fs = true →
    Eval.Counts D lim (fun ws : List (Name × Value) => ∀ fv ∈ ws, fv.2.AllocFree D lim)
      (Eval.fields run' fs) (Eval.fields run fs)
  | [], _ => pure (by simp)
  | (f, e) :: fs, hfs => by
    simp only [fieldsAllocFree, Bool.and_eq_true] at hfs
    exact bind (h e hfs.1) fun v hv => bind (fields fs hfs.2) fun ws hws => pure fun fv hfv => by
      rcases List.mem_cons.1 hfv with rfl | hfv
      · exact hv
      · exact hws fv hfv

theorem path : ∀ ps : List Projection, pathAllocFree D lim ps = true →
    Eval.Counts D lim (fun _ => True) (Eval.path run' ps) (Eval.path run ps)
  | [], _ => pure trivial
  | .field _ :: ps, hps => by
    simp only [pathAllocFree] at hps
    exact bind (path ps hps) fun _ _ => pure trivial
  | .index i :: ps, hps => by
    simp only [pathAllocFree, Bool.and_eq_true] at hps
    exact bind (bind (h i hps.1) fun v _ => asInt v) fun _ _ =>
      bind (path ps hps.2) fun _ _ => pure trivial

theorem args : ∀ as : List Arg, argsAllocFree D lim as = true →
    Eval.Counts D lim (fun passed : List Passed => ∀ q ∈ passed, q.AllocFree D lim)
      (Eval.args run' as) (Eval.args run as)
  | [], _ => pure (by simp)
  | .value e :: as, has => by
    simp only [argsAllocFree, Bool.and_eq_true] at has
    exact bind (h e has.1) fun v hv => bind (args as has.2) fun ps hps => pure fun q hq => by
      rcases List.mem_cons.1 hq with rfl | hq
      · cases e <;> exact hv
      · exact hps q hq
  | .inout ⟨x, projections⟩ :: as, has => by
    simp only [argsAllocFree, Bool.and_eq_true] at has
    exact bind (path h projections has.1) fun p _ => bind (args as has.2) fun ps hps =>
      pure fun q hq => by
        rcases List.mem_cons.1 hq with rfl | hq
        · trivial
        · exact hps q hq

theorem assign (x : Name) {ps : List Projection} (hps : pathAllocFree D lim ps = true)
    {value : Expr} (hv : value.allocFreeIn D lim = true) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.assign Count.memory run' x ps value)
      (Eval.assign Copy.memory run x ps value) :=
  bind (path h ps hps) fun p _ => bind (h value hv) fun v hw =>
    bind (update (fun c s => Count.write_lift c s x p v) fun s s' hs he => by
      obtain ⟨fr, w⟩ := s
      cases hwr : Copy.write fr x p v with
      | error e => simp [Copy.memory, Frames.withWorld, Copy.frames, hwr, Functor.map,
          Except.map] at he
      | ok fr' =>
        simp [Copy.memory, Frames.withWorld, Copy.frames, hwr, Functor.map, Except.map] at he
        subst he
        exact ⟨hs.1.write hw hwr, hs.2⟩) fun _ _ => pure .unit

end Runs

/-- A callee's outcome as its call's, from a state whose frame allocates nothing when called. -/
theorem leaveCall {s : Copy.State} (hs : Frame.AllocFree D lim s.1) (bound : List (Name × Passed))
    (c : Nat) : ∀ {o : Outcome Copy.State Value}, o.Good D lim (Value.AllocFree D lim) →
      (o.atCount c).leaveCall Count.memory bound (Count.lift c s) =
          (o.leaveCall Copy.memory bound s).atCount c ∧
        (o.leaveCall Copy.memory bound s).Good D lim (Value.AllocFree D lim)
  | .done v s', hg | .raised v s', hg | .jumped (.ret v) s', hg => by
    simp only [Outcome.atCount, Outcome.leaveCall, Count.leave_lift, Count.setWorld_lift,
      Count.world_lift']
    obtain ⟨fr, w⟩ := s
    obtain ⟨fr', w'⟩ := s'
    cases hl : Copy.leave fr fr' bound with
    | ok fr'' =>
      have : Copy.memory.leave (fr, w) (fr', w') bound = .ok (fr'', w') := by
        simp [Copy.memory, Frames.withWorld, Copy.frames, hl, Functor.map, Except.map]
      rw [this]
      exact ⟨rfl, hg.1, Frame.AllocFree.leave hg.2.1 bound hs hl, hg.2.2⟩
    | error f =>
      have : Copy.memory.leave (fr, w) (fr', w') bound = .error f := by
        simp [Copy.memory, Frames.withWorld, Copy.frames, hl, Functor.map, Except.map]
      rw [this]
      exact ⟨Outcome.atCount_fault c f _ |>.symm, Outcome.good_fault f _⟩
  | .panicked k s', _ => by
    simp only [Outcome.atCount, Outcome.leaveCall, Count.leave_lift, Count.setWorld_lift,
      Count.world_lift']
    cases Copy.memory.leave s s' bound with
    | ok s'' => exact ⟨rfl, trivial⟩
    | error f => exact ⟨Outcome.atCount_fault c f _ |>.symm, Outcome.good_fault f _⟩
  | .jumped .brk _, _ | .jumped .cont _, _ | .outOfFuel, _ | .stuck, _ => ⟨rfl, trivial⟩
  | .performed .., hg => hg.elim

/-- A call of a function value whose body counts no allocation. -/
theorem invoke {captured : List (Name × Value)} (hc : ∀ xv ∈ captured, xv.2.AllocFree D lim)
    {params : List Param} {passed : List Passed} (hp : ∀ q ∈ passed, q.AllocFree D lim)
    {body' : Eval Count.State Value} {body : Eval Copy.State Value}
    (hb : Eval.Counts D lim (Value.AllocFree D lim) body' body) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.invoke Count.memory captured params passed body')
      (Eval.invoke Copy.memory captured params passed body) := by
  intro c s hs
  unfold Eval.invoke
  cases hbind : bindArgs params passed with
  | none => exact ⟨rfl, trivial⟩
  | some bound =>
    have hsnd := (InPlace.bindArgs_spec hbind).2
    have hbound : ∀ ya ∈ bound, ya.2.AllocFree D lim := fun ya hya =>
      hp _ (hsnd ▸ List.mem_map_of_mem hya)
    dsimp only
    rw [Count.enter_lift]
    obtain ⟨fr, w⟩ := s
    cases he : Copy.enter fr captured bound with
    | error f =>
      have : Copy.memory.enter (fr, w) captured bound = .error f := by
        simp [Copy.memory, Frames.withWorld, Copy.frames, he, Functor.map, Except.map]
      rw [this]
      exact ⟨Outcome.atCount_fault c f _ |>.symm, Outcome.good_fault f _⟩
    | ok callee =>
      have : Copy.memory.enter (fr, w) captured bound = .ok (callee, w) := by
        simp [Copy.memory, Frames.withWorld, Copy.frames, he, Functor.map, Except.map]
      rw [this]
      have hce : State.AllocFree D lim (callee, w) :=
        ⟨Frame.AllocFree.enter hs.1 bound hc hbound he, hs.2⟩
      obtain ⟨hbe, hbg⟩ := hb c (callee, w) hce
      show (body' (Count.lift c (callee, w))).leaveCall Count.memory bound (Count.lift c (fr, w)) = _ ∧ _
      rw [hbe]
      exact leaveCall hs.1 bound c hbg

/-- A call of a function value that allocates nothing when called. -/
theorem call (hD : D.MakesCover lim) {run' : Expr → Eval Count.State Value}
    {run : Expr → Eval Copy.State Value} (h : CountsRun D lim run' run) {f : Value}
    (hf : f.AllocFree D lim) {passed : List Passed} (hp : ∀ q ∈ passed, q.AllocFree D lim) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.call D Count.memory run' f passed)
      (Eval.call D Copy.memory run f passed) := by
  cases f with
  | closure captured params result ρ body =>
    cases hf with
    | closure hb hc => exact invoke hc hp (h body hb)
  | function name types rows =>
    unfold Eval.call
    dsimp only
    cases hd : D.fn? name with
    | none => exact fail _
    | some d =>
      refine invoke (captured := []) (by simp) hp (h _ ?_)
      rw [Expr.allocFreeIn_substRows]
      have hname : d.name = name := by simpa using List.find?_some hd
      cases hf with
      | function hl =>
        exact Expr.allocFreeIn_substTys _ _ (hD.fns d (List.mem_of_find?_eq_some hd) (hname ▸ hl))
  | _ => exact fail _

/-- A call as code makes it. -/
theorem callAs (hD : D.MakesCover lim) {run' : Expr → Eval Count.State Value}
    {run : Expr → Eval Copy.State Value} (h : CountsRun D lim run' run) (control : Bool)
    {f : Value} (hf : f.AllocFree D lim) {passed : List Passed}
    (hp : ∀ q ∈ passed, q.AllocFree D lim) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.callAs D Count.memory run' control f passed)
      (Eval.callAs D Copy.memory run control f passed) := by
  unfold Eval.callAs
  split
  · exact fail _
  · exact call hD h hf hp

theorem method (hD : D.MakesCover lim) {t m : Name} (τ : Ty) (hm : lim.method t m = true) :
    Eval.Counts D lim (Value.AllocFree D lim) (Eval.method D t m τ) (Eval.method D t m τ) := by
  unfold Eval.method
  split
  · rename_i hh _
    split
    · rename_i i hi
      exact pure (.function (hD.methods t m hh i hm hi))
    · exact fail _
  · exact fail _

end Eval.Counts

end Stilt
