import Stilt.Optimality.Eval

/-!
# The witness in place

The in-place run of the witness. When the call starts, each parameter refers
to its place in `main`'s store: `p_a` to `ss[a]`'s place and `p_b` to
`ss[b]`'s, which lies `extra` below it. The body writes 1 to `p_b.v`, where it
is, and then reads `p_a.extra.v`, which is the same part of the store. So the
probe `[0][1]` panics with the kind `bounds` (effects.panic-kinds; std.lists), and so does the run.
-/

namespace Stilt.Optimality

open InPlace (State Ref enterStep enter_eq placeRef)

/-! ## `main`'s state -/

/-- Every variable of the state is a whole location of its own, and every
location holds `u` (values.let-and-var). -/
def Whole (u : Value) (s : State) : Prop :=
  (∀ e ∈ s.env, e.2.path = [] ∧ e.2.loc < s.store.length) ∧ ∀ w ∈ s.store, w = u

theorem whole_bind {u : Value} {s : State} (h : Whole u s) (x : Name) :
    Whole u (InPlace.bind s x u) := by
  show Whole u (InPlace.bind s x u)
  refine ⟨fun e he => ?_, fun w hw => ?_⟩
  · simp only [InPlace.bind, List.mem_cons] at he
    simp only [InPlace.bind, List.length_append, List.length_singleton]
    rcases he with rfl | he
    · exact ⟨rfl, by simp⟩
    · have := h.1 e he
      exact ⟨this.1, by omega⟩
  · simp only [InPlace.bind, List.mem_append, List.mem_singleton] at hw
    exact hw.elim (h.2 w) id

/-- Binding each name to `u` in turn keeps every variable a whole location
holding `u`, and binds every name (values.let-and-var). -/
theorem whole_binds {u : Value} :
    ∀ (xs : List Name) (s : State), Whole u s →
      Whole u ((xs.map fun x => (x, u)).foldl (fun s xv => InPlace.bind s xv.1 xv.2) s) ∧
      ∀ x ∈ s.env.map Prod.fst ++ xs,
        x ∈ ((xs.map fun x => (x, u)).foldl
          (fun s xv => InPlace.bind s xv.1 xv.2) s).env.map Prod.fst
  | [], s, h => ⟨h, by simp⟩
  | x :: xs, s, h => by
    obtain ⟨hw, hk⟩ := whole_binds xs _ (whole_bind h x)
    refine ⟨hw, fun y hy => hk y ?_⟩
    simp only [List.mem_append, List.mem_cons] at hy
    simp only [InPlace.bind, List.map_cons, List.mem_append, List.mem_cons]
    rcases hy with hy | hy | hy
    · exact .inl (.inr hy)
    · exact .inl (.inl hy)
    · exact .inr hy

theorem whole_lookup {u : Value} {s : State} (h : Whole u s) {x : Name}
    (hx : x ∈ s.env.map Prod.fst) :
    ∃ r, s.env.lookup x = some r ∧ r.path = [] ∧ s.store[r.loc]? = some u := by
  obtain ⟨r, hr⟩ := lookup_of_mem_keys hx
  have hmem := h.1 _ (mem_of_lookup hr)
  refine ⟨r, hr, hmem.1, ?_⟩
  rw [List.getElem?_eq_getElem hmem.2, h.2 _ (List.getElem_mem hmem.2)]

/-! ## The start of the call -/

/-- In place, each `inout` parameter refers to its argument's place (values.index-reads). -/
theorem enter_fold {caller : State} (ref : Name × Passed → Ref) :
    ∀ (bound : List (Name × Passed)) (st : State),
      (∀ e ∈ bound, ∃ x P r u, e.2 = .place x P ∧ caller.env.lookup x = some r ∧
        InPlace.deref caller r P = .ok u ∧ ref e = placeRef r P) →
      bound.foldlM (enterStep caller) st =
        .ok ⟨(bound.map fun e => (e.1, ref e)).reverse ++ st.env, st.store⟩
  | [], _, _ => rfl
  | (y, p) :: bound, st, h => by
    obtain ⟨x, P, r, u, he, hr, hd, href⟩ := h (y, p) List.mem_cons_self
    simp only at he
    subst he
    have hstep : enterStep caller st (y, .place x P) =
        .ok ⟨(y, ref (y, .place x P)) :: st.env, st.store⟩ := by
      simp [enterStep, hr, hd, href, Functor.map, Except.map]
    rw [List.foldlM_cons, hstep]
    show List.foldlM _ _ bound = _
    rw [enter_fold ref bound _ fun e he => h e (List.mem_cons_of_mem _ he)]
    simp

variable {ss : List Shape} {a b : Nat} {extra : List Name}

/-- `main`'s state when the call starts: each root in a location of its own
(values.let-and-var). -/
def callerState (ss : List Shape) : State :=
  ((ss.map Shape.root).map fun x => (x, litv (fieldNames ss) (leafName ss) (depth ss))).foldl
    (fun s xv => InPlace.bind s xv.1 xv.2) ⟨[], []⟩

theorem callerState_lookup {t : Shape} (ht : t ∈ ss) :
    ∃ r, (callerState ss).env.lookup t.root = some r ∧ r.path = [] ∧
      (callerState ss).store[r.loc]? = some (litv (fieldNames ss) (leafName ss) (depth ss)) := by
  obtain ⟨hw, hk⟩ := whole_binds (u := litv (fieldNames ss) (leafName ss) (depth ss))
    (ss.map Shape.root) ⟨[], []⟩ ⟨by simp, by simp⟩
  exact whole_lookup hw (hk _ (by simpa using ⟨t, ht, rfl⟩))

/-- The reference that the start of the call gives a parameter: its
argument's place (values.index-reads). -/
def calleeRef (ss : List Shape) : Name × Passed → Ref
  | (_, .place x P) => placeRef (((callerState ss).env.lookup x).getD ⟨0, []⟩) P
  | (_, .value _) | (_, .moved _ _) => ⟨0, []⟩

/-- The callee's state when the call starts: it shares `main`'s store
(values.inout-arguments). -/
def calleeState (ss : List Shape) : State :=
  ⟨((bound ss).map fun e => (e.1, calleeRef ss e)).reverse, (callerState ss).store⟩

theorem inPlace_enter_frames :
    InPlace.frames.enter (callerState ss) [] (bound ss) = .ok (calleeState ss) := by
  rw [enter_eq, enter_fold (calleeRef ss) _ _ ?_]
  · simp [calleeState]
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 he
  have ht : ss[i] ∈ ss := List.getElem_mem hi
  obtain ⟨r, hr, hpath, hstore⟩ := callerState_lookup ht
  refine ⟨ss[i].root, ss[i].fields.map Step.field, r,
    litv (fieldNames ss) (leafName ss) (depth ss - ss[i].fields.length), rfl, hr, ?_,
    by simp [calleeRef, placePassed, hr]⟩
  simp only [InPlace.deref, hstore, hpath, List.nil_append]
  exact litv_get leafName_not_mem (fun f hf => mem_fieldNames ht hf) (length_le_depth ht)

theorem inPlace_enter (x : World) :
    InPlace.memory.enter (callerState ss, x) [] (bound ss) = .ok (calleeState ss, x) := by
  show (·, x) <$> InPlace.frames.enter (callerState ss) [] (bound ss) = _
  rw [inPlace_enter_frames]
  rfl

theorem lookup_calleeState {i : Nat} (hi : i < ss.length) :
    (calleeState ss).env.lookup (nameOf 'p' i) =
      some (placeRef (((callerState ss).env.lookup ss[i].root).getD ⟨0, []⟩)
        (ss[i].fields.map Step.field)) := by
  refine lookup_named (fun s => placeRef (((callerState ss).env.lookup s.root).getD ⟨0, []⟩)
    (s.fields.map Step.field)) hi fun e => ?_
  rw [calleeState, List.mem_reverse, bound, map_mapIdx]
  simp [calleeRef, placePassed]

/-! ## The run -/

/-- In place, the body writes 1 to `p_b.v` in `main`'s store, and `p_a.extra.v`
is that same part of the store, so the probe `[0][1]` panics. -/
theorem inPlace_body (h : Overlap ss a b extra) (m : Nat) (x : World) : ∃ s',
    eval (decls ss a b extra) InPlace.memory (m + extra.length + 5) (body ss a b extra)
      (calleeState ss, x) = .panicked .bounds s' := by
  have := h.lt_a
  have := h.lt_b
  have hD := decls_records ss a b extra
  have hbm : ss[b] ∈ ss := List.getElem_mem h.lt_b
  obtain ⟨r, hr, hpath, hstore⟩ := callerState_lookup hbm
  have hroot : ss[a].root = ss[b].root := h.root
  have hfp := (fieldPath_recTy hD leafName_not_mem (fs := ss[b].fields) (b := depth ss)
    (fun f hf => mem_fieldNames hbm hf) (length_le_depth hbm) (Nat.le_refl _)).append
    (fieldPath_leaf hD (Nat.sub_le _ _))
  obtain ⟨w, hset, -⟩ := hfp.set (u := .int 1) (.int (by decide)) (litv_hasType hD (Nat.le_refl _))
  have hloc : r.loc < (callerState ss).store.length := (List.getElem?_eq_some_iff.1 hstore).1
  have hw : InPlace.memory.write (calleeState ss, x) (nameOf 'p' b) [.field (leafName ss)] (.int 1) =
      .ok ({ calleeState ss with store := (callerState ss).store.set r.loc w }, x) := by
    simp only [List.map_append, List.map_cons, List.map_nil] at hset
    show (·, x) <$> InPlace.write (calleeState ss) (nameOf 'p' b) [.field (leafName ss)] (.int 1) = _
    simp only [InPlace.write, lookup_calleeState h.lt_b, hr, Option.getD_some, placeRef]
    simp [calleeState, hstore, hpath, hset, Functor.map, Except.map]
  have hget := Value.get_of_set hset
  rw [List.map_append, ← h.fields, List.map_append, List.append_assoc, ← List.map_append,
    Value.get_append] at hget
  cases hwa : w.get (ss[a].fields.map Step.field) with
  | error _ => simp [hwa, Except.bind] at hget
  | ok wa =>
    simp only [hwa, Except.bind] at hget
    rw [eval_body hw ?_ hget]
    · exact ⟨_, rfl⟩
    show InPlace.read { calleeState ss with store := (callerState ss).store.set r.loc w }
      (nameOf 'p' a) [] = _
    simp only [InPlace.read, InPlace.deref]
    rw [show ({ calleeState ss with store := (callerState ss).store.set r.loc w } : State).env =
      (calleeState ss).env from rfl, lookup_calleeState h.lt_a]
    simp [hroot, hr, placeRef, hpath, List.getElem?_set_self hloc, hwa]

/-- The in-place run of the witness panics with the kind `bounds`. -/
theorem inPlace_run (h : Overlap ss a b extra) :
    ((witness ss a b extra).runInPlace (depth ss + extra.length + 6 + ss.length)).observe =
      .panicked .bounds := by
  obtain ⟨s', hbody⟩ := inPlace_body h (depth ss) {}
  have hinit : ∀ m, depth ss + 2 ≤ m → ∀ s,
      eval (decls ss a b extra) InPlace.memory m (rootLit ss) s =
        .done (litv (fieldNames ss) (leafName ss) (depth ss)) s :=
    fun m hm s => eval_lit _ _ (decls_records ss a b extra) leafName_not_mem (Nat.le_refl _) hm s
  unfold Program.runInPlace Program.run
  rw [show depth ss + extra.length + 6 + ss.length =
      (depth ss + extra.length + 6) + (ss.map Shape.root).length by simp]
  simp only [witness, main]
  rw [eval_vars _ _ hinit (rootLit_not_move ss) _ (by omega), observe_withVars,
    InPlace.memory, Frames.withWorld_foldl_bind, ← InPlace.memory,
    show depth ss + extra.length + 6 = (depth ss + extra.length + 4) + 2 from rfl,
    eval_theCall _ _ _ _ _ _ (decls_fn? ss a b extra)]
  change (Eval.invoke InPlace.memory [] (params ss) (ss.map placePassed)
    (eval _ _ (depth ss + extra.length + 5) (body ss a b extra)) (callerState ss, {})).leaveBody.observe
      = _
  rw [invoke_panicked InPlace.memory (bindArgs_witness ss) (inPlace_enter _) hbody rfl]
  rfl

end Stilt.Optimality
