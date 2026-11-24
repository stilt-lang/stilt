import Stilt.Optimality.Eval

/-!
# The witness under copy-in, copy-out

The reference interpreter's run of the witness (values.inout-arguments and values.inout-argument-order). When the call
starts, each parameter gets a copy of its place: `p_a` a copy of `ss[a]`'s
value, all of whose `i64` fields are 0. The body writes 1 to `p_b.v`, a field
of `p_b`'s own copy, and reads `p_a.extra.v` from `p_a`'s, which still holds 0,
so `[0][0]` doesn't panic. When the call ends, each parameter's value is
written back to its place, from left to right; every write-back succeeds,
since each value has its place's type. So `main` returns `()`.

The run is the same in every order of write-back (`copy_runWith`): the body
returns before any place is written back, and the write-back succeeds in
every order, since each write keeps every root's value of its type.
-/

namespace Stilt.Optimality

open InPlace (copyEnterStep copyLeaveStep copy_enter_eq copy_leave_eq)

/-! ## The start and the end of a call -/

/-- Copy-in reads each place, from left to right, and binds its parameter to
the copy (values.left-to-right). -/
theorem copy_enter_fold {caller : Copy.Frame} (val : Name × Passed → Value) :
    ∀ (bound : List (Name × Passed)) (fr : Copy.Frame),
      (∀ e ∈ bound, ∃ x P, e.2 = .place x P ∧ Copy.read caller x P = .ok (val e)) →
      bound.foldlM (copyEnterStep caller) fr =
        .ok ((bound.map fun e => (e.1, val e)).reverse ++ fr)
  | [], _, _ => rfl
  | (y, p) :: bound, fr, h => by
    obtain ⟨x, P, he, hr⟩ := h (y, p) List.mem_cons_self
    simp only at he
    subst he
    have hstep : copyEnterStep caller fr (y, .place x P) =
        .ok ((y, val (y, .place x P)) :: fr) := by
      simp [copyEnterStep, hr, Functor.map, Except.map]
    rw [List.foldlM_cons, hstep]
    show List.foldlM _ _ bound = _
    rw [copy_enter_fold val bound _ fun e he => h e (List.mem_cons_of_mem _ he)]
    simp

/-- Copy-out writes each parameter's value back to its place, from left to
right, and succeeds when each value has the type its place reaches in values
of the frame's type (values.inout-arguments and values.inout-argument-order). -/
theorem copy_leave_fold {D : Decls} {τ : Ty} {callee : Copy.Frame} :
    ∀ (bound : List (Name × Passed)) (fr : Copy.Frame), (∀ e ∈ fr, ValueHasType D e.2 τ) →
      (∀ e ∈ bound, ∃ x fs u τ', e.2 = .place x (fs.map Step.field) ∧
        x ∈ fr.map Prod.fst ∧
        callee.lookup e.1 = some u ∧ ValueHasType D u τ' ∧ FieldPath D τ fs τ') →
      ∃ fr', bound.foldlM (copyLeaveStep callee) fr = .ok fr'
  | [], fr, _, _ => ⟨fr, rfl⟩
  | (y, p) :: bound, fr, hfr, hb => by
    obtain ⟨x, fs, u, τ', he, hx, hu, hτ', hpath⟩ := hb (y, p) List.mem_cons_self
    simp only at he hu
    subst he
    obtain ⟨r, hr⟩ := lookup_of_mem_keys hx
    obtain ⟨r', hset, hr'⟩ := hpath.set hτ' (hfr _ (mem_of_lookup hr))
    have hstep : copyLeaveStep callee fr (y, .place x (fs.map Step.field)) =
        .ok (assocSet fr x r') := by
      simp [copyLeaveStep, Copy.read, hu, Value.get, Copy.write, hr, hset, Functor.map,
        Except.map, Except.bind]
    rw [List.foldlM_cons, hstep]
    refine copy_leave_fold bound _ (fun e he => (mem_assocSet he).elim (hfr e) (· ▸ hr')) ?_
    intro e he
    obtain ⟨x', fs', u', τ'', he', hx', rest⟩ := hb e (List.mem_cons_of_mem _ he)
    exact ⟨x', fs', u', τ'', he', by rwa [map_fst_assocSet], rest⟩

/-! ## The run -/

variable {ss : List Shape} {a b : Nat} {extra : List Name}

/-- What copy-in gives a parameter: a copy of its place's value (values.index-reads). -/
def copyVal (ss : List Shape) : Name × Passed → Value
  | (_, .place _ P) => litv (fieldNames ss) (leafName ss) (depth ss - P.length)
  | (_, .value w) | (_, .moved _ w) => w

/-- The callee's frame when the call starts: each parameter bound to its
copy (values.index-reads). -/
def calleeFrame (ss : List Shape) : Copy.Frame :=
  ((bound ss).map fun e => (e.1, copyVal ss e)).reverse

theorem lookup_calleeFrame {i : Nat} (hi : i < ss.length) :
    (calleeFrame ss).lookup (nameOf 'p' i) =
      some (litv (fieldNames ss) (leafName ss) (depth ss - ss[i].fields.length)) := by
  refine lookup_named (fun s => litv (fieldNames ss) (leafName ss) (depth ss - s.fields.length)) hi
    fun e => ?_
  rw [calleeFrame, List.mem_reverse, bound, map_mapIdx]
  simp [copyVal, placePassed]

/-- The frame of `main` when the call starts: each root bound to the
literal's value (values.let-and-var). -/
def callerFrame (ss : List Shape) : Copy.Frame :=
  ((ss.map Shape.root).map fun x => (x, litv (fieldNames ss) (leafName ss) (depth ss))).reverse

theorem copy_binds (w : WriteBack) (x : World) :
    ∀ (bs : List (Name × Value)) (fr : Copy.Frame),
      bs.foldl (fun s xv => (Copy.memoryWith w).bind s xv.1 xv.2) (fr, x) = (bs.reverse ++ fr, x)
  | [], _ => rfl
  | (y, v) :: bs, fr => by
    simp only [List.foldl_cons]
    rw [show (Copy.memoryWith w).bind (fr, x) y v = ((y, v) :: fr, x) from rfl, copy_binds w x bs]
    simp

theorem lookup_callerFrame {t : Shape} (ht : t ∈ ss) :
    (callerFrame ss).lookup t.root = some (litv (fieldNames ss) (leafName ss) (depth ss)) :=
  lookup_of_all (by simp [callerFrame]) (by simpa [callerFrame] using ⟨t, ht, rfl⟩)

/-- Copy-in reads each place: a literal's value, read along its fields. -/
theorem copy_enter (w : WriteBack) (x : World) :
    (Copy.memoryWith w).enter (callerFrame ss, x) [] (bound ss) = .ok (calleeFrame ss, x) := by
  show (·, x) <$> Copy.frames.enter (callerFrame ss) [] (bound ss) = _
  rw [copy_enter_eq, copy_enter_fold (copyVal ss) _ _ ?_, List.append_nil]
  · rfl
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 he
  have ht : ss[i] ∈ ss := List.getElem_mem hi
  refine ⟨ss[i].root, ss[i].fields.map Step.field, rfl, ?_⟩
  simp only [Copy.read, lookup_callerFrame ht, copyVal, placePassed, List.length_map]
  exact litv_get leafName_not_mem (fun f hf => mem_fieldNames ht hf) (length_le_depth ht)

/-- The body's write: `p_b`'s copy gets 1 in its field `v`. -/
theorem copy_write (w : WriteBack) (h : Overlap ss a b extra) (x : World) :
    ∃ wb, ValueHasType (decls ss a b extra) wb (paramTy ss (ss[b]'h.lt_b)) ∧
      (Copy.memoryWith w).write (calleeFrame ss, x) (nameOf 'p' b) [.field (leafName ss)] (.int 1) =
        .ok (assocSet (calleeFrame ss) (nameOf 'p' b) wb, x) := by
  have hD := decls_records ss a b extra
  have hle := Nat.sub_le (depth ss) (ss[b]'h.lt_b).fields.length
  obtain ⟨wb, hset, hwb⟩ := (fieldPath_leaf hD hle).set (u := .int 1) (.int (by decide)) (litv_hasType hD hle)
  refine ⟨wb, hwb, ?_⟩
  simp only [Copy.memoryWith, Frames.withWorld, Copy.frames, Copy.write, lookup_calleeFrame h.lt_b]
  simp only [List.map_cons, List.map_nil] at hset
  simp [hset, Functor.map, Except.map]

/-- The body's read: `p_a`'s copy is still the literal's value, whose field
`v` below `extra` is 0, so the probe `[0][0]` gives 0 and the body `()`. The
body makes no call, so no order of write-back bears on it. -/
theorem copy_body (w : WriteBack) (h : Overlap ss a b extra) {wb : Value} {x : World}
    (hw : (Copy.memoryWith w).write (calleeFrame ss, x) (nameOf 'p' b) [.field (leafName ss)] (.int 1) =
      .ok (assocSet (calleeFrame ss) (nameOf 'p' b) wb, x)) (m : Nat) :
    eval (decls ss a b extra) (Copy.memoryWith w) (m + extra.length + 5) (body ss a b extra)
      (calleeFrame ss, x) = .done .unit (assocSet (calleeFrame ss) (nameOf 'p' b) wb, x) := by
  have := h.lt_a
  have := h.lt_b
  have hbm : ss[b] ∈ ss := List.getElem_mem h.lt_b
  have hlen : ss[a].fields.length + extra.length = ss[b].fields.length := by
    simpa using congrArg List.length h.fields
  have hdb := length_le_depth hbm
  have hpb : nameOf 'p' a ≠ nameOf 'p' b := fun he => h.ne (nameOf_inj he)
  rw [eval_body (D := decls ss a b extra) (M := Copy.memoryWith w) (k := 0)
    (wa := litv (fieldNames ss) (leafName ss) (depth ss - ss[a].fields.length)) hw ?_ ?_]
  · rfl
  · simp [Copy.memoryWith, Frames.withWorld, Copy.frames, Copy.read,
      lookup_assocSet_ne _ _ hpb,
      lookup_calleeFrame h.lt_a, Value.get]
  · rw [List.map_append, Value.get_append, litv_get leafName_not_mem
      (fun f hf => mem_fieldNames hbm (h.fields ▸ List.mem_append_right _ hf)) (by omega)]
    exact litv_get_leaf _

/-- Copy-out succeeds, in every order: each parameter's value has its place's
type, and each write keeps every root's value of its type. -/
theorem copy_leave_frames (w : WriteBack) (h : Overlap ss a b extra) {wb : Value}
    (hwb : ValueHasType (decls ss a b extra) wb (paramTy ss (ss[b]'h.lt_b))) :
    ∃ fr, Copy.frames.leave (callerFrame ss) (assocSet (calleeFrame ss) (nameOf 'p' b) wb)
      (w.order (bound ss)) = .ok fr := by
  have hD := decls_records ss a b extra
  rw [copy_leave_eq]
  refine copy_leave_fold (D := decls ss a b extra) (τ := rootTy ss) _ _ ?_ fun e he => ?_
  · intro e he
    simp only [callerFrame, List.mem_reverse, List.mem_map] at he
    obtain ⟨_, _, rfl⟩ := he
    exact litv_hasType hD (Nat.le_refl _)
  obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 ((w.perm _).mem_iff.1 he)
  have ht : ss[i] ∈ ss := List.getElem_mem hi
  have hpath := fieldPath_recTy hD leafName_not_mem (fs := ss[i].fields) (b := depth ss)
    (fun f hf => mem_fieldNames ht hf) (length_le_depth ht) (Nat.le_refl _)
  have hroot : ss[i].root ∈ (callerFrame ss).map Prod.fst := by
    simpa [callerFrame] using ⟨ss[i], ht, rfl⟩
  by_cases hib : i = b
  · subst hib
    exact ⟨_, _, wb, _, rfl, hroot,
      lookup_assocSet_self _ _ _ (by simp [lookup_calleeFrame hi]), hwb, hpath⟩
  · have hne : nameOf 'p' i ≠ nameOf 'p' b := fun he => hib (nameOf_inj he)
    exact ⟨_, _, _, _, rfl, hroot, by simp [lookup_assocSet_ne _ _ hne, lookup_calleeFrame hi],
      litv_hasType hD (Nat.sub_le _ _), hpath⟩

theorem copy_leave (w : WriteBack) (h : Overlap ss a b extra) {wb : Value} (x : World)
    (hwb : ValueHasType (decls ss a b extra) wb (paramTy ss (ss[b]'h.lt_b))) :
    ∃ fr, (Copy.memoryWith w).leave (callerFrame ss, x)
      (assocSet (calleeFrame ss) (nameOf 'p' b) wb, x) (bound ss) = .ok fr := by
  obtain ⟨fr, hfr⟩ := copy_leave_frames w h hwb
  exact ⟨(fr, x), by show (·, x) <$> Copy.frames.leave _ _ _ = _; rw [hfr]; rfl⟩

/-- The copy-in, copy-out run of the witness returns `()`, whatever the order
in which copy-out writes the places back. -/
theorem copy_runWith (w : WriteBack) (h : Overlap ss a b extra) :
    ((witness ss a b extra).runCopyWith w (depth ss + extra.length + 6 + ss.length)).observe =
      .returned .unit := by
  obtain ⟨wb, hwb, hw⟩ := copy_write w h {}
  obtain ⟨fr, hleave⟩ := copy_leave w h {} hwb
  have hinit : ∀ m, depth ss + 2 ≤ m → ∀ s,
      eval (decls ss a b extra) (Copy.memoryWith w) m (rootLit ss) s =
        .done (litv (fieldNames ss) (leafName ss) (depth ss)) s :=
    fun m hm s => eval_lit _ _ (decls_records ss a b extra) leafName_not_mem (Nat.le_refl _) hm s
  unfold Program.runCopyWith Program.run
  rw [show depth ss + extra.length + 6 + ss.length =
      (depth ss + extra.length + 6) + (ss.map Shape.root).length by simp]
  simp only [witness, main]
  rw [eval_vars _ _ hinit (rootLit_not_move ss) _ (by omega), observe_withVars, copy_binds,
    List.append_nil, show depth ss + extra.length + 6 = (depth ss + extra.length + 4) + 2 from rfl,
    eval_theCall _ _ _ _ _ _ (decls_fn? ss a b extra)]
  change (Eval.invoke (Copy.memoryWith w) [] (params ss) (ss.map placePassed)
    (eval _ _ (depth ss + extra.length + 5) (body ss a b extra)) (callerFrame ss, {})).leaveBody.observe
      = _
  rw [invoke_done (Copy.memoryWith w) (bindArgs_witness ss) (copy_enter w _) (copy_body w h hw _) hleave]
  rfl

/-- The reference interpreter's run of the witness, which writes back from left to right
(values.inout-argument-order), returns `()`. -/
theorem copy_run (h : Overlap ss a b extra) :
    ((witness ss a b extra).runCopy (depth ss + extra.length + 6 + ss.length)).observe =
      .returned .unit :=
  copy_runWith .leftToRight h

end Stilt.Optimality
