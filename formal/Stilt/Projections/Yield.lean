import Stilt.Projections.Runs

/-!
# A `yield`, run

`yield p` reads the list of kept values, calls the access, which writes no `res` and ends with
no jump, and stores the list with the access's value added: from none kept, one
(`yield_yielding`, projections.yield and projections.when-projection-runs). A `match` runs
one arm, each of whose guards runs no `yield`, and its paths are those of its arms
(`select_yielding`).
-/

namespace Stilt

theorem map_fst_assocSet' {β : Type} (k : Name) (b : β) :
    ∀ l : List (Name × β), (assocSet l k b).map Prod.fst = l.map Prod.fst
  | [] => rfl
  | (k', b') :: l => by
    unfold assocSet
    split
    · rfl
    · simp [map_fst_assocSet' k b l]

variable (D : Decls) {res : Name} {N : List Name}

/-- Reading `res` from a frame that keeps none gives the empty list. -/
theorem read_yielding : ∀ fuel, Eval.Yielding res N 0 (some (some 0)) (fun v => v = .list [])
    (eval D Copy.memory fuel (.var res))
  | 0 => fun _ _ => trivial
  | _ + 1 => by
    intro s hs
    obtain ⟨fr, w⟩ := s
    obtain ⟨hn, l, hl, hlen⟩ := hs
    have hl' : l = [] := List.eq_nil_of_length_eq_zero hlen
    subst hl'
    have hr : Copy.memory.read (fr, w) res [] = .ok (.list []) := by
      simp [Copy.memory, Frames.withWorld, Copy.frames, Copy.read, hl, Value.get]
    show (Eval.inspect (fun s => Copy.memory.read s res []) (fr, w)).Yielding res N _ _
    simp only [Eval.inspect, Eval.ofExcept, hr]
    exact ⟨rfl, 0, Nat.zero_le _, rfl, hn, [], hl, rfl⟩

/-- Storing a list of one value in `res` keeps one. -/
theorem write_yielding (u : Value) : Eval.Yielding res N 0 (some (some 1)) (fun _ => True)
    (Eval.update (fun s => Copy.memory.write s res [] (.list [u])) >>= fun _ =>
      (Pure.pure .unit : Eval Copy.State Value)) := by
  intro s hs
  obtain ⟨fr, w⟩ := s
  obtain ⟨hn, l, hl, _⟩ := hs
  have hw : Copy.memory.write (fr, w) res [] (.list [u]) = .ok (assocSet fr res (.list [u]), w) := by
    simp [Copy.memory, Frames.withWorld, Copy.frames, Copy.write, hl, Value.set]
    rfl
  show ((Eval.update (fun s => Copy.memory.write s res [] (.list [u])) (fr, w)).bind
    fun a s' => (Pure.pure .unit : Eval Copy.State Value) s').Yielding res N _ _
  simp only [Eval.update, hw]
  refine ⟨trivial, 1, Nat.le_refl _, rfl, ?_, [u], ?_, rfl⟩
  · rw [map_fst_assocSet']
    exact hn
  · exact lookup_assocSet_self fr res _ (by simp [hl])

/-- The value `yield` stores: the list kept, empty, with the access's value added. -/
theorem push_yielding {a : Expr} (hres : res ∉ a.writes) (hex : a.exits false false = true) :
    ∀ fuel, Eval.Yielding res N 0 (some (some 0)) (fun v => ∃ u, v = .list [u])
      (eval D Copy.memory fuel (.op (.list .push) [.var res, .try a]))
  | 0 => fun _ _ => trivial
  | fuel + 1 => by
    refine Eval.Yielding.bind (P := fun vs => ∃ u, vs = [.list [], u]) (r := some (some 0)) ?_
      fun vs k hvs hk hk1 => ?_
    · refine Eval.Yielding.bind (read_yielding D fuel) fun v k hv hk hk1 => ?_
      cases hk1
      refine Eval.Yielding.bind (P := fun vs => ∃ u, vs = [u]) (r := some (some 0)) ?_
        fun us k' hus _ hk1' => ?_
      · refine Eval.Yielding.bind (keeps_yielding' D fuel (e := .try a) (n := 0) hres
          (by simpa [Expr.exits] using hex) (Nat.zero_le _)) fun u k' _ _ hk1' => ?_
        cases hk1'
        refine Eval.Yielding.bind (Eval.Yielding.pure [] (P := fun vs => vs = []) rfl (Nat.zero_le _))
          fun us _ hus _ hk1'' => ?_
        cases hk1''
        exact Eval.Yielding.pure _ ⟨u, by rw [hus]⟩ (Nat.zero_le _)
      · cases hk1'
        obtain ⟨u, rfl⟩ := hus
        exact Eval.Yielding.pure _ ⟨u, by rw [hv]⟩ (Nat.zero_le _)
    · cases hk1
      obtain ⟨u, rfl⟩ := hvs
      intro s hs
      obtain ⟨fr, w⟩ := s
      have h : (Op.list .push).run [.list [], u] w = .ok (.list [u], w) := rfl
      show (Eval.world Copy.frames.withWorld ((Op.list .push).run [.list [], u]) (fr, w)).Yielding res N _ _
      rw [Eval.world_ok h]
      exact ⟨⟨u, rfl⟩, 0, Nat.zero_le _, rfl, hs⟩

/-- `yield p`, from no value kept, keeps one: the access's (projections.yield). -/
theorem yield_yielding {a : Expr} (hres : res ∉ a.writes) (hex : a.exits false false = true) :
    ∀ fuel, Eval.Yielding res N 0 (some (some 1)) (fun _ => True)
      (eval D Copy.memory fuel (.assign ⟨res, []⟩ (.op (.list .push) [.var res, .try a])))
  | 0 => fun _ _ => trivial
  | fuel + 1 => by
    show Eval.Yielding res N 0 _ _ (Eval.assign Copy.memory (eval D Copy.memory fuel) res [] _)
    unfold Eval.assign
    refine Eval.Yielding.bind (Eval.Yielding.pure [] (P := fun p => p = []) rfl (Nat.zero_le _))
      fun p _ hp _ hk => ?_
    cases hk
    subst hp
    refine Eval.Yielding.bind (push_yielding D hres hex fuel) fun v _ hv _ hk => ?_
    cases hk
    obtain ⟨u, rfl⟩ := hv
    exact write_yielding u

end Stilt
