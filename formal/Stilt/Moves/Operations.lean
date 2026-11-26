import Stilt.Moves.Relation

/-!
# Operations

Each operation of the evaluator keeps `MAgrees`: writing a live binding,
binding a new variable, ending the newest binding, capturing the newest
binding of each variable a closure literal captures when those are live, and binding the last use of a variable, which ends it and
hands its storage over (values.passing-values).
-/

namespace Stilt.Moving

open InPlace

variable {m : List Bool} {fr : Copy.Frame} {s : State}

theorem names_assocSet {β : Type} (k : Name) (b : β) :
    ∀ l : List (Name × β), (assocSet l k b).map Prod.fst = l.map Prod.fst
  | [] => rfl
  | (k', b') :: l => by by_cases h : k = k' <;> simp [assocSet, h, names_assocSet k b l]

theorem write_shape {x : Name} {p : Path} {w : Value} {s' : State}
    (h : InPlace.write s x p w = .ok s') : s'.env = s.env ∧ s'.store.length = s.store.length := by
  unfold InPlace.write at h
  split at h
  · rename_i r _
    split at h
    · rename_i u _
      cases hu : u.set (r.path ++ p) w with
      | error e => rw [hu] at h; cases h
      | ok u' =>
        rw [hu] at h
        cases h
        simp
    · cases h
  · cases h

theorem write_store {x : Name} {p : Path} {w : Value}
    (hl : (keep m s.env).lookup x = s.env.lookup x) :
    InPlace.write s x p w = (fun t => ⟨s.env, t.store⟩) <$>
      InPlace.write ⟨keep m s.env, s.store⟩ x p w := by
  unfold InPlace.write
  rw [hl]
  rcases s.env.lookup x with _ | r
  · rfl
  · dsimp only
    rcases s.store[r.loc]? with _ | u
    · rfl
    · dsimp only
      cases u.set (r.path ++ p) w <;> rfl

/-- A write to `x` is a write below the reference of `x`. -/
theorem write_grows {x : Name} {p : Path} {w : Value} {s' : State} {r : Ref}
    (hl : s.env.lookup x = some r) (h : InPlace.write s x p w = .ok s') :
    Evolves ⟨[(x, r)], s.store⟩ ⟨[(x, r)], s'.store⟩ := by
  unfold InPlace.write at h
  rw [hl] at h
  dsimp only at h
  split at h
  · rename_i u hu
    cases hu' : u.set (r.path ++ p) w with
    | error e => rw [hu'] at h; cases h
    | ok u' =>
      rw [hu'] at h
      cases h
      refine ⟨rfl, [(r.toPath ++ p, w)], s.store.set r.loc u', [], by simp, ?_, ?_⟩
      · intro pw hpw
        rw [List.mem_singleton.1 hpw]
        exact ⟨r.toPath, by simp [State.paths], p, rfl⟩
      · simp [Value.setSeq, set_whole hu, hu', Functor.map, Except.map, Except.bind]
  · cases h

/-- Writing a live variable writes it among the live bindings. -/
theorem write_keep {m : List Bool} {fr : Copy.Frame} {x : Name} (hlen : m.length = fr.length)
    (hx : LiveAt x m (names fr)) (p : Path) (w : Value) :
    (keep m ·) <$> Copy.write fr x p w = Copy.write (keep m fr) x p w := by
  unfold Copy.write
  rw [lookup_keep hlen hx]
  split
  · cases _ : (_ : Value).set p w <;> simp [Functor.map, Except.map, keep_assocSet hlen hx]
  · rfl

theorem write_names {fr fr₂ : Copy.Frame} {x : Name} {p : Path} {w : Value}
    (h : Copy.write fr x p w = .ok fr₂) : names fr₂ = names fr := by
  unfold Copy.write at h
  split at h
  · rename_i v _
    cases hv : v.set p w with
    | error e => rw [hv] at h; cases h
    | ok v' =>
      rw [hv] at h
      cases h
      exact names_assocSet x v' fr
  · cases h

/-- A write keeps the names of a frame, and writes a value a run may hold into
a live binding. -/
theorem write_just {m : List Bool} {fr fr' : Copy.Frame} {x : Name} {p : Path} {w : Value}
    (hlen : m.length = fr.length) (hx : LiveAt x m (names fr)) (hj : w.Justified)
    (hfr : ∀ xv ∈ keep m fr, xv.2.Justified) (h : Copy.write fr x p w = .ok fr') :
    ∀ xv ∈ keep m fr', xv.2.Justified := by
  unfold Copy.write at h
  split at h
  · rename_i v hv
    cases hv' : v.set p w with
    | error e => rw [hv'] at h; cases h
    | ok v' =>
      rw [hv'] at h
      cases h
      intro xv hxv
      rw [keep_assocSet hlen hx] at hxv
      rcases mem_assocSet hxv with hxv | hxv
      · exact hfr xv hxv
      · have hv₀ : (keep m fr).lookup x = some v := by rw [lookup_keep hlen hx]; exact hv
        exact hxv ▸ Value.Justified.set (hfr _ (mem_of_lookup hv₀)) hj hv'
  · cases h

/-- The newest binding of each name `keep` holds is the same among the live
bindings when each is live. -/
theorem newestOf_keep {β : Type} : ∀ (keep : Name → Bool) {m : List Bool} {l : List (Name × β)},
    m.length = l.length → (∀ x, keep x = true → LiveAt x m (l.map Prod.fst)) →
      newestOf keep (Moving.keep m l) = newestOf keep l
  | _, [], [], _, _ => rfl
  | keep, b :: m, (y, v) :: l, hl, hk => by
    have hl' : m.length = l.length := by simpa using hl
    by_cases hy : keep y = true
    · have hb : b = true := by simpa [LiveAt] using hk y hy
      subst hb
      simp only [Moving.keep, ↓reduceIte, newestOf, hy]
      refine congrArg _ (newestOf_keep _ hl' fun x hx => ?_)
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hx
      simpa [LiveAt, Ne.symm hx.2] using hk x hx.1
    · have ih := newestOf_keep keep hl' fun x hx => by
        have hxy : y ≠ x := fun e => hy (e ▸ hx)
        simpa [LiveAt, hxy] using hk x hx
      cases b <;> simp [Moving.keep, newestOf, hy, ih]
  | _, [], _ :: _, hl, _ | _, _ :: _, [], hl, _ => by simp at hl

namespace MAgrees

/-- Both models write a live binding alike. -/
theorem write (h : MAgrees m fr s) {x : Name} (hx : LiveAt x m (names fr)) {w : Value}
    (hw : w.Safe) (hj : w.Justified) (p : Path) :
    (∃ f, Copy.write fr x p w = .error f ∧ InPlace.write s x p w = .error f) ∨
      ∃ fr' s', Copy.write fr x p w = .ok fr' ∧ InPlace.write s x p w = .ok s' ∧
        MAgrees m fr' s' ∧ s'.env = s.env ∧ ∃ r, s.env.lookup x = some r ∧
          Evolves ⟨[(x, r)], s.store⟩ ⟨[(x, r)], s'.store⟩ := by
  have hc := write_keep h.len hx p w
  have hi : InPlace.write s x p w = (fun t => ⟨s.env, t.store⟩) <$>
      InPlace.write ⟨keep m s.env, s.store⟩ x p w := write_store (h.lookup_env hx)
  rcases h.agrees.write hw x p with ⟨f, h₁, h₂⟩ | ⟨fr₁, s₁, h₁, h₂, hag, hev⟩
  · refine .inl ⟨f, ?_, by rw [hi, h₂]; rfl⟩
    cases hcw : Copy.write fr x p w with
    | error f' => rw [hcw] at hc; rw [h₁] at hc; cases hc; rfl
    | ok _ => rw [hcw, h₁] at hc; cases hc
  · cases hcw : Copy.write fr x p w with
    | error f' => rw [hcw, h₁] at hc; cases hc
    | ok fr' =>
      rw [hcw, h₁] at hc
      simp only [Functor.map, Except.map, Except.ok.injEq] at hc
      obtain ⟨henv, hlen⟩ := write_shape h₂
      have hs₁ : s₁ = ⟨keep m s.env, s₁.store⟩ := by
        cases s₁
        simp only at henv
        rw [henv]
      have hw' : InPlace.write s x p w = .ok ⟨s.env, s₁.store⟩ := by rw [hi, h₂]; rfl
      refine .inr ⟨fr', ⟨s.env, s₁.store⟩, rfl, hw', ?_, rfl, ?_⟩
      · have hshape : names fr' = names fr ∧ ∀ xv ∈ keep m fr', xv.2.Justified :=
          ⟨write_names hcw, write_just h.len hx hj h.just hcw⟩
        refine ⟨?_, hshape.1.trans h.align, ?_, ?_, hshape.2⟩
        · rw [h.len]
          simpa using (congrArg List.length hshape.1).symm
        · rw [hc]
          rw [hs₁] at hag
          exact hag
        · intro xr hxr
          rw [hlen]
          exact h.valid xr hxr
      · obtain ⟨_, r, -, hr, -⟩ := h.agrees.holds.lookup x |>.resolve_left (by
          intro hn
          have := hn.1
          rw [h.lookup_frame hx] at this
          unfold Copy.write at hcw
          rw [this] at hcw
          cases hcw)
        rw [h.lookup_env hx] at hr
        exact ⟨r, hr, write_grows hr hw'⟩

/-- A new binding is live, in a new location. -/
theorem bind (h : MAgrees m fr s) (x : Name) {v : Value} (hv : v.Safe) (hj : v.Justified) :
    MAgrees (true :: m) ((x, v) :: fr) (InPlace.bind s x v) := by
  refine ⟨by simp [h.len], by simp [InPlace.bind, h.align], h.agrees.bind x hv, ?_, ?_⟩
  · intro xr hxr
    simp only [InPlace.bind, List.mem_cons, List.length_append, List.length_singleton] at hxr ⊢
    rcases hxr with rfl | hxr
    · simp
    · have := h.valid xr hxr
      omega
  · intro xv hxv
    rcases List.mem_cons.1 hxv with rfl | hxv
    · exact hj
    · exact h.just xv hxv

/-- Ending the newest binding, live or not. -/
theorem unbind {b : Bool} {a : Name × Value} (h : MAgrees (b :: m) (a :: fr) s) :
    MAgrees m fr ⟨s.env.tail, s.store⟩ := by
  obtain ⟨len, align, agrees, valid, just⟩ := h
  match s, align, agrees, valid with
  | ⟨e :: env, st⟩, align, agrees, valid =>
    simp only [List.map_cons, List.cons.injEq] at align
    refine ⟨by simpa using len, align.2, ?_, fun xr hxr => valid xr (List.mem_cons_of_mem _ hxr),
      fun xv hxv => just xv ?_⟩
    · cases b
      · exact agrees
      · exact agrees.unbind
    · cases b
      · exact hxv
      · exact List.mem_cons_of_mem _ hxv

/-- When the newest binding of each name `keep` holds is live, a closure
captures the same values in both models (expressions.capture). -/
theorem capture (h : MAgrees m fr s) {keep : Name → Bool}
    (hk : ∀ x, keep x = true → LiveAt x m (names fr)) :
    Moving.frames.capture s keep = .ok (newestOf keep fr) ∧
      ∀ xv ∈ newestOf keep fr, xv.2.Safe ∧ xv.2.Justified := by
  have hf : newestOf keep (Moving.keep m fr) = newestOf keep fr := newestOf_keep keep h.len hk
  have he : newestOf keep (Moving.keep m s.env) = newestOf keep s.env :=
    newestOf_keep keep h.len_env (by rw [← h.align]; exact hk)
  have hc := h.agrees.holds.capture s.env keep
  rw [hf, he] at hc
  refine ⟨hc, fun xv hxv => ?_⟩
  rw [← hf] at hxv
  have hxv' := mem_of_mem_newestOf hxv
  exact ⟨h.agrees.safe xv hxv', h.just xv hxv'⟩

/-- Ending the newest binding of a live variable. -/
theorem kill (h : MAgrees m fr s) {x : Name} (hx : LiveAt x m (names fr)) :
    MAgrees (Moving.kill x m (names fr)) fr s := by
  have hx' : LiveAt x m (s.env.map Prod.fst) := by rw [← h.align]; exact hx
  refine ⟨by rw [length_kill, h.len], h.align, ?_, h.valid, fun xv hxv => ?_⟩
  · rw [keep_kill h.len hx]
    have := h.agrees.drop x
    rwa [show names fr = s.env.map Prod.fst from h.align, keep_kill h.len_env hx']
  · rw [keep_kill h.len hx] at hxv
    exact h.just xv ((sublist_dropName x _).subset hxv)

theorem lookup_ref (h : MAgrees m fr s) {x : Name} (hx : LiveAt x m (names fr)) {v : Value}
    (hv : fr.lookup x = some v) : ∃ r, s.env.lookup x = some r := by
  rcases h.agrees.holds.lookup x with ⟨h₁, -⟩ | ⟨_, r, -, h₂, -⟩
  · rw [h.lookup_frame hx, hv] at h₁
    cases h₁
  · exact ⟨r, by rw [← h.lookup_env hx]; exact h₂⟩

/-- Binding the last use of a live variable ends it and hands its storage over
to the new binding (values.passing-values). -/
theorem bindMoved (h : MAgrees m fr s) {x : Name} (hx : LiveAt x m (names fr)) (y : Name)
    {v : Value} (hv : fr.lookup x = some v) :
    MAgrees (true :: Moving.kill x m (names fr)) ((y, v) :: fr) (Moving.bindMoved s y x v) := by
  obtain ⟨r, hr⟩ := h.lookup_ref hx hv
  have hx' : LiveAt x m (s.env.map Prod.fst) := by rw [← h.align]; exact hx
  have hb : Moving.bindMoved s y x v = { s with env := (y, r) :: s.env } := by
    simp [Moving.bindMoved, hr]
  rw [hb]
  refine ⟨by simp [length_kill, h.len], by simp [h.align], ?_, ?_, ?_⟩
  · show Agrees ((y, v) :: keep (Moving.kill x m (names fr)) fr)
      ⟨(y, r) :: keep (Moving.kill x m (names fr)) s.env, s.store⟩
    rw [keep_kill h.len hx]
    rw [show names fr = s.env.map Prod.fst from h.align, keep_kill h.len_env hx']
    exact h.agrees.rebind (by rw [h.lookup_frame hx]; exact hv) (by rw [h.lookup_env hx]; exact hr)
  · intro xr hxr
    rcases List.mem_cons.1 hxr with rfl | hxr
    · exact h.valid (x, r) (mem_of_lookup hr)
    · exact h.valid xr hxr
  · intro xv hxv
    rcases List.mem_cons.1 hxv with rfl | hxv
    · exact (h.read_ok hx (p := []) (by simp [Copy.read, hv, Value.get])).2
    · rw [keep_kill h.len hx] at hxv
      exact h.just xv ((sublist_dropName x _).subset hxv)

end MAgrees

end Stilt.Moving
