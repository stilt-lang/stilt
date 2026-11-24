import Stilt.Sharing.Modify

/-!
# Assigning the whole of a binding when every binding is shared

An assignment of the whole of a binding either redirects a local of a copy-on-write type to the
place it is given (modes.copies), or gives every binding that referred into its home a copy of
its own and writes the value at the home, copying nothing (modes.shared-writes). Either way the
binding reads the value assigned, as the copy model's write of the whole does.
-/

namespace Stilt.Sharing

open InPlace (Ref)

/-- After `evacuate` of a binding's home, skipping the binding, no other binding's part overlaps
the home. -/
theorem Evacuated.apart_home {fr : Copy.Frame} {s s' : State} (h : AgreesAll fr s) {x : Name}
    {e : Entry} {i : Nat} (hi : s.env.findIdx? (·.1 == x) = some i) (hx : s.env.lookup x = some e)
    {env' : List (Name × Entry)} (hE : Evacuated e.home i s s' 0 s.env env') :
    ∀ ye ∈ env', ye.2 ≠ e → overlaps e.home ye.2.ref = false := by
  have hxe : (x, e) ∈ s.env := List.mem_of_getElem? (lookup_of_findIdx? hi hx)
  have hs : ∀ j ye, s.env[j]? = some ye → j + 0 = i → ye.2 = e := fun j ye hj hji => by
    rw [Nat.add_zero] at hji
    subst hji
    rw [lookup_of_findIdx? hi hx, Option.some.injEq] at hj
    rw [← hj]
  intro ye hye hne
  rcases hE.unmoved hs ye hye hne with ⟨ya, hya, he, hany⟩ | ⟨ha', hl⟩
  · rw [← he]
    cases hr : ya.2.alias with
    | some r =>
      rw [hr] at hany
      simpa [Entry.ref, hr] using hany
    | none =>
      have hne' : (x, e) ≠ ya := fun heq => hne (by rw [← he, ← heq])
      simpa [Entry.ref, hr] using homes_apart_of_mem h.homes hxe hya hne'
  · have hr : ye.2.ref = ye.2.home := by simp [Entry.ref, ha']
    rw [hr]
    exact (overlaps_comm _ _).trans
      (overlaps_fresh (Nat.lt_of_lt_of_le (h.has (x, e) hxe).1 hl))

/-- Replacing the first binding of `x` with one that reads `w`, every other binding reading what
it read, gives a state that holds the frame with `x` written whole. -/
theorem Holds.set_first {st st' : Array Value} {x : Name} {e e' : Entry} {w : Value}
    (h₁ : deref ⟨[], st'⟩ e'.ref [] = .ok w) :
    ∀ {fr : Copy.Frame} {env : List (Name × Entry)} {i : Nat}, Holds st fr env →
      env.findIdx? (·.1 == x) = some i → env.lookup x = some e →
      env.Pairwise (fun a b => overlaps a.2.home b.2.home = false) →
      (∀ ye ∈ env, ye.2 ≠ e → deref ⟨[], st'⟩ ye.2.ref [] = deref ⟨[], st⟩ ye.2.ref []) →
      Holds st' (assocSet fr x w) (env.set i (x, e'))
  | [], [], _, _, hi, _, _, _ => by simp at hi
  | (z, v) :: fr, (_, f) :: env, i, ⟨rfl, hd, h⟩, hi, hl, hp, ho => by
    rw [List.pairwise_cons] at hp
    have hrest : ∀ ye ∈ env, ye.2 ≠ e → deref ⟨[], st'⟩ ye.2.ref [] = deref ⟨[], st⟩ ye.2.ref [] :=
      fun ye hye => ho ye (List.mem_cons_of_mem _ hye)
    by_cases hx : z = x
    · subst hx
      simp only [List.findIdx?_cons, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hi
      subst hi
      rw [List.lookup_cons_self, Option.some.injEq] at hl
      subst hl
      simp only [assocSet, ↓reduceIte, List.set_cons_zero]
      exact ⟨rfl, h₁, Holds.alike h (ReadsAlike.same fun ye hye =>
        hrest ye hye (fun he => ne_of_apart (hp.1 ye hye) he.symm))⟩
    · have hb : (z == x) = false := by simpa using hx
      rw [List.findIdx?_cons, hb] at hi
      simp only [Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at hi
      obtain ⟨j, hj, rfl⟩ := hi
      rw [lookup_cons_ne (Ne.symm hx)] at hl
      have hxz : x ≠ z := Ne.symm hx
      simp only [assocSet, hxz, ↓reduceIte, List.set_cons_succ]
      have hne : f ≠ e := ne_of_apart (b := (x, e)) (hp.1 _ (mem_of_lookup hl))
      exact ⟨rfl, (ho _ List.mem_cons_self hne).trans hd, Holds.set_first h₁ h hj hl hp.2 hrest⟩
  | [], _ :: _, _, h, _, _, _, _ => h.elim
  | _ :: _, [], _, h, _, _, _, _ => h.elim

/-- Replacing a binding with one of the same home keeps the homes apart. -/
theorem pairwise_set_home {b : Name × Entry} :
    ∀ {env : List (Name × Entry)} {i : Nat} {a : Name × Entry}, env[i]? = some a →
      b.2.home = a.2.home → env.Pairwise (fun c d => overlaps c.2.home d.2.home = false) →
      (env.set i b).Pairwise (fun c d => overlaps c.2.home d.2.home = false)
  | [], _, _, ha, _, _ => by simp at ha
  | c :: env, 0, a, ha, hb, hp => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
    subst ha
    rw [List.pairwise_cons] at hp
    rw [List.set_cons_zero, List.pairwise_cons]
    exact ⟨fun d hd => by rw [hb]; exact hp.1 d hd, hp.2⟩
  | c :: env, i + 1, a, ha, hb, hp => by
    simp only [List.getElem?_cons_succ] at ha
    rw [List.pairwise_cons] at hp
    rw [List.set_cons_succ, List.pairwise_cons]
    refine ⟨fun d hd => ?_, pairwise_set_home ha hb hp.2⟩
    rcases List.mem_or_eq_of_mem_set hd with hd | rfl
    · exact hp.1 d hd
    · rw [hb]
      exact hp.1 a (List.mem_of_getElem? ha)

/-- A state follows from another whose store it grows when each path of its bindings lies below
one of the other's, or past its store. -/
theorem Follows.of_paths {s s' : State} (hg : Grows s.store s'.store)
    (hm : ∀ P ∈ s'.paths, P.Under s.paths ∨ ∀ i q, P = .index i :: q → s.store.size ≤ i)
    (hk : Kept s s') : Follows s s' :=
  ⟨Evolves.grows hg, fun P hP i q hq hi => (hm P hP).resolve_right fun h => by
    have := h i q hq
    omega, hk⟩

/-- Replacing a binding with one of the same name keeps the frame's names. -/
theorem map_fst_set {x : Name} {e' : Entry} :
    ∀ {env : List (Name × Entry)} {i : Nat} {e : Entry}, env[i]? = some (x, e) →
      (env.set i (x, e')).map Prod.fst = env.map Prod.fst
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp
  | _ :: env, i + 1, _, h => by
    simp only [List.getElem?_cons_succ] at h
    simp [map_fst_set h]

/-- An assignment that redirects a local of a copy-on-write type to the place `r`, which reads
the value assigned (modes.copies). -/
theorem AgreesAll.redirect {fr : Copy.Frame} {s : State} (h : AgreesAll fr s) (hsh : AllShared s)
    {w : Value} (hw : w.Safe) {x : Name} {e : Entry} {i : Nat} {r : Ref}
    (hi : s.env.findIdx? (·.1 == x) = some i) (hx : s.env.lookup x = some e)
    (hinout : e.inout = false) (hr : deref s r [] = .ok w) (hu : r.toPath.Under s.paths) :
    AgreesAll (assocSet fr x w) { s with env := s.env.set i (x, { e with alias := some r }) } ∧
      AllShared { s with env := s.env.set i (x, { e with alias := some r }) } ∧
      Follows s { s with env := s.env.set i (x, { e with alias := some r }) } := by
  have hxi := lookup_of_findIdx? hi hx
  have hxe : (x, e) ∈ s.env := List.mem_of_getElem? hxi
  have hhome : e.home.path = [] :=
    (hsh.homes (x, e) hxe).resolve_right fun ⟨_, hio⟩ => by simp [hinout] at hio
  have hlen : (assocSet fr x w).length = (s.env.set i (x, { e with alias := some r })).length := by
    rw [List.length_set, ← List.length_map (f := Prod.fst), map_fst_assocSet, h.align,
      List.length_map]
  refine ⟨⟨by simp, by rw [map_fst_assocSet, h.align, map_fst_set hxi], ?_, fun yb hyb => ?_,
      pairwise_set_home hxi rfl h.homes, fun xv hxv => ?_⟩,
    ⟨fun yb hyb => ?_, fun yb hyb => ?_, fun yb hyb => ?_⟩,
    Follows.of_paths (Grows.refl _) (fun P hP => .inl ?_)
      (Kept.set rfl hxi rfl fun hin => by simp [hinout] at hin)⟩
  · rw [Moving.keep_all (by simp) (by simp), Moving.keep_all (by simp) (by simp [hlen])]
    have hr' : deref ⟨[], s.store⟩ r [] = .ok w := hr
    exact Holds.set_first (by simpa [Entry.ref] using hr') h.holds_all hi hx h.homes
      fun _ _ _ => rfl
  · rcases List.mem_or_eq_of_mem_set hyb with hyb | rfl
    · exact h.has yb hyb
    · have hhas := has_of_deref hr
      exact ⟨(h.has (x, e) hxe).1, by simpa [Entry.ref, State.Has] using hhas⟩
  · rcases mem_assocSet hxv with hxv | hxv
    · exact h.safe xv hxv
    · rw [hxv]
      exact hw
  · rcases List.mem_or_eq_of_mem_set hyb with hyb | rfl
    · exact hsh.shared yb hyb
    · exact hsh.shared (x, e) hxe
  · rcases List.mem_or_eq_of_mem_set hyb with hyb | rfl
    · exact hsh.homes yb hyb
    · exact .inl hhome
  · rcases List.mem_or_eq_of_mem_set hyb with hyb | rfl
    · exact hsh.inout yb hyb
    · intro hin
      simp [hinout] at hin
  · obtain ⟨yb, hyb, hP⟩ := List.mem_flatMap.1 hP
    rcases List.mem_or_eq_of_mem_set hyb with hyb | rfl
    · exact ⟨P, List.mem_flatMap.2 ⟨yb, hyb, hP⟩, [], by rw [List.append_nil]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · exact ⟨_, List.mem_flatMap.2 ⟨(x, e), hxe, List.mem_cons_self⟩, [],
          by rw [List.append_nil]⟩
      · simpa [Entry.ref] using hu

/-- Frames with the same names find a name at the same position. -/
theorem findIdx?_of_names {x : Name} :
    ∀ {env env' : List (Name × Entry)}, env'.map Prod.fst = env.map Prod.fst →
      env'.findIdx? (·.1 == x) = env.findIdx? (·.1 == x)
  | [], [], _ => rfl
  | (y, _) :: env, (y', _) :: env', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [List.findIdx?_cons, findIdx?_of_names h]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- What a state of sharing holds of a binding's home when every binding is shared: a value. -/
theorem AllShared.home_reads {fr : Copy.Frame} {s : State} (h : AgreesAll fr s)
    (hsh : AllShared s) {ye : Name × Entry} (hye : ye ∈ s.env) :
    ∃ u, deref s ye.2.home [] = .ok u := by
  rcases hsh.homes ye hye with hp | ⟨ha, -⟩
  · have hlt := (h.has ye hye).1
    unfold deref
    rw [hp, List.nil_append]
    obtain ⟨V, hV⟩ : ∃ V, s.store[ye.2.home.loc]? = some V :=
      ⟨_, Array.getElem?_eq_getElem hlt⟩
    exact ⟨V, by simp [hV, Value.get]⟩
  · have hr : ye.2.ref = ye.2.home := by simp [Entry.ref, ha]
    obtain ⟨v, hv⟩ := h.reads ye hye
    exact ⟨v, hr ▸ hv⟩

/-- The state that a replacing assignment leaves agrees with the frame with the binding written,
every binding still shared. -/
theorem AgreesAll.replaced {fr : Copy.Frame} {s s₂ s' : State} (h : AgreesAll fr s)
    {w : Value} (hw : w.Safe) {x : Name} {e : Entry} {i : Nat} {env₂ : List (Name × Entry)}
    (hxe : (x, e) ∈ s.env) (hE : Evacuated e.home i s s₂ 0 s.env env₂) (hap : HomesApart s₂ env₂)
    (hra : ReadsAlike s.store s₂.store s.env env₂) (hl₂ : env₂.lookup x = some e)
    (hi₂ : env₂.findIdx? (·.1 == x) = some i) (hxi₂ : env₂[i]? = some (x, e))
    (hg : Grows s.store s₂.store)
    (hs' : setAt { s₂ with env := env₂.set i (x, { e with alias := none }) } e.home [] w = .ok s')
    (hwrote : deref ⟨[], s'.store⟩ ({ e with alias := none } : Entry).ref [] = .ok w)
    (hothers : ∀ ye ∈ env₂, ye.2 ≠ e →
      deref ⟨[], s'.store⟩ ye.2.ref [] = deref ⟨[], s₂.store⟩ ye.2.ref []) :
    AgreesAll (assocSet fr x w) s' := by
  have henv := setAt_env hs'
  have hsize := setAt_size hs'
  have hholds : Holds s'.store (assocSet fr x w) s'.env := by
    rw [henv]
    exact Holds.set_first hwrote (Holds.alike h.holds_all hra) hi₂ hl₂ hap.1 hothers
  have hlen : (assocSet fr x w).length = s'.env.length := by
    rw [henv, List.length_set, ← List.length_map (f := Prod.fst), map_fst_assocSet, h.align,
      ← hra.names, List.length_map]
  have hrefs : ∀ yb ∈ env₂, yb.2.ref.loc < s₂.store.size := fun yb hyb => by
    rcases hE.mem_settled yb hyb with ⟨ya, hya, he⟩ | ⟨-, -, -, ha', -, -⟩
    · rw [← he]
      exact State.Has.grows hg (h.has ya hya).2
    · rw [show yb.2.ref = yb.2.home by simp [Entry.ref, ha']]
      exact hap.2 yb hyb
  refine ⟨by simp, by rw [map_fst_assocSet, h.align, henv, map_fst_set hxi₂, hra.names], ?_,
    fun yb hyb => ?_, henv ▸ pairwise_set_home hxi₂ rfl hap.1, fun xv hxv => ?_⟩
  · rw [Moving.keep_all (by simp) (by simp), Moving.keep_all (by simp) (by simp [hlen])]
    exact hholds
  · rw [henv] at hyb
    simp only [State.Has, hsize]
    rcases List.mem_or_eq_of_mem_set hyb with hyb | rfl
    · exact ⟨hap.2 yb hyb, hrefs yb hyb⟩
    · have hlt := Nat.lt_of_lt_of_le (h.has (x, e) hxe).1 hg.size
      exact ⟨hlt, by simpa [Entry.ref] using hlt⟩
  · rcases mem_assocSet hxv with hxv | hxv
    · exact h.safe xv hxv
    · rw [hxv]
      exact hw

/-- Every binding stays shared through a replacing assignment. -/
theorem AllShared.replaced {s s₂ s' : State} (hsh : AllShared s) {x : Name} {e : Entry} {i : Nat}
    {env₂ : List (Name × Entry)} {w : Value} (hxe : (x, e) ∈ s.env)
    (hsh₂ : AllShared { s₂ with env := env₂ })
    (hs' : setAt { s₂ with env := env₂.set i (x, { e with alias := none }) } e.home [] w = .ok s') :
    AllShared s' := by
  refine ⟨fun yb hyb => ?_, fun yb hyb => ?_, fun yb hyb => ?_⟩ <;> rw [setAt_env hs'] at hyb <;>
    rcases List.mem_or_eq_of_mem_set hyb with hyb | rfl
  · exact hsh₂.shared yb hyb
  · exact hsh.shared (x, e) hxe
  · exact hsh₂.homes yb hyb
  · rcases hsh.homes (x, e) hxe with hp | ⟨-, hio⟩
    · exact .inl hp
    · exact .inr ⟨rfl, hio⟩
  · exact hsh₂.inout yb hyb
  · exact fun _ => rfl

/-- The state with every binding that referred into a home settled, and the binding replaced
by one at its home, follows from the first. -/
theorem Follows.replaced {s s₂ : State} {x : Name} {e : Entry} {i : Nat}
    {env₂ : List (Name × Entry)} (hxe : (x, e) ∈ s.env)
    (hE : Evacuated e.home i s { s₂ with env := env₂.set i (x, { e with alias := none }) } 0
      s.env env₂) (hg : Grows s.store s₂.store)
    (hio : ∀ ye ∈ s.env, ye.2.inout = true → ye.2.alias = none) (hxi : env₂[i]? = some (x, e)) :
    Follows s { s₂ with env := env₂.set i (x, { e with alias := none }) } := by
  have hk₁ : Kept s ⟨env₂, s₂.store⟩ := hE.kept hio
  have hk₂ : Kept ⟨env₂, s₂.store⟩ { s₂ with env := env₂.set i (x, { e with alias := none }) } :=
    Kept.set rfl hxi rfl fun hin => by
      have ha := hio (x, e) hxe hin
      cases e
      simp_all
  refine Follows.of_paths hg (fun P hP => ?_) (hk₁.trans hk₂)
  obtain ⟨yb, hyb, hP⟩ := List.mem_flatMap.1 hP
  have hhome : e.home.toPath.Under s.paths :=
    ⟨_, List.mem_flatMap.2 ⟨(x, e), hxe, List.mem_cons_self⟩, [], by rw [List.append_nil]⟩
  rcases List.mem_or_eq_of_mem_set hyb with hyb | rfl
  · rcases hE.mem_settled yb hyb with ⟨ya, hya, he⟩ | ⟨-, -, -, ha', hl, -⟩
    · exact .inl ⟨P, List.mem_flatMap.2 ⟨ya, hya, he ▸ hP⟩, [], by rw [List.append_nil]⟩
    · refine .inr fun j q hq => ?_
      have hr : yb.2.ref = yb.2.home := by simp [Entry.ref, ha']
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · simp only [InPlace.Ref.toPath, List.cons.injEq, Step.index.injEq] at hq
        omega
      · rw [hr] at hq
        simp only [InPlace.Ref.toPath, List.cons.injEq, Step.index.injEq] at hq
        omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · exact .inl hhome
    · exact .inl (by simpa [Entry.ref] using hhome)

/-- The write of a replacing assignment at the binding's home follows. -/
theorem Follows.written {s₂ s' : State} {x : Name} {e : Entry} {i : Nat}
    {env₂ : List (Name × Entry)} {w : Value} (hxi : env₂[i]? = some (x, e))
    (hs' : setAt { s₂ with env := env₂.set i (x, { e with alias := none }) } e.home [] w = .ok s') :
    Follows { s₂ with env := env₂.set i (x, { e with alias := none }) } s' := by
  have hlt : i < env₂.length := (List.getElem?_eq_some_iff.1 hxi).1
  refine ⟨Evolves.setAt hs' ⟨e.home.toPath, List.mem_flatMap.2 ⟨(x, { e with alias := none }),
    List.mem_set hlt _, List.mem_cons_self⟩, [], by simp [InPlace.Ref.at, InPlace.Ref.toPath]⟩,
    fun P hP _ _ _ _ => ⟨P, by rwa [State.paths, setAt_env hs'] at hP, [],
      by rw [List.append_nil]⟩, Kept.same (setAt_env hs')⟩

/-- An assignment that writes the value at the binding's home, after every other binding that
referred into it gets a copy of its own (modes.shared-writes). -/
theorem AgreesAll.replace {fr : Copy.Frame} {s : State} (h : AgreesAll fr s) (hsh : AllShared s)
    {w : Value} (hw : w.Safe) {x : Name} {e : Entry} {i : Nat}
    (hi : s.env.findIdx? (·.1 == x) = some i) (hx : s.env.lookup x = some e) :
    ∃ s₂ env₂ s', evacuate e.home i 0 s s.env = .ok (s₂, env₂) ∧
      setAt { s₂ with env := env₂.set i (x, { e with alias := none }) } e.home [] w = .ok s' ∧
      AgreesAll (assocSet fr x w) s' ∧ AllShared s' ∧ Follows s s' := by
  obtain ⟨s₂, env₂, hev⟩ := evacuate_ok e.home i 0 s s.env h.reads
  obtain ⟨hg, -, hE⟩ := evacuate_spec hev
  let e₀ : Entry := { e with alias := none }
  let s₃ : State := { s₂ with env := env₂.set i (x, e₀) }
  let s₄ : State := { s₂ with env := env₂ }
  have hE₃ : Evacuated e.home i s s₃ 0 s.env env₂ := Evacuated.congr (s₁ := s₂) (s₂ := s₃) rfl hE
  have hE₄ : Evacuated e.home i s s₄ 0 s.env s₄.env := Evacuated.congr (s₁ := s₂) (s₂ := s₄) rfl hE
  have hap := evacuate_apart hev ⟨h.homes, fun ye hye => (h.has ye hye).1⟩
  have hxe : (x, e) ∈ s.env := List.mem_of_getElem? (lookup_of_findIdx? hi hx)
  have hra : ReadsAlike s.store s₃.store s.env env₂ := hE₃.alike fun ye hye => (h.has ye hye).2
  have hl₂ : env₂.lookup x = some e := (hE₃.lookup_skip (by simp [hi])).trans hx
  have hi₂ : env₂.findIdx? (·.1 == x) = some i := (findIdx?_of_names hra.names).trans hi
  have hxi₂ := lookup_of_findIdx? hi₂ hl₂
  obtain ⟨u, hu⟩ := AllShared.home_reads h hsh hxe
  have hu₃ : deref s₃ e.home [] = .ok u := (deref_grows hg (h.has (x, e) hxe).1 []).trans hu
  obtain ⟨s', hs'⟩ := setAt_ok_of_deref hu₃ (show u.set [] w = .ok w from rfl)
  have hfar := hE₃.apart_home h hi hx
  have hwrote : deref ⟨[], s'.store⟩ e₀.ref [] = .ok w := by
    have h0 := deref_setAt_self hs'
    have hat : e.home.at [] = e.home := by
      simp [InPlace.Ref.at]
    rw [hat] at h0
    exact h0
  have hothers : ∀ ye ∈ env₂, ye.2 ≠ e →
      deref ⟨[], s'.store⟩ ye.2.ref [] = deref ⟨[], s₃.store⟩ ye.2.ref [] := fun ye hye hne =>
    deref_setAt_other hs' (overlaps_at (hfar ye hye hne) []) []
  refine ⟨s₂, env₂, s', hev, hs', h.replaced hw hxe hE hap hra hl₂ hi₂ hxi₂ hg hs' hwrote hothers,
    AllShared.replaced hsh hxe (AllShared.evacuated hsh hE₄) hs', ?_⟩
  exact (Follows.replaced hxe hE₃ hg hsh.inout hxi₂).trans (Follows.written hxi₂ hs')

/-- An assignment of the whole of a binding, of the value `w` that the part `r` holds when
`alias? = some r`, when every binding is shared: both models fail alike, or write it, the frame
and the state still agreeing on every binding, every binding still shared, and the state
following from the first (modes.copies and modes.shared-writes). -/
theorem AgreesAll.assignWhole {fr : Copy.Frame} {s : State} (h : AgreesAll fr s)
    (hsh : AllShared s) {w : Value} (hw : w.Safe) (x : Name) {alias? : Option Ref}
    (ha : ∀ r, alias? = some r → deref s r [] = .ok w ∧ r.toPath.Under s.paths) :
    (∃ f, Copy.write fr x [] w = .error f ∧ Sharing.assignWhole s x w alias? = .error f) ∨
      ∃ fr' s', Copy.write fr x [] w = .ok fr' ∧ Sharing.assignWhole s x w alias? = .ok s' ∧
        AgreesAll fr' s' ∧ AllShared s' ∧ Follows s s' := by
  rcases h.holds_all.lookup x with ⟨h₁, h₂⟩ | ⟨v, e, h₁, h₂, -⟩
  · refine .inl ⟨.stuck, by simp [Copy.write, h₁], ?_⟩
    unfold Sharing.assignWhole
    rw [h₂]
    cases s.env.findIdx? (·.1 == x) <;> rfl
  obtain ⟨i, hi⟩ := findIdx?_of_lookup h₂
  have hcw : Copy.write fr x [] w = .ok (assocSet fr x w) := by
    simp only [Copy.write, h₁]
    rfl
  obtain ⟨s₂, env₂, s', hev, hs', hA, hS, hF⟩ := h.replace hsh hw hi h₂
  have hrep : Sharing.assignWhole.replace s x w i e = .ok s' := by
    unfold Sharing.assignWhole.replace
    rw [hev]
    exact hs'
  cases halias : alias? with
  | none =>
    refine .inr ⟨_, s', hcw, ?_, hA, hS, hF⟩
    simp only [Sharing.assignWhole, hi, h₂]
    exact hrep
  | some r =>
    by_cases hc : (e.cow && !e.inout) = true
    · obtain ⟨hr, hu⟩ := ha r halias
      have hinout : e.inout = false := by simp_all
      obtain ⟨hA', hS', hF'⟩ := h.redirect hsh hw hi h₂ hinout hr hu
      refine .inr ⟨_, _, hcw, ?_, hA', hS', hF'⟩
      simp only [Sharing.assignWhole, hi, h₂, hc, ↓reduceIte]
    · refine .inr ⟨_, s', hcw, ?_, hA, hS, hF⟩
      simp only [Sharing.assignWhole, hi, h₂, hc, Bool.false_eq_true, ↓reduceIte]
      exact hrep

end Stilt.Sharing
