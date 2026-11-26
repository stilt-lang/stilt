import Stilt.Moves.Back

/-!
# Calls

A call keeps the simulation. It starts as in place, from the caller's live
bindings, with each last use passed as its variable's place
(`Stilt.Moves.Start`); its body runs with every binding live; and it ends
with the write-back of `inout` arguments and the end of the variables whose
last use it passed (`Stilt.Moves.Leave`).
-/

namespace Stilt.Moving

open InPlace

/-- What a call needs of its caller once its arguments are evaluated: the
places it passes and the variables it hands over are live and mentioned by
the call, each last use holds its value and is mentioned by nothing after the
call, and the places don't overlap. -/
structure Ready (L X : Live) (m : List Bool) (fr : Copy.Frame) (s : State)
    (bound : List (Name × Passed)) : Prop where
  agrees : MAgrees m fr s
  places : ∀ y x p, (y, Passed.place x p) ∈ bound → LiveAt x m (names fr) ∧ X.mem x = true
  moved : ∀ y x v, (y, Passed.moved x v) ∈ bound →
    LiveAt x m (names fr) ∧ fr.lookup x = some v ∧ X.mem x = true ∧ L.mem x = false
  compat : ((bound.map Moving.handOver).map Prod.snd).Pairwise Passed.Compat
  nodup : (movedOf (bound.map Prod.snd)).Nodup
  passed : PassedOk (bound.map Prod.snd)

namespace Ready

variable {L X : Live} {m : List Bool} {fr : Copy.Frame} {s : State} {bound : List (Name × Passed)}

theorem places' (h : Ready L X m fr s bound) :
    ∀ y x p, (y, Passed.place x p) ∈ bound.map Moving.handOver → LiveAt x m (names fr) ∧ X.mem x = true := by
  intro y x p hm
  obtain ⟨⟨y', q⟩, hq, he⟩ := List.mem_map.1 hm
  cases q with
  | value _ => cases he
  | place x' p' =>
    cases he
    exact h.places _ _ _ hq
  | moved x' v =>
    simp only [Moving.handOver, Prod.mk.injEq, Passed.place.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨h₁, -, h₂, -⟩ := h.moved _ _ v hq
    exact ⟨h₁, h₂⟩

theorem mem_movedOf {x : Name} (hx : x ∈ movedOf (bound.map Prod.snd)) :
    ∃ y v, (y, Passed.moved x v) ∈ bound := by
  obtain ⟨q, hq, he⟩ := List.mem_filterMap.1 hx
  obtain ⟨⟨y, q'⟩, hm, rfl⟩ := List.mem_map.1 hq
  cases q' with
  | moved x' v => cases he; exact ⟨y, v, hm⟩
  | _ => cases he

/-- The caller after the call: the write-back on its frame, its store as the
callee left it, and the variables whose last use the call passed ended, in
any one world whose cells hold values that a run may hold. -/
theorem post (h : Ready L X m fr s bound) {frc : Copy.Frame} {sc : State}
    (hent : Entered ⟨keep m s.env, s.store⟩ (bound.map Moving.handOver) frc sc) {fr' : Copy.Frame}
    {s' : State} (hev : Evolves sc s')
    (hread : ∀ y x p, (y, Passed.place x p) ∈ bound →
      Copy.read fr' y [] = InPlace.read s' y [] ∧ ∀ v, Copy.read fr' y [] = .ok v → VOk v) :
    ∃ fr₂, Copy.frames.leave fr fr' bound = .ok fr₂ ∧
      ∀ w, w.All VOk → Post L X m s (fr₂, w) (⟨s.env, s'.store⟩, w) := by
  let D := movedOf (bound.map Prod.snd)
  have hag := h.agrees
  obtain ⟨frL, hleave, hagL, hevL⟩ := leave_moved hag.agrees hent h.compat hev
    (fun y x p hm => ⟨(hread y x p hm).1, fun v hv => ((hread y x p hm).2 v hv).1⟩) D
    (fun y x v hm => List.mem_filterMap.2 ⟨_, List.mem_map_of_mem hm, rfl⟩)
    (E := sel m X s.env) fun y x p r hm hl => by
      obtain ⟨h₁, h₂⟩ := h.places' y x p hm
      exact mem_sel_of_lookup hag.len_env (hag.liveAt_env h₁)
        (by rw [← hag.lookup_env h₁]; exact hl) h₂
  obtain ⟨fr₂, hfr, hleave', hn⟩ := leave_full hag.len (fun y x p hm => (h.places y x p hm).1) hleave
  have hj : ∀ xv ∈ frL, xv.2.Justified := by
    rw [copy_leave_eq] at hleave
    exact leave_just bound (keep m fr) frL hag.just
      (fun y x p v hm hv => ((hread y x p hm).2 v hv).2) hleave
  have hlen₂ : m.length = fr₂.length := by
    have := congrArg List.length hn
    simp only [names, List.length_map] at this
    rw [hag.len, this]
  have hlive : ∀ x ∈ D, LiveAt x m (names fr₂) := fun x hx => by
    obtain ⟨y, v, hm⟩ := mem_movedOf hx
    rw [hn]
    exact (h.moved y x v hm).1
  have hks : names fr₂ = keys s := hn.trans hag.keys_eq
  have e₁ : keep (killAll D m (keys s)) fr₂ = dropAll D frL := by
    rw [← hks, keep_killAll h.nodup hlen₂ hlive, hleave']
  have e₂ : keep (killAll D m (keys s)) s.env = dropAll D (keep m s.env) :=
    keep_killAll h.nodup hag.len_env fun x hx => by
      have := hlive x hx
      rw [hks] at this
      exact this
  have hle : s.store.length ≤ s'.store.length := by
    obtain ⟨F, hF⟩ := hent.store
    have := Evolves.length_le hev
    simp only [hF, List.length_append] at this
    omega
  refine ⟨fr₂, hfr, fun w hw => ⟨killAll D m (keys s), ⟨⟨?_, hks, ?_, ?_, ?_⟩, rfl, hw⟩,
    Kills.killAll (fun x hx => ?_) m _ (by simp [hag.len_env]), rfl, hevL⟩⟩
  · rw [length_killAll, hlen₂]
  · show Agrees (keep _ fr₂) ⟨keep _ s.env, s'.store⟩
    rw [e₁, e₂]
    exact hagL
  · intro xr hxr
    exact Nat.lt_of_lt_of_le (hag.valid xr hxr) hle
  · intro xv hxv
    rw [e₁] at hxv
    exact hj xv ((sublist_dropAll D frL).subset hxv)
  · obtain ⟨y, v, hm⟩ := mem_movedOf hx
    obtain ⟨-, -, h₁, h₂⟩ := h.moved y x v hm
    exact ⟨h₂, h₁⟩

end Ready

end Stilt.Moving
