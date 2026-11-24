import Stilt.Held.World
import Stilt.Holding

/-!
# What a `when` puts back

However a `when`'s block ends, with a value, a raise, a jump or a panic, the `when` puts
the value each of its names has at that point back in the name's cell and lets the cell
go, and leaves every other cell and its frames as they were (`release_puts_back`,
shared.when). So the cell's value after the `when` is the one its name was left with:
every access to it during the block was an access to the name.
-/

namespace Stilt

variable {τ σ α : Type}

/-- The state an outcome ends in, unless it is a performance on its way to a handler or
it ends with no state. -/
def Outcome.ending? : Outcome σ α → Option σ
  | .done _ s | .raised _ s | .jumped _ s | .panicked _ s => some s
  | .performed .. | .outOfFuel | .stuck => none

/-- The state `s'` is `s` with the value of each name of `cells`, read in `s`, put back in its
cell, held as `held` says, and every other cell and the frames as they were. -/
def Memory.PutBack (F : Frames τ) (held : Bool) (cells : List (Name × Ty × Nat))
    (s s' : τ × World) : Prop :=
  s'.1 = s.1 ∧ (∀ h, h ∉ cells.map Prod.snd → s'.2.cell? h.1 h.2 = s.2.cell? h.1 h.2) ∧
    ∀ x h v, (x, h) ∈ cells → F.read s.1 x [] = .ok v →
      s'.2.cell? h.1 h.2 = (s.2.cell? h.1 h.2).map fun c => { c with value := v, held }

theorem World.cell?_put_ne {w : World} {h h' : Ty × Nat} (hne : h' ≠ h) (v : Value) (held : Bool) :
    (w.put h v held).cell? h'.1 h'.2 = w.cell? h'.1 h'.2 := by
  rw [World.put, World.cell?_modify (f := fun c => { c with value := v, held }) (fun _ => rfl)]
  simp only [ite_eq_right_iff]
  intro he
  exact absurd he hne

theorem World.cell?_put_self {w : World} (h : Ty × Nat) (v : Value) (held : Bool) :
    (w.put h v held).cell? h.1 h.2 = (w.cell? h.1 h.2).map fun c => { c with value := v, held } := by
  rw [World.put, World.cell?_modify (f := fun c => { c with value := v, held }) (fun _ => rfl)]
  simp

/-- Putting back the values of names with distinct cells puts each in its own cell. -/
theorem Memory.putBack_spec (F : Frames τ) (held : Bool) : ∀ (cells : List (Name × Ty × Nat))
    {s s' : τ × World}, (cells.map Prod.snd).Nodup →
      F.withWorld.putBack held cells s = .ok s' → Memory.PutBack F held cells s s'
  | [], _, _, _, h => by
    cases h
    exact ⟨rfl, fun _ _ => rfl, fun _ _ _ hm => nomatch hm⟩
  | (y, c) :: rest, (fr, w), s', hn, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [Memory.putBack] at h
    cases hr : F.withWorld.read (fr, w) y [] with
    | error e => rw [hr] at h; cases h
    | ok v₀ =>
      rw [hr] at h
      obtain ⟨h₁, h₂, h₃⟩ := Memory.putBack_spec F held rest (s := (fr, w.put c v₀ held)) hn.2 h
      refine ⟨h₁, fun h' hm => ?_, fun x h' v hm hx => ?_⟩
      · simp only [List.map_cons, List.mem_cons, not_or] at hm
        rw [h₂ h' hm.2, World.cell?_put_ne hm.1]
      · rcases List.mem_cons.1 hm with he | hm
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          have e : (Except.ok v : Except Fault Value) = .ok v₀ := hx.symm.trans hr
          cases e
          rw [h₂ _ hn.1, World.cell?_put_self]
        · have hne : h' ≠ c := fun he => hn.1 (he ▸ List.mem_map_of_mem hm)
          rw [h₃ x h' v hm hx, World.cell?_put_ne hne]

/-- **What a `when` puts back**: however its block ends, in a state `s` whose frames hold its
names, the `when` ends the same way in a state that is `s` with each name's value put back in
its cell and the cell let go, every other cell and the frames as they were (shared.when). -/
theorem Outcome.release_puts_back (F : Frames τ) {cells : List (Name × Ty × Nat)}
    (hn : (cells.map Prod.snd).Nodup) {o : Outcome (τ × World) α} {s s' : τ × World}
    (hs : o.ending? = some s) (hr : ∀ x h, (x, h) ∈ cells → ∃ v, F.read s.1 x [] = .ok v)
    (hs' : (o.release F.withWorld cells).ending? = some s') : Memory.PutBack F false cells s s' := by
  have hok : ∀ {s₀ : τ × World}, s₀.1 = s.1 → ∀ (rest : List (Name × Ty × Nat)), rest ⊆ cells →
      ∃ s₁, F.withWorld.putBack false rest s₀ = .ok s₁ := by
    intro s₀ h₀ rest hsub
    induction rest generalizing s₀ with
    | nil => exact ⟨_, rfl⟩
    | cons xh rest ih =>
      obtain ⟨x, h⟩ := xh
      obtain ⟨v, hv⟩ := hr x h (hsub List.mem_cons_self)
      obtain ⟨fr, w⟩ := s₀
      cases h₀
      simp only [Memory.putBack]
      rw [show F.withWorld.read (s.1, w) x [] = .ok v from hv]
      exact ih rfl ((List.subset_cons_self _ _).trans hsub)
  obtain ⟨s₁, h₁⟩ := hok rfl cells (List.Subset.refl _)
  have hafter : ∀ {β : Type} (g : τ × World → Outcome (τ × World) β),
      Outcome.after (F.withWorld.putBack false cells) s g = g s₁ := by
    intro β g
    simp [Outcome.after, h₁]
  have hspec := Memory.putBack_spec F false cells hn h₁
  cases o <;> simp only [Outcome.ending?, Option.some.injEq, reduceCtorEq] at hs
  all_goals
    subst hs
    simp only [Outcome.release, hafter, Outcome.ending?, Option.some.injEq] at hs'
    subst hs'
    exact hspec

end Stilt
