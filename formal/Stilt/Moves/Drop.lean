import Stilt.Moves.Kills
import Stilt.Moves.Relation

/-!
# Ending several bindings

A call ends each variable it passes at its last use when it starts (values.passing-values). `killAll` ends their newest bindings in a mask, and `dropAll` leaves
them out of a frame or an environment.
-/

namespace Stilt.Moving

open InPlace

/-- Ends the newest binding of each variable of `D`. -/
def killAll (D : List Name) (m : List Bool) (ns : List Name) : List Bool :=
  D.foldl (fun m x => kill x m ns) m

/-- Leaves out the newest entry of each variable of `D`. -/
def dropAll {β : Type} (D : List Name) (l : List (Name × β)) : List (Name × β) :=
  D.foldl (fun l x => dropName x l) l

variable {β : Type}

theorem lookup_dropName_ne {x y : Name} (h : y ≠ x) :
    ∀ l : List (Name × β), (dropName x l).lookup y = l.lookup y
  | [] => rfl
  | (z, b) :: l => by
    unfold dropName
    split
    · rename_i hz
      subst hz
      rw [lookup_cons_ne h]
    · by_cases hy : y = z
      · subst hy
        simp
      · rw [lookup_cons_ne hy, lookup_cons_ne hy, lookup_dropName_ne h l]

theorem sublist_dropAll : ∀ (D : List Name) (l : List (Name × β)), (dropAll D l).Sublist l
  | [], _ => List.Sublist.refl _
  | x :: D, l => (sublist_dropAll D (dropName x l)).trans (sublist_dropName x l)

theorem lookup_dropAll {y : Name} : ∀ {D : List Name}, y ∉ D →
    ∀ l : List (Name × β), (dropAll D l).lookup y = l.lookup y
  | [], _, _ => rfl
  | x :: D, h, l => by
    simp only [List.mem_cons, not_or] at h
    show (dropAll D (dropName x l)).lookup y = _
    rw [lookup_dropAll h.2, lookup_dropName_ne h.1]

theorem length_killAll : ∀ (D : List Name) (m : List Bool) (ns : List Name),
    (killAll D m ns).length = m.length
  | [], _, _ => rfl
  | x :: D, m, ns => (length_killAll D (kill x m ns) ns).trans (length_kill x m ns)

theorem LiveAt.killAll {z : Name} : ∀ {D : List Name} {m : List Bool} {ns : List Name},
    LiveAt z m ns → z ∉ D → LiveAt z (Moving.killAll D m ns) ns
  | [], _, _, h, _ => h
  | x :: D, _, _, h, hz => by
    simp only [List.mem_cons, not_or] at hz
    exact LiveAt.killAll (m := Moving.kill x _ _) (LiveAt.kill h hz.1) hz.2

/-- Ending live bindings in a mask leaves them out of what it keeps. -/
theorem keep_killAll : ∀ {D : List Name}, D.Nodup → ∀ {m : List Bool} {l : List (Name × β)},
    m.length = l.length → (∀ x ∈ D, LiveAt x m (l.map Prod.fst)) →
    keep (killAll D m (l.map Prod.fst)) l = dropAll D (keep m l)
  | [], _, _, _, _, _ => rfl
  | x :: D, hnd, m, l, hl, hlive => by
    rw [List.nodup_cons] at hnd
    show keep (killAll D (kill x m _) _) l = dropAll D (dropName x (keep m l))
    rw [keep_killAll hnd.2 (by rw [length_kill]; exact hl) fun z hz =>
      (hlive z (List.mem_cons_of_mem _ hz)).kill (fun h => hnd.1 (by rw [← h]; exact hz)),
      keep_kill hl (hlive x List.mem_cons_self)]

theorem Kills.killAll {L X : Live} : ∀ {D : List Name}, (∀ x ∈ D, L.mem x = false ∧ X.mem x = true) →
    ∀ (m : List Bool) (ns : List Name), m.length = ns.length → Kills L X m (killAll D m ns) ns
  | [], _, m, ns, hl => Kills.refl L X m ns hl
  | x :: D, h, m, ns, hl => by
    obtain ⟨h₁, h₂⟩ := h x List.mem_cons_self
    exact (Kills.kill h₁ h₂ m ns hl).trans
      (Kills.killAll (fun z hz => h z (List.mem_cons_of_mem _ hz)) _ ns (by rw [length_kill]; exact hl))
      (Live.Sub.refl L)

/-- Leaving out bindings keeps the agreement of the others. -/
theorem Agrees.dropAll : ∀ (D : List Name) {fr : Copy.Frame} {s : State}, Agrees fr s →
    Agrees (Moving.dropAll D fr) ⟨Moving.dropAll D s.env, s.store⟩
  | [], _, _, h => h
  | x :: D, _, _, h => Agrees.dropAll D (h.drop x)

/-- What is left once the newest binding of `x` is out reaches parts disjoint
from the reference of `x`. -/
theorem disjoint_dropAll {x : Name} {r : Ref} : ∀ {D : List Name}, x ∈ D →
    ∀ {env : List (Name × Ref)}, env.Pairwise (fun a b => a.2.Disjoint b.2) →
      env.lookup x = some r → ∀ e ∈ Moving.dropAll D env, e.2.Disjoint r
  | [], h, _, _, _ => by simp at h
  | d :: D, h, env, hp, hl => by
    show ∀ e ∈ Moving.dropAll D (dropName d env), _
    by_cases hd : d = x
    · subst hd
      exact fun e he => disjoint_dropName hp hl e ((sublist_dropAll D _).subset he)
    · have hx : x ∈ D := (List.mem_cons.1 h).resolve_left (Ne.symm hd)
      exact disjoint_dropAll hx (hp.sublist (sublist_dropName d env))
        (by rw [lookup_dropName_ne (Ne.symm hd)]; exact hl)

end Stilt.Moving
