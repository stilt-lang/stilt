import Stilt.Paths

/-!
# Writes

The laws of writing along paths that in-place agreement needs, beyond those of
`Stilt.Paths`: a write succeeds wherever a read does, a write along an
extension of a path is a write of the path's part, and of two writes to one
path the second wins.

The last law is about sequences of writes. A sequence of writes below
disjoint paths, each of which can be read, comes to one write to each path of
the part it ends with. In place, a callee writes through its `inout`
parameters in whatever order its body runs; copy-in, copy-out writes each
parameter's final value back once, in the order values.inout-argument-order gives. This
law makes the two agree.
-/

namespace Stilt

namespace Path

theorem Disjoint.symm {p q : Path} (h : p.Disjoint q) : q.Disjoint p := by
  induction p generalizing q with
  | nil => cases q <;> simp [Path.Disjoint] at h
  | cons s p ih =>
    cases q with
    | nil => simp [Path.Disjoint] at h
    | cons t q =>
      simp only [Path.Disjoint] at h ⊢
      rcases h with h | h
      · exact .inl (Ne.symm h)
      · exact .inr (ih h)

theorem not_disjoint_self (p : Path) : ¬p.Disjoint p := by
  induction p with
  | nil => simp [Path.Disjoint]
  | cons s p ih => simpa [Path.Disjoint] using ih

/-- Extending two disjoint paths keeps them disjoint. -/
theorem Disjoint.append {p q : Path} (h : p.Disjoint q) (a b : Path) :
    (p ++ a).Disjoint (q ++ b) := by
  induction p generalizing q with
  | nil => cases q <;> simp [Path.Disjoint] at h
  | cons s p ih =>
    cases q with
    | nil => simp [Path.Disjoint] at h
    | cons t q =>
      simp only [Path.Disjoint, List.cons_append] at h ⊢
      rcases h with h | h
      · exact .inl h
      · exact .inr (ih h)

/-- Disjoint paths below a common prefix are disjoint. -/
theorem Disjoint.prefix (p : Path) {a b : Path} (h : a.Disjoint b) :
    (p ++ a).Disjoint (p ++ b) := by
  induction p with
  | nil => exact h
  | cons s p ih => exact .inr ih

/-- Two different paths of a list whose paths are pairwise disjoint are
disjoint. -/
theorem disjoint_of_mem {Ps : List Path} (hd : Ps.Pairwise Path.Disjoint) {P Q : Path}
    (hP : P ∈ Ps) (hQ : Q ∈ Ps) (hPQ : P ≠ Q) : P.Disjoint Q := by
  induction Ps with
  | nil => simp at hP
  | cons R Ps ih =>
    rw [List.pairwise_cons] at hd
    rcases List.mem_cons.1 hP with hPR | hP' <;> rcases List.mem_cons.1 hQ with hQR | hQ'
    · exact absurd (hPR.trans hQR.symm) hPQ
    · exact hPR ▸ hd.1 Q hQ'
    · exact hQR ▸ (hd.1 P hP').symm
    · exact ih hd.2 hP' hQ'

/-- `p` extends one of the paths `Ps`. -/
def Under (Ps : List Path) (p : Path) : Prop := ∃ P ∈ Ps, ∃ q, p = P ++ q

end Path

namespace Value

/-- A write succeeds wherever a read does. -/
theorem set_ok_of_get {v u : Value} {p : Path} (h : v.get p = .ok u) (w : Value) :
    ∃ v', v.set p w = .ok v' := by
  induction p generalizing v with
  | nil => exact ⟨w, rfl⟩
  | cons s p ih =>
    cases s with
    | field f =>
      cases v with
      | record R fields =>
        simp only [get] at h
        split at h
        · rename_i x hx
          obtain ⟨x', hx'⟩ := ih h
          exact ⟨.record R (assocSet fields f x'), by simp [set, hx, hx', Functor.map, Except.map]⟩
        · cases h
      | _ => cases h
    | index i =>
      cases v with
      | list vs =>
        simp only [get] at h
        split at h
        · rename_i x hx
          obtain ⟨x', hx'⟩ := ih h
          exact ⟨.list (vs.set i.toNat x'), by simp [set, hx, hx', Functor.map, Except.map]⟩
        · cases h
      | _ => cases h

/-- Of two writes to one path, the second wins. -/
theorem set_set_self {v a b v₁ : Value} {p : Path} (h : v.set p a = .ok v₁) :
    v₁.set p b = v.set p b := by
  induction p generalizing v v₁ with
  | nil =>
    cases h
    rfl
  | cons s p ih =>
    cases s with
    | field f =>
      cases v with
      | record R fields =>
        simp only [set] at h
        split at h
        · rename_i x hx
          cases hx' : x.set p a with
          | error e => simp [hx', Functor.map, Except.map] at h
          | ok x' =>
            simp only [hx', Functor.map, Except.map, Except.ok.injEq] at h
            subst h
            have hsome : (fields.lookup f).isSome = true := by simp [hx]
            simp [set, lookup_assocSet_self _ _ _ hsome, hx, ih hx', assocSet_assocSet_self]
        · cases h
      | _ => cases h
    | index i =>
      cases v with
      | list vs =>
        simp only [set] at h
        split at h
        · rename_i x hx
          cases hx' : x.set p a with
          | error e => simp [hx', Functor.map, Except.map] at h
          | ok x' =>
            simp only [hx', Functor.map, Except.map, Except.ok.injEq] at h
            subst h
            simp [set, elemAt?_set_self hx, hx, ih hx', List.set_set]
        · cases h
      | _ => cases h

/-- Writing along an extension of a path is writing the path's part: reading
it, writing along the rest of the extension, and writing back what that
gives. -/
theorem set_append (v : Value) (p q : Path) (w : Value) :
    v.set (p ++ q) w = (v.get p).bind fun u => (u.set q w).bind fun u' => v.set p u' := by
  induction p generalizing v with
  | nil =>
    show v.set q w = (v.set q w).bind fun u' => .ok u'
    cases v.set q w <;> rfl
  | cons s p ih =>
    cases s with
    | field f =>
      cases v with
      | record R fields =>
        simp only [List.cons_append, set, get]
        split
        · rename_i x hx
          rw [ih x]
          cases x.get p with
          | error e => rfl
          | ok u =>
            simp only [Except.bind]
            cases u.set q w with
            | error e => rfl
            | ok u' => simp
        · rfl
      | _ => rfl
    | index i =>
      cases v with
      | list vs =>
        simp only [List.cons_append, set, get]
        split
        · rename_i x hx
          rw [ih x]
          cases x.get p with
          | error e => rfl
          | ok u =>
            simp only [Except.bind]
            cases u.set q w with
            | error e => rfl
            | ok u' => simp
        · rfl
      | _ => rfl

/-- Writes each part of a list in turn, the first first. -/
def setSeq (v : Value) : List (Path × Value) → Except Fault Value
  | [] => .ok v
  | (p, w) :: W => (v.set p w).bind fun v' => v'.setSeq W

theorem setSeq_append (v : Value) (W₁ W₂ : List (Path × Value)) :
    v.setSeq (W₁ ++ W₂) = (v.setSeq W₁).bind (·.setSeq W₂) := by
  induction W₁ generalizing v with
  | nil => rfl
  | cons pw W₁ ih =>
    obtain ⟨p, w⟩ := pw
    simp only [List.cons_append, setSeq]
    cases v.set p w with
    | error e => rfl
    | ok v' => exact ih v'

/-- Writing each path the part it holds changes nothing. -/
theorem setSeq_self {v : Value} :
    ∀ {L : List (Path × Value)}, (∀ pw ∈ L, v.get pw.1 = .ok pw.2) → v.setSeq L = .ok v
  | [], _ => rfl
  | (p, w) :: L, h => by
    have hp : v.set p w = .ok v := set_of_get (h (p, w) (List.mem_cons_self ..))
    simp only [setSeq, hp]
    exact setSeq_self fun pw hpw => h pw (List.mem_cons_of_mem _ hpw)

/-- A write to one of a list of disjoint paths is lost under a sequence of
writes that writes each of them. -/
theorem setSeq_absorb :
    ∀ {L : List (Path × Value)} {P : Path} {v v₁ c r : Value},
      (L.map Prod.fst).Pairwise Path.Disjoint → P ∈ L.map Prod.fst → v.set P c = .ok v₁ →
      v₁.setSeq L = .ok r → v.setSeq L = .ok r
  | [], _, _, _, _, _, _, hP, _, _ => by simp at hP
  | (Q, y) :: L, P, v, v₁, c, r, hd, hP, h, hr => by
    simp only [setSeq] at hr ⊢
    cases h₂ : v₁.set Q y with
    | error e => simp [h₂, Except.bind] at hr
    | ok v₂ =>
      simp only [h₂, Except.bind] at hr
      simp only [List.map_cons, List.pairwise_cons] at hd
      by_cases hPQ : P = Q
      · subst hPQ
        rw [← set_set_self h, h₂]
        exact hr
      · have hPL : P ∈ L.map Prod.fst := by simpa [hPQ] using hP
        obtain ⟨v₁', h₁', h₂'⟩ := set_set_disjoint (hd.1 P hPL).symm h h₂
        rw [h₁']
        exact setSeq_absorb hd.2 hPL h₂' hr

/-- The parts of a value at paths it can read. -/
theorem exists_parts {v : Value} :
    ∀ {Ps : List Path}, (∀ P ∈ Ps, ∃ u, v.get P = .ok u) →
      ∃ L : List (Path × Value), L.map Prod.fst = Ps ∧ ∀ pw ∈ L, v.get pw.1 = .ok pw.2
  | [], _ => ⟨[], rfl, by simp⟩
  | P :: Ps, h => by
    obtain ⟨u, hu⟩ := h P (List.mem_cons_self ..)
    obtain ⟨L, hL, hv⟩ := exists_parts fun Q hQ => h Q (List.mem_cons_of_mem _ hQ)
    refine ⟨(P, u) :: L, by simp [hL], ?_⟩
    intro pw hpw
    rcases List.mem_cons.1 hpw with rfl | hpw
    · exact hu
    · exact hv pw hpw

/-- A write to one of disjoint paths keeps every one of them readable. -/
theorem get_ok_of_set_below {Ps : List Path} (hd : Ps.Pairwise Path.Disjoint) {P : Path}
    (hP : P ∈ Ps) {v v₁ u' : Value} (hset : v.set P u' = .ok v₁)
    (hv : ∀ Q ∈ Ps, ∃ u, v.get Q = .ok u) : ∀ Q ∈ Ps, ∃ u, v₁.get Q = .ok u := by
  intro Q hQ
  by_cases hPQ : P = Q
  · subst hPQ
    exact ⟨u', get_of_set hset⟩
  · rw [get_of_set_disjoint (Path.disjoint_of_mem hd hP hQ hPQ) hset]
    exact hv Q hQ

/-- **Writes below disjoint paths.** A sequence of writes, each below one of
the disjoint paths `Ps`, from a value that can read each of them, ends where
one write to each path of the part it ends with ends. -/
theorem setSeq_canon {Ps : List Path} (hd : Ps.Pairwise Path.Disjoint) :
    ∀ {W : List (Path × Value)} {v v' : Value}, (∀ P ∈ Ps, ∃ u, v.get P = .ok u) →
      (∀ pw ∈ W, pw.1.Under Ps) → v.setSeq W = .ok v' →
      ∃ L : List (Path × Value), L.map Prod.fst = Ps ∧ (∀ pw ∈ L, v'.get pw.1 = .ok pw.2) ∧
        v.setSeq L = .ok v'
  | [], v, v', hv, _, h => by
    cases h
    obtain ⟨L, hL, hget⟩ := exists_parts hv
    exact ⟨L, hL, hget, setSeq_self hget⟩
  | (p, a) :: W, v, v', hv, hW, h => by
    obtain ⟨P, hP, q, rfl⟩ := hW (p, a) (List.mem_cons_self ..)
    obtain ⟨u, hu⟩ := hv P hP
    simp only [setSeq, set_append, hu, Except.bind] at h
    cases hu' : u.set q a with
    | error e => simp [hu'] at h
    | ok u' =>
      cases hset : v.set P u' with
      | error e => simp [hu', hset] at h
      | ok v₁ =>
        simp only [hu', hset] at h
        obtain ⟨L, hL, hget, hseq⟩ := setSeq_canon hd (get_ok_of_set_below hd hP hset hv)
          (fun pw hpw => hW pw (List.mem_cons_of_mem _ hpw)) h
        exact ⟨L, hL, hget, setSeq_absorb (by rw [hL]; exact hd) (by rw [hL]; exact hP) hset hseq⟩

end Value

end Stilt
