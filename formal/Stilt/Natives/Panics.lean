import Stilt.Natives.Kinds

/-!
# The natives panic only where their paragraphs say

Every native of the calculus, on operands whose lengths fit in `i64`, ends with a value, stuck,
or a panic of one of the kinds its paragraph names (`Op.panicKinds`). Where a value may be
missing, the natives give the calculus's list of none or one value instead
(std.no-panics-by-default).
-/

namespace Stilt

namespace PanicsWith

variable {α : Type} {ks : List PanicKind}

/-- `if c then panic k else x`, `k` among the kinds. -/
theorem panicOr {c : Prop} [Decidable c] {k : PanicKind} {x : Except Fault α} (hk : k ∈ ks)
    (hx : PanicsWith ks x) : PanicsWith ks (if c then .error (.panic k) else x) :=
  ite (panic hk) hx

end PanicsWith

/-- The methods of the integer types panic only with the kinds of std.integers: `min`, `max`,
the saturating operations and the counts of bits never do, on operands of their type. -/
theorem IntTy.method_panics (k : IntTy) (m : IntMethod) (a b : Int) :
    PanicsWith m.panicKinds (k.method m a b) := by
  have hk : k.min ≤ k.max := by have := k.min_le_zero; have := k.zero_le_max; omega
  have hb := k.bits_le
  cases m <;> simp only [IntTy.method]
  case abs | gcd | lcm => exact PanicsWith.check_mem _ _ (by simp [IntMethod.panicKinds])
  case pow =>
    exact PanicsWith.ite (PanicsWith.check_mem _ _ (by simp [IntMethod.panicKinds]))
      (PanicsWith.panicOr (by simp [IntMethod.panicKinds])
        (PanicsWith.check_mem _ _ (by simp [IntMethod.panicKinds])))
  case min | max =>
    exact PanicsWith.within _ _ _ fun ha hb => PanicsWith.check_of (by split <;> assumption)
  case saturatingAdd | saturatingSub =>
    refine PanicsWith.check_of ⟨?_, ?_⟩ <;> simp only [Int.max_def, Int.min_def] <;>
      split <;> (try split) <;> omega
  case divEuclid | remEuclid =>
    exact PanicsWith.within _ _ _ fun _ _ => by
      unfold IntTy.euclid
      exact PanicsWith.panicOr (by simp [IntMethod.panicKinds])
        (PanicsWith.panicOr (by simp [IntMethod.panicKinds])
          (PanicsWith.check_mem _ _ (by simp [IntMethod.panicKinds])))
  case countOnes =>
    refine PanicsWith.check_of (i64_contains_le_bits k ?_)
    have := List.countP_le_length (l := List.range k.bits) (p := (k.bitsOf a).testBit)
    simpa using this
  case leadingZeros =>
    have hlt : k.bitsOf a < 2 ^ k.bits := (k.toBits a).isLt
    have h64 : (64 : Int) ≤ IntTy.i64.max := by decide
    have := IntTy.min_le_zero .i64
    refine PanicsWith.check_of ⟨?_, ?_⟩ <;> split
    all_goals first
      | omega
      | (rename_i h0
         have := (Nat.log2_lt h0).2 hlt
         omega)
  case trailingZeros =>
    refine PanicsWith.check_of (i64_contains_le_bits k ?_)
    cases h : (List.range k.bits).find? (k.bitsOf a).testBit with
    | none => simp
    | some j =>
      have := List.mem_range.1 (List.mem_of_find?_eq_some h)
      simp only [Option.getD_some]; omega

/-- What an operation on scalars computes panics only with the kinds of its paragraph, on
strings that fit in `i64`. -/
theorem Op.compute_panics (o : Op) (ss : List Scalar) (hss : ∀ s ∈ ss, s.Fits) :
    PanicsWith o.panicKinds (o.compute ss) := by
  unfold Op.compute
  split
  all_goals first
    | exact PanicsWith.ok _
    | exact PanicsWith.stuck
    | exact PanicsWith.map _ (PanicsWith.orStuck _)
    | exact PanicsWith.ite PanicsWith.stuck (PanicsWith.ok _)
    | skip
  case h_3 => exact PanicsWith.map _ (PanicsWith.check_mem _ _ (by simp [Op.panicKinds]))
  case h_4 o k a b =>
    cases o <;> simp only [IntTy.arith]
    case div =>
      exact PanicsWith.map _ (PanicsWith.within _ _ _ fun _ _ =>
        PanicsWith.panicOr (by simp [Op.panicKinds])
          (PanicsWith.check_mem _ _ (by simp [Op.panicKinds])))
    case rem =>
      exact PanicsWith.map _ (PanicsWith.within _ _ _ fun _ _ =>
        PanicsWith.panicOr (by simp [Op.panicKinds])
          (PanicsWith.ite (PanicsWith.ok _) (PanicsWith.panic (by simp [Op.panicKinds]))))
    all_goals exact PanicsWith.map _ (PanicsWith.check_mem _ _ (by simp [Op.panicKinds]))
  case h_6 =>
    simp only [IntTy.shift]
    exact PanicsWith.map _ (PanicsWith.panicOr (by simp [Op.panicKinds]) (PanicsWith.ok _))
  case h_28 m k a => exact PanicsWith.map _ (IntTy.method_panics k m a 0)
  case h_29 m k a b => exact PanicsWith.map _ (IntTy.method_panics k m a b)
  case h_36 s =>
    have h : Str.Fits s := hss (.str s) (by simp)
    exact PanicsWith.map _ (PanicsWith.check_of (i64_contains h.1))
  case h_38 s a b =>
    simp only [Str.slice]
    exact PanicsWith.map _ (PanicsWith.panicOr (by simp [Op.panicKinds])
      (PanicsWith.ite (PanicsWith.ok _) (PanicsWith.panic (by simp [Op.panicKinds]))))
  case h_41 s =>
    have h : Str.Fits s := hss (.str s) (by simp)
    exact PanicsWith.map _ (PanicsWith.check_of (i64_contains (by have := h.2.1; omega)))
  case h_42 s t =>
    have h : Str.Fits s := hss (.str s) (by simp)
    exact PanicsWith.map _ (PanicsWith.check_of (i64_contains
      (by have := h.2.1; have := Str.count_le s t; omega)))

/-- A scalar read from a value that fits fits. -/
theorem mapM_scalar?_fits : ∀ {vs : List Value} {ss : List Scalar},
    vs.mapM Value.scalar? = some ss → (∀ v ∈ vs, v.Fits) → ∀ s ∈ ss, s.Fits
  | [], ss, h, _, s, hs => by simp at h; subst h; cases hs
  | v :: vs, ss, h, hvs, s, hs => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨t, ht, ts, hts, rfl⟩ := h
    rcases List.mem_cons.1 hs with rfl | hs
    · cases v <;> simp only [Value.scalar?, Option.some.injEq, reduceCtorEq] at ht <;> subst ht <;>
        first | trivial | exact (hvs _ (by simp)).2.2.2 _ rfl
    · exact mapM_scalar?_fits hts (fun w hw => hvs w (by simp [hw])) s hs

/-- An operation on scalars applied to values panics only with the kinds of its paragraph. -/
theorem Op.applyScalars_panics (o : Op) {vs : List Value} (hvs : ∀ v ∈ vs, v.Fits) :
    PanicsWith o.panicKinds (o.applyScalars vs) := by
  unfold Op.applyScalars
  split
  · rename_i ss hss
    exact PanicsWith.map _ (o.compute_panics ss (mapM_scalar?_fits hss hvs))
  · exact PanicsWith.stuck

/-- `onList` of a result that is a value, stuck or a panic of `bounds`. -/
theorem PanicsWith.boundsOr {ks : List PanicKind} (hk : PanicKind.bounds ∈ ks) {c : Prop}
    [Decidable c] (v : Value) : PanicsWith ks (if c then .ok v else .error (.panic .bounds)) :=
  PanicsWith.ite (PanicsWith.ok _) (PanicsWith.panic hk)

/-- The functions of lists panic only with `bounds`, and only `slice`, `insert` and `remove`
(std.lists), on lists and strings whose lengths fit in `i64`. -/
theorem ListOp.apply_panics (l : ListOp) {vs : List Value} (hvs : ∀ v ∈ vs, v.Fits) :
    PanicsWith l.panicKinds (l.apply vs) := by
  unfold ListOp.apply
  split
  all_goals first
    | exact PanicsWith.ok _
    | exact PanicsWith.stuck
    | exact PanicsWith.onList fun _ _ => PanicsWith.ok _
    | skip
  case h_1 u =>
    exact PanicsWith.onList fun xs hxs =>
      PanicsWith.map _ (PanicsWith.check_of (i64_contains ((hvs u (by simp)).1 xs hxs)))
  case h_4 => split <;> first | exact PanicsWith.ok _ | exact PanicsWith.stuck
  case h_5 | h_6 | h_7 =>
    exact PanicsWith.onList fun _ _ => PanicsWith.boundsOr (by simp [ListOp.panicKinds]) _
  case h_12 =>
    exact PanicsWith.onList fun _ _ => by
      split
      · split; exact PanicsWith.ok _
      · exact PanicsWith.stuck
  case h_17 last s sub =>
    split
    · exact PanicsWith.ok _
    · rename_i n hn
      have h := (hvs (.str s) (by simp)).2.2.2 s rfl
      exact PanicsWith.map _ (PanicsWith.check_of (i64_contains
        (by have := Str.find_le hn; have := h.2.2; omega)))
  case h_21 =>
    exact PanicsWith.onList fun _ _ => by
      split
      · exact PanicsWith.ok _
      · exact PanicsWith.stuck

/-- The functions of maps panic only with `missing-key`, and only `m[k]` (std.maps). -/
theorem MapOp.apply_panics (m : MapOp) {vs : List Value} (hvs : ∀ v ∈ vs, v.Fits) :
    PanicsWith m.panicKinds (m.apply vs) := by
  unfold MapOp.apply
  split
  all_goals first
    | exact PanicsWith.ok _
    | exact PanicsWith.stuck
    | exact PanicsWith.onMap fun _ _ _ => PanicsWith.ok _
    | exact PanicsWith.onMap fun _ _ _ => PanicsWith.ite (PanicsWith.ok _) PanicsWith.stuck
    | exact PanicsWith.onMap fun _ _ _ => PanicsWith.onMap fun _ _ _ => PanicsWith.ok _
    | skip
  case h_3 u =>
    exact PanicsWith.onMap fun es d hes =>
      PanicsWith.map _ (PanicsWith.check_of (i64_contains ((hvs u (by simp)).2.1 es d hes)))
  case h_6 =>
    exact PanicsWith.onMap fun _ _ _ => by
      unfold Entries.index
      split
      · exact PanicsWith.ok _
      · exact PanicsWith.ok _
      · exact PanicsWith.panic (by simp [MapOp.panicKinds])

/-- The functions of sets never panic. -/
theorem SetOp.apply_panics (m : SetOp) {vs : List Value} (hvs : ∀ v ∈ vs, v.Fits) :
    PanicsWith [] (m.apply vs) := by
  unfold SetOp.apply
  split
  all_goals first
    | exact PanicsWith.ok _
    | exact PanicsWith.stuck
    | exact PanicsWith.onList fun _ _ => PanicsWith.ok _
    | exact PanicsWith.onSet fun _ _ => PanicsWith.ok _
    | exact PanicsWith.onSet fun _ _ => PanicsWith.onSet fun _ _ => PanicsWith.ok _
    | skip
  case h_3 u =>
    exact PanicsWith.onSet fun ks hks =>
      PanicsWith.map _ (PanicsWith.check_of (i64_contains ((hvs u (by simp)).2.2.1 ks hks)))

/-- Every native applied to values whose lengths fit in `i64` panics only with the kinds its
paragraph names (`Op.panicKinds`). -/
theorem Op.apply_panics (o : Op) {vs : List Value} (hvs : ∀ v ∈ vs, v.Fits) :
    PanicsWith o.panicKinds (o.apply vs) := by
  cases o
  case list l => exact ListOp.apply_panics l hvs
  case map m => exact MapOp.apply_panics m hvs
  case set m => exact (SetOp.apply_panics m hvs).mono (by simp)
  case panic k => exact PanicsWith.panic (by simp [Op.panicKinds])
  case view =>
    simp only [Op.apply]
    split
    · exact PanicsWith.ok _
    · exact (Op.applyScalars_panics .slice hvs).mono (by simp [Op.panicKinds])
    · exact (ListOp.apply_panics .slice hvs).mono (by simp [Op.panicKinds, ListOp.panicKinds])
    · exact PanicsWith.stuck
  all_goals first
    | exact Op.applyScalars_panics _ hvs
    | (simp only [Op.apply]
       first
         | exact PanicsWith.ok _
         | (split <;> first | exact PanicsWith.ok _ | exact PanicsWith.stuck))

/-- Indexing a list, as a value or through a place, panics only with `bounds` (std.lists). -/
theorem Value.get_panics (v : Value) (p : Path) {k : PanicKind}
    (h : v.get p = .error (.panic k)) : k = .bounds := by
  induction p generalizing v with
  | nil => cases v <;> simp [Value.get] at h
  | cons s p ih =>
    cases v <;> cases s <;> simp [Value.get] at h
    case record.field =>
      split at h
      · exact ih _ h
      · cases h
    case list.index =>
      split at h
      · exact ih _ h
      · cases h; rfl

/-- Storing into a list, through a place, panics only with `bounds` (std.lists). -/
theorem Value.set_panics (v : Value) (p : Path) (w : Value) {k : PanicKind}
    (h : v.set p w = .error (.panic k)) : k = .bounds := by
  induction p generalizing v with
  | nil => cases v <;> simp [Value.set] at h
  | cons s p ih =>
    cases v <;> cases s <;> simp [Value.set] at h
    case record.field =>
      split at h
      · rename_i v' _
        cases hs : v'.set p w <;> simp [hs, Functor.map, Except.map] at h
        subst h; exact ih _ hs
      · cases h
    case list.index =>
      split at h
      · rename_i v' _
        cases hs : v'.set p w <;> simp [hs, Functor.map, Except.map] at h
        subst h; exact ih _ hs
      · cases h; rfl

/-- **std.no-panics-by-default**: every native of the calculus, on operands whose lengths fit in
`i64`, in any world, ends with a value, stuck, or a panic of a kind its paragraph names: `bounds`
for an index out of bounds, in `slice`, `insert` and `remove` of a list and `slice` of a string;
a precondition its paragraph states, `utf8-boundary` for a string sliced inside a scalar value
(std.str) and `missing-key` for `m[k]` with no entry and no default (std.maps); `overflow` and
`divide-by-zero` for the operators and the integer methods whose panics their paragraphs name
(numbers.integer-panics and std.integers); and for `panic(msg)`, `unreachable()` and the other
panics written out, `unwrap` and `expect` among them, their own kind. Every other native, the
natives of strings but `slice`, the functions of sets, `min`, `max`, the saturating operations,
the counts of bits, the natives that give an `Option` as a list of none or one value, and the
operations on the world, never panics. The model states the natives' half of the paragraph: a
function written in Stilt panics where its source does. -/
theorem Op.run_panics (o : Op) {vs : List Value} (hvs : ∀ v ∈ vs, v.Fits) (w : World)
    {k : PanicKind} (h : o.run vs w = .error (.panic k)) : k ∈ o.panicKinds := by
  rcases Op.run_error h with h' | h'
  · cases h'
  · exact o.apply_panics hvs k h'

end Stilt
