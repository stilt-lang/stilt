import Stilt.Panics.Writes
import Stilt.Numbers
import Stilt.Maps

/-!
# Facts that tests give

A test gives the code it guards facts about variables (facts.guarding-tests):
`d != 0`, `d > 0` or `d < 0` that `d` isn't zero (facts.divisors), `i >= 0` that
`i` isn't negative, and `i < xs.len()` that `i` is below the length of the list
`xs` holds (facts.guards), each with its mirror, and the negation of a test
gives the facts of the opposite test. A frame meets a list of facts when each
holds of its variables (`Frame.Meets`). Code keeps a fact while it writes none of
its variables, and a binding of one of their names hides it.
-/

namespace Stilt

/-- A key that verification can follow from a test to an access: the name of a
binding, or an integer or Boolean literal (facts.keys). -/
inductive KeyTerm where
  | var (x : Name)
  | int (k : Int)
  | bool (b : Bool)
  deriving DecidableEq

/-- The variables a key reads. -/
def KeyTerm.reads : KeyTerm → List Name
  | .var x => [x]
  | _ => []

/-- The value a key has in a frame. -/
def KeyTerm.value (s : Copy.Frame) : KeyTerm → Option Value
  | .var x => s.lookup x
  | .int k => some (.int k)
  | .bool b => some (.bool b)

/-- The key an expression is, if it is one. -/
def Expr.keyTerm? : Expr → Option KeyTerm
  | .var x => some (.var x)
  | .int k => some (.int k)
  | .bool b => some (.bool b)
  | _ => none

/-- A fact about the values of variables. `longer` is the proof's own: that a
variable holds a list longer than an integer, which a `for` loop over a range up
to the list's length, less a literal, keeps for each of its elements, plus that
literal, while its body doesn't write the list. `atLeast` and `belowBy` are a
range loop's variable's: no less than the range's start, and below the list's
length by more than a literal (facts.range-loops). -/
inductive Known where
  | nonzero (x : Name)
  | nonneg (x : Name)
  | below (x xs : Name)
  | longer (xs : Name) (k : Int)
  | has (m : Name) (k : KeyTerm)
  | atLeast (x : Name) (a : Int)
  | belowBy (x xs : Name) (c : Int)
  deriving DecidableEq

/-- The variables a fact reads. -/
def Known.reads : Known → List Name
  | .nonzero x | .nonneg x => [x]
  | .below x xs => [x, xs]
  | .longer xs _ => [xs]
  | .has m k => m :: k.reads
  | .atLeast x _ => [x]
  | .belowBy x xs _ => [x, xs]

/-- The variables a fact reads only the list length of: the list of `below`,
`longer` and `belowBy`. -/
def Known.lenReads : Known → List Name
  | .below _ xs | .longer xs _ | .belowBy _ xs _ => [xs]
  | _ => []

/-- The variables a fact reads the value of: every other one it reads. -/
def Known.valReads : Known → List Name
  | .below x _ | .belowBy x _ _ => [x]
  | .longer _ _ => []
  | f => f.reads

theorem Known.valReads_sub {f : Known} {x : Name} (h : x ∈ f.valReads) : x ∈ f.reads := by
  cases f <;> simp_all [Known.valReads, Known.reads]

theorem Known.lenReads_sub {f : Known} {x : Name} (h : x ∈ f.lenReads) : x ∈ f.reads := by
  cases f <;> simp_all [Known.lenReads, Known.reads]

/-- Whether a fact holds of a frame. -/
def Known.Holds (s : Copy.Frame) : Known → Prop
  | .nonzero x => ∃ n, s.lookup x = some (.int n) ∧ n ≠ 0
  | .nonneg x => ∃ n, s.lookup x = some (.int n) ∧ 0 ≤ n
  | .below x xs => ∃ n vs, s.lookup x = some (.int n) ∧ s.lookup xs = some (.list vs) ∧ n < vs.length
  | .longer xs k => ∃ vs, s.lookup xs = some (.list vs) ∧ k < vs.length
  | .has m k => ∃ mv v es d, s.lookup m = some mv ∧ k.value s = some v ∧ mv.map? = some (es, d) ∧
      Entries.has v es = true
  | .atLeast x a => ∃ n, s.lookup x = some (.int n) ∧ a ≤ n
  | .belowBy x xs c => ∃ n vs, s.lookup x = some (.int n) ∧ s.lookup xs = some (.list vs) ∧
      n + c < vs.length

/-- Two frames that agree on what a fact reads agree on the fact. -/
theorem Known.holds_of_lookup {f : Known} {s s' : Copy.Frame} (h : ∀ x ∈ f.reads, s'.lookup x = s.lookup x)
    (hf : f.Holds s) : f.Holds s' := by
  cases f <;> simp only [Known.reads, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at h <;> simp only [Known.Holds] at hf ⊢
  · rw [h]; exact hf
  · rw [h]; exact hf
  · rw [h.1, h.2]; exact hf
  · rw [h]; exact hf
  · rename_i m k
    obtain ⟨hm, hk⟩ := h
    have hv : k.value s' = k.value s := by
      cases k <;> simp_all [KeyTerm.value, KeyTerm.reads]
    rw [hm, hv]; exact hf
  · rw [h]; exact hf
  · rw [h.1, h.2]; exact hf

/-- The facts of `G` that read none of `W`. -/
def withoutNames (G : List Known) (W : List Name) : List Known :=
  G.filter fun f => f.reads.all fun x => decide (x ∉ W)

@[simp] theorem mem_withoutNames {G : List Known} {W : List Name} {f : Known} :
    f ∈ withoutNames G W ↔ f ∈ G ∧ ∀ x ∈ f.reads, x ∉ W := by
  simp [withoutNames]

/-- The facts of `G` that read the value of none of `W`, and the length of none of
`L`. -/
def withoutWrites (G : List Known) (W L : List Name) : List Known :=
  G.filter fun f => f.valReads.all (fun x => decide (x ∉ W)) && f.lenReads.all (fun x => decide (x ∉ L))

@[simp] theorem mem_withoutWrites {G : List Known} {W L : List Name} {f : Known} :
    f ∈ withoutWrites G W L ↔ f ∈ G ∧ (∀ x ∈ f.valReads, x ∉ W) ∧ ∀ x ∈ f.lenReads, x ∉ L := by
  simp [withoutWrites]

/-- Facts that read none of `W` read the value of none of `W` and the length of none of
`L`, for `L` within `W`. -/
theorem withoutNames_sub_withoutWrites {G : List Known} {W L : List Name} (hL : L ⊆ W) {f : Known}
    (h : f ∈ withoutNames G W) : f ∈ withoutWrites G W L := by
  obtain ⟨hG, hW⟩ := mem_withoutNames.1 h
  exact mem_withoutWrites.2 ⟨hG, fun x hx => hW x (Known.valReads_sub hx),
    fun x hx hxL => hW x (Known.lenReads_sub hx) (hL hxL)⟩

/-- A fact holds after code that keeps the values it reads, and the lengths of the
lists it reads only the length of. -/
theorem Known.holds_of_keeps {W L : List Name} {f : Known} {s s' : Copy.Frame} (k : Frame.Keeps W L s s')
    (hW : ∀ x ∈ f.valReads, x ∉ W) (hL : ∀ x ∈ f.lenReads, x ∉ L) (hf : f.Holds s) : f.Holds s' := by
  cases f with
  | below x xs =>
    simp only [Known.valReads, Known.lenReads, List.mem_singleton, forall_eq] at hW hL
    obtain ⟨n, vs, hx, hv, hlt⟩ := hf
    obtain ⟨vs', hv', hl⟩ := k.lookup_list hL hv
    exact ⟨n, vs', by rw [k.lookup hW, hx], hv', by omega⟩
  | longer xs c =>
    simp only [Known.lenReads, List.mem_singleton, forall_eq] at hL
    obtain ⟨vs, hv, hlt⟩ := hf
    obtain ⟨vs', hv', hl⟩ := k.lookup_list hL hv
    exact ⟨vs', hv', by omega⟩
  | belowBy x xs c =>
    simp only [Known.valReads, Known.lenReads, List.mem_singleton, forall_eq] at hW hL
    obtain ⟨n, vs, hx, hv, hlt⟩ := hf
    obtain ⟨vs', hv', hl⟩ := k.lookup_list hL hv
    exact ⟨n, vs', by rw [k.lookup hW, hx], hv', by omega⟩
  | _ => exact Known.holds_of_lookup (fun x hx => k.lookup (hW x (by simpa [Known.valReads] using hx))) hf

/-- Each fact of `G` holds of the frame. -/
def Frame.Meets (G : List Known) (s : Copy.Frame) : Prop := ∀ f ∈ G, f.Holds s

namespace Frame.Meets

variable {G G' : List Known} {W : List Name} {s s' : Copy.Frame}

theorem nil (s : Copy.Frame) : Frame.Meets [] s := fun _ h => nomatch h

theorem mono (h : Frame.Meets G s) (hG : G' ⊆ G) : Frame.Meets G' s := fun f hf => h f (hG hf)

theorem append (h : Frame.Meets G s) (h' : Frame.Meets G' s) : Frame.Meets (G ++ G') s :=
  fun f hf => (List.mem_append.1 hf).elim (h f) (h' f)

/-- Code that keeps the variables outside `W` keeps the facts that read none of them. -/
theorem keep {L : List Name} (h : Frame.Meets G s) (k : Frame.Keeps W L s s') :
    Frame.Meets (withoutNames G W) s' :=
  fun f hf => by
    obtain ⟨hG, hW⟩ := mem_withoutNames.1 hf
    exact Known.holds_of_lookup (fun x hx => k.lookup (hW x hx)) (h f hG)

/-- Code that keeps the variables outside `W`, and the lengths of the lists outside
`L`, keeps the facts that read the value of none of `W` and the length of none of `L`. -/
theorem keepLen {L : List Name} (h : Frame.Meets G s) (k : Frame.Keeps W L s s') :
    Frame.Meets (withoutWrites G W L) s' :=
  fun f hf => by
    obtain ⟨hG, hW, hL⟩ := mem_withoutWrites.1 hf
    exact Known.holds_of_keeps k hW hL (h f hG)

/-- A new binding hides the facts that read its name. -/
theorem bind (h : Frame.Meets G s) (x : Name) (v : Value) :
    Frame.Meets (withoutNames G [x]) ((x, v) :: s) := fun f hf => by
  obtain ⟨hG, hx⟩ := mem_withoutNames.1 hf
  refine Known.holds_of_lookup (fun y hy => ?_) (h f hG)
  have : (y == x) = false := by simpa using hx y hy
  simp only [List.lookup_cons, this]

end Frame.Meets

/-- The variable an expression reads, if it is one. -/
def Expr.readVar? : Expr → Option Name
  | .var d => some d
  | _ => none

/-- Whether an expression is the literal `0`. -/
def Expr.isZero : Expr → Bool
  | .int 0 => true
  | _ => false

theorem Expr.eq_of_readVar? {e : Expr} {d : Name} (h : e.readVar? = some d) : e = .var d := by
  cases e <;> simp_all [Expr.readVar?]

theorem Expr.eq_of_isZero {e : Expr} (h : e.isZero = true) : e = .int 0 := by
  unfold Expr.isZero at h
  split at h
  · rfl
  · cases h

/-- The list whose length an expression reads, `xs.len()`. -/
def Expr.lenOf? : Expr → Option Name
  | .op (.list .len) [a] => a.readVar?
  | _ => none

theorem Expr.eq_of_lenOf? {e : Expr} {xs : Name} (h : e.lenOf? = some xs) :
    e = .op (.list .len) [.var xs] := by
  unfold Expr.lenOf? at h
  split at h
  · rw [Expr.eq_of_readVar? h]
  · cases h

/-- The integer literal an expression is, if it is one. -/
def Expr.intLit? : Expr → Option Int
  | .int k => some k
  | _ => none

/-- An arithmetic operation on `i64`, and its operands. -/
def Expr.arithOf? : Expr → Option (Arith × Expr × Expr)
  | .op (.arith o .i64) [a, b] => some (o, a, b)
  | _ => none

theorem Expr.eq_of_arithOf? {e a b : Expr} {o : Arith} (h : e.arithOf? = some (o, a, b)) :
    e = .op (.arith o .i64) [a, b] := by
  unfold Expr.arithOf? at h
  split at h
  · cases h; rfl
  · cases h

theorem Expr.eq_of_intLit? {e : Expr} {k : Int} (h : e.intLit? = some k) : e = .int k := by
  unfold Expr.intLit? at h
  split at h
  · cases h; rfl
  · cases h

/-- The list whose length less a non-negative literal an expression reads:
`xs.len()`, less `0`, and `xs.len() - c` (facts.range-loops). -/
def Expr.lenLess? (e : Expr) : Option (Name × Int) :=
  match e.arithOf? with
  | some (.sub, a, b) => match a.lenOf?, b.intLit? with
    | some xs, some c => if 0 ≤ c then some (xs, c) else none
    | _, _ => none
  | _ => e.lenOf?.map (·, 0)

theorem Expr.eq_of_lenLess? {e : Expr} {xs : Name} {c : Int} (h : e.lenLess? = some (xs, c)) :
    0 ≤ c ∧ (e = .op (.list .len) [.var xs] ∧ c = 0 ∨
      e = .op (.arith .sub .i64) [.op (.list .len) [.var xs], .int c]) := by
  unfold Expr.lenLess? at h
  split at h
  · rename_i a b he
    split at h
    · rename_i ys c' ha hb
      split at h
      · cases h
        exact ⟨by assumption, .inr (by rw [Expr.eq_of_arithOf? he, Expr.eq_of_lenOf? ha,
          Expr.eq_of_intLit? hb])⟩
      · cases h
    · cases h
  · cases he : e.lenOf? with
    | none => rw [he] at h; cases h
    | some ys =>
      rw [he] at h
      cases h
      exact ⟨Int.le_refl _, .inl ⟨Expr.eq_of_lenOf? he, rfl⟩⟩

/-- The variable and the literal offset an index reads: `j` with `0`, `j + k` with
`k`, and `j - k` with `-k`, for a literal `k` that isn't negative (facts.range-loops). -/
def Expr.offset? (e : Expr) : Option (Name × Int) :=
  match e.readVar? with
  | some j => some (j, 0)
  | none => match e.arithOf? with
    | some (o, a, b) => match a.readVar?, b.intLit? with
      | some j, some k =>
        if 0 ≤ k then
          match o with
          | .add => some (j, k)
          | .sub => some (j, -k)
          | _ => none
        else none
      | _, _ => none
    | none => none

theorem Expr.eq_of_offset? {e : Expr} {j : Name} {k : Int} (h : e.offset? = some (j, k)) :
    e = .var j ∧ k = 0 ∨ 0 ≤ k ∧ e = .op (.arith .add .i64) [.var j, .int k] ∨
      0 ≤ -k ∧ e = .op (.arith .sub .i64) [.var j, .int (-k)] := by
  unfold Expr.offset? at h
  split at h
  · rename_i j' hj
    cases h; exact .inl ⟨Expr.eq_of_readVar? hj, rfl⟩
  · split at h
    · rename_i o a b _ he
      split at h
      · rename_i j' k' ha hb
        split at h
        · rename_i hk
          rw [Expr.eq_of_arithOf? he, Expr.eq_of_readVar? ha, Expr.eq_of_intLit? hb]
          split at h <;> cases h
          · exact .inr (.inl ⟨hk, rfl⟩)
          · exact .inr (.inr ⟨by simpa using hk, by simp⟩)
        · cases h
      · cases h
    · cases h

/-- A test that gives facts: of a variable against `0`, or of a variable against a
list's length, with its comparison and whether the variable is on the left. -/
inductive Atom where
  | zero (c : Cmp) (x : Name) (left : Bool)
  | len (c : Cmp) (x xs : Name) (left : Bool)

/-- The test that an expression is, if it is one. -/
def Expr.test? : Expr → Option Atom
  | .op (.compare c _) [a, b] =>
    match a.readVar?, b.isZero, a.isZero, b.readVar?, b.lenOf?, a.lenOf? with
    | some d, true, _, _, _, _ => some (.zero c d true)
    | _, _, true, some d, _, _ => some (.zero c d false)
    | some i, _, _, _, some xs, _ => some (.len c i xs true)
    | _, _, _, some i, _, some xs => some (.len c i xs false)
    | _, _, _, _, _, _ => none
  | _ => none

/-- The shapes of a test. -/
theorem Expr.test?_spec {e : Expr} {t : Atom} (h : e.test? = some t) : ∃ k,
    (∃ c d, t = .zero c d true ∧ e = .op (.compare c k) [.var d, .int 0]) ∨
    (∃ c d, t = .zero c d false ∧ e = .op (.compare c k) [.int 0, .var d]) ∨
    (∃ c i xs, t = .len c i xs true ∧ e = .op (.compare c k) [.var i, .op (.list .len) [.var xs]]) ∨
    (∃ c i xs, t = .len c i xs false ∧ e = .op (.compare c k) [.op (.list .len) [.var xs], .var i]) := by
  unfold Expr.test? at h
  split at h
  · rename_i c k a b
    refine ⟨k, ?_⟩
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
    · rename_i d ha hb; exact .inl ⟨c, d, rfl, by rw [Expr.eq_of_readVar? ha, Expr.eq_of_isZero hb]⟩
    · rename_i d ha hb _; exact .inr (.inl ⟨c, d, rfl, by rw [Expr.eq_of_isZero ha, Expr.eq_of_readVar? hb]⟩)
    · rename_i i xs ha hb _ _
      exact .inr (.inr (.inl ⟨c, i, xs, rfl, by rw [Expr.eq_of_readVar? ha, Expr.eq_of_lenOf? hb]⟩))
    · rename_i i xs ha hb _ _ _
      exact .inr (.inr (.inr ⟨c, i, xs, rfl, by rw [Expr.eq_of_readVar? ha, Expr.eq_of_lenOf? hb]⟩))
  · cases h

/-- The comparison with its operands swapped: `a < b` is `b > a`. -/
def Cmp.mirror : Cmp → Cmp
  | .lt => .gt | .le => .ge | .gt => .lt | .ge => .le | c => c

/-- The comparison that holds exactly when this one doesn't. -/
def Cmp.negate : Cmp → Cmp
  | .eq => .ne | .ne => .eq | .lt => .ge | .ge => .lt | .gt => .le | .le => .gt

/-- The comparison of the variable on the left that a test's being `b` shows. -/
def Cmp.norm (b : Bool) (c : Cmp) (left : Bool) : Cmp :=
  let c := if left then c else c.mirror
  if b then c else c.negate

theorem Cmp.norm_ints {b : Bool} {c : Cmp} {left : Bool} {x y : Int}
    (h : (if left then c.ints x y else c.ints y x) = b) : (Cmp.norm b c left).ints x y = true := by
  cases c <;> cases left <;> cases b <;>
    simp_all [Cmp.norm, Cmp.mirror, Cmp.negate, Cmp.ints] <;> omega

/-- Whether an expression is the Boolean literal `b`. -/
def Expr.isBool (b : Bool) : Expr → Bool
  | .bool b' => b == b'
  | _ => false

theorem Expr.eq_of_isBool {b : Bool} {e : Expr} (h : e.isBool b = true) : e = .bool b := by
  cases e <;> simp_all [Expr.isBool]

/-- The facts that a test gives when it is `b`: that the variable isn't zero when
the comparison it shows is `!=`, `<` or `>` with `0`, that it isn't negative when
it is `>=`, `>` or `==` with `0`, and that it is below the list's length when it
is `<` with that length. -/
def testFacts (b : Bool) : Option Atom → List Known
  | some (.zero c x left) =>
    let c := Cmp.norm b c left
    (if c == .ne || c == .lt || c == .gt then [.nonzero x] else []) ++
      (if c == .ge || c == .gt || c == .eq then [.nonneg x] else [])
  | some (.len c x xs left) => if Cmp.norm b c left == .lt then [.below x xs] else []
  | none => []

/-- The fact that `m.contains(k)` gives when it holds: that the map has the key. -/
def containsFacts (a k : Expr) : List Known :=
  match a.readVar?, k.keyTerm? with
  | some m, some kt => [.has m kt]
  | _, _ => []

mutual

/-- The facts that a condition gives the code it guards when it is `b`
(facts.guarding-tests): a test's, `m.contains(k)`'s (facts.keys), each conjunct's of an `&&` chain when it holds,
each disjunct's negation of an `||` chain when it doesn't, read through `!`. The
calculus writes `a && x` as `if a { x } else { false }` and `a || y` as
`if a { true } else { y }`; a conjunct's facts hold after the conjuncts after it
only for the variables that they don't write. -/
def Expr.factsAs (b : Bool) : Expr → List Known
  | .if a _ x y =>
    if b && y.isBool false then withoutNames (a.factsAs true) x.writes ++ x.factsAs true
    else if !b && x.isBool true then withoutNames (a.factsAs false) y.writes ++ y.factsAs false
    else []
  | .op o es => opFacts b o es
  | _ => []

/-- The facts of an operation: `!`'s operand's for the other Boolean, and a test's. -/
def opFacts (b : Bool) : Op → List Expr → List Known
  | .not, [a] => a.factsAs (!b)
  | .compare cmp k, [l, r] => testFacts b (Expr.op (.compare cmp k) [l, r]).test?
  | .map .contains, [a, k] => if b then containsFacts a k else []
  | _, _ => []

end

/-- The facts a condition gives the code it guards when it holds. -/
def Expr.facts (c : Expr) : List Known := c.factsAs true

/-- The facts a condition gives the code it guards when it doesn't hold. -/
def Expr.negFacts (c : Expr) : List Known := c.factsAs false

mutual

/-- Whether code never ends with a value: each of its paths ends in `return`, `break`,
`continue` or `raise` (facts.guarding-tests), through sequences, the bodies of `let`
and `var`, both branches of an `if` and every arm of a `match`. -/
def Expr.alwaysJumps : Expr → Bool
  | .return _ | .break | .continue | .raise _ => true
  | .seq _ b | .letIn _ _ _ b | .varIn _ _ _ b => b.alwaysJumps
  | .if _ _ a b => a.alwaysJumps && b.alwaysJumps
  | .match _ _ arms => armsAlwaysJump arms
  | _ => false

/-- Whether every arm's body always jumps. -/
def armsAlwaysJump : List Arm → Bool
  | [] => true
  | ⟨_, _, _, body⟩ :: arms => body.alwaysJumps && armsAlwaysJump arms

end

theorem armsAlwaysJump_mem : ∀ {arms : List Arm} {arm : Arm}, armsAlwaysJump arms = true →
    arm ∈ arms → arm.body.alwaysJumps = true
  | ⟨_, _, _, _⟩ :: _, _, h, hm => by
    simp only [armsAlwaysJump, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h.1
    · exact armsAlwaysJump_mem h.2 hm

/-- The facts that an `if` whose then-branch always jumps gives the code after it:
its condition's negation's, but those of the variables its else-branch writes. -/
def Expr.after : Expr → List Known
  | .if c _ t e => if t.alwaysJumps then withoutNames c.negFacts e.writes else []
  | _ => []

/-- What the facts of a test against `0` say, from the comparison it shows. -/
theorem Cmp.facts_zero {c : Cmp} {x : Int} (h : c.ints x 0 = true) :
    ((c == .ne || c == .lt || c == .gt) = true → x ≠ 0) ∧
      ((c == .ge || c == .gt || c == .eq) = true → 0 ≤ x) := by
  cases c <;> simp_all [Cmp.ints] <;> omega

end Stilt
