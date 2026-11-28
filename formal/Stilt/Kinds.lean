import Stilt.Declarations

/-!
# Kinds in the core calculus

A program's traits over type constructors, their impls and the functions that they bound, as the
program writes them (`Stilt.Syntax.Kinds`), checked as the checker checks their kinds, and what
that check promises of the instances the export writes for each use: each is made of types, and
finds, for each method of its bounds, the member of the impl that its constructor has, of the
trait's signature at that constructor.

The functions run as those instances, functions of the calculus that name no constructor
parameter: a call takes each constructor parameter to be the head of its argument's type, which
the export reads from the checker's instantiation. So a generic body is checked at each of its
instances, not once with its constructor parameters rigid, and the instance's body isn't related
to the declaration's. `Stilt.Traits` states, on a calculus of its own with curried application,
that replacing a constructor parameter by a constructor of its arity keeps every kind.
-/

namespace Stilt

namespace KTy

mutual

/-- Whether a type as written is a type, of kind 0, given the number of type parameters of each
named constructor (`ar`) and the arity of each type parameter in scope (`ctx`): its head is
applied to as many arguments as its arity, each a type, and a tuple's, a function type's or an
anonymous record's parts are types. A constructor parameter of arity `n` and the `Self` of a trait
over constructors of `n` arguments are written with `n` arguments, and a type parameter of a
function that no such trait bounds, and the `Self` of a trait over types, with none; written
otherwise, as `F` alone or `F<i64, i64>` under `F: Mappable`, the type is E0337
(traits.constructor-traits and traits.constructor-parameters). -/
def isType (ar ctx : Name → Option Nat) : KTy → Bool
  | .con c args => ar c == some args.length && allTypes ar ctx args
  | .param p args => ctx p == some args.length && allTypes ar ctx args
  | .other parts => allTypes ar ctx parts

/-- Whether each type of a list is a type. -/
def allTypes (ar ctx : Name → Option Nat) : List KTy → Bool
  | [] => true
  | t :: ts => isType ar ctx t && allTypes ar ctx ts

end

mutual

/-- The type with the parameter `p`, applied to its arguments, replaced by the constructor `c`
applied to them, as an instance gives a constructor parameter its constructor and an impl's
members are the trait's with `Self<…>` replaced by `Con<…>`. -/
def substCtor (p c : Name) : KTy → KTy
  | .con d args => .con d (substCtorList p c args)
  | .param q args =>
    if q = p then .con c (substCtorList p c args) else .param q (substCtorList p c args)
  | .other parts => .other (substCtorList p c parts)

/-- Each type of a list with `p` replaced by `c`. -/
def substCtorList (p c : Name) : List KTy → List KTy
  | [] => []
  | t :: ts => substCtor p c t :: substCtorList p c ts

end

/-- The type with each constructor parameter that `σ` names replaced by its constructor. -/
def substCtors (σ : List (Name × Name)) (τ : KTy) : KTy :=
  σ.foldl (fun τ gc => τ.substCtor gc.1 gc.2) τ

theorem substCtorList_length (p c : Name) :
    (ts : List KTy) → (substCtorList p c ts).length = ts.length
  | [] => rfl
  | _ :: ts => by simp [substCtorList, substCtorList_length p c ts]

mutual

/-- Replacing a parameter of arity `n` by a constructor of `n` type parameters keeps a type a
type. -/
theorem isType_substCtor {ar ctx : Name → Option Nat} {p c : Name} {n : Nat}
    (hp : ctx p = some n) (hc : ar c = some n) :
    (τ : KTy) → isType ar ctx τ = true → isType ar ctx (substCtor p c τ) = true
  | .con d args, h => by
    simp only [isType, substCtor, Bool.and_eq_true, beq_iff_eq] at h ⊢
    exact ⟨by rw [substCtorList_length]; exact h.1, allTypes_substCtor hp hc args h.2⟩
  | .param q args, h => by
    simp only [isType, Bool.and_eq_true, beq_iff_eq] at h
    by_cases hq : q = p
    · rw [show substCtor p c (.param q args) = .con c (substCtorList p c args) by
        simp [substCtor, hq]]
      simp only [isType, Bool.and_eq_true, beq_iff_eq]
      rw [hq, hp] at h
      exact ⟨by rw [substCtorList_length, hc]; exact h.1, allTypes_substCtor hp hc args h.2⟩
    · rw [show substCtor p c (.param q args) = .param q (substCtorList p c args) by
        simp [substCtor, hq]]
      simp only [isType, Bool.and_eq_true, beq_iff_eq]
      exact ⟨by rw [substCtorList_length]; exact h.1, allTypes_substCtor hp hc args h.2⟩
  | .other parts, h => by
    simp only [isType, substCtor] at h ⊢
    exact allTypes_substCtor hp hc parts h

/-- Replacing a parameter of arity `n` by a constructor of `n` type parameters keeps each type of
a list a type. -/
theorem allTypes_substCtor {ar ctx : Name → Option Nat} {p c : Name} {n : Nat}
    (hp : ctx p = some n) (hc : ar c = some n) :
    (ts : List KTy) → allTypes ar ctx ts = true → allTypes ar ctx (substCtorList p c ts) = true
  | [], _ => rfl
  | t :: ts, h => by
    simp only [allTypes, substCtorList, Bool.and_eq_true] at h ⊢
    exact ⟨isType_substCtor hp hc t h.1, allTypes_substCtor hp hc ts h.2⟩

end

/-- Replacing parameters each by a constructor of its arity keeps a type a type. -/
theorem isType_substCtors {ar ctx : Name → Option Nat} :
    (σ : List (Name × Name)) → (∀ gc ∈ σ, ∃ n, ctx gc.1 = some n ∧ ar gc.2 = some n) →
    ∀ τ : KTy, isType ar ctx τ = true → isType ar ctx (τ.substCtors σ) = true
  | [], _, _, h => h
  | gc :: σ, hσ, τ, h => by
    obtain ⟨n, hp, hc⟩ := hσ gc (List.mem_cons_self ..)
    exact isType_substCtors σ (fun g hg => hσ g (List.mem_cons_of_mem _ hg)) _
      (isType_substCtor hp hc τ h)

/-- Whether a type is the parameter `p` applied to arguments. -/
def isParam (p : Name) : KTy → Bool
  | .param q _ => q == p
  | _ => false

/-- Whether a type is the constructor `c` applied to arguments. -/
def isCon (c : Name) : KTy → Bool
  | .con d _ => d == c
  | _ => false

end KTy

/-- The written type of a receiver, if it has one. -/
def KReceiver.types : KReceiver → List KTy
  | .typed τ => [τ]
  | _ => []

/-- Whether a function writes no receiver's type. -/
def KReceiver.unwritten : KReceiver → Bool
  | .typed _ => false
  | _ => true

/-- Whether a receiver, if the function has one, writes a type that `ok` allows. -/
def KReceiver.writes (ok : KTy → Bool) : KReceiver → Bool
  | .none => true
  | .bare => false
  | .typed τ => ok τ

/-- Every type a signature writes: its receiver's, its parameters' and its result's. -/
def KSig.types (s : KSig) : List KTy := s.receiver.types ++ s.params ++ [s.result]

/-- The signature with the parameter `p` replaced by the constructor `c`. -/
def KSig.substCtor (p c : Name) (s : KSig) : KSig :=
  { s with
    receiver := match s.receiver with
      | .typed τ => .typed (τ.substCtor p c)
      | r => r
    params := s.params.map (·.substCtor p c)
    result := s.result.substCtor p c }

namespace Kinds

/-- The number of type parameters of a named constructor. -/
def arity? (K : Kinds) (c : Name) : Option Nat := K.arities.lookup c

/-- The trait with this name. -/
def trait? (K : Kinds) (t : Name) : Option KTrait := K.traits.find? (·.name == t)

/-- The arity of a trait: the number of arguments its `Self` takes, 0 for a trait over types and
for a trait of the standard library. -/
def traitArity (K : Kinds) (t : Name) : Nat := (K.trait? t).elim 0 (·.arity)

/-- The arity of a generic with these bounds: the largest of its traits'. -/
def genericArity (K : Kinds) (bounds : List Name) : Nat :=
  bounds.foldr (fun t n => max (K.traitArity t) n) 0

/-- The arity of each type parameter in scope in a signature: its own generics, then `outer`. -/
def sigCtx (K : Kinds) (outer : List (Name × Nat)) (s : KSig) : Name → Option Nat :=
  fun x => (s.generics.map (fun g => (g.1, K.genericArity g.2)) ++ outer).lookup x

/-- One arity for each generic of a signature: a bound list that mixes a trait over constructors
with a trait over types, or two traits over constructors of different arities, is E0337
(traits.constructor-parameters). -/
def boundsAgree (K : Kinds) (s : KSig) : Bool :=
  s.generics.all fun g => g.2.all fun t => K.traitArity t == K.genericArity g.2

/-- A signature whose bounds agree and whose every type is a type, with its generics in scope
before `outer`. -/
def sigKinded (K : Kinds) (outer : List (Name × Nat)) (s : KSig) : Bool :=
  K.boundsAgree s && s.types.all (·.isType K.arity? (K.sigCtx outer s))

/-- A trait's checks of kinds. Each member's types are types, with `Self` of the trait's arity
and its parameters types in scope, so a trait whose members write `Self<A>` is over constructors
of one argument and every `Self` in it takes one, `Self` alone being E0337
(traits.constructor-traits). Each method of a trait over constructors writes its receiver's type,
`self: Self<A>`, `Self` applied to types, and no method of a trait over types writes one, each
otherwise E0338 (traits.receiver-types). -/
def traitChecked (K : Kinds) (t : KTrait) : Bool :=
  t.members.all fun m =>
    K.sigKinded ((selfParam, t.arity) :: t.params.map (·, 0)) m &&
      if t.arity = 0 then m.receiver.unwritten else m.receiver.writes (KTy.isParam selfParam)

/-- The arity of an impl's trait, 0 for an inherent block. -/
def implArity (K : Kinds) (i : KImpl) : Nat := i.trait.elim 0 K.traitArity

/-- The checks of an impl of a trait over constructors of `n > 0` arguments, of trait `t`. Its
type is a named constructor of `n` type parameters written without arguments, and it has no
generics: an applied type, as `List<i64>`, a constructor of another arity, as `Map` for a trait
over `Self<A>`, a tuple or a function type is E0337 (traits.constructor-impls). Each method writes
its receiver's type with the impl's constructor, as `self: Option<A>` (traits.receiver-types).
Its members are the trait's, with each `Self<…>` replaced by `Con<…>` (E0307), every member of
the trait among them. The orphan rule (E0303) and the effects that the members' non-escaping
parameters pass through are left out: kinds read neither modules nor rows. -/
def ctorImplChecked (K : Kinds) (n : Nat) (t : Name) (i : KImpl) : Bool :=
  match i.type with
  | .con c [] =>
    K.arity? c == some n && i.generics.isEmpty &&
      i.members.all (·.receiver.writes (KTy.isCon c)) &&
      (((K.trait? t).elim [] (·.members)).all fun m => i.members.contains (m.substCtor selfParam c)) &&
      i.members.all fun m' => ((K.trait? t).elim [] (·.members)).any fun m =>
        m.substCtor selfParam c == m'
  | _ => false

/-- An impl's checks of kinds. A trait over constructors bounds no generic of an impl block,
E0337 (traits.constructor-parameters); its members' types are types, with its generics in scope;
an impl of a trait over constructors keeps `ctorImplChecked`, and no method of another impl writes
its receiver's type, E0338 (traits.receiver-types). -/
def implChecked (K : Kinds) (i : KImpl) : Bool :=
  i.generics.all (fun g => g.2.all (K.traitArity · == 0)) &&
    i.members.all (K.sigKinded (i.generics.map (·.1, 0))) &&
    match K.implArity i, i.trait with
    | 0, _ => i.members.all (·.receiver.unwritten)
    | n + 1, some t => K.ctorImplChecked (n + 1) t i
    | _ + 1, none => false

/-- Each impl of a trait over constructors, by its trait and its constructor. -/
def ctorImplKey (K : Kinds) (i : KImpl) : Option (Name × Name) :=
  match i.trait, i.type with
  | some t, .con c [] => if 0 < K.traitArity t then some (t, c) else none
  | _, _ => none

/-- The checks of a use of a function with constructor parameters, as an instance. Each
constructor parameter takes a named constructor of its arity, the head of the argument's type:
another type, as `i64` where `F<i64>` is expected, is E0311; and the constructor has an impl of
each trait of the parameter's bounds, a tuple, which has none, being E0318
(traits.constructor-parameters). -/
def useChecked (K : Kinds) (u : KUse) : Bool :=
  K.functions.any (·.name == u.fn) &&
    K.functions.all fun f => f.name != u.fn ||
      (u.ctors.all fun gc => match K.sigCtx [] f gc.1 with
        | some (n + 1) => K.arity? gc.2 == some (n + 1)
        | _ => false) &&
      f.generics.all fun g => K.genericArity g.2 == 0 ||
        match u.ctors.lookup g.1 with
        | some c => g.2.all fun t => K.impls.any fun i => i.trait == some t && i.type == .con c []
        | none => false

end Kinds

/-- The checks of kinds of a program's declarations as written: its traits', its impls', at most
one impl of a trait over constructors for a constructor (E0304, traits.constructor-impls), its
functions', whose types are types and which write no receiver's type (E0338,
traits.receiver-types), and its uses'. -/
def Kinds.Checked (K : Kinds) : Prop :=
  K.traits.all K.traitChecked = true ∧ K.impls.all K.implChecked = true ∧
    (K.impls.filterMap K.ctorImplKey).Nodup ∧
    K.functions.all (fun f => K.sigKinded [] f && f.receiver.unwritten) = true ∧
    K.uses.all K.useChecked = true

instance (K : Kinds) : Decidable K.Checked := by unfold Kinds.Checked; infer_instance

/-- What the checks of kinds promise of each use of a function with constructor parameters,
which the export writes as an instance with no constructor parameter. The function exists, and
for each function of its name: every type of its signature, each constructor parameter replaced
by the constructor the use gives it, is a type, so the instance is made of types; and each
constructor parameter takes a constructor that has, for each trait of its bounds, one impl, which
holds each member of the trait with each `Self<…>` replaced by `Con<…>`. So a method call whose
receiver's type is headed by the parameter finds the method of its bound, which the instance calls
as the member of that impl, of the trait's signature at the constructor
(traits.constructor-parameters and traits.constructor-impls). -/
def Kinds.Kept (K : Kinds) : Prop :=
  ∀ u ∈ K.uses, (∃ f ∈ K.functions, f.name = u.fn) ∧ ∀ f ∈ K.functions, f.name = u.fn →
    (∀ τ ∈ f.types, (τ.substCtors u.ctors).isType K.arity? (K.sigCtx [] f) = true) ∧
    ∀ g ∈ f.generics, 0 < K.genericArity g.2 → ∃ c, u.ctors.lookup g.1 = some c ∧
      ∀ t ∈ g.2, ∃ i ∈ K.impls, i.trait = some t ∧ i.type = .con c [] ∧
        (∀ tr, K.trait? t = some tr → ∀ m ∈ tr.members, m.substCtor selfParam c ∈ i.members) ∧
        ∀ i' ∈ K.impls, i'.trait = some t → i'.type = .con c [] → i' = i

/-- Two elements of a list that a function keys alike are one, when its keys are distinct. -/
theorem eq_of_filterMap_nodup {α β : Type} {f : α → Option β} :
    {l : List α} → (l.filterMap f).Nodup → ∀ {x y : α} {k : β}, x ∈ l → y ∈ l → f x = some k →
      f y = some k → x = y
  | [], _, _, _, _, hx, _, _, _ => absurd hx List.not_mem_nil
  | a :: l, hn, x, y, k, hx, hy, fx, fy => by
    rw [List.filterMap_cons] at hn
    cases ha : f a with
    | none =>
      rw [ha] at hn
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [ha] at fx; cases fx
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [ha] at fy; cases fy
      exact eq_of_filterMap_nodup hn hx hy fx fy
    | some b =>
      rw [ha] at hn
      obtain ⟨hb, hn⟩ := List.nodup_cons.1 hn
      have notIn : ∀ {z}, z ∈ l → f z = some k → b ≠ k := fun hz fz e =>
        hb (List.mem_filterMap.2 ⟨_, hz, e ▸ fz⟩)
      rcases List.mem_cons.1 hx with ex | hx' <;> rcases List.mem_cons.1 hy with ey | hy'
      · rw [ex, ey]
      · subst ex; rw [ha] at fx; cases fx; exact absurd rfl (notIn hy' fy)
      · subst ey; rw [ha] at fy; cases fy; exact absurd rfl (notIn hx' fx)
      · exact eq_of_filterMap_nodup hn hx' hy' fx fy

/-- The checks of kinds keep their promise (`Kinds.Kept`). -/
theorem Kinds.Checked.kept {K : Kinds} (h : K.Checked) : K.Kept := by
  obtain ⟨_, himp, hnd, hfn, huse⟩ := h
  intro u hu
  have hu' := List.all_eq_true.1 huse u hu
  simp only [Kinds.useChecked, Bool.and_eq_true, List.any_eq_true, beq_iff_eq,
    List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hu'
  obtain ⟨⟨f0, hf0, hn0⟩, hall⟩ := hu'
  refine ⟨⟨f0, hf0, hn0⟩, fun f hf hname => ?_⟩
  rcases hall f hf with hne | ⟨hctors, hgens⟩
  · exact absurd hname hne
  have hf' := List.all_eq_true.1 hfn f hf
  simp only [Kinds.sigKinded, Bool.and_eq_true, List.all_eq_true] at hf'
  obtain ⟨⟨hagree, htypes⟩, _⟩ := hf'
  refine ⟨fun τ hτ => KTy.isType_substCtors _ (fun gc hgc => ?_) τ (htypes τ hτ),
    fun g hg hpos => ?_⟩
  · have hc := hctors gc hgc
    cases hs : K.sigCtx [] f gc.1 with
    | none => rw [hs] at hc; cases hc
    | some n =>
      cases n with
      | zero => rw [hs] at hc; cases hc
      | succ n => rw [hs] at hc; exact ⟨n + 1, rfl, by simpa using hc⟩
  · rcases hgens g hg with h0 | hm
    · omega
    cases hl : u.ctors.lookup g.1 with
    | none => rw [hl] at hm; cases hm
    | some c =>
      rw [hl] at hm
      simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
      refine ⟨c, rfl, fun t ht => ?_⟩
      obtain ⟨i, hi, hit, hity⟩ := hm t ht
      have hta : K.traitArity t = K.genericArity g.2 := by
        have hb := List.all_eq_true.1 hagree g hg
        simpa using List.all_eq_true.1 hb t ht
      obtain ⟨n, hn⟩ : ∃ n, K.genericArity g.2 = n + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      have hic := List.all_eq_true.1 himp i hi
      have hia : K.implArity i = n + 1 := by simp [Kinds.implArity, hit, hta, hn]
      simp only [Kinds.implChecked, Bool.and_eq_true, hia, hit] at hic
      obtain ⟨_, hctor⟩ := hic
      simp only [Kinds.ctorImplChecked, hity, Bool.and_eq_true, List.all_eq_true,
        List.contains_iff_mem] at hctor
      obtain ⟨⟨_, hmem⟩, _⟩ := hctor
      refine ⟨i, hi, hit, hity, fun tr htr m hm => hmem m (by simp [htr, hm]),
        fun i' hi' hit' hity' => ?_⟩
      have hk : K.ctorImplKey i = some (t, c) := by
        simp [Kinds.ctorImplKey, hit, hity, hta, hn]
      have hk' : K.ctorImplKey i' = some (t, c) := by
        simp [Kinds.ctorImplKey, hit', hity', hta, hn]
      exact eq_of_filterMap_nodup hnd hi' hi hk' hk

end Stilt
