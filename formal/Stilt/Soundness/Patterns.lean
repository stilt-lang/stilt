import Stilt.Soundness.Inhabited
import Stilt.Soundness.Lists
import Stilt.Exhaustive

/-!
# Patterns of well-typed values

A pattern that fits a type and matches a value of it binds values of the types
its typing gives its names (patterns.pattern-types and
patterns.bindings-are-copies), and arms that the usefulness algorithm finds
exhaustive match every value of the type (patterns.algorithm): a well-typed
`match` always finds an arm.
-/

namespace Stilt

section

variable {D : Decls} {η : REnv}

theorem ValuesAt.length : ∀ {vs : List Value} {τs : List Ty}, ValuesAt D η vs τs →
    vs.length = τs.length
  | _, _, .nil => rfl
  | _, _, .cons _ h => by simp [ValuesAt.length h]

theorem ValuesAt.append : ∀ {vs ws : List Value} {τs σs : List Ty}, ValuesAt D η vs τs →
    ValuesAt D η ws σs → ValuesAt D η (vs ++ ws) (τs ++ σs)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hv hvs, h => .cons hv (ValuesAt.append hvs h)

theorem ValuesAt.of_elems : ∀ {vs : List Value} {τs : List Ty},
    Elems.Typed D vs (closeTys η τs) → ValuesAt D η vs τs
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons hv hvs => .cons hv (ValuesAt.of_elems hvs)
  | [], _ :: _, h | _ :: _, [], h => nomatch h

/-- Values each of a type are values of as many copies of it. -/
theorem ValuesAt.of_replicate {τ : Ty} : ∀ {vs : List Value}, (∀ v ∈ vs, Value.Typed D v (τ.close η)) →
    ValuesAt D η vs (List.replicate vs.length τ)
  | [], _ => .nil
  | _ :: _, h => .cons (h _ List.mem_cons_self)
      (ValuesAt.of_replicate fun v hv => h v (List.mem_cons_of_mem _ hv))

theorem Values.Typed.at (η : REnv) :
    ∀ {vs : List Value} {τs : List Ty}, (∀ τ ∈ τs, τ.Closed) → Values.Typed D vs τs →
      ValuesAt D η vs τs
  | _, _, _, .nil => .nil
  | _, τ :: _, hc, .cons hv hvs =>
    .cons ((hc τ List.mem_cons_self).close η ▸ hv)
      (Values.Typed.at η (fun τ h => hc τ (List.mem_cons_of_mem _ h)) hvs)

/-- A record's fields, in their declared order, have the declared names and
values of the declared types. -/
theorem Fields.Typed.at (η : REnv) :
    ∀ {fields : List (Name × Value)} {declared : List (Name × Ty)},
      (∀ f ∈ declared, f.2.Closed) → Fields.Typed D fields declared →
        fields.map Prod.fst = declared.map Prod.fst ∧
          ValuesAt D η (fields.map Prod.snd) (declared.map Prod.snd)
  | _, _, _, .nil => ⟨rfl, .nil⟩
  | _, (f, τ) :: _, hc, .cons hv hfs => by
    obtain ⟨h₁, h₂⟩ := Fields.Typed.at η (fun f h => hc f (List.mem_cons_of_mem _ h)) hfs
    refine ⟨by simp [h₁], .cons ?_ h₂⟩
    exact (hc (f, τ) List.mem_cons_self).close η ▸ hv

mutual

/-- A pattern that matches a value of its type binds values of the types its
typing gives (patterns.pattern-types). -/
theorem PatFits.bound (hD : D.WellFormed) : ∀ {p : Pattern} {σ : Ty} {σs : List Ty}, PatFits D p σ σs →
    ∀ {v : Value} {us : List Value}, Value.Typed D v (σ.close η) → p.matchOn v = some us →
      ValuesAt D η us σs
  | _, _, _, .wild, _, _, _, h => by cases h; exact .nil
  | _, _, _, .bind, _, _, hv, h => by cases h; exact .cons hv .nil
  | _, _, _, .int _, v, _, _, h | _, _, _, .bool, v, _, _, h | _, _, _, .str, v, _, _, h
  | _, _, _, .unit, v, _, _, h => by
    cases v <;> simp only [Pattern.matchOn, reduceCtorEq] at h <;> (try split at h) <;>
      first | (cases h; exact .nil) | exact nomatch h
  | _, _, _, .tuple hps, _, _, hv, h => by
    obtain ⟨ws, rfl, hws⟩ := hv.tuple_inv
    simp only [Value.tuple, Pattern.matchOn, positions, map_snd_positionsFrom] at h
    exact PatsFit.bound hD hps (ValuesAt.of_elems hws) h
  | _, _, _, .record hR _ hfps, _, _, hv, h => by
    obtain ⟨r, fields, rfl, hR', hfs⟩ := hv.record_inv
    obtain rfl := Option.some.inj (hR.symm.trans hR')
    simp only [Pattern.matchOn] at h
    exact FieldPatsFit.bound hD (hD.fieldsClosed _ (Decls.mem_of_record? hR)) hfps hfs h
  | _, _, _, .variant hT hC hps, _, _, hv, h => by
    obtain ⟨t, C', τs', payload, rfl, hT', hC', hp⟩ := hv.variant_inv
    obtain rfl := Option.some.inj (hT.symm.trans hT')
    simp only [Pattern.matchOn] at h
    split at h
    · rename_i hc
      subst hc
      obtain rfl := Option.some.inj (hC.symm.trans hC')
      exact PatsFit.bound hD hps (hp.at η (hD.payloadsClosed _ (Decls.mem_of_variant? hT) _
        (List.mem_of_lookup hC))) h
    · exact nomatch h
  | _, _, _, .or hp hq _, v, _, hv, h => by
    simp only [Pattern.matchOn] at h
    split at h
    · rename_i us' h'
      cases h
      exact PatFits.bound hD hp hv h'
    · exact PatFits.bound hD hq hv h
  | _, _, _, .list hps, _, _, hv, h => by
    obtain ⟨vs, rfl, hvs⟩ := hv.list_inv
    simp only [Pattern.matchOn] at h
    exact matchOnList_bound hD hps (fun _ h => (List.eq_of_mem_replicate h)) hvs h

/-- A list pattern's elements, each of a list's element type, matching typed
elements bind values of the types their typing gives, and its rest a list of
the element type (patterns.pattern-forms). -/
theorem matchOnList_bound (hD : D.WellFormed) : ∀ {ps : List Pattern} {τs σs : List Ty} {τ : Ty}
    {r : ListRest}, PatsFit D ps τs σs → (∀ σ ∈ τs, σ = τ) →
    ∀ {vs : List Value} {us : List Value}, (∀ v ∈ vs, Value.Typed D v (τ.close η)) →
      matchOnList ps r vs = some us → ValuesAt D η us (σs ++ r.binders.map fun _ => .list τ)
  | _, _, _, _, .exact, .nil, _, [], _, _, h | _, _, _, _, .any, .nil, _, _, _, _, h => by
    simp only [matchOnList, Option.some.injEq] at h; subst h; exact .nil
  | _, _, _, _, .exact, .nil, _, _ :: _, _, _, h => by simp [matchOnList] at h
  | _, _, _, _, .bind _, .nil, _, vs, _, hvs, h => by
    simp only [matchOnList, Option.some.injEq] at h; subst h
    exact .cons (.list hvs) .nil
  | _, _, _, _, _, .cons _ _, _, [], _, _, h => by simp [matchOnList] at h
  | _, _, _, _, r, .cons hp hps, hτ, v :: vs, _, hvs, h => by
    simp only [matchOnList] at h
    split at h
    · rename_i a b ha hb
      cases h
      have hv := hvs v List.mem_cons_self
      rw [← hτ _ List.mem_cons_self] at hv
      rw [List.append_assoc]
      exact (PatFits.bound hD hp hv ha).append (matchOnList_bound hD hps
        (fun σ h => hτ σ (List.mem_cons_of_mem _ h)) (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) hb)
    · exact nomatch h

theorem PatsFit.bound (hD : D.WellFormed) : ∀ {ps : List Pattern} {τs σs : List Ty}, PatsFit D ps τs σs →
    ∀ {vs : List Value} {us : List Value}, ValuesAt D η vs τs → matchOnAll ps vs = some us →
      ValuesAt D η us σs
  | _, _, _, .nil, _, _, .nil, h => by cases h; exact .nil
  | _, _, _, .cons hp hps, _, _, .cons hv hvs, h => by
    simp only [matchOnAll] at h
    split at h
    · rename_i a b ha hb
      cases h
      exact (PatFits.bound hD hp hv ha).append (PatsFit.bound hD hps hvs hb)
    · exact nomatch h

theorem FieldPatsFit.bound (hD : D.WellFormed) : ∀ {declared : List (Name × Ty)} {fps : List (Name × Pattern)}
    {σs : List Ty}, (∀ f ∈ declared, f.2.Closed) → FieldPatsFit D declared fps σs →
      ∀ {fields : List (Name × Value)} {us : List Value}, Fields.Typed D fields declared →
        matchOnFields fps fields = some us → ValuesAt D η us σs
  | _, _, _, _, .nil, _, _, _, h => by cases h; exact .nil
  | _, _, _, hc, .cons (τ := τ) hl hp hfps, fields, _, hfs, h => by
    obtain ⟨v, hv, hvt⟩ := hfs.lookup hl
    simp only [matchOnFields, hv] at h
    split at h
    · rename_i a b ha hb
      cases h
      have hvt' : Value.Typed D v (τ.close η) := (hc _ (mem_of_lookup hl)).close η ▸ hvt
      exact (PatFits.bound hD hp hvt' ha).append (FieldPatsFit.bound hD hc hfps hfs hb)
    · exact nomatch h

end

variable (hD : D.WellFormed)
include hD

/-- **Exhaustiveness**: rows that the usefulness algorithm finds exhaustive
match every vector of values of their types (patterns.algorithm). -/
theorem Exhaustive.sound {P : Rows} {τs : List Ty} (h : Exhaustive D P τs) :
    ∀ {vs : List Value}, ValuesAt D η vs τs → ∃ row ∈ P, RowMatches row vs := by
  induction h with
  | done hP => intro vs hvs; cases hvs; exact ⟨[], hP, rowMatches_nil⟩
  | empty hτ =>
    intro vs hvs
    cases hvs with | cons hv _ => exact (hτ (hv.inhabited _ _ rfl)).elim
  | default _ ih =>
    intro vs hvs
    cases hvs with
    | cons hv hvs => exact (defaultRow_sound _).lift (ih hvs)
  | bool _ _ iht ihf =>
    intro vs hvs
    cases hvs with
    | cons hv hvs =>
      obtain ⟨b, rfl⟩ := hv.bool_inv
      cases b
      · exact (boolRow_sound false).lift (ihf hvs)
      · exact (boolRow_sound true).lift (iht hvs)
  | unit _ ih =>
    intro vs hvs
    cases hvs with
    | cons hv hvs =>
      obtain rfl := hv.unit_inv
      exact unitRow_sound.lift (ih hvs)
  | tuple _ ih =>
    intro vs hvs
    cases hvs with
    | cons hv hvs =>
      obtain ⟨ws, rfl, hws⟩ := hv.tuple_inv
      have hw := ValuesAt.of_elems hws
      have h := ih (hw.append hvs)
      rw [← hw.length] at h
      exact (tupleRow_sound ws).lift h
  | record hR _ ih =>
    intro vs hvs
    cases hvs with
    | cons hv hvs =>
      obtain ⟨r', fields, rfl, hR', hfs⟩ := hv.record_inv
      obtain rfl := Option.some.inj (hR.symm.trans hR')
      obtain ⟨hn, hw⟩ := Fields.Typed.at η (hD.fieldsClosed _ (Decls.mem_of_record? hR)) hfs
      have h := ih (hw.append hvs)
      rw [← hn] at h
      exact (recordRow_sound _ fields).lift h
  | variant hT _ ih =>
    intro vs hvs
    cases hvs with
    | cons hv hvs =>
      obtain ⟨t', C, τs', payload, rfl, hT', hC, hp⟩ := hv.variant_inv
      obtain rfl := Option.some.inj (hT.symm.trans hT')
      have hmem := List.mem_of_lookup hC
      have hw := hp.at η (hD.payloadsClosed _ (Decls.mem_of_variant? hT) _ hmem)
      have h := ih (C, τs') hmem (hw.append hvs)
      dsimp only at h
      rw [← hw.length] at h
      exact (variantRow_sound _ C payload).lift h
  | list m _ _ ih ihl =>
    intro vs hvs
    cases hvs with
    | cons hv hvs =>
      obtain ⟨xs, rfl, hxs⟩ := hv.list_inv
      by_cases hm : xs.length ≤ m
      · exact (listRow_sound xs).lift (ih xs.length hm ((ValuesAt.of_replicate hxs).append hvs))
      · have hw := ValuesAt.of_replicate (vs := xs.take m) fun u hu => hxs u (List.mem_of_mem_take hu)
        rw [List.length_take, Nat.min_eq_left (by omega)] at hw
        exact (listRow_long_sound m xs (by omega)).lift (ihl (hw.append hvs))

/-- A well-typed `match` finds an arm for every value of its scrutinee's type. -/
theorem Exhaustive.select {arms : List Arm} {σ : Ty} (h : Exhaustive D (armRows arms) [σ])
    {v : Value} (hv : Value.Typed D v (σ.close η)) : (selectArm arms v).isSome := by
  obtain ⟨row, hrow, hm⟩ := Exhaustive.sound hD h (.cons hv .nil)
  obtain ⟨arm, harm, rfl⟩ := List.mem_map.1 hrow
  refine selectArm_isSome harm ?_
  obtain ⟨h₁, _⟩ := rowMatches_cons.1 hm
  exact h₁

end

end Stilt
