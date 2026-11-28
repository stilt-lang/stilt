import Stilt.Show

/-!
# Anonymous records

An anonymous record type, `{ f: T, g: U }`, is in the calculus a record declaration named by
the type's own text (`anonymousName`), which no declared record's name is, as the export writes
it: so it is a record of the calculus in every other respect, its literals record literals
(`HasType.record`) and its fields read and written as a record's are. What the calculus states
of it beside a declared record's rules is `Decls.AnonymousRecords`, which `Program.Accepted`
checks.
-/

namespace Stilt

/-- The record declarations of anonymous record types (records.anonymous-types), each named by
its own text, `{ f: T, … }`, which no declared record's name is:

* it has one field or more, so `{}` is no type, each field named once (E0316), as every
  record's are (`Decls.WellFormed`), and it has no type parameters;
* two of the same field names with the same types, in any order, are one declaration, so one
  type, and none is a declared record, whose name is no anonymous record's, whatever their
  fields (`Decls.AnonymousRecords.same_type`);
* it has no home module (records.no-home): no `impl` block is of it, so it has no inherent
  function, and no trait impl is for it, so it has only the structural impls. -/
structure Decls.AnonymousRecords (D : Decls) : Prop where
  fields : ∀ r ∈ D.records, anonymousName r.name = true → r.fields ≠ [] ∧ r.typeParams = []
  same : ∀ r ∈ D.records, ∀ r' ∈ D.records, anonymousName r.name = true →
    anonymousName r'.name = true → r.fields.Perm r'.fields → r.name = r'.name
  noInherent : ∀ i ∈ D.impls, anonymousName i.type = false
  noImpls : ∀ i ∈ D.traitImpls, ∀ R, i.type = .record R → anonymousName R = false

/-- The record that `D.record? R` finds is named `R`. -/
theorem Decls.record?_name {D : Decls} {R : Name} {r : RecordDecl} (h : D.record? R = some r) :
    r ∈ D.records ∧ r.name = R := by
  simp only [Decls.record?] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- Two anonymous record types whose declarations have the same fields with the same types, in
any order, are the same type (records.anonymous-types). -/
theorem Decls.AnonymousRecords.same_type {D : Decls} (h : D.AnonymousRecords) {R R' : Name}
    {r r' : RecordDecl} (hr : D.record? R = some r) (hr' : D.record? R' = some r')
    (ha : anonymousName R = true) (ha' : anonymousName R' = true) (hp : r.fields.Perm r'.fields) :
    Ty.record R [] = Ty.record R' [] := by
  obtain ⟨hm, rfl⟩ := Decls.record?_name hr
  obtain ⟨hm', rfl⟩ := Decls.record?_name hr'
  rw [h.same r hm r' hm' ha ha' hp]

end Stilt
