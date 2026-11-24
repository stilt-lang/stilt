import Stilt.Soundness.Lists

/-!
# Uses of functions

A use of a declared function instantiates its row variables (effects.inference),
and the function's body runs under the environment that the instantiation
composes with the use's own. That environment keeps the promises of the
function's signature: a variable that the signature pairs with `E` raises only
`E`. A concrete row that the use gives the variable has `E` as its one
`raise` label, by effects.one-error-type, and a variable of the enclosing function
that the row holds raises only `E`, by effects.passing-to-paired-variables and the enclosing
function's own environment.
-/

namespace Stilt

mutual

/-- A row of a type comes with the rows of its error type. -/
theorem Ty.rows_raise : ∀ (τ : Ty) {ρ : Row} {E : Ty}, ρ ∈ τ.rows → ρ.raise = some E →
    ∀ ρ' ∈ E.rows, ρ' ∈ τ.rows
  | .list τ, _, _, h, hE => Ty.rows_raise τ h hE
  | .tuple τs, _, _, h, hE => tysRows_raise τs h hE
  | .map κ τ, _, _, h, hE => by
    simp only [Ty.rows, List.mem_append] at h ⊢
    rcases h with h | h
    · exact fun ρ' h' => .inl (Ty.rows_raise κ h hE ρ' h')
    · exact fun ρ' h' => .inr (Ty.rows_raise τ h hE ρ' h')
  | .set τ, _, _, h, hE => Ty.rows_raise τ h hE
  | .view τ, _, _, h, hE => Ty.rows_raise τ h hE
  | .shared τ, _, _, h, hE => Ty.rows_raise τ h hE
  | .fn ps r σ, _, _, h, hE => by
    simp only [Ty.rows, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact fun ρ' h' => .inl (.inl (paramRows_raise ps h hE ρ' h'))
    · exact fun ρ' h' => .inl (.inr (Ty.rows_raise r h hE ρ' h'))
    · exact fun ρ' h' => .inr (Row.rows_raise σ h hE ρ' h')
  | .i64, _, _, h, _ | .bool, _, _, h, _ | .unit, _, _, h, _ | .never, _, _, h, _
  | .record _, _, _, h, _ | .variant _, _, _, h, _ => nomatch h

theorem tysRows_raise : ∀ (τs : List Ty) {ρ : Row} {E : Ty}, ρ ∈ tysRows τs →
    ρ.raise = some E → ∀ ρ' ∈ E.rows, ρ' ∈ tysRows τs
  | [], _, _, h, _ => nomatch h
  | τ :: τs, _, _, h, hE => by
    simp only [tysRows, List.mem_append] at h ⊢
    rcases h with h | h
    · exact fun ρ' h' => .inl (Ty.rows_raise τ h hE ρ' h')
    · exact fun ρ' h' => .inr (tysRows_raise τs h hE ρ' h')

theorem paramRows_raise : ∀ (ps : List (Mode × Ty)) {ρ : Row} {E : Ty}, ρ ∈ paramRows ps →
    ρ.raise = some E → ∀ ρ' ∈ E.rows, ρ' ∈ paramRows ps
  | [], _, _, h, _ => nomatch h
  | (_, τ) :: ps, _, _, h, hE => by
    simp only [paramRows, List.mem_append] at h ⊢
    rcases h with h | h
    · exact fun ρ' h' => .inl (Ty.rows_raise τ h hE ρ' h')
    · exact fun ρ' h' => .inr (paramRows_raise ps h hE ρ' h')

theorem Row.rows_raise : ∀ (σ : Row) {ρ : Row} {E : Ty}, ρ ∈ σ.rows → ρ.raise = some E →
    ∀ ρ' ∈ E.rows, ρ' ∈ σ.rows
  | ⟨io, some F, vs, es, r⟩, _, _, h, hE => by
    simp only [Row.rows, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · obtain rfl := Option.some.inj hE
      exact fun ρ' h' => .inr h'
    · exact fun ρ' h' => .inr (Ty.rows_raise F h hE ρ' h')
  | ⟨_, none, _, _, _⟩, _, _, h, hE => by
    simp only [Row.rows, List.mem_singleton] at h
    subst h
    exact nomatch hE

end

/-- A row that the signature pairs a variable in is a row of its type. -/
theorem FnDecl.mem_rows_of_pairs {d : FnDecl} {ρ : Row}
    (h : ρ ∈ paramRows (d.params.map Param.sig) ++ [d.row]) : ρ ∈ d.type.rows := by
  simp only [List.mem_append, List.mem_singleton] at h
  simp only [FnDecl.type, Ty.rows, List.mem_append]
  rcases h with h | rfl
  · exact .inl (.inl h)
  · exact .inr (Row.mem_rows_self _)

/-- A variable that a use's function pairs with `E` raises, under the composed
environment, only what `E` reads as there. -/
theorem REnv.Respects.pairs_compose {D : Decls} {scope : RowScope} {η : REnv}
    (hη : η.Respects scope) (hD : D.WellFormed) {d : FnDecl} (hd : d ∈ D.fns) {rows : List Row}
    (hlen : rows.length = d.rowParams.length)
    (hinst : d.type.InstantiableBy (d.rowParams.zip rows))
    (hpass : PassesOnPairs scope d (d.rowParams.zip rows)) {v : Name} {E : Ty}
    (hp : d.pairs v E) :
    ∀ F ∈ RowSubst.compose (d.rowParams.zip rows) η v, ¬ F.IsLabel →
      STy.Fits F (E.close (RowSubst.compose (d.rowParams.zip rows) η)) := by
  intro F hF hlab
  obtain ⟨ρ, hρ, hv, hE⟩ := hp
  have hρt := FnDecl.mem_rows_of_pairs hρ
  have heqv := Ty.close_substRows _ η E fun ρ' h' => hinst ρ' (Ty.rows_raise _ hρt hE ρ' h')
  rcases RowSubst.mem_compose.1 hF with ⟨hl, _⟩ | ⟨σ, hl, hF⟩
  · have : ((d.rowParams.zip rows).lookup v).isSome :=
      List.lookup_zip_isSome ((hD.signatures d hd).1 ρ hρt v hv) hlen
    rw [hl] at this
    exact nomatch this
  · rcases Row.mem_close.1 hF with ⟨G, hG, rfl⟩ | ⟨r, hr, hF⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · have hGl : G ∈ ρ.labels (d.rowParams.zip rows) := by
        simp only [Row.labels, List.mem_append, List.mem_filterMap]
        exact .inr ⟨v, hv, by simp [hl, hG]⟩
      have hEl : E.substRows (d.rowParams.zip rows) ∈ ρ.labels (d.rowParams.zip rows) := by
        simp [Row.labels, hE]
      obtain rfl := (hinst ρ hρt).1 G hGl _ hEl
      exact .of_eqv heqv
    · exact (hη.passOn r _ (hpass v E σ r ⟨ρ, hρ, hv, hE⟩ hl hr) F hF hlab).trans (.of_eqv heqv)
    · exact absurd trivial hlab
    · exact absurd trivial hlab

/-- The environment a use composes keeps its function's promises. -/
theorem REnv.Respects.compose {D : Decls} {scope : RowScope} {η : REnv}
    (hη : η.Respects scope) (hD : D.WellFormed) {d : FnDecl} (hd : d ∈ D.fns) {rows : List Row}
    (hlen : rows.length = d.rowParams.length)
    (hinst : d.type.InstantiableBy (d.rowParams.zip rows)) (hres : ∀ ρ ∈ rows, ρ.resume = none)
    (hpass : PassesOnPairs scope d (d.rowParams.zip rows)) :
    (RowSubst.compose (d.rowParams.zip rows) η).Respects d.scope.instantiated where
  pairs _ _ hp := hη.pairs_compose hD hd hlen hinst hpass hp
  passOn _ _ hp := hη.pairs_compose hD hd hlen hinst hpass hp
  types := rfl
  noResume v a r h := by
    rcases RowSubst.mem_compose.1 h with ⟨_, h⟩ | ⟨σ, hl, h⟩
    · exact hη.noResume v a r h
    · have hσ : σ.resume = none := hres σ (List.mem_of_lookup_zip hl)
      rcases Row.mem_close.1 h with ⟨E, _, hE⟩ | ⟨u, _, hu⟩ | ⟨_, _, hE⟩ | ⟨p, hp, _⟩
      · exact Ty.close_not_label η E (hE ▸ trivial)
      · exact hη.noResume u a r hu
      · exact nomatch hE
      · rw [hσ] at hp; exact nomatch hp

end Stilt
