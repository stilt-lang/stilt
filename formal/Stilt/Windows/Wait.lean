import Stilt.Windows.Steps
import Stilt.Windows.Fits

/-!
# Values that wait

While the operands after a value run, the value waits, and the parts its windows read must stay
as they were: they join the waiting windows (`pins`), which the reads around guard, its sources
among them (views.reads-that-last). `SimP.wait` runs a step with more windows waiting and more
places being read, and gives back the relation of the context around it.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {α β : Type} {D : Decls} {c : Ctx} {pend : List (Window × Value)}

/-- A value's windows, each with the part it reads in a store of windows. -/
def pins (sw : List (Option Value)) (w : Value) : List (Window × Value) :=
  (windowsOf w).map fun win =>
    (win, match regionW sw win with
      | .ok d => d
      | .error _ => .unit)

theorem mem_pins {sw : List (Option Value)} {w : Value} {wd : Window × Value}
    (h : wd ∈ pins sw w) : wd.1 ∈ windowsOf w ∧ ∀ d, regionW sw wd.1 = .ok d → wd.2 = d := by
  obtain ⟨win, hwin, rfl⟩ := List.mem_map.1 h
  refine ⟨hwin, fun d hd => ?_⟩
  simp only [hd]

theorem pins_spec {si : List Value} {sw : List (Option Value)} {w v : Value} (h : VRel si sw w v) :
    ∀ wd ∈ pins sw w, regionW sw wd.1 = .ok wd.2 ∧ regionI si wd.1 = .ok wd.2 ∧ Free wd.2 ∧
      viewable wd.2 = true := by
  intro wd hwd
  obtain ⟨hwin, hd⟩ := mem_pins hwd
  obtain ⟨d, h₁, h₂, h₃, h₄⟩ := h.2 _ hwin
  rw [hd d h₁]
  exact ⟨h₁, h₂, h₃, h₄⟩

/-- A value whose windows were pinned is read alike while the pins hold. -/
theorem VRel.of_pins {si si' : List Value} {sw sw' : List (Option Value)} {w v : Value}
    (h : VRel si sw w v)
    (hp : ∀ wd ∈ pins sw w, regionW sw' wd.1 = .ok wd.2 ∧ regionI si' wd.1 = .ok wd.2) :
    VRel si' sw' w v := by
  refine h.region (fun win hwin => ?_) (fun win hwin => ?_)
  · obtain ⟨d, h₁, -⟩ := h.2 win hwin
    have hm : (win, d) ∈ pins sw w := List.mem_map.2 ⟨win, hwin, by simp [h₁]⟩
    rw [(hp _ hm).1, h₁]
  · obtain ⟨d, h₁, h₂, -⟩ := h.2 win hwin
    have hm : (win, d) ∈ pins sw w := List.mem_map.2 ⟨win, hwin, by simp [h₁]⟩
    rw [(hp _ hm).2, h₂]

theorem Pre.reads {c' : Ctx} {pend' : List (Window × Value)} {si : IState} {sw : WState}
    (h : Pre D c pend si sw) (hΓ : c'.Γ = c.Γ) (hIn : c'.In = c.In) (hL : c'.L = c.L)
    (hOld : c'.Old = c.Old) (hStart : c'.Start = c.Start) (hpend : ∀ wd ∈ pend', wd ∈ pend) : Pre D c' pend' si sw := by
  obtain ⟨hag, hfits, houter, howned, hpend', hstart, halive⟩ := h
  refine ⟨hag, ?_, ?_, ?_, fun wd hwd => hpend' wd (hpend wd hwd), ?_, ?_⟩
  · rw [hΓ, hIn, hL]; exact hfits
  · rw [hL, hOld, hStart]; exact houter
  · rw [hL]; exact howned
  · rw [hL]; exact hstart
  · rw [hL, hStart]; exact halive

theorem Fits.mono {top top' : Name × ViewBinding → Name × Ref → List (Name × Ref) → Prop}
    {base base' : Name × Ref → Prop}
    (ht : ∀ xb xr older, top xb xr older → top' xb xr older) (hb : ∀ xr, base xr → base' xr) :
    ∀ {Γ : ViewScope} {env : List (Name × Ref)}, Fits top base Γ env → Fits top' base' Γ env
  | _, _, .base hΓ henv => .base hΓ fun xr hxr => hb xr (henv xr hxr)
  | _, _, .cons hx htop hrest => .cons hx (ht _ _ _ htop) (Fits.mono ht hb hrest)

/-- A step run with more windows waiting and more places being read, from states where the
waiting windows read their parts and the reads guard them, ends as one in the context around. -/
theorem SimP.wait {Q : IState → WState → Prop} {G : α → β → IState → WState → Prop}
    {m : Eval IState α} {m' : Eval WState β} (X : List Shape)
    (extra : IState → WState → List (Window × Value))
    (hm : ∀ si sw, Pre D c pend si sw → Q si sw →
      SimP D { c with R := X ++ c.R } (extra si sw ++ pend) (fun si' sw' => si' = si ∧ sw' = sw)
        G m m')
    (hpin : ∀ si sw, Pre D c pend si sw → Q si sw → ∀ wd ∈ extra si sw,
      regionW sw.1.store wd.1 = .ok wd.2 ∧ regionI si.1.store wd.1 = .ok wd.2 ∧ Free wd.2 ∧
        viewable wd.2 = true)
    (hg : ∀ si sw, Pre D c pend si sw → Guards D c pend sw.1.env → Q si sw → ∀ wd ∈ extra si sw,
      InPlace.Guarded (X ++ c.R) sw.1.env wd.1.ref.toPath) :
    SimP D c pend Q G m m' := by
  intro si sw hp hgd hq
  have hR : ∀ t ∈ c.R, t ∈ X ++ c.R := fun t ht => List.mem_append_right _ ht
  have hp' : Pre D { c with R := X ++ c.R } (extra si sw ++ pend) si sw := by
    refine ⟨hp.agree, hp.fits, hp.outer, hp.owned, fun wd hwd => ?_, hp.start, hp.alive⟩
    rcases List.mem_append.1 hwd with hwd | hwd
    · exact hpin si sw hp hq wd hwd
    · exact hp.pend wd hwd
  have hg' : Guards D { c with R := X ++ c.R } (extra si sw ++ pend) sw.1.env := by
    refine ⟨Fits.mono (fun xb xr older h hp hs w hw ht => (h hp hs w hw ht).mono hR)
      (fun _ _ => trivial) hgd.fenced, hgd.brought, hgd.old, fun wd hwd => ?_,
      hgd.start⟩
    rcases List.mem_append.1 hwd with hwd | hwd
    · exact hg si sw hp hgd hq wd hwd
    · exact (hgd.pend wd hwd).mono hR
  refine Outcome.Rel.mono (hm si sw hp hq si sw hp' hg' ⟨rfl, rfl⟩) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro a s b t ⟨h₁, h₂, h₃⟩
    exact ⟨h₁.reads rfl rfl rfl rfl rfl fun wd hwd => List.mem_append_right _ hwd, h₂, h₃⟩
  · rintro e s e' t ⟨h₁, h₂, h₃⟩
    exact ⟨h₁.reads rfl rfl rfl rfl rfl fun wd hwd => List.mem_append_right _ hwd, h₂, h₃⟩
  · rintro j s j' t ⟨h₁, h₂, h₃⟩
    exact ⟨h₁.reads rfl rfl rfl rfl rfl fun wd hwd => List.mem_append_right _ hwd, h₂, h₃⟩
  · rintro k s k' t ⟨h₁, h₂, h₃⟩
    exact ⟨h₁.reads rfl rfl rfl rfl rfl fun wd hwd => List.mem_append_right _ hwd, h₂, h₃⟩
  · rintro op v s op' v' t ⟨h₁, h₂, h₃⟩
    exact ⟨h₁.reads rfl rfl rfl rfl rfl fun wd hwd => List.mem_append_right _ hwd, h₂, h₃⟩
  · exact fun _ _ _ _ _ h => h

/-- The windows of a value that its sources `X` track are guarded by reads that hold `X`. -/
theorem guarded_pins {si : IState} {sw : WState} (hp : Pre D c pend si sw)
    (hgd : Guards D c pend sw.1.env) {X : List Shape} {v w : Value} (h : ValG D c X v w si sw) :
    ∀ wd ∈ pins sw.1.store w, InPlace.Guarded (X ++ c.R) sw.1.env wd.1.ref.toPath := by
  intro wd hwd
  obtain ⟨hwin, -⟩ := mem_pins hwd
  have hd : sw.1.env.Pairwise fun a b => a.2.Disjoint b.2 := by
    rw [hp.agree.env]; exact hp.agree.disjoint
  exact guarded_of_tracked hd (fun xv hxv w' hw' => (hgd.brought xv hxv w' hw').2)
    (fun s hs => .inl (List.mem_append_left _ hs)) (h.2.1 _ hwin)

/-- A step after a value, run while the value waits with its sources being read. -/
theorem SimP.after {Q : IState → WState → Prop} {G : α → β → IState → WState → Prop}
    {X : List Shape} {v w : Value} {m : Eval IState α} {m' : Eval WState β}
    (hm : ∀ si sw, Pre D c pend si sw → ValG D c X v w si sw → Q si sw →
      SimP D { c with R := X ++ c.R } (pins sw.1.store w ++ pend)
        (fun si' sw' => si' = si ∧ sw' = sw) G m m') :
    SimP D c pend (fun si sw => ValG D c X v w si sw ∧ Q si sw) G m m' :=
  SimP.wait X (fun _ sw => pins sw.1.store w) (fun si sw hp hq => hm si sw hp hq.1 hq.2)
    (fun _ _ _ hq => pins_spec hq.1.1) (fun _ _ hp hgd hq => guarded_pins hp hgd hq.1)

end Windows

end Stilt
