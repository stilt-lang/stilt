import Stilt.Windows.AssignVars
import Stilt.Windows.Path
import Stilt.Windows.Bind

/-!
# Assignment, on the relation of windows

An assignment `x.ps = e` (values.assignment-order): the indexes of the place run, then the value,
then both models write it at the same path below `x` (values.let-and-var). They fail alike, or
give states the simulation keeps, with the same variables: the write misses every live and
waiting window (E0423), the value's windows lie before the written location and are tracked by
the written variable's sources (E0422), and a location of the callers that a variable reaches
held no window when the body started, so it holds none after.
-/

namespace Stilt

namespace Windows

open InPlace (Ref)

variable {D : Decls} {c : Ctx} {pend : List (Window × Value)}

namespace Write

variable {si : IState} {sw : WState} {r : Ref} {p : Path} {w v y u y' u' : Value}

/-- A captured variable, after the write: the written one only if the value holds no window. -/
theorem base_after (h : Write si sw pend r p w v y u y' u') (hag : Agree D si sw) {x : Name}
    (hl : sw.1.env.lookup x = some r)
    (hwv : ∀ win ∈ windowsOf w, ∃ b, c.Γ.lookup x = some b ∧ b.param = false) {xr : Name × Ref}
    (hxr : xr ∈ sw.1.env) (hpar : xr = (x, r) → ∀ b, c.Γ.lookup x = some b → b.param = true)
    (hb : BaseHolds sw.1.store xr) : BaseHolds h.storeW xr := by
  obtain ⟨y₀, hy₀, hpath, hfree⟩ := hb
  by_cases hloc : xr.2.loc = r.loc
  · have heq : xr = (x, r) := by
      refine eq_of_not_disjoint (env_pairwise hag) hxr (mem_of_lookup hl) fun hd => ?_
      simp [InPlace.Ref.Disjoint, InPlace.Ref.toPath, hpath, hloc, Path.Disjoint] at hd
    subst heq
    have hy := eq_of_cell h.cellW hy₀
    subst hy
    refine ⟨y', cell_set_self h.lt y', hpath, List.eq_nil_iff_forall_not_mem.2 fun win hwin => ?_⟩
    rcases h.sub win hwin with hw | hw
    · rw [hfree] at hw; cases hw
    · obtain ⟨b, hb, hb'⟩ := hwv win hw
      simp [hpar rfl b hb] at hb'
  · exact BaseHolds.transport ⟨y₀, hy₀, hpath, hfree⟩
      (by simp [Kept, List.getElem?_set_ne (Ne.symm hloc)])

/-- The variables after the write fit the scope as before. -/
theorem fits (h : Write si sw pend r p w v y u y' u') (hp : Pre D c pend si sw)
    (hg : Guards D c pend sw.1.env) {x : Name} (hl : sw.1.env.lookup x = some r) {V : List Shape}
    (hV : AssignSources c x V) (hvw : ∀ win ∈ windowsOf w, Tracked sw.1.env c.In V win) :
    Fits (TopHolds h.storeW sw.1.env c.In c.L) (BaseHolds h.storeW) c.Γ sw.1.env := by
  have hnd : sw.1.env.Nodup := (env_pairwise hp.agree).imp fun hd he => by
    subst he
    exact disjoint_self _ hd
  refine Fits.mono_at hp.fits hnd (fun _ => hl) (fun xb xr older hs hfirst htop => ?_)
    fun xr hxr hpar hb => h.base_after hp.agree hl (fun win hw => ?_) hxr hpar hb
  · by_cases heq : xr = (x, r)
    · subst heq
      refine h.top_written hp.agree (fun win hw => ?_) htop
      obtain ⟨b, hb, hpar, hty, ht, -⟩ := value_windows hp hg hl hV (hvw win hw)
      rw [hfirst rfl, Option.some.injEq] at hb
      subst hb
      exact ⟨hpar, hty, ht⟩
    · by_cases hloc : xr.2.loc = r.loc
      · have hd : xr.2.Disjoint r := Classical.byContradiction fun hd =>
          heq (eq_of_not_disjoint (env_pairwise hp.agree) (hs.subset List.mem_cons_self)
            (mem_of_lookup hl) hd)
        refine h.top_shared hp.agree hloc ?_ htop
        simpa [InPlace.Ref.Disjoint, InPlace.Ref.toPath, hloc, Path.Disjoint] using hd
      · exact h.top_other hp.agree hloc htop
  · obtain ⟨b, hb, hpar, -⟩ := value_windows hp hg hl hV (hvw win hw)
    exact ⟨b, hb, hpar⟩

theorem getElem?_storeW_ne (h : Write si sw pend r p w v y u y' u') {ℓ : Nat} (hl : ℓ ≠ r.loc) :
    h.storeW[ℓ]? = sw.1.store[ℓ]? :=
  List.getElem?_set_ne (Ne.symm hl)

theorem getElem?_storeW_self (h : Write si sw pend r p w v y u y' u') :
    h.storeW[r.loc]? = some (some y') :=
  List.getElem?_set_self h.lt

/-- A location of the callers, after the write: the written one held no window. -/
theorem outer (h : Write si sw pend r p w v y u y' u') (hp : Pre D c pend si sw)
    (hg : Guards D c pend sw.1.env) {x : Name} (hl : sw.1.env.lookup x = some r) {V : List Shape}
    (hV : AssignSources c x V) (hvw : ∀ win ∈ windowsOf w, Tracked sw.1.env c.In V win)
    (ℓ : Nat) (z : Value) (hℓ : ℓ < c.L) (hz : h.storeW[ℓ]? = some (some z)) :
    (∀ win ∈ windowsOf z, win ∈ c.Old ℓ) ∧ ∃ y₀, c.Start ℓ = some y₀ ∧ (z = y₀ ∨ Free z) := by
  by_cases hloc : ℓ = r.loc
  · subst hloc
    rw [h.getElem?_storeW_self, Option.some.injEq, Option.some.injEq] at hz
    subst hz
    obtain ⟨hold, y₀, hst, hor⟩ := hp.outer r.loc y hℓ h.cellW
    have hw : ∀ win ∈ windowsOf w, False := fun win hwin => by
      obtain ⟨-, -, -, -, -, -, hL⟩ := value_windows hp hg hl hV (hvw win hwin)
      omega
    have hy : Free y := hor.elim (fun he => hg.start (x, r) (mem_of_lookup hl) hℓ y (he ▸ hst)) id
    refine ⟨fun win hwin => (h.sub win hwin).elim (hold win) fun hw' => (hw win hw').elim, y₀, hst,
      .inr (List.eq_nil_iff_forall_not_mem.2 fun win hwin => ?_)⟩
    rcases h.sub win hwin with hw' | hw'
    · rw [hy] at hw'; cases hw'
    · exact hw win hw'
  · rw [h.getElem?_storeW_ne hloc] at hz
    exact hp.outer ℓ z hℓ hz

/-- The states after the write are ones the simulation keeps. -/
theorem pre (h : Write si sw pend r p w v y u y' u') (hp : Pre D c pend si sw)
    (hg : Guards D c pend sw.1.env) {x : Name} (hl : sw.1.env.lookup x = some r) {V : List Shape}
    (hV : AssignSources c x V) (hvw : ∀ win ∈ windowsOf w, Tracked sw.1.env c.In V win)
    (hvv : v.Viewed D) :
    Pre D c pend ({ si.1 with store := h.storeI }, si.2) ({ sw.1 with store := h.storeW }, sw.2) where
  agree := h.agree hp.agree hvv
  fits := h.fits hp hg hl hV hvw
  outer := h.outer hp hg hl hV hvw
  owned ℓ z hℓ hz := by
    by_cases hloc : ℓ = r.loc
    · subst hloc
      change h.storeW[r.loc]? = _ at hz
      rw [h.getElem?_storeW_self, Option.some.injEq, Option.some.injEq] at hz
      subst hz
      obtain ⟨hex, hlt⟩ := hp.owned r.loc y hℓ h.cellW
      refine ⟨hex, fun win hwin => (h.sub win hwin).elim (hlt win) fun hw => ?_⟩
      obtain ⟨-, -, -, -, -, hlt', -⟩ := value_windows hp hg hl hV (hvw win hw)
      exact hlt'
    · change h.storeW[ℓ]? = _ at hz
      rw [h.getElem?_storeW_ne hloc] at hz
      exact hp.owned ℓ z hℓ hz
  pend wd hwd := by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hp.pend wd hwd
    exact ⟨regionW_write h.cellW h.setW (h.missesP wd hwd) h₁,
      (regionI_write h.cellI h.setI (h.missesP wd hwd)).trans h₂, h₃, h₄⟩
  start := by
    show c.L ≤ h.storeW.length
    rw [List.length_set]
    exact hp.start
  alive ℓ y₀ hℓ hst := by
    show ∃ z, h.storeW[ℓ]? = some (some z)
    by_cases hloc : ℓ = r.loc
    · subst hloc
      exact ⟨y', h.getElem?_storeW_self⟩
    · rw [h.getElem?_storeW_ne hloc]
      exact hp.alive ℓ y₀ hℓ hst

end Write

/-- The write of an assignment, in both models: failing alike, or giving states the simulation
keeps, with the same variables. -/
theorem write_step {si : IState} {sw : WState} (hp : Pre D c pend si sw)
    (hg : Guards D c pend sw.1.env) {x : Name} {ps₀ : List Projection} {p : Path}
    (hres : p.Resolves ps₀) (hu : unread c.R (Place.mk x ps₀).shape = true) {V : List Shape}
    (hV : AssignSources c x V) {v w : Value} (hvw : ValG D c V v w si sw) :
    (∃ f, InPlace.memory.write si x p v = .error f ∧ memory.write sw x p w = .error f) ∨
      ∃ si' sw', InPlace.memory.write si x p v = .ok si' ∧ memory.write sw x p w = .ok sw' ∧
        Pre D c pend si' sw' ∧ sw'.1.env = sw.1.env := by
  have hag := hp.agree
  cases hl : sw.1.env.lookup x with
  | none =>
    refine .inl ⟨.stuck, ?_, ?_⟩
    · simp [InPlace.memory, Frames.withWorld, InPlace.frames, InPlace.write, Functor.map,
        Except.map, ← hag.env, hl]
    · simp [memory, Frames.withWorld, frames, Windows.write, Functor.map, Except.map, hl]
  | some r =>
    have hli : si.1.env.lookup x = some r := by rw [← hag.env]; exact hl
    obtain ⟨y, hy⟩ : ∃ y, cell sw.1.store r.loc = .ok y := by
      rcases Fits.lookup hp.fits hl with ⟨-, -, -, y, hy, -⟩ | ⟨y, hy, -⟩
      · exact ⟨y, hy⟩
      · exact ⟨y, hy⟩
    have hy' := cell_eq_ok hy
    obtain ⟨u, hui, hyu⟩ := hag.live r.loc y hy'
    rcases setW_rel hyu.1 hyu.readAlike hvw.1.1 (r.path ++ p) with ⟨f, h₁, h₂⟩ |
      ⟨y', u', h₁, h₂, h₃, h₄⟩
    · refine .inl ⟨f, ?_, ?_⟩
      · simp [InPlace.memory, Frames.withWorld, InPlace.frames, InPlace.write, Functor.map,
          Except.map, hli, hui, h₂]
      · simp [memory, Frames.withWorld, frames, Windows.write, Functor.map, Except.map, hl, hy',
          h₁]
    · have hW : Write si sw pend r p w v y u y' u' :=
        { cellW := hy', cellI := hui, setW := h₁, setI := h₂, rel := hyu, val := hvw.1, sub := h₄,
          resolve := h₃
          misses := fun ℓ z hz win hwin => misses_of_disjoint
            ((Pre.watched hp hg ℓ z hz win hwin).avoids hl hres hu)
          missesW := fun win hwin => by
            obtain ⟨-, -, -, -, -, hlt, -⟩ := value_windows hp hg hl hV (hvw.2.1 win hwin)
            exact misses_of_lt hlt
          missesP := fun wd hwd => misses_of_disjoint
            (Watched.avoids (.inr (hg.pend wd hwd)) hl hres hu) }
      refine .inr ⟨_, _, ?_, ?_, hW.pre hp hg hl hV hvw.2.1 hvw.2.2, rfl⟩
      · simp [InPlace.memory, Frames.withWorld, InPlace.frames, InPlace.write, Functor.map,
          Except.map, hli, hui, h₂]
      · simp [memory, Frames.withWorld, frames, Windows.write, Functor.map, Except.map, hl, hy',
          h₁]

/-- Changing the states alike: failing alike, or giving states the simulation keeps, with the
same variables. -/
theorem SimP.update {Q : IState → WState → Prop} {G : Unit → Unit → IState → WState → Prop}
    {f : IState → Except Fault IState} {f' : WState → Except Fault WState}
    (h : ∀ si sw, Pre D c pend si sw → Guards D c pend sw.1.env → Q si sw →
      (∃ e, f si = .error e ∧ f' sw = .error e) ∨ ∃ si' sw', f si = .ok si' ∧ f' sw = .ok sw' ∧
        Pre D c pend si' sw' ∧ sw'.1.env = sw.1.env ∧ G () () si' sw') :
    SimP D c pend Q G (Eval.update f) (Eval.update f') := by
  intro si sw hp hg hq
  simp only [Eval.update]
  rcases h si sw hp hg hq with ⟨e, h₁, h₂⟩ | ⟨si', sw', h₁, h₂, hp', he, hG⟩
  · simp only [h₁, h₂]
    exact CorrG.fault hp e
  · simp only [h₁, h₂]
    exact ⟨hp', he, hG⟩

/-- An assignment: its indexes, then its value, then the write (values.assignment-order). -/
theorem SimP.assign {c : Ctx} {pend : List (Window × Value)} (n : Nat) {x : Name}
    {ps₀ ps : List Projection} {value₀ value : Expr} (hps : PathInst D ps₀ ps)
    (hv : Expr.Inst D value₀ value) (hk : ScopeKeeps D c.Γ)
    (ih : ∀ (c' : Ctx), ScopeKeeps D c'.Γ → ∀ e₀ e, Expr.Inst D e₀ e →
      RunsIn D c' (Stilt.eval D InPlace.memory n) (Windows.eval D n) e₀ e)
    (hr : (Expr.assign ⟨x, ps₀⟩ value₀).viewsRead D c.Γ c.R = true)
    (hc : (Expr.assign ⟨x, ps₀⟩ value₀).contained D c.Γ c.P = true) :
    Sim D c pend [] (Eval.assign InPlace.memory (Stilt.eval D InPlace.memory n) x ps value)
      (Eval.assign memory (Windows.eval D n) x ps value) := by
  simp only [Expr.viewsRead, Bool.and_eq_true] at hr
  simp only [Expr.contained, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hrp, hrv⟩, hu⟩, hra⟩ := hr
  obtain ⟨⟨hcp, hcv⟩, hca⟩ := hc
  have hV := assignSources_of_checks hra hca
  unfold Eval.assign
  refine SimP.bind (SimP.path hps c pend (ih c hk) hrp hcp) fun p p' => ?_
  by_cases hpp : p' = p ∧ p.Resolves ps₀
  · obtain ⟨rfl, hres⟩ := hpp
    refine SimP.bind ((ih c hk value₀ value hv c.R pend hrv hcv).mono (fun _ _ _ => trivial)
      fun _ _ _ _ h => h) fun v w => ?_
    refine SimP.bind (G := fun _ _ _ _ => True) (SimP.update fun si sw hp hg hq => ?_) fun _ _ =>
      SimP.pure fun _ _ _ _ => ⟨VRel.free rfl, fun _ h => by simp [windowsOf] at h, .unit⟩
    rcases write_step hp hg hres hu hV hq with h | ⟨si', sw', h₁, h₂, hp', he⟩
    · exact .inl h
    · exact .inr ⟨si', sw', h₁, h₂, hp', he, trivial⟩
  · exact fun _ _ _ _ hq => absurd hq hpp

end Windows

end Stilt
