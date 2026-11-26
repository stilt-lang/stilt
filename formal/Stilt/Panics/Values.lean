import Stilt.Panics.Syntax
import Stilt.InPlace.Safe
import Stilt.Memory
import Stilt.Cells

/-!
# Values without panics

A value is panic-free under `lim` when every closure it holds has a body without an
operation that adds `panic`, and every function it names is one that `lim` covers, so
that calling it runs such a body, wherever the value was made
(facts.calls-through-function-values). Places whose
paths take only fields are read and written without a panic: only an index
can be out of bounds (std.lists). So copy-in, copy-out binds, reads, writes,
enters and leaves calls on such paths with no panic, and keeps every value of
its frames panic-free.
-/

namespace Stilt

/-- Every closure a value holds, at any depth, has a body panic-free under `lim`, and
every function it names is one `lim` covers. -/
inductive Value.PanicFree (lim : Limited) : Value → Prop
  | int {n : Int} : Value.PanicFree lim (.int n)
  | float {x : FloatVal} : Value.PanicFree lim (.float x)
  | str {s : String} : Value.PanicFree lim (.str s)
  | bool {b : Bool} : Value.PanicFree lim (.bool b)
  | unit : Value.PanicFree lim .unit
  | record {R : Name} {fields : List (Name × Value)} :
      (∀ fv ∈ fields, Value.PanicFree lim fv.2) → Value.PanicFree lim (.record R fields)
  | variant {T C : Name} {payload : List Value} :
      (∀ v ∈ payload, Value.PanicFree lim v) → Value.PanicFree lim (.variant T C payload)
  | list {vs : List Value} : (∀ v ∈ vs, Value.PanicFree lim v) → Value.PanicFree lim (.list vs)
  | closure {captured : List (Name × Value)} {ps : List Param} {result : Ty} {ρ : Row}
      {body : Expr} :
      body.panicFree lim = true → (∀ xv ∈ captured, Value.PanicFree lim xv.2) →
      Value.PanicFree lim (.closure captured ps result ρ body)
  | function {f : Name} {types : List Ty} {rows : List Row} :
      lim.fn f = true → Value.PanicFree lim (.function f types rows)
  | handle {u : Ty} {k : Nat} : Value.PanicFree lim (.handle u k)

variable {lim : Limited}

theorem Value.PanicFree.hereditary : Value.Hereditary (Value.PanicFree lim) where
  int _ := .int
  float _ := .float
  bool _ := .bool
  str _ := .str
  record _ _ := ⟨fun h => by cases h; assumption, .record⟩
  list _ := ⟨fun h => by cases h; assumption, .list⟩
  handle _ _ := .handle

theorem Value.PanicFree.passesToParts : Value.PassesToParts (Value.PanicFree lim) where
  record _ _ h := by cases h; assumption
  variant _ _ _ h := by cases h; assumption
  list _ := ⟨fun h => by cases h; assumption, .list⟩

/-- A path that takes only fields. -/
def Path.Fields (p : Path) : Prop := ∀ s ∈ p, ∃ f, s = .field f

theorem Path.Fields.tail {s : Step} {p : Path} (h : Path.Fields (s :: p)) : Path.Fields p :=
  fun t ht => h t (List.mem_cons_of_mem _ ht)

/-- The path of a place without an index takes only fields. -/
theorem Path.fields_append {p q : Path} (hp : p.Fields) (hq : q.Fields) : (p ++ q).Fields := by
  intro s hs
  rcases List.mem_append.1 hs with h | h
  · exact hp s h
  · exact hq s h

namespace Value.PanicFree

/-- Reading a panic-free value along fields doesn't panic, and gives a panic-free part. -/
theorem get {v : Value} {p : Path} (hv : v.PanicFree lim) (hp : p.Fields) :
    CalmTo (Value.PanicFree lim) (v.get p) := by
  induction p generalizing v with
  | nil => exact CalmTo.ok hv
  | cons s p ih =>
    obtain ⟨f, rfl⟩ := hp s List.mem_cons_self
    cases v with
    | record R fields =>
      simp only [Value.get]
      split
      · rename_i x hx
        cases hv with
        | record hfs => exact ih (hfs (f, x) (mem_of_lookup hx)) hp.tail
      · exact CalmTo.stuck
    | _ => exact CalmTo.stuck

/-- Writing a panic-free value into one along fields doesn't panic, and gives a
panic-free value. -/
theorem set {v w : Value} {p : Path} (hv : v.PanicFree lim) (hw : w.PanicFree lim) (hp : p.Fields) :
    CalmTo (Value.PanicFree lim) (v.set p w) := by
  induction p generalizing v with
  | nil => exact CalmTo.ok hw
  | cons s p ih =>
    obtain ⟨f, rfl⟩ := hp s List.mem_cons_self
    cases v with
    | record R fields =>
      simp only [Value.set]
      split
      · rename_i x hx
        cases hv with
        | record hfs =>
          refine CalmTo.map (ih (hfs (f, x) (mem_of_lookup hx)) hp.tail) fun x' hx' => ?_
          refine .record fun fv hfv => ?_
          rcases mem_assocSet hfv with hfv | hfv
          · exact hfs fv hfv
          · exact hfv ▸ hx'
      · exact CalmTo.stuck
    | _ => exact CalmTo.stuck

end Value.PanicFree

/-! ## Frames -/

/-- Every value of a frame is panic-free. -/
def Frame.PanicFree (lim : Limited) (fr : Copy.Frame) : Prop := ∀ xv ∈ fr, xv.2.PanicFree lim

/-- Every value of a state is panic-free: those of its frame, and those its world's cells
hold, which a `when` takes out (shared.when). -/
def State.PanicFree (lim : Limited) (s : Copy.State) : Prop :=
  Frame.PanicFree lim s.1 ∧ s.2.All (Value.PanicFree lim)

/-- What a call passes: a panic-free value, or a place along fields. -/
def Passed.PanicFree (lim : Limited) : Passed → Prop
  | .value v | .moved _ v => v.PanicFree lim
  | .place _ p => p.Fields

namespace Frame.PanicFree

theorem cons {fr : Copy.Frame} {x : Name} {v : Value} (hfr : Frame.PanicFree lim fr)
    (hv : v.PanicFree lim) : Frame.PanicFree lim ((x, v) :: fr) := by
  intro xv h
  rcases List.mem_cons.1 h with rfl | h
  · exact hv
  · exact hfr xv h

theorem tail {fr : Copy.Frame} (hfr : Frame.PanicFree lim fr) : Frame.PanicFree lim fr.tail :=
  fun xv h => hfr xv (List.mem_of_mem_tail h)

theorem read {fr : Copy.Frame} (hfr : Frame.PanicFree lim fr) (x : Name) {p : Path}
    (hp : p.Fields) : CalmTo (Value.PanicFree lim) (Copy.read fr x p) := by
  unfold Copy.read
  split
  · rename_i v hv
    exact Value.PanicFree.get (hfr (x, v) (mem_of_lookup hv)) hp
  · exact CalmTo.stuck

theorem write {fr : Copy.Frame} (hfr : Frame.PanicFree lim fr) (x : Name) {p : Path} {w : Value}
    (hw : w.PanicFree lim) (hp : p.Fields) : CalmTo (Frame.PanicFree lim) (Copy.write fr x p w) := by
  unfold Copy.write
  split
  · rename_i v hv
    refine CalmTo.map (Value.PanicFree.set (hfr (x, v) (mem_of_lookup hv)) hw hp) fun v' hv' => ?_
    intro xv hxv
    rcases mem_assocSet hxv with hxv | hxv
    · exact hfr xv hxv
    · exact hxv ▸ hv'
  · exact CalmTo.stuck

/-- Entering a call binds panic-free values: the captured ones, the arguments,
and the places read along fields. -/
theorem enter {caller : Copy.Frame} (hc : Frame.PanicFree lim caller) :
    ∀ {fr : Copy.Frame} (params : List (Name × Passed)), Frame.PanicFree lim fr →
      (∀ ya ∈ params, ya.2.PanicFree lim) → CalmTo (Frame.PanicFree lim) (Copy.enter caller fr params)
  | fr, [], hfr, _ => CalmTo.ok hfr
  | fr, (y, a) :: params, hfr, hps => by
    have ha := hps (y, a) List.mem_cons_self
    have hrest : ∀ ya ∈ params, ya.2.PanicFree lim := fun ya h => hps ya (List.mem_cons_of_mem _ h)
    unfold Copy.enter
    rw [List.foldlM_cons]
    cases a with
    | value v | moved _ v => exact CalmTo.bind (CalmTo.ok (hfr.cons ha)) fun fr' h => enter hc params h hrest
    | place x path =>
      exact CalmTo.bind (CalmTo.map (read hc x (p := path) ha) fun v hv => hfr.cons hv)
        fun fr' h => enter hc params h hrest

/-- Leaving a call writes panic-free values of the callee's frame back along fields. -/
theorem leave {callee : Copy.Frame} (hce : Frame.PanicFree lim callee) :
    ∀ {fr : Copy.Frame} (params : List (Name × Passed)), Frame.PanicFree lim fr →
      (∀ ya ∈ params, ya.2.PanicFree lim) → CalmTo (Frame.PanicFree lim) (Copy.leave fr callee params)
  | fr, [], hfr, _ => CalmTo.ok hfr
  | fr, (y, a) :: params, hfr, hps => by
    have ha := hps (y, a) List.mem_cons_self
    have hrest : ∀ ya ∈ params, ya.2.PanicFree lim := fun ya h => hps ya (List.mem_cons_of_mem _ h)
    unfold Copy.leave
    rw [List.foldlM_cons]
    cases a with
    | value v | moved _ v => exact CalmTo.bind (CalmTo.ok hfr) fun fr' h => leave hce params h hrest
    | place x path =>
      refine CalmTo.bind (CalmTo.bind (read hce y (p := []) (fun _ h => nomatch h))
        fun v hv => write hfr x hv ha) fun fr' h => leave hce params h hrest

end Frame.PanicFree

end Stilt
