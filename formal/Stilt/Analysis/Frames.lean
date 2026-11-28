import Stilt.Analysis.Facts
import Stilt.Panics.Kept

/-!
# Terms in a frame

What each term stands for where the evaluation is: a binding's value and its length, read
from the frame, the values the evaluation has read and not yet used, from a stack beside it, and
the value an expression gave (`Copy.Frame.nu`). A value that isn't an integer stands for 0, and
one that isn't a list has length 0, so every term has an integer; a fact the analysis gives is
about the integers and lists that the code it proves reads, which are what they are.

`Res` is what the analysis gives an expression, and `Outcome.Meets` what it says of the
expression's outcome: the facts at its end, where it is true and where it is false, and at each
`break` and `continue` that leaves it.
-/

namespace Stilt

/-- A value as an integer: itself when it is one, and 0 otherwise. -/
def Value.intOr : Value → Int
  | .int n => n
  | _ => 0

/-- A value's length: its number of elements when it is a list, and 0 otherwise. -/
def Value.lenOr : Value → Int
  | .list vs => vs.length
  | _ => 0

/-- What each term stands for, in a frame, with the values read and not yet used `st`, after
an expression gave `v` (facts.terms). -/
def Copy.Frame.nu (fr : Copy.Frame) (st : List Value) (v : Value) : Valuation
  | .zero => 0
  | .res => v.intOr
  | .reslen => v.lenOr
  | .opnd i => (st.getD i .unit).intOr
  | .opndLen i => (st.getD i .unit).lenOr
  | .val x => ((fr.lookup x).getD .unit).intOr
  | .len xs => ((fr.lookup xs).getD .unit).lenOr

@[simp] theorem Copy.Frame.nu_zero (fr : Copy.Frame) (st : List Value) (v : Value) :
    fr.nu st v .zero = 0 := rfl

/-- The binding whose value or length a term stands for, if it stands for one. -/
def Term.name? : Term → Option Name
  | .val x | .len x => some x
  | _ => none

/-- Whether a term keeps what it stands for across code that writes the names of `W` and gives
a value of its own: neither the value given nor a binding of `W`. -/
def Term.keeps (W : List Name) : Term → Bool
  | .res | .reslen => false
  | .val x | .len x => decide (x ∉ W)
  | _ => true

/-- Whether a term keeps what it stands for while the values read and not yet used are those
below `d`: every pending value from the `d`th on is gone. -/
def Term.below (d : Nat) : Term → Bool
  | .opnd i | .opndLen i => decide (i < d)
  | _ => true

/-- Whether a term is the value an expression gives. -/
def Term.isRes : Term → Bool
  | .res | .reslen => true
  | _ => false

/-- The facts that hold after code that writes the names of `W`, of the ones before it. -/
def Facts.after (F : Facts) (W : List Name) : Facts := F.restrict (Term.keeps W)

/-- The facts of the code around, before an expression gives its value. -/
def Facts.noRes (F : Facts) : Facts := F.restrict fun t => !t.isRes

/-- The facts on the values read and not yet used below `d`. -/
def Facts.within (F : Facts) (d : Nat) : Facts := F.restrict (Term.below d)

namespace Copy.Frame

variable {W L : List Name} {fr fr' : Copy.Frame} {st : List Value} {v v' : Value}

/-- Code that keeps the names outside `W` keeps every term that `Term.keeps` holds of. -/
theorem nu_keeps (k : Frame.Keeps W L fr fr') {t : Term} (ht : t.keeps W = true) :
    fr'.nu st v' t = fr.nu st v t := by
  cases t with
  | val x =>
    simp only [Term.keeps, decide_eq_true_eq] at ht
    simp only [Copy.Frame.nu, k.lookup ht]
  | len x =>
    simp only [Term.keeps, decide_eq_true_eq] at ht
    simp only [Copy.Frame.nu, k.lookup ht]
  | res | reslen => simp [Term.keeps] at ht
  | zero | opnd _ | opndLen _ => rfl

theorem nu_noRes {t : Term} (ht : (!t.isRes) = true) : fr.nu st v' t = fr.nu st v t := by
  cases t <;> simp_all [Term.isRes, Copy.Frame.nu]

/-- A new binding of `x` keeps every term but `x`'s value and length. -/
theorem nu_bind {x : Name} {u : Value} {t : Term} (ht : t.name? ≠ some x) :
    Copy.Frame.nu ((x, u) :: fr) st v t = fr.nu st v t := by
  cases t with
  | val y =>
    have : (y == x) = false := by simpa [Term.name?] using ht
    simp [Copy.Frame.nu, List.lookup_cons, this]
  | len y =>
    have : (y == x) = false := by simpa [Term.name?] using ht
    simp [Copy.Frame.nu, List.lookup_cons, this]
  | _ => rfl

/-- A value read and pushed on the stack keeps every term below. -/
theorem nu_push {u : Value} {t : Term} (ht : t.below st.length = true) :
    fr.nu (st ++ [u]) v t = fr.nu st v t := by
  cases t <;> simp_all [Term.below, Copy.Frame.nu, List.getD_eq_getElem?_getD,
    List.getElem?_append_left]

theorem nu_push_opnd {u : Value} : fr.nu (st ++ [u]) v (.opnd st.length) = u.intOr := by
  simp [Copy.Frame.nu, List.getD_eq_getElem?_getD]

theorem nu_push_opndLen {u : Value} : fr.nu (st ++ [u]) v (.opndLen st.length) = u.lenOr := by
  simp [Copy.Frame.nu, List.getD_eq_getElem?_getD]

end Copy.Frame

namespace Facts

variable {F : Facts} {W L : List Name} {fr fr' : Copy.Frame} {st : List Value} {v v' : Value}

theorem Holds.after (h : F.Holds (fr.nu st v)) (k : Frame.Keeps W L fr fr') :
    (F.after W).Holds (fr'.nu st v') :=
  h.restrict fun _ ht => Copy.Frame.nu_keeps k ht

theorem Holds.noRes (h : F.Holds (fr.nu st v)) : F.noRes.Holds (fr.nu st v') :=
  h.restrict fun _ ht => Copy.Frame.nu_noRes ht

theorem Holds.within (h : F.Holds (fr.nu (st ++ [v']) v)) : (F.within st.length).Holds (fr.nu st v) :=
  h.restrict fun _ ht => (Copy.Frame.nu_push ht).symm

end Facts

/-- What the analysis gives an expression (facts.analysis-order): the facts where it ends with
a value, the value standing for `res`; where that value is `true`, and where it is `false`, as a
condition gives them (facts.conditions); at each `break` and `continue` that leaves it
(facts.paths-that-leave); the linear form of its value, when it has one (facts.linear-forms); and
whether the analysis proves each operation that a mark in it says is proved. -/
structure Res where
  post : Facts
  tt : Facts
  ff : Facts
  brk : Facts
  cont : Facts
  lin : Option (Term × Int) := none
  lo : Option (Term × Int) := none
  hi : Option (Term × Int) := none
  ok : Bool

/-- What holds of an outcome: `P` where it ends with a value, `B` at a `break` and `C` at a
`continue`, and so again in the rest of a performance once resumed. -/
def Outcome.Sat {α : Type} (P : α → Copy.State → Prop) (B C : Copy.State → Prop) :
    Outcome Copy.State α → Prop
  | .done a s => P a s
  | .jumped .brk s => B s
  | .jumped .cont s => C s
  | .performed _ _ _ k => ∀ w x, Outcome.Sat P B C (k w x)
  | _ => True

/-- The facts of `R` where an expression ends with `v`, with the values read and not yet used
`st`: its facts, and those where it is true or false. -/
def Res.Done (R : Res) (st : List Value) (v : Value) (s : Copy.State) : Prop :=
  R.post.Holds (s.1.nu st v) ∧ (v = .bool true → R.tt.Holds (s.1.nu st v)) ∧
    (v = .bool false → R.ff.Holds (s.1.nu st v))

/-- What the analysis says of an outcome, with the values read and not yet used `st`: each
fact holds where the expression ends, or jumps, and in the rest of a performance once
resumed. -/
def Outcome.Meets (R : Res) (st : List Value) (o : Outcome Copy.State Value) : Prop :=
  o.Sat (R.Done st) (fun s => R.brk.Holds (s.1.nu st .unit)) (fun s => R.cont.Holds (s.1.nu st .unit))

/-- Facts that every outcome of code writing `W` keeps, of those before it: at its end and at
each jump. -/
def Res.after (F : Facts) (W : List Name) (ok : Bool) : Res :=
  let G := F.after W
  { post := G, tt := G, ff := G, brk := G, cont := G, ok }

/-- Code that keeps the names outside `W` meets the facts before it that read none of them. -/
theorem Outcome.Keeps.meets {W L : List Name} {F : Facts} {st : List Value} {s : Copy.State}
    {ok : Bool} (hF : F.Holds (s.1.nu st .unit)) :
    ∀ {o : Outcome Copy.State Value}, o.Keeps W L (fun _ => True) s.1 → o.Meets (Res.after F W ok) st
  | .done _ _, ⟨_, k⟩ => ⟨hF.after k, fun _ => hF.after k, fun _ => hF.after k⟩
  | .jumped .brk _, k => hF.after k
  | .jumped .cont _, k => hF.after k
  | .jumped (.ret _) _, _ => trivial
  | .performed _ _ _ _, ⟨_, hk⟩ => fun w x => Outcome.Keeps.meets hF (hk w x)
  | .raised _ _, _ | .panicked _ _, _ | .outOfFuel, _ | .stuck, _ => trivial

end Stilt
