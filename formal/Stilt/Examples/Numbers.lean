import Stilt.Typing
import Stilt.Semantics

/-!
# Numbers

Runs of the required tests of numbers.integer-panics, numbers.division-and-remainder,
numbers.wrapping, numbers.shifts, numbers.shift-amounts, numbers.bitwise-operators,
numbers.comparisons and numbers.wrapping-conversions, in both models of memory, and
the literals and operators that typing rejects (numbers.integer-literals,
numbers.no-implicit-conversions and numbers.unsigned-negation). Each program
raises the value it shows, as in `Stilt.Examples`. Floats compute as Lean's
`Float32` and `Float` do, which a proof by evaluation can't run, so no run
here shows one.
-/

namespace Stilt.Examples.Numbers

/-- A program whose `main` raises a value of type `shown`. -/
private def program (shown : Ty) (main : Expr) : Program :=
  ⟨⟨[], [], [], [], [], [], [], []⟩, main, ⟨false, some shown, [], [], none⟩, {}⟩

/-- Both models give the same observation. -/
private def agree (p : Program) (o : Observation) : Prop :=
  (p.runCopy 64).observe = o ∧ (p.runInPlace 64).observe = o

/-- `let a: T = m; let b: T = n; raise e`, with `a` and `b` in scope. -/
private def withPair (k : IntTy) (m n : Int) (e : Expr) : Expr :=
  .letIn "a" (.int k) (.int m) (.letIn "b" (.int k) (.int n) (.raise e))

/-- `a op b`. -/
private def bin (o : Op) : Expr := .op o [.var "a", .var "b"]

/-- What `withPair k m n (bin o)` shows. -/
private def shows (k : IntTy) (o : Op) (m n : Int) (shown : Ty) (out : Observation) : Prop :=
  agree (program shown (withPair k m n (bin o))) out

/-! ## numbers.integer-panics: overflow and division by zero -/

example : shows .i8 (.arith .add .i8) 127 1 (.int .i8) (.panicked .overflow) := ⟨rfl, rfl⟩
example : shows .i8 (.arith .sub .i8) (-128) 1 (.int .i8) (.panicked .overflow) := ⟨rfl, rfl⟩
example : shows .u8 (.arith .sub .u8) 0 1 (.int .u8) (.panicked .overflow) := ⟨rfl, rfl⟩
example : shows .i16 (.arith .mul .i16) 256 128 (.int .i16) (.panicked .overflow) := ⟨rfl, rfl⟩
example : shows .i64 (.arith .div .i64) 7 0 .i64 (.panicked .divideByZero) := ⟨rfl, rfl⟩
example : shows .u32 (.arith .rem .u32) 7 0 (.int .u32) (.panicked .divideByZero) := ⟨rfl, rfl⟩

/-- `MIN / -1` and `MIN % -1` overflow; `MIN % 1` is 0. -/
example : shows .i8 (.arith .div .i8) (-128) (-1) (.int .i8) (.panicked .overflow) := ⟨rfl, rfl⟩
example : shows .i16 (.arith .rem .i16) (-32768) (-1) (.int .i16) (.panicked .overflow) :=
  ⟨rfl, rfl⟩
example : shows .i16 (.arith .rem .i16) (-32768) 1 (.int .i16) (.raised (.int 0)) := ⟨rfl, rfl⟩

/-- Unary `-` on the minimum overflows. -/
example : agree (program (.int .i8)
    (.letIn "a" (.int .i8) (.int (-128)) (.raise (.op (.neg .i8) [.var "a"]))))
    (.panicked .overflow) := ⟨rfl, rfl⟩

/-! ## numbers.division-and-remainder: `/` truncates, `%` has the dividend's sign -/

example : shows .i64 (.arith .div .i64) (-7) 2 .i64 (.raised (.int (-3))) := ⟨rfl, rfl⟩
example : shows .i64 (.arith .div .i64) 7 (-2) .i64 (.raised (.int (-3))) := ⟨rfl, rfl⟩
example : shows .i64 (.arith .rem .i64) (-7) 2 .i64 (.raised (.int (-1))) := ⟨rfl, rfl⟩
example : shows .i64 (.arith .rem .i64) 7 (-2) .i64 (.raised (.int 1)) := ⟨rfl, rfl⟩
example : shows .u8 (.arith .div .u8) 200 7 (.int .u8) (.raised (.int 28)) := ⟨rfl, rfl⟩

/-! ## numbers.wrapping: two's complement -/

example : shows .i8 (.wrapping .add .i8) 127 1 (.int .i8) (.raised (.int (-128))) := ⟨rfl, rfl⟩
example : shows .i8 (.wrapping .mul .i8) (-128) (-1) (.int .i8) (.raised (.int (-128))) :=
  ⟨rfl, rfl⟩
example : shows .i16 (.wrapping .add .i16) 32767 32767 (.int .i16) (.raised (.int (-2))) :=
  ⟨rfl, rfl⟩
example : shows .u32 (.wrapping .sub .u32) 0 1 (.int .u32) (.raised (.int 4294967295)) :=
  ⟨rfl, rfl⟩

/-! ## numbers.shifts and numbers.shift-amounts -/

/-- `<<` discards the bits it shifts out: `1 << 7` on `i8` is `i8.MIN`. -/
example : shows .i8 (.shift .left .i8 .i8) 1 7 (.int .i8) (.raised (.int (-128))) := ⟨rfl, rfl⟩

/-- `>>` is arithmetic on a signed type and logical on an unsigned one. -/
example : shows .i8 (.shift .right .i8 .i8) (-8) 1 (.int .i8) (.raised (.int (-4))) := ⟨rfl, rfl⟩
example : shows .u8 (.shift .right .u8 .u8) 200 1 (.int .u8) (.raised (.int 100)) := ⟨rfl, rfl⟩
example : shows .i8 (.shift .right .i8 .i8) 127 7 (.int .i8) (.raised (.int 0)) := ⟨rfl, rfl⟩

/-- An amount of the type's width, or a negative one, overflows. -/
example : shows .i8 (.shift .left .i8 .i8) 1 8 (.int .i8) (.panicked .overflow) := ⟨rfl, rfl⟩
example : shows .i8 (.shift .right .i8 .i8) 1 8 (.int .i8) (.panicked .overflow) := ⟨rfl, rfl⟩
example : shows .i8 (.shift .left .i8 .i8) 1 (-1) (.int .i8) (.panicked .overflow) := ⟨rfl, rfl⟩

/-! ## numbers.bitwise-operators and numbers.comparisons -/

example : shows .u8 (.bitwise .and .u8) 12 10 (.int .u8) (.raised (.int 8)) := ⟨rfl, rfl⟩
example : shows .i8 (.bitwise .xor .i8) (-1) 5 (.int .i8) (.raised (.int (-6))) := ⟨rfl, rfl⟩
example : agree (program (.int .u8)
    (.letIn "a" (.int .u8) (.int 0) (.raise (.op (.complement .u8) [.var "a"]))))
    (.raised (.int 255)) := ⟨rfl, rfl⟩
example : shows .i32 (.compare .lt .i32) (-3) 2 .bool (.raised (.bool true)) := ⟨rfl, rfl⟩
example : shows .i32 (.compare .ge .i32) (-3) 2 .bool (.raised (.bool false)) := ⟨rfl, rfl⟩

/-! ## numbers.wrapping-conversions -/

/-- `.wrap_to_u8()` keeps the low bits: 300 is 44, and -1 is 255. -/
example : agree (program (.int .u8)
    (.letIn "a" .i64 (.int 300) (.raise (.op (.wrapTo .i64 .u8) [.var "a"]))))
    (.raised (.int 44)) := ⟨rfl, rfl⟩
example : agree (program (.int .u8)
    (.letIn "a" .i64 (.int (-1)) (.raise (.op (.wrapTo .i64 .u8) [.var "a"]))))
    (.raised (.int 255)) := ⟨rfl, rfl⟩

/-! ## What typing rejects -/

/-- A literal that doesn't fit its type has no type (numbers.integer-literals). -/
example (D : Decls) (s : RowScope) (Γ : Ctx) (fx : Effects) :
    ¬ HasType D s Γ fx (.int 128) (.int .i8) := by
  intro h
  cases h with
  | int h => exact absurd h (by decide)

/-- An integer literal at a float type must be one the type represents exactly
(numbers.integer-literals): `2^53` is an `f64`, and `2^53 + 1` isn't. -/
example : FloatTy.f64.Represents 9007199254740992 := ⟨1, 53, by decide, by decide, by decide⟩

example : ¬ FloatTy.f64.Represents 9007199254740993 := by
  rintro ⟨m, e, h, hm, -⟩
  cases e with
  | zero => simp at h; omega
  | succ e =>
    rw [Nat.pow_succ, ← Nat.mul_assoc] at h
    generalize m * 2 ^ e = k at h
    omega

/-- `-128` is an `i8`, and `-0` a `u8` (numbers.negative-literals). -/
example (D : Decls) (s : RowScope) (Γ : Ctx) (fx : Effects) :
    HasType D s Γ fx (.int (-128)) (.int .i8) := .int (by decide)

example (D : Decls) (s : RowScope) (Γ : Ctx) (fx : Effects) :
    HasType D s Γ fx (.int 0) (.int .u8) := .int (by decide)

/-- The operands of an arithmetic operator have one type: `i64 * f64` has no
signature (numbers.no-implicit-conversions). -/
example (τ : Ty) : ¬ Op.Sig (.arith .mul .i64) [.i64, .float .f64] τ := nofun

/-- Unary `-` is not defined on an unsigned type (numbers.unsigned-negation). -/
example (τs : List Ty) (τ : Ty) : ¬ Op.Sig (.neg .u8) τs τ := by
  intro h
  cases h with
  | neg h => exact absurd h (by decide)

/-- `%` on floats, `fmod`, is outside the model. -/
example (τs : List Ty) (τ : Ty) : ¬ Op.Sig (.farith .rem .f64) τs τ := by
  intro h
  cases h with
  | farith h => exact h rfl

end Stilt.Examples.Numbers
