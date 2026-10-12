import Verified.Examples.SinhWords
import LeanExe.ProofKit.F64MulEnclosure
import LeanExe.ProofKit.F64RoundFinish
import LeanExe.ProofKit.F64Sterbenz

/-!
Overflow of a product.  The rounding of a scaled product magnitude `n ≥ 2 ^ 3172`, whose value is
at least `2 ^ 1024`, is the infinity of its sign (`dyadic_overflow`): the shifted magnitude
rounds into `[2 ^ 52, 2 ^ 53]` and the shift reaches the exponent field 2047.  So `x · 1.0e+307`
is the infinity of the sign of `x` from `abs(x) ≥ 512` on (`mul_shuge`), the last branch of
`Sinh.sinhWith`.
-/

namespace Verified.Examples.SinhOverflow
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096
set_option maxRecDepth 100000

theorem dyadic_overflow (neg : Bool) (n : Nat) (hn : 2 ^ 3172 ≤ n) :
    Wasm.IEEE64.roundDyadicMagnitude neg n 1074 = Wasm.IEEE64.infinity neg := by
  have hn0 : n ≠ 0 := by positivity
  have hL1 : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn0
  have hL2 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have hL : 3172 ≤ Nat.log2 n := (Nat.le_log2 hn0).2 hn
  set L := Nat.log2 n with hLdef
  set os := L - (1074 + 52) with hos
  have hos1 : 2046 ≤ os := by omega
  have hLos : L = os + 1126 := by omega
  -- The shifted magnitude rounds into `[2 ^ 52, 2 ^ 53]`.
  have he := F64Adjacent.shift_real_error n 1074 os (by norm_num)
  set r := Wasm.IEEE32.roundShift n (1074 + os) with hrdef
  have hn1 : (2 : ℝ) ^ (52 + os) ≤ (n : ℝ) / 2 ^ 1074 := by
    rw [le_div_iff₀ (by positivity), ← pow_add]
    have : (2 : ℝ) ^ L ≤ n := by exact_mod_cast hL1
    rw [hLos] at this
    calc (2 : ℝ) ^ (52 + os + 1074) = 2 ^ (os + 1126) := by ring_nf
      _ ≤ n := this
  have hn2 : (n : ℝ) / 2 ^ 1074 < 2 ^ (53 + os) := by
    rw [div_lt_iff₀ (by positivity), ← pow_add]
    have : (n : ℝ) < 2 ^ (L + 1) := by exact_mod_cast hL2
    rw [hLos] at this
    calc (n : ℝ) < 2 ^ (os + 1126 + 1) := this
      _ = 2 ^ (53 + os + 1074) := by ring_nf
  obtain ⟨he1, he2⟩ := abs_le.mp he
  have hp : (0 : ℝ) < 2 ^ os := by positivity
  have hr1 : (2 : ℝ) ^ 52 - 1 < r := by
    have h1 : ((2 : ℝ) ^ 52 - 1 / 2) * 2 ^ os ≤ (r : ℝ) * 2 ^ os := by
      have : (2 : ℝ) ^ (52 + os) = 2 ^ 52 * 2 ^ os := pow_add _ _ _
      linarith
    have h2 := le_of_mul_le_mul_right h1 hp
    linarith
  have hr2 : (r : ℝ) < 2 ^ 53 + 1 := by
    have h1 : (r : ℝ) * 2 ^ os ≤ ((2 : ℝ) ^ 53 + 1 / 2) * 2 ^ os := by
      have : (2 : ℝ) ^ (53 + os) = 2 ^ 53 * 2 ^ os := pow_add _ _ _
      linarith
    have h2 := le_of_mul_le_mul_right h1 hp
    linarith
  have hrlo : 2 ^ 52 ≤ r := by
    have : ((2 ^ 52 - 1 : ℕ) : ℝ) < r := by push_cast; linarith
    have := Nat.cast_lt.mp this
    omega
  have hrhi : r ≤ 2 ^ 53 := by
    have : (r : ℝ) < ((2 ^ 53 + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.mp this
    omega
  unfold Wasm.IEEE64.roundDyadicMagnitude
  have hnz : (n == 0) = false := by simp [hn0]
  have hosz : (os == 0) = false := by
    rw [beq_eq_false_iff_ne]
    exact (lt_of_lt_of_le (by norm_num) hos1).ne'
  simp only [hnz, Bool.false_eq_true, ite_false, ← hLdef, ← hos, hosz]
  rw [← hrdef, F64RoundFinish.roundScaled_mul_pow neg r os (by omega) hrlo hrhi]
  have h1 : 2047 ≤ os + 1 := by omega
  have h2 : 2047 ≤ os + 2 := by omega
  split_ifs <;> rfl

/-- `x · 1.0e+307` for `abs(x) ≥ 512`. -/
theorem mul_shuge (x : UInt64) (hxf : Finite x) (hx : 512 ≤ |value x|) :
    Wasm.IEEE64.mul x 0x7FAC7B1F3CAC7433 = Wasm.IEEE64.infinity (Wasm.IEEE64.sign x) := by
  have hsf : Finite (0x7FAC7B1F3CAC7433 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  rw [mul_finite_rounder _ _ hxf hsf]
  have hss : Wasm.IEEE64.sign (0x7FAC7B1F3CAC7433 : UInt64) = false := by decide +kernel
  have hsm : 2 ^ 2092 ≤ Wasm.IEEE64.scaledMagnitude (0x7FAC7B1F3CAC7433 : UInt64) := by
    decide +kernel
  have hxm : 2 ^ 1083 ≤ Wasm.IEEE64.scaledMagnitude x := by
    have h := F64Sterbenz.value_abs_scaled x
    have : (2 : ℝ) ^ 1083 ≤ Wasm.IEEE64.scaledMagnitude x := by
      rw [← h]
      have : (2 : ℝ) ^ 1083 = 512 * 2 ^ 1074 := by norm_num
      rw [this]
      exact mul_le_mul_of_nonneg_right hx (by positivity)
    exact_mod_cast this
  rw [hss, show (Wasm.IEEE64.sign x != false) = Wasm.IEEE64.sign x by
    cases Wasm.IEEE64.sign x <;> rfl]
  apply dyadic_overflow
  calc 2 ^ 3172 ≤ 2 ^ 1083 * 2 ^ 2092 := by norm_num
    _ ≤ _ := Nat.mul_le_mul hxm hsm

#print axioms dyadic_overflow
#print axioms mul_shuge

end Verified.Examples.SinhOverflow
