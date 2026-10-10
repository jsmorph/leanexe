import LeanExe.ProofKit.F64DyadicBounds
import CodeLib.IEEE64.Operations

/-!
Multiplication by a power of two.  A normal power of two times a normal operand gives the exact
product while the product's exponent field stays below the infinity field, and an infinity of
the operand's sign from there on.
-/

namespace LeanExe.ProofKit.F64PowerScale
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

/-- A dyadic magnitude `m · 2 ^ (1074 + shift)` with `m < 2 ^ 53` rounds as the scaled magnitude
`m · 2 ^ shift`. -/
theorem dyadic_shifted_exact (negative : Bool) (m shift : Nat) (hm : m < 2 ^ 53) :
    Wasm.IEEE64.roundDyadicMagnitude negative (m * 2 ^ (1074 + shift)) 1074 =
      Wasm.IEEE64.roundScaledMagnitude negative (m * 2 ^ shift) := by
  by_cases hz : m = 0
  · subst m
    simp only [zero_mul]
    cases negative <;> decide +kernel
  let n := m * 2 ^ (1074 + shift)
  let outputShift := Nat.log2 n - (1074 + 52)
  have hn : n ≠ 0 := Nat.mul_ne_zero hz (by positivity)
  have hlog : Nat.log2 m < 53 := (Nat.log2_lt hz).mpr hm
  have hout : outputShift ≤ shift := by
    dsimp [outputShift, n]
    rw [F64DyadicBounds.log2_mul_two_pow m _ hz]
    omega
  change Wasm.IEEE64.roundDyadicMagnitude negative n 1074 =
    Wasm.IEEE64.roundScaledMagnitude negative (m * 2 ^ shift)
  unfold Wasm.IEEE64.roundDyadicMagnitude
  simp only [beq_iff_eq, ite_eq_right hn]
  change Wasm.IEEE64.roundScaledMagnitude negative
    (if outputShift = 0 then Wasm.IEEE32.roundShift n 1074
      else Wasm.IEEE32.roundShift n (1074 + outputShift) * 2 ^ outputShift) =
    Wasm.IEEE64.roundScaledMagnitude negative (m * 2 ^ shift)
  by_cases ho : outputShift = 0
  · have hid : n = (m * 2 ^ shift) * 2 ^ 1074 := by
      dsimp [n]
      rw [pow_add]
      ring
    rw [ite_eq_left ho, hid, F64DyadicBounds.roundShift_mul_two_pow _ _ (by norm_num)]
  · have hid : n =
        (m * 2 ^ (shift - outputShift)) * 2 ^ (1074 + outputShift) := by
      have he : 1074 + shift =
          (shift - outputShift) + (1074 + outputShift) := by omega
      dsimp [n]
      rw [Nat.mul_assoc, ← pow_add, he]
    rw [ite_eq_right ho, hid,
      F64DyadicBounds.roundShift_mul_two_pow _ _ (by omega), Nat.mul_assoc, ← pow_add,
      Nat.sub_add_cancel hout]

/-- A normal significand `s` shifted left by `shift` packs exactly, or as an infinity once the
exponent field reaches `0x7FF`. -/
theorem roundScaledMagnitude_shifted (negative : Bool) (s shift : Nat)
    (hl : 2 ^ 52 ≤ s) (hu : s < 2 ^ 53) :
    Wasm.IEEE64.roundScaledMagnitude negative (s * 2 ^ shift) =
      if 0x7FF ≤ shift + 1 then Wasm.IEEE64.infinity negative
      else Wasm.IEEE64.encodeFinite negative (shift + 1) (s - 2 ^ 52) := by
  by_cases hs : shift = 0
  · subst shift
    have h1 : ¬ s < 2 ^ 52 := by omega
    have h2 : ¬ (0x7FF ≤ 0 + 1) := by decide
    simp only [pow_zero, Nat.mul_one, Wasm.IEEE64.roundScaledMagnitude, h1, hu, h2,
      ite_false, ite_true]
  · have hsz : s ≠ 0 := by omega
    have hlog : Nat.log2 s = 52 := by
      apply le_antisymm
      · exact Nat.lt_succ_iff.mp ((Nat.log2_lt hsz).mpr hu)
      · exact (Nat.le_log2 hsz).mpr hl
    have hn : Nat.log2 (s * 2 ^ shift) = 52 + shift := by
      rw [F64DyadicBounds.log2_mul_two_pow s shift hsz, hlog]
    have h2 : 2 ≤ 2 ^ shift := Nat.one_lt_two_pow hs
    have hbig : 2 ^ 53 ≤ s * 2 ^ shift :=
      calc
        2 ^ 53 = 2 ^ 52 * 2 := by norm_num
        _ ≤ s * 2 ^ shift := Nat.mul_le_mul hl h2
    have hlt52 : ¬ s * 2 ^ shift < 2 ^ 52 :=
      not_lt.mpr (le_trans (by norm_num) hbig)
    have hlt53 : ¬ s * 2 ^ shift < 2 ^ 53 := not_lt.mpr hbig
    have hr : Wasm.IEEE32.roundShift (s * 2 ^ shift) shift = s :=
      F64DyadicBounds.roundShift_mul_two_pow s shift (Nat.pos_of_ne_zero hs)
    have hne : (s == 2 ^ 53) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      omega
    unfold Wasm.IEEE64.roundScaledMagnitude
    simp only [hlt52, hlt53, ite_false, hn, show 52 + shift - 52 = shift by omega, hr, hne]
    rfl

/-- The product of the power of two with exponent field `ea` and a normal operand `y`, when the
product is at least the smallest normal magnitude. -/
theorem mul_power (ea : Nat) (y : UInt64) (hea : 1 ≤ ea) (hea' : ea < 0x7FF)
    (hyf : Finite y) (hye : 1 ≤ Wasm.IEEE64.exponent y)
    (hsum : 1024 ≤ Wasm.IEEE64.exponent y + ea) :
    Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false ea 0) y =
      if 0x7FF ≤ Wasm.IEEE64.exponent y + ea - 1023 then
        Wasm.IEEE64.infinity (Wasm.IEEE64.sign y)
      else Wasm.IEEE64.encodeFinite (Wasm.IEEE64.sign y)
        (Wasm.IEEE64.exponent y + ea - 1023) (Wasm.IEEE64.fraction y) := by
  have haf : Finite (Wasm.IEEE64.encodeFinite false ea 0) :=
    finite_encodeFinite false ea 0 hea' (by norm_num)
  have has : Wasm.IEEE64.sign (Wasm.IEEE64.encodeFinite false ea 0) = false :=
    sign_encodeFinite false ea 0 (by omega) (by norm_num)
  have ham : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.encodeFinite false ea 0) =
      2 ^ 52 * 2 ^ (ea - 1) := by
    rw [scaledMagnitude_encodeFinite false ea 0 (by omega) (by norm_num)]
    simp [show ea ≠ 0 by omega]
  have hym : Wasm.IEEE64.scaledMagnitude y =
      (2 ^ 52 + Wasm.IEEE64.fraction y) * 2 ^ (Wasm.IEEE64.exponent y - 1) := by
    simp [Wasm.IEEE64.scaledMagnitude, show Wasm.IEEE64.exponent y ≠ 0 by omega]
  have hf : Wasm.IEEE64.fraction y < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hprod : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.encodeFinite false ea 0) *
      Wasm.IEEE64.scaledMagnitude y =
      (2 ^ 52 + Wasm.IEEE64.fraction y) *
        2 ^ (1074 + (Wasm.IEEE64.exponent y + ea - 1024)) := by
    rw [ham, hym]
    have he : 52 + (ea - 1) + (Wasm.IEEE64.exponent y - 1) =
        1074 + (Wasm.IEEE64.exponent y + ea - 1024) := by omega
    rw [← he, pow_add, pow_add]
    ring
  rw [mul_finite_rounder _ y haf hyf, has, hprod]
  have hsign : (false != Wasm.IEEE64.sign y) = Wasm.IEEE64.sign y := by
    cases Wasm.IEEE64.sign y <;> rfl
  rw [hsign, dyadic_shifted_exact _ _ _ (by omega),
    roundScaledMagnitude_shifted _ _ _ (by omega) (by omega)]
  have h1 : Wasm.IEEE64.exponent y + ea - 1024 + 1 = Wasm.IEEE64.exponent y + ea - 1023 := by
    omega
  rw [h1, Nat.add_sub_cancel_left]

private theorem pow_shift (e ea : Nat) (h1 : 1 ≤ e) (h : 1024 ≤ e + ea) :
    (2 : ℝ) ^ (e + ea - 1024) = (2 : ℝ) ^ ((ea : Int) - 1023) * (2 : ℝ) ^ (e - 1) := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  omega

theorem mul_power_finite (ea : Nat) (y : UInt64) (hea : 1 ≤ ea) (hea' : ea < 0x7FF)
    (hyf : Finite y) (hye : 1 ≤ Wasm.IEEE64.exponent y)
    (hsum : 1024 ≤ Wasm.IEEE64.exponent y + ea)
    (hfin : Wasm.IEEE64.exponent y + ea - 1023 < 0x7FF) :
    Finite (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false ea 0) y) ∧
      value (Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false ea 0) y) =
        (2 : ℝ) ^ ((ea : Int) - 1023) * value y := by
  have hf : Wasm.IEEE64.fraction y < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  rw [mul_power ea y hea hea' hyf hye hsum, ite_eq_right (by omega)]
  refine ⟨finite_encodeFinite _ _ _ hfin hf, ?_⟩
  have hym : Wasm.IEEE64.scaledMagnitude y =
      (2 ^ 52 + Wasm.IEEE64.fraction y) * 2 ^ (Wasm.IEEE64.exponent y - 1) := by
    simp [Wasm.IEEE64.scaledMagnitude, show Wasm.IEEE64.exponent y ≠ 0 by omega]
  have hrm : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.encodeFinite (Wasm.IEEE64.sign y)
      (Wasm.IEEE64.exponent y + ea - 1023) (Wasm.IEEE64.fraction y)) =
      (2 ^ 52 + Wasm.IEEE64.fraction y) * 2 ^ (Wasm.IEEE64.exponent y + ea - 1024) := by
    rw [scaledMagnitude_encodeFinite _ _ _ (by omega) hf]
    simp only [show Wasm.IEEE64.exponent y + ea - 1023 ≠ 0 by omega, ite_false,
      show Wasm.IEEE64.exponent y + ea - 1023 - 1 = Wasm.IEEE64.exponent y + ea - 1024 by omega]
  have hrs : Wasm.IEEE64.sign (Wasm.IEEE64.encodeFinite (Wasm.IEEE64.sign y)
      (Wasm.IEEE64.exponent y + ea - 1023) (Wasm.IEEE64.fraction y)) = Wasm.IEEE64.sign y :=
    sign_encodeFinite _ _ _ (by omega) hf
  simp only [value, Wasm.IEEE64.scaledValue, hrm, hrs, hym]
  split <;> push_cast <;> rw [pow_shift _ _ hye hsum] <;> ring

theorem mul_power_overflow (ea : Nat) (y : UInt64) (hea : 1 ≤ ea) (hea' : ea < 0x7FF)
    (hyf : Finite y) (hye : 1 ≤ Wasm.IEEE64.exponent y)
    (hsum : 1024 ≤ Wasm.IEEE64.exponent y + ea)
    (hinf : 0x7FF ≤ Wasm.IEEE64.exponent y + ea - 1023) :
    Wasm.IEEE64.mul (Wasm.IEEE64.encodeFinite false ea 0) y =
      Wasm.IEEE64.infinity (Wasm.IEEE64.sign y) := by
  rw [mul_power ea y hea hea' hyf hye hsum, ite_eq_left hinf]

#print axioms dyadic_shifted_exact
#print axioms roundScaledMagnitude_shifted
#print axioms mul_power
#print axioms mul_power_finite
#print axioms mul_power_overflow

end LeanExe.ProofKit.F64PowerScale
