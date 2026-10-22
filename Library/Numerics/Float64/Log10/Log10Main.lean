import Library.Numerics.Float64.Log10.Log10Final
import Library.Numerics.Float64.Log.LogMain

/-!
`Log10.log10` on positive normal and subnormal arguments other than 1: one step of the
nearest-even reference of `Real.logb 10 x`.  `reduce10` gives the reduced argument `x'` and `k`
from the exponent field `E` and fraction field `F` of the argument word, scaled by `2 ^ 54` for a
subnormal argument: `x = 2 ^ k x'` with `x'` from `0.7071` to below `1.4143`, so `f = x' - 1` is
exact by Sterbenz's lemma and lies on the grid of `2 ^ -53`.  `Log10Final.tail10` does the rest.
-/

namespace Library.Numerics.Float64.Log10.Log10Main
open CodeLib.IEEE64 LeanExe.ProofKit Log10Bits

set_option exponentiation.threshold 4096

theorem one_word : Finite (0x3FF0000000000000 : UInt64) ∧ value (0x3FF0000000000000 : UInt64) = 1 := by
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_⟩
  have h : PolyBound.ratOfWord 0x3FF0000000000000 = 1 := by decide +kernel
  rw [← PolyBound.ratOfWord_cast, h]
  norm_num

/-- The reduction of an argument word with exponent field `E` and fraction field `F`. -/
theorem reduce10 (xw k0 : UInt64) (E F : Nat) (K0 : Int) (hE1 : 1 ≤ E) (hE2 : E ≤ 2046)
    (hF : F < 4503599627370496) (hxw : xw.toNat = E * 4503599627370496 + F)
    (hk0 : (k0.toNat : Int) = K0 % 18446744073709551616) :
    ∃ b : Nat, b ≤ 1 ∧
      Finite (Wasm.IEEE64.sub (xrOf xw) 0x3FF0000000000000) ∧
      value (Wasm.IEEE64.sub (xrOf xw) 0x3FF0000000000000) =
        ((2 : ℝ) ^ 52 + F) / 2 ^ (52 + b) - 1 ∧
      -29290 / 100000 ≤ ((2 : ℝ) ^ 52 + F) / 2 ^ (52 + b) - 1 ∧
      ((2 : ℝ) ^ 52 + F) / 2 ^ (52 + b) - 1 ≤ 41422 / 100000 ∧
      ((kWord10 xw k0).toNat : Int) = (K0 + E - 1023 + b) % 18446744073709551616 ∧
      Wasm.IEEE64.isNaN (xrOf xw) = false ∧
      (b = 0 ↔ F / 4294967296 < 434332) := by
  obtain ⟨hxr, hk, hb1⟩ := xr_fields xw k0 E F K0 hE1 hE2 hF hxw hk0
  set b := (F / 4294967296 + 614244) / 1048576 with hb
  have hbiff : b = 0 ↔ F / 4294967296 < 434332 := by omega
  have hxrs : Wasm.IEEE64.sign (xrOf xw) = false := by
    simp only [Wasm.IEEE64.sign, hxr, decide_eq_false_iff_not, not_le, Nat.reducePow]
    omega
  have hxre : Wasm.IEEE64.exponent (xrOf xw) = 1023 - b := by
    simp only [Wasm.IEEE64.exponent, hxr, Nat.reducePow]
    omega
  have hxrf : Wasm.IEEE64.fraction (xrOf xw) = F := by
    simp only [Wasm.IEEE64.fraction, hxr, Nat.reducePow]
    omega
  have hxrfin : Finite (xrOf xw) := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hxre, bne_iff_ne, ne_eq]
    omega
  have hxrv : value (xrOf xw) = ((2 : ℝ) ^ 52 + F) / 2 ^ (52 + b) := by
    rw [F64Magnitude.normal_value _ hxrs (by omega), hxre, hxrf]
    rw [div_eq_div_iff (by positivity) (by positivity), mul_assoc, ← pow_add,
      show 1023 - b - 1 + (52 + b) = 1074 by omega]
  have hFr : (F : ℝ) < 2 ^ 52 := by exact_mod_cast hF
  have hxrb : 70710 / 100000 ≤ value (xrOf xw) ∧ value (xrOf xw) ≤ 141422 / 100000 := by
    rw [hxrv]
    rcases Nat.lt_or_ge (F / 4294967296) 434332 with h | h
    · have hb0 : b = 0 := hbiff.mpr h
      rw [hb0]
      have hF2 : F < 434332 * 4294967296 := by omega
      have hF2r : (F : ℝ) < 434332 * 4294967296 := by exact_mod_cast hF2
      constructor
      · rw [le_div_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ F := Nat.cast_nonneg F
        norm_num
        linarith
      · rw [div_le_iff₀ (by positivity)]
        norm_num
        linarith
    · have hb0 : b = 1 := by omega
      rw [hb0]
      have hF2 : 434332 * 4294967296 ≤ F := by omega
      have hF2r : (434332 * 4294967296 : ℝ) ≤ F := by exact_mod_cast hF2
      constructor
      · rw [le_div_iff₀ (by positivity)]
        norm_num
        linarith
      · rw [div_le_iff₀ (by positivity)]
        norm_num
        linarith
  obtain ⟨hxl, hxu⟩ := hxrb
  obtain ⟨hof, hov⟩ := one_word
  obtain ⟨hsf, hsv⟩ := F64Sterbenz.sub_exact (xrOf xw) 0x3FF0000000000000 hxrfin hof
    (by rw [hov, abs_of_pos (by linarith : (0 : ℝ) < value (xrOf xw)), abs_le]
        constructor <;> linarith)
    (by rw [hov, abs_one, abs_le]; constructor <;> linarith)
    (by rw [hov, abs_one]; norm_num)
  rw [hov, hxrv] at hsv
  rw [hxrv] at hxl hxu
  refine ⟨b, hb1, hsf, hsv, by linarith, by linarith, hk, not_nan_of_finite hxrfin, hbiff⟩

#print axioms one_word
#print axioms reduce10

/-- The high and low words of an argument word with exponent field `E` and fraction field `F`. -/
theorem words (w : UInt64) (E F : Nat) (hw : w.toNat = E * 4503599627370496 + F)
    (hF : F < 4503599627370496) :
    (w >>> 32).toNat = E * 1048576 + F / 4294967296 ∧
      (w >>> 32 >>> 31).toNat = (E * 1048576 + F / 4294967296) / 2147483648 ∧
      (w &&& 0xFFFFFFFF).toNat = F % 4294967296 ∧
      (w >>> 32 &&& 0x7fffffff).toNat = (E * 1048576 + F / 4294967296) % 2147483648 := by
  have h1 : (w >>> 32).toNat = E * 1048576 + F / 4294967296 := by
    simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow,
      Nat.reducePow, hw]
    omega
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [UInt64.toNat_shiftRight, h1]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  · rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, hw]
    omega
  · rw [UInt64.toNat_and, h1, show (0x7fffffff : UInt64).toNat = 2 ^ 31 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]

/-- `f = x' - 1` is 0 or at least `2 ^ -53` in magnitude, and its word is zero or of exponent
field at least 2. -/
theorem f_grid (fw : UInt64) (F b : Nat) (hb : b ≤ 1)
    (hfv : value fw = ((2 : ℝ) ^ 52 + F) / 2 ^ (52 + b) - 1) :
    (value fw = 0 ∨ 1 / 2 ^ 60 ≤ |value fw|) ∧
      (Wasm.IEEE64.scaledMagnitude fw = 0 ∨ 2 ≤ Wasm.IEEE64.exponent fw) := by
  set N : Int := (2 ^ 52 + F : Int) - 2 ^ (52 + b) with hN
  have hv : value fw = (N : ℝ) / 2 ^ (52 + b) := by
    rw [hfv, hN]
    push_cast
    field_simp <;> norm_num
  have hgrid : value fw = 0 ∨ 1 / 2 ^ 60 ≤ |value fw| := by
    by_cases h0 : N = 0
    · left
      rw [hv, h0]
      simp
    · right
      have h1 : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs h0
      rw [hv, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (52 + b)), le_div_iff₀ (by positivity)]
      have h2 : (2 : ℝ) ^ (52 + b) ≤ 2 ^ 53 := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : (1 : ℝ) / 2 ^ 60 * 2 ^ 53 ≤ 1 := by norm_num
      nlinarith
  refine ⟨hgrid, ?_⟩
  rcases hgrid with h | h
  · left
    have h2 := F64Sterbenz.value_abs_scaled fw
    rw [h, abs_zero, zero_mul] at h2
    exact_mod_cast h2.symm
  · right
    exact Log10Final.exponent_two fw (le_trans (by norm_num) h)

#print axioms words
#print axioms f_grid

/-- The main path from an argument word with exponent field `E` and fraction field `F`, scaled
by `2 ^ -K0` before the reduction: one step against `log (2 ^ K0 X) / log 10`, where `X` is the
value of the word, when the result is not exactly 0. -/
theorem main10 (xw k0 : UInt64) (E F : Nat) (K0 : Int) (hE1 : 1 ≤ E) (hE2 : E ≤ 2046)
    (hF : F < 4503599627370496) (hxw : xw.toNat = E * 4503599627370496 + F)
    (hk0 : (k0.toNat : Int) = K0 % 18446744073709551616) (hK0 : -54 ≤ K0 ∧ K0 ≤ 0)
    (hnot : K0 + E = 1023 → F ≠ 0) :
    Wasm.IEEE64.isNaN (xrOf xw) = false ∧
    Wasm.IEEE64.isNaN (Wasm.IEEE64.sub (Wasm.IEEE64.sub (xrOf xw) 0x3FF0000000000000)
      (Wasm.IEEE64.mul (Wasm.IEEE64.mul 0x3FE0000000000000
        (Wasm.IEEE64.sub (xrOf xw) 0x3FF0000000000000))
        (Wasm.IEEE64.sub (xrOf xw) 0x3FF0000000000000)) &&& (0xFFFFFFFF00000000 : UInt64)) = false ∧
    F64SignedRounding.WithinSteps 1
      (Real.log (((2 : ℝ) ^ 52 + F) * (2 : ℝ) ^ ((E : Int) - 1075) * (2 : ℝ) ^ K0) / Real.log 10)
      (tailWord (Wasm.IEEE64.sub (xrOf xw) 0x3FF0000000000000)
        (Library.Numerics.Float64.Log2.Log2Power.kdBits (kWord10 xw k0))) := by
  obtain ⟨b, hb1, hff, hfv, hflo, hfhi, hk, hxrn, hbiff⟩ := reduce10 xw k0 E F K0 hE1 hE2 hF hxw hk0
  obtain ⟨hgrid, hmag⟩ := f_grid _ F b hb1 hfv
  set fw := Wasm.IEEE64.sub (xrOf xw) 0x3FF0000000000000 with hfw
  have hkd := Library.Numerics.Float64.Log.LogCoreBits.kd_value (kWord10 xw k0) (K0 + E - 1023 + b) (by omega) (by omega) hk
  rw [Library.Numerics.Float64.Log2.Log2Power.kd_bits] at hkd
  have hK : |K0 + (E : Int) - 1023 + (b : Int)| ≤ 1077 := by
    rw [abs_le]
    constructor <;> omega
  have hK0' : K0 + (E : Int) - 1023 + (b : Int) = 0 → value fw ≠ 0 := by
    intro hKz hf0
    rw [hfv] at hf0
    have h1 : ((2 : ℝ) ^ 52 + F) = 2 ^ (52 + b) := by
      have h2 : ((2 : ℝ) ^ 52 + F) / 2 ^ (52 + b) = 1 := by linarith
      rwa [div_eq_one_iff_eq (by positivity)] at h2
    have h1n : 2 ^ 52 + F = 2 ^ (52 + b) := by exact_mod_cast h1
    rcases (show b = 0 ∨ b = 1 by omega) with hb | hb <;> rw [hb] at h1n <;> norm_num at h1n
    · exact hnot (by omega) h1n
    · omega
  obtain ⟨hnan, hw⟩ := Log10Final.tail10 fw (Library.Numerics.Float64.Log2.Log2Power.kdBits (kWord10 xw k0))
    (K0 + E - 1023 + b) hff (by rw [hfv]; exact hflo) (by rw [hfv]; exact hfhi) hmag hgrid
    hkd.1 hkd.2 hK hK0'
  refine ⟨hxrn, hnan, ?_⟩
  have hX : ((2 : ℝ) ^ 52 + F) * (2 : ℝ) ^ ((E : Int) - 1075) * (2 : ℝ) ^ K0 =
      (2 : ℝ) ^ (K0 + (E : Int) - 1023 + (b : Int)) * (1 + value fw) := by
    rw [hfv, show (1 : ℝ) + (((2 : ℝ) ^ 52 + F) / 2 ^ (52 + b) - 1) =
      ((2 : ℝ) ^ 52 + F) / 2 ^ (52 + b) by ring]
    rw [show K0 + (E : Int) - 1023 + (b : Int) = ((E : Int) - 1075) + K0 + ((52 + b : Nat) : Int) by
      push_cast; ring, zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), zpow_natCast]
    field_simp
  have hpos : 0 < 1 + value fw := by linarith
  rw [hX, Real.log_mul (by positivity) hpos.ne', Real.log_zpow]
  push_cast at hw ⊢
  exact hw

#print axioms main10

end Library.Numerics.Float64.Log10.Log10Main
