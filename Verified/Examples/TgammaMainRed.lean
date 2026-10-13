import Verified.Examples.TgammaFloor
import Verified.Examples.TgammaSpecial
import Verified.Examples.TgammaRecip
import LeanExe.ProofKit.F64Convert
import LeanExe.ProofKit.F64GridExact

/-!
The reduction of `tgammaWith` on `(-3, 4)`.  For a finite `x` with `-3 < x < 4` and `|x| ≥ 1/4`,
`i = roundEven (x - 7/2)` is an integer `I` from -7 to 0, `i + 7/2` is exact, and
`d = x - (i + 7/2)` is exact with `|d| ≤ 1/2 + 2 ^ -50` (`main_red`).  The subtraction `x - 7/2` is
exact from 2 on, which excludes `I = 1`.  `d` is exact because `x` is a multiple of `2 ^ -53` from
`1/2` on and of `2 ^ -54` from `1/4` on, where `|d| ≤ 1/4`.  `count_spec` gives `|i|`, the test
`|i| > 0`, and the loop count `(|i| - 1).toUInt64`.
-/

namespace Verified.Examples.TgammaMainRed
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest F64TwoSum Tgamma TgammaDD
  TgammaFloor

set_option exponentiation.threshold 4096

theorem half7_bits : (3.5 : Float).toBits = 0x400C000000000000 := rfl

theorem half7_finite : Finite (3.5 : Float).toBits := by
  rw [half7_bits]; unfold CodeLib.IEEE64.Finite; decide

theorem half7_value : value (3.5 : Float).toBits = 7 / 2 := by
  rw [half7_bits, TgammaSpecial.lit_value 0x400C000000000000 (7 / 2) (by decide +kernel)]
  norm_num

theorem natAbs_of_abs (z : ℤ) (hz : |(z : ℝ)| ≤ 2 ^ 53) : z.natAbs ≤ 2 ^ 53 := by
  have h1 : |z| ≤ 2 ^ 53 := by exact_mod_cast hz
  have h2 : (z.natAbs : ℤ) ≤ 2 ^ 53 := by rw [Int.natCast_natAbs]; exact h1
  exact_mod_cast h2

theorem sv_eq (a b : UInt64) (z : ℤ) (g : ℕ) (h : (value a - value b) * 2 ^ 1074 = z * 2 ^ g) :
    Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b = z * 2 ^ g := by
  have : ((Wasm.IEEE64.scaledValue a - Wasm.IEEE64.scaledValue b : ℤ) : ℝ) = ((z * 2 ^ g : ℤ) : ℝ) := by
    rw [value, value, sub_mul, div_mul_cancel₀ _ (by positivity), div_mul_cancel₀ _ (by positivity)]
      at h
    push_cast
    exact h
  exact_mod_cast this

/-- A difference of two words on the grid `2 ^ (g - 1074)` with at most 53 bits is exact. -/
theorem sub_exact (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (z : ℤ) (g : ℕ)
    (hg : g ≤ 2043) (h : (value a.toBits - value b.toBits) * 2 ^ 1074 = z * 2 ^ g)
    (hz : |(z : ℝ)| ≤ 2 ^ 53) :
    Finite (a - b).toBits ∧ value (a - b).toBits = value a.toBits - value b.toBits := by
  rw [F64Bits.toBits_sub]
  obtain ⟨hf, hv⟩ := F64GridExact.sub_grid_exact a.toBits b.toBits ha hb z g
    (sv_eq _ _ z g h) (natAbs_of_abs z hz) hg
  refine ⟨hf, ?_⟩
  rw [value, value, value, hv]
  push_cast
  ring

/-- A sum of two words on the grid `2 ^ (g - 1074)` with at most 53 bits is exact. -/
theorem add_exact (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (z : ℤ) (g : ℕ)
    (hg : g ≤ 2043) (h : (value a.toBits + value b.toBits) * 2 ^ 1074 = z * 2 ^ g)
    (hz : |(z : ℝ)| ≤ 2 ^ 53) :
    Finite (a + b).toBits ∧ value (a + b).toBits = value a.toBits + value b.toBits := by
  have hs : Wasm.IEEE64.scaledValue a.toBits + Wasm.IEEE64.scaledValue b.toBits = z * 2 ^ g := by
    have : ((Wasm.IEEE64.scaledValue a.toBits + Wasm.IEEE64.scaledValue b.toBits : ℤ) : ℝ) =
        ((z * 2 ^ g : ℤ) : ℝ) := by
      rw [value, value, add_mul, div_mul_cancel₀ _ (by positivity),
        div_mul_cancel₀ _ (by positivity)] at h
      push_cast
      exact h
    exact_mod_cast this
  rw [F64Bits.toBits_add]
  obtain ⟨hf, hv⟩ := F64GridExact.grid_add_exact a.toBits b.toBits ha hb z g hs
    (natAbs_of_abs z hz) hg
  refine ⟨hf, ?_⟩
  rw [value, value, value, hv]
  push_cast
  ring

/-- A word of magnitude at least `2 ^ (53 + g - 1074)` is a multiple of `2 ^ (g + 1 - 1074)`. -/
theorem grid (w : UInt64) (hw : Finite w) (g : ℕ) (hg : g ≤ 2042)
    (h : (2 : ℝ) ^ (53 + g) / 2 ^ 1074 ≤ |value w|) :
    ∃ K : ℤ, value w * 2 ^ 1074 = K * 2 ^ (g + 1) := by
  obtain ⟨K, hK⟩ := rounded_dvd w (value w) (rounded_self w hw) g hg h
  refine ⟨K, ?_⟩
  rw [value, div_mul_cancel₀ _ (by positivity), hK]
  push_cast
  ring

/-- **The reduction about `7/2`.** -/
theorem main_red (x : Float) (hx : Finite x.toBits) (h1 : -3 < value x.toBits)
    (h2 : value x.toBits < 4) (h4 : 1 / 4 ≤ |value x.toBits|) :
    ∃ I : ℤ, -7 ≤ I ∧ I ≤ 0 ∧ Finite (roundEven (x - 3.5)).toBits ∧
      value (roundEven (x - 3.5)).toBits = I ∧
      Finite (roundEven (x - 3.5) + 3.5).toBits ∧
      value (roundEven (x - 3.5) + 3.5).toBits = I + 7 / 2 ∧
      Finite (x - (roundEven (x - 3.5) + 3.5)).toBits ∧
      value (x - (roundEven (x - 3.5) + 3.5)).toBits = value x.toBits - (I + 7 / 2) ∧
      |value x.toBits - (I + 7 / 2)| ≤ 1 / 2 + 1 / 2 ^ 50 := by
  set vx := value x.toBits with hvx
  have hs := fapprox_sub (fapprox_self x hx) (fapprox_self 3.5 half7_finite) 7
    (by
      rw [half7_value, add_zero, add_zero, abs_le]
      constructor <;> linarith)
    (by norm_num)
  rw [half7_value] at hs
  set s := x - 3.5 with hsdef
  have hse : |value s.toBits - (vx - 7 / 2)| ≤ 1 / 2 ^ 50 := by
    have := hs.2
    linarith [(by norm_num : (0 : ℝ) + 0 + 7 / 2 ^ 53 ≤ 1 / 2 ^ 50)]
  obtain ⟨hif, ⟨R, hR⟩, hRs, -⟩ := roundEven_spec s hs.1
  obtain ⟨hRs1, hRs2⟩ := abs_le.mp hRs
  obtain ⟨hse1, hse2⟩ := abs_le.mp hse
  -- `I ≤ 0`
  have hR0 : R ≤ 0 := by
    have hlt : (R : ℝ) < 1 := by
      by_cases h2x : 2 ≤ vx
      · obtain ⟨K, hK⟩ := grid x.toBits hx 1022 (by norm_num) (by
          rw [abs_of_pos (by linarith)]
          norm_num
          linarith)
        rw [← hvx] at hK
        have hKv : (K : ℝ) = vx * 2 ^ 51 := by
          have h' : (K : ℝ) * 2 ^ 1023 = vx * 2 ^ 51 * 2 ^ 1023 := by linear_combination -1 * hK
          exact mul_right_cancel₀ (by positivity) h'
        have hex := sub_exact x 3.5 hx half7_finite (K - 7 * 2 ^ 50) 1023 (by norm_num)
          (by rw [half7_value, sub_mul, hK]; push_cast; ring)
          (by
            push_cast
            rw [abs_le]
            constructor <;> linarith)
        have hsv : value s.toBits = vx - 7 / 2 := by rw [hsdef, hex.2, half7_value]
        rw [← hR]
        linarith
      · push Not at h2x
        rw [← hR]
        linarith
    have : R < 1 := by exact_mod_cast hlt
    omega
  have hR7 : -7 ≤ R := by
    have hgt : (-8 : ℝ) < R := by rw [← hR]; linarith
    have : -8 < R := by exact_mod_cast hgt
    omega
  have hd : |vx - (R + 7 / 2)| ≤ 1 / 2 + 1 / 2 ^ 50 := by
    rw [abs_le]
    constructor <;> linarith
  -- `i + 7/2`
  have hh := add_exact (roundEven s) 3.5 hif half7_finite (2 * R + 7) 1073 (by norm_num)
    (by rw [hR, half7_value]; push_cast; ring)
    (by
      push_cast
      rw [abs_le]
      have : (-7 : ℝ) ≤ R := by exact_mod_cast hR7
      have : (R : ℝ) ≤ 0 := by exact_mod_cast hR0
      constructor <;> linarith)
  rw [hR, half7_value] at hh
  -- `d = x - (i + 7/2)`
  have hdx : Finite (x - (roundEven s + 3.5)).toBits ∧
      value (x - (roundEven s + 3.5)).toBits = vx - (R + 7 / 2) := by
    by_cases hbig : 1 / 2 ≤ |vx|
    · obtain ⟨K, hK⟩ := grid x.toBits hx 1020 (by norm_num) (by norm_num; linarith)
      rw [← hvx] at hK
      have hd' := sub_exact x (roundEven s + 3.5) hx hh.1 (K - (2 * R + 7) * 2 ^ 52) 1021
        (by norm_num) (by rw [hh.2, sub_mul, hK]; push_cast; ring)
        (by
          have hKv : (K : ℝ) = vx * 2 ^ 53 := by
            have h' : (K : ℝ) * 2 ^ 1021 = vx * 2 ^ 53 * 2 ^ 1021 := by linear_combination -1 * hK
            exact mul_right_cancel₀ (by positivity) h'
          obtain ⟨hd1, hd2⟩ := abs_le.mp hd
          push_cast
          rw [abs_le]
          constructor <;> linarith)
      rw [hh.2] at hd'
      exact hd'
    · push Not at hbig
      obtain ⟨K, hK⟩ := grid x.toBits hx 1019 (by norm_num) (by norm_num; linarith)
      rw [← hvx] at hK
      -- here `I` is -4 or -3, and `|d| ≤ 1/4`
      obtain ⟨hb1, hb2⟩ := abs_lt.mp hbig
      obtain ⟨hd1, hd2⟩ := abs_le.mp hd
      have hRb : (R : ℝ) = -4 ∨ (R : ℝ) = -3 := by
        have hlo : (-5 : ℝ) < R := by linarith
        have hhi : (R : ℝ) < -2 := by linarith
        have : -5 < R := by exact_mod_cast hlo
        have : R < -2 := by exact_mod_cast hhi
        rcases (by omega : R = -4 ∨ R = -3) with h' | h'
        · left; rw [h']; norm_num
        · right; rw [h']; norm_num
      have hsmall : |vx - (R + 7 / 2)| ≤ 1 / 2 := by
        rw [abs_le]
        rcases le_abs'.mp h4 with hs4 | hs4 <;> rcases hRb with h' | h' <;> constructor <;> linarith
      have hd' := sub_exact x (roundEven s + 3.5) hx hh.1 (K - (2 * R + 7) * 2 ^ 53) 1020
        (by norm_num) (by rw [hh.2, sub_mul, hK]; push_cast; ring)
        (by
          have hKv : (K : ℝ) = vx * 2 ^ 54 := by
            have h' : (K : ℝ) * 2 ^ 1020 = vx * 2 ^ 54 * 2 ^ 1020 := by linear_combination -1 * hK
            exact mul_right_cancel₀ (by positivity) h'
          obtain ⟨hs1, hs2⟩ := abs_le.mp hsmall
          push_cast
          rw [abs_le]
          constructor <;> linarith)
      rw [hh.2] at hd'
      exact hd'
  exact ⟨R, hR7, hR0, hif, hR, hh.1, hh.2, hdx.1, hdx.2, hd⟩

/-- `Float.toUInt64` of a finite word with a natural value. -/
theorem toUInt64_nat (x : Float) (N : ℕ) (hf : Finite x.toBits) (hv : value x.toBits = N)
    (h2 : N < 2 ^ 63) : x.toUInt64 = UInt64.ofNat N := by
  rw [F64Convert.toUInt64_eq]
  have hfin : Wasm.IEEE64.isFinite x.toBits = true := hf
  have hnan : Wasm.IEEE64.isNaN x.toBits = false := not_nan_of_finite hf
  have hm : Wasm.IEEE64.scaledMagnitude x.toBits = N * 2 ^ 1074 := by
    have h := F64RoundNearest.abs_value x.toBits
    rw [hv, abs_of_nonneg (by positivity), eq_div_iff (by positivity)] at h
    exact_mod_cast h.symm
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    have htr : Wasm.IEEE64.truncatedInt x.toBits = some 0 := by
      unfold Wasm.IEEE64.truncatedInt
      simp only [hfin, ite_true, hm, zero_mul, Nat.zero_div, Nat.cast_zero, neg_zero, ite_self]
    rw [show UInt64.ofNat 0 = 0 from rfl]
    unfold Wasm.IEEE64.truncSatI64U
    simp only [hnan, Bool.false_eq_true, ite_false, htr, le_refl, ite_true]
  · have hsg : Wasm.IEEE64.sign x.toBits = false := by
      rcases Bool.eq_false_or_eq_true (Wasm.IEEE64.sign x.toBits) with h | h
      · have := value_nonpos_of_sign x.toBits h
        rw [hv] at this
        have : (0 : ℝ) < N := by exact_mod_cast hpos
        linarith
      · exact h
    have htr : Wasm.IEEE64.truncatedInt x.toBits = some (N : Int) := by
      unfold Wasm.IEEE64.truncatedInt
      simp only [hfin, ite_true, hm, hsg, Bool.false_eq_true, ite_false,
        Nat.mul_div_cancel _ (show 0 < 2 ^ 1074 by positivity)]
    unfold Wasm.IEEE64.truncSatI64U
    simp only [hnan, Bool.false_eq_true, ite_false, htr]
    rw [ite_eq_right (show ¬ ((N : ℤ) ≤ 0) by omega),
      ite_eq_right (show ¬ ((2 : ℤ) ^ 64 - 1 ≤ N) by omega)]
    unfold Wasm.IEEE64.intToUInt64
    rw [ite_eq_right (show ¬ ((N : ℤ) < 0) by omega)]
    rfl

theorem zero_finite : Finite (0.0 : Float).toBits := by
  rw [TgammaSpecial.zero_bits]; unfold CodeLib.IEEE64.Finite; decide

theorem zero_value : value (0.0 : Float).toBits = 0 := by
  rw [TgammaSpecial.zero_bits, F64Magnitude.value_zero]

/-- `jm = |i|`, the test `jm > 0`, and the loop count `(jm - 1).toUInt64`. -/
theorem count_spec (i : Float) (R : ℤ) (hi : Finite i.toBits) (hv : value i.toBits = R)
    (hR7 : -7 ≤ R) (hR0 : R ≤ 0) :
    Finite i.abs.toBits ∧ value i.abs.toBits = -R ∧ (i.abs > 0.0 ↔ R < 0) ∧
      (R < 0 → (i.abs - 1.0).toUInt64 = UInt64.ofNat (-R - 1).toNat) := by
  obtain ⟨haf, hav⟩ := abs_float i hi
  have hRr : (R : ℝ) ≤ 0 := by exact_mod_cast hR0
  rw [hv, abs_of_nonpos hRr] at hav
  refine ⟨haf, hav, ?_, ?_⟩
  · rw [GT.gt, F64UpperWord.float_lt_iff _ _ zero_finite haf, zero_value, hav]
    constructor
    · intro h
      have : (R : ℝ) < 0 := by linarith
      exact_mod_cast this
    · intro h
      have : (R : ℝ) < 0 := by exact_mod_cast h
      linarith
  · intro hneg
    have hs := sub_exact i.abs 1.0 haf TgammaRecip.one_finite (-R - 1) 1074 (by norm_num)
      (by rw [hav, TgammaRecip.one_value]; push_cast; ring)
      (by
        push_cast
        have : (-7 : ℝ) ≤ R := by exact_mod_cast hR7
        have : (R : ℝ) ≤ -1 := by exact_mod_cast (show R ≤ -1 by omega)
        rw [abs_le]
        constructor <;> linarith)
    rw [hav, TgammaRecip.one_value] at hs
    apply toUInt64_nat _ _ hs.1 _ (by omega)
    rw [hs.2]
    have : (((-R - 1).toNat : ℤ) : ℝ) = ((-R - 1 : ℤ) : ℝ) := by
      rw [Int.toNat_of_nonneg (by omega)]
    push_cast at this ⊢
    linarith

#print axioms main_red
#print axioms count_spec

end Verified.Examples.TgammaMainRed
