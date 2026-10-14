import Verified.Examples.TgammaLogdParts
import Verified.Examples.SinpiFloor

/-!
The argument reduction of `Tgamma.asSinpid` for `x = n/2^53` with `0 < n < 2^53`, the form of
`x - ⌊x⌋` at the call sites of `tgamma` and `lgamma`.  The code computes `x' = |x - 0.5| · 128`,
`ix = roundEven x'`, `d = ix - x'`, and the table index `ky = ix.toUInt64`.  `x - 0.5` is a multiple
of `2^-53` below `1/2` in magnitude and `x'` a multiple of `2^-46` below 64, so both are exact, and
`d` is exact because it is a multiple of `2^-46` within `1/2` of zero (`red_spec`).
-/

namespace Verified.Examples.TgammaSinpidRed
open CodeLib.IEEE64 LeanExe.ProofKit TgammaFloor TgammaLogdTab
open Verified.Examples.Tgamma (roundEven)

set_option exponentiation.threshold 4096

theorem half_word : (0.5 : Float).toBits = 0x3FE0000000000000 := rfl

theorem half_value : value (0.5 : Float).toBits = 1 / 2 := by
  rw [half_word, ← PolyBound.ratOfWord_cast,
    show PolyBound.ratOfWord 0x3FE0000000000000 = 1 / 2 by decide +kernel]
  norm_num

theorem half_finite : Finite (0.5 : Float).toBits := by
  rw [half_word]; unfold CodeLib.IEEE64.Finite; decide

theorem w128_word : (128.0 : Float).toBits = 0x4060000000000000 := rfl

theorem w128_finite : Finite (128.0 : Float).toBits := by
  rw [w128_word]; unfold CodeLib.IEEE64.Finite; decide

theorem w128_mag : Wasm.IEEE64.scaledMagnitude (128.0 : Float).toBits = 1 * 2 ^ 1081 := by
  rw [w128_word]; decide +kernel

/-- A finite double for each multiple of `2^-e` up to `2^53` units. -/
theorem grid_float (z : ℤ) (e : ℕ) (hz : z.natAbs ≤ 2 ^ 53) (he : e ≤ 1074) :
    ∃ w : Float, Finite w.toBits ∧ value w.toBits = z / 2 ^ e := by
  obtain ⟨hf, hv⟩ := F64GridExact.signed_grid_packing_exact z (1074 - e) hz (by omega)
  refine ⟨Float.ofBits (Wasm.IEEE64.roundScaledMagnitude (decide (z < 0))
    (z.natAbs * 2 ^ (1074 - e))), ?_, ?_⟩
  · rw [F64Bits.toBits_ofBits, not_nan_of_finite hf]
    simp only [Bool.false_eq_true, ite_false]
    exact hf
  · rw [F64Bits.toBits_ofBits, not_nan_of_finite hf]
    simp only [Bool.false_eq_true, ite_false]
    rewrite [value, hv, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      div_eq_div_iff (by positivity) (by positivity), mul_assoc, ← pow_add,
      show 1074 - e + e = 1074 by omega]
    rfl

/-- `toUInt64` of a zero. -/
theorem toUInt64_zero (x : Float) (hf : Finite x.toBits) (hv : value x.toBits = 0) :
    x.toUInt64 = 0 := by
  rw [F64Convert.toUInt64_eq]
  have hm : Wasm.IEEE64.scaledMagnitude x.toBits = 0 := by
    rw [mag_eq_natAbs]
    have : sv x.toBits = 0 := by
      rw [value_eq, div_eq_zero_iff] at hv
      rcases hv with h | h
      · exact_mod_cast h
      · exact absurd h (by positivity)
    rw [this]; rfl
  have hfin : Wasm.IEEE64.isFinite x.toBits = true := hf
  have hnan : Wasm.IEEE64.isNaN x.toBits = false := not_nan_of_finite hf
  have htr : Wasm.IEEE64.truncatedInt x.toBits = some 0 := by
    unfold Wasm.IEEE64.truncatedInt
    simp only [hfin, ite_true, hm, Nat.zero_div, Nat.cast_zero, neg_zero, ite_self]
  unfold Wasm.IEEE64.truncSatI64U
  simp only [hnan, Bool.false_eq_true, ite_false, htr, le_refl, ite_true]

/-- `toUInt64` of a double with a natural value below `2^63`. -/
theorem toUInt64_nat (x : Float) (N : ℕ) (hf : Finite x.toBits) (hv : value x.toBits = N)
    (hN : N < 2 ^ 63) : x.toUInt64 = UInt64.ofNat N := by
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    rw [toUInt64_zero x hf (by rw [hv]; simp)]
    rfl
  · exact SinpiFloor.toUInt64_int x N hf hv hpos hN

/-- **The argument reduction.** -/
theorem red_spec (x : Float) (n : ℕ) (hn0 : 0 < n) (hn : n < 2 ^ 53) (hx : Finite x.toBits)
    (hv : value x.toBits = n / 2 ^ 53) :
    ∃ k : ℕ, k ≤ 64 ∧ (roundEven ((x - 0.5).abs * 128.0)).toUInt64 = UInt64.ofNat k ∧
      Finite (roundEven ((x - 0.5).abs * 128.0) - (x - 0.5).abs * 128.0).toBits ∧
      value (roundEven ((x - 0.5).abs * 128.0) - (x - 0.5).abs * 128.0).toBits =
        k - 128 * |(n : ℝ) / 2 ^ 53 - 1 / 2| ∧
      |(k : ℝ) - 128 * (|(n : ℝ) / 2 ^ 53 - 1 / 2|)| ≤ 1 / 2 := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = (n : ℤ) - 2 ^ 52 := ⟨_, rfl⟩
  have hzb : |z| < 2 ^ 52 := by rw [hz, abs_lt]; constructor <;> omega
  have hzr : (z : ℝ) / 2 ^ 53 = (n : ℝ) / 2 ^ 53 - 1 / 2 := by
    have : (z : ℝ) = (n : ℝ) - 2 ^ 52 := by rw [hz]; push_cast; ring
    rw [this]; ring
  have hzn : z.natAbs ≤ 2 ^ 53 := by
    have : (z.natAbs : ℤ) = |z| := Int.natCast_natAbs z
    omega
  -- `x - 0.5`
  obtain ⟨w1, hw1f, hw1v⟩ := grid_float z 53 hzn (by norm_num)
  have hX : |(n : ℝ) / 2 ^ 53 - 1 / 2| < 1 / 2 := by
    rw [← hzr, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53), div_lt_iff₀ (by positivity),
      ← Int.cast_abs]
    have : ((|z| : ℤ) : ℝ) < 2 ^ 52 := by exact_mod_cast hzb
    linarith [(by norm_num : (1 / 2 : ℝ) * 2 ^ 53 = 2 ^ 52)]
  obtain ⟨haf, hav⟩ := fsub_exact x 0.5 w1 hx half_finite hw1f
    (by rw [hw1v, hv, half_value, hzr]) (by
      rw [hv, half_value]; linarith [abs_nonneg ((n : ℝ) / 2 ^ 53 - 1 / 2),
        (by norm_num : (1 / 2 : ℝ) < 2 ^ 1023)])
  rw [hv, half_value] at hav
  -- the magnitude
  obtain ⟨hbf, hbv⟩ := abs_float (x - 0.5) haf
  rw [hav] at hbv
  have hbsv : sv (x - 0.5).abs.toBits = |z| * 2 ^ 1021 := by
    apply TgammaLogdParts.sv_eq_of_value
    rw [hbv, ← hzr, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53), Int.cast_mul,
      Int.cast_abs, Int.cast_pow, Int.cast_ofNat, div_eq_div_iff (by positivity) (by positivity),
      mul_assoc, ← pow_add]
  have hbm : Wasm.IEEE64.scaledMagnitude (x - 0.5).abs.toBits = z.natAbs * 2 ^ 1021 := by
    rw [mag_eq_natAbs, hbsv, Int.natAbs_mul, Int.natAbs_abs, Int.natAbs_pow]
    rfl
  -- `x' = 128 |x - 0.5|`
  obtain ⟨hx'f, hx'v, -, -⟩ := F64ExactProduct.mul_exact_scaled (x - 0.5).abs.toBits
    (128.0 : Float).toBits hbf w128_finite z.natAbs 1 1021 1081 hbm w128_mag
    (by have : (z.natAbs : ℤ) = |z| := Int.natCast_natAbs z
        omega) (by norm_num) (by norm_num)
  rw [← F64Bits.toBits_mul] at hx'f hx'v
  have h128 : value (128.0 : Float).toBits = 128 := by
    rw [w128_word, ← PolyBound.ratOfWord_cast,
      show PolyBound.ratOfWord 0x4060000000000000 = 128 by decide +kernel]
    norm_num
  rw [hbv, h128] at hx'v
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 128 * |(n : ℝ) / 2 ^ 53 - 1 / 2| := ⟨_, rfl⟩
  have hxt : value ((x - 0.5).abs * 128.0).toBits = t := by rw [hx'v, ht]; ring
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht64 : t < 64 := by rw [ht]; linarith
  -- `ix`
  obtain ⟨hrf, ⟨R, hR⟩, hrd, -⟩ := roundEven_spec _ hx'f
  rw [hR, hxt] at hrd
  have hR0 : 0 ≤ R := by
    have h1 : (-1 : ℝ) < R := by have := (abs_le.mp hrd).1; linarith
    have h2 : (-1 : ℤ) < R := by exact_mod_cast h1
    omega
  have hR64 : R ≤ 64 := by
    have h1 : (R : ℝ) < 65 := by have := (abs_le.mp hrd).2; linarith
    have h2 : R < 65 := by exact_mod_cast h1
    omega
  have hRk : ((R.toNat : ℕ) : ℝ) = R := by
    have : ((R.toNat : ℕ) : ℤ) = R := Int.toNat_of_nonneg hR0
    exact_mod_cast this
  refine ⟨R.toNat, by omega, ?_, ?_⟩
  · apply toUInt64_nat _ _ hrf _ (by omega)
    rw [hR, hRk]
  rw [hRk, ← ht]
  -- `d = ix - x'`
  have htz : t = |(z : ℝ)| / 2 ^ 46 := by
    rw [ht, ← hzr, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53)]
    field_simp; ring
  obtain ⟨w2, hw2f, hw2v⟩ := grid_float (R * 2 ^ 46 - (|z|)) 46 (by
    have h1 : |((R * 2 ^ 46 - (|z|) : ℤ) : ℝ)| ≤ 2 ^ 45 := by
      rw [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_abs]
      rw [show (R : ℝ) * 2 ^ 46 - |(z : ℝ)| = 2 ^ 46 * ((R : ℝ) - t) by
        rw [htz]; field_simp, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 46)]
      calc (2 : ℝ) ^ 46 * |(R : ℝ) - t| ≤ 2 ^ 46 * (1 / 2) := by gcongr
        _ = 2 ^ 45 := by norm_num
    rw [← Int.cast_abs] at h1
    have h2 : |R * 2 ^ 46 - (|z|)| ≤ 2 ^ 45 := by exact_mod_cast h1
    have : ((R * 2 ^ 46 - (|z|)).natAbs : ℤ) = |R * 2 ^ 46 - (|z|)| := Int.natCast_natAbs _
    omega) (by norm_num)
  have hdv : value w2.toBits = (R : ℝ) - t := by
    rw [hw2v, htz, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_abs]
    field_simp
  obtain ⟨hdf, hdv'⟩ := fsub_exact (roundEven ((x - 0.5).abs * 128.0)) ((x - 0.5).abs * 128.0) w2
    hrf hx'f hw2f (by rw [hdv, hR, hxt]) (by
      rw [hR, hxt]; linarith [abs_le.mp hrd, (by norm_num : (1 / 2 : ℝ) < 2 ^ 1023)])
  rw [hR, hxt] at hdv'
  exact ⟨hdf, hdv', hrd⟩

#print axioms red_spec

end Verified.Examples.TgammaSinpidRed
