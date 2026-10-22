import Library.Numerics.Float64.Tgamma.TgammaSinpidRed

/-!
The argument reduction of `Lgamma.asSinpipidAccurate` for `x = n/2^54` with `0 < n < 2^54`
(`red54`).  The accurate path of `lgamma` calls it at `x - ⌊x⌋` for `x < -1/2`, a multiple of
`2^-53`, and at `-x` for `-1/2 ≤ x < -1/4`, a multiple of `2^-54`.  The proof is that of
`Library.Numerics.Float64.Tgamma.TgammaSinpidRed.red_spec` on the finer grid: `x - 0.5` is a multiple of `2^-54` below `1/2` in
magnitude, `x' = 128 |x - 0.5|` a multiple of `2^-47` below 64, and `d = ix - x'` a multiple of
`2^-47` within `1/2` of zero, so all three are exact.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaSinAccRed
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Tgamma.TgammaFloor Library.Numerics.Float64.Tgamma.TgammaLogdTab Library.Numerics.Float64.Tgamma.TgammaSinpidRed
open Library.Numerics.Float64.Tgamma (roundEven)

set_option exponentiation.threshold 4096

/-- **The argument reduction** on the grid `2^-54`. -/
theorem red54 (x : Float) (n : ℕ) (hn0 : 0 < n) (hn : n < 2 ^ 54) (hx : Finite x.toBits)
    (hv : value x.toBits = n / 2 ^ 54) :
    ∃ k : ℕ, k ≤ 64 ∧ (roundEven ((x - 0.5).abs * 128.0)).toUInt64 = UInt64.ofNat k ∧
      Finite (roundEven ((x - 0.5).abs * 128.0) - (x - 0.5).abs * 128.0).toBits ∧
      value (roundEven ((x - 0.5).abs * 128.0) - (x - 0.5).abs * 128.0).toBits =
        k - 128 * |(n : ℝ) / 2 ^ 54 - 1 / 2| ∧
      |(k : ℝ) - 128 * (|(n : ℝ) / 2 ^ 54 - 1 / 2|)| ≤ 1 / 2 := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = (n : ℤ) - 2 ^ 53 := ⟨_, rfl⟩
  have hzb : |z| < 2 ^ 53 := by rw [hz, abs_lt]; constructor <;> omega
  have hzr : (z : ℝ) / 2 ^ 54 = (n : ℝ) / 2 ^ 54 - 1 / 2 := by
    have : (z : ℝ) = (n : ℝ) - 2 ^ 53 := by rw [hz]; push_cast; ring
    rw [this]; ring
  have hzn : z.natAbs ≤ 2 ^ 53 := by
    have : (z.natAbs : ℤ) = |z| := Int.natCast_natAbs z
    omega
  -- `x - 0.5`
  obtain ⟨w1, hw1f, hw1v⟩ := grid_float z 54 hzn (by norm_num)
  have hX : |(n : ℝ) / 2 ^ 54 - 1 / 2| < 1 / 2 := by
    rw [← hzr, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 54), div_lt_iff₀ (by positivity),
      ← Int.cast_abs]
    have : ((|z| : ℤ) : ℝ) < 2 ^ 53 := by exact_mod_cast hzb
    linarith [(by norm_num : (1 / 2 : ℝ) * 2 ^ 54 = 2 ^ 53)]
  obtain ⟨haf, hav⟩ := fsub_exact x 0.5 w1 hx half_finite hw1f
    (by rw [hw1v, hv, half_value, hzr]) (by
      rw [hv, half_value]; linarith [abs_nonneg ((n : ℝ) / 2 ^ 54 - 1 / 2),
        (by norm_num : (1 / 2 : ℝ) < 2 ^ 1023)])
  rw [hv, half_value] at hav
  -- the magnitude
  obtain ⟨hbf, hbv⟩ := abs_float (x - 0.5) haf
  rw [hav] at hbv
  have hbsv : sv (x - 0.5).abs.toBits = |z| * 2 ^ 1020 := by
    apply Library.Numerics.Float64.Tgamma.TgammaLogdParts.sv_eq_of_value
    rw [hbv, ← hzr, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 54), Int.cast_mul,
      Int.cast_abs, Int.cast_pow, Int.cast_ofNat, div_eq_div_iff (by positivity) (by positivity),
      mul_assoc, ← pow_add]
  have hbm : Wasm.IEEE64.scaledMagnitude (x - 0.5).abs.toBits = z.natAbs * 2 ^ 1020 := by
    rw [mag_eq_natAbs, hbsv, Int.natAbs_mul, Int.natAbs_abs, Int.natAbs_pow]
    rfl
  -- `x' = 128 |x - 0.5|`
  obtain ⟨hx'f, hx'v, -, -⟩ := F64ExactProduct.mul_exact_scaled (x - 0.5).abs.toBits
    (128.0 : Float).toBits hbf w128_finite z.natAbs 1 1020 1081 hbm w128_mag
    (by have : (z.natAbs : ℤ) = |z| := Int.natCast_natAbs z
        omega) (by norm_num) (by norm_num)
  rw [← F64Bits.toBits_mul] at hx'f hx'v
  have h128 : value (128.0 : Float).toBits = 128 := by
    rw [w128_word, ← PolyBound.ratOfWord_cast,
      show PolyBound.ratOfWord 0x4060000000000000 = 128 by decide +kernel]
    norm_num
  rw [hbv, h128] at hx'v
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 128 * |(n : ℝ) / 2 ^ 54 - 1 / 2| := ⟨_, rfl⟩
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
  have htz : t = |(z : ℝ)| / 2 ^ 47 := by
    rw [ht, ← hzr, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 54)]
    field_simp; ring
  obtain ⟨w2, hw2f, hw2v⟩ := grid_float (R * 2 ^ 47 - (|z|)) 47 (by
    have h1 : |((R * 2 ^ 47 - (|z|) : ℤ) : ℝ)| ≤ 2 ^ 46 := by
      rw [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_abs]
      rw [show (R : ℝ) * 2 ^ 47 - |(z : ℝ)| = 2 ^ 47 * ((R : ℝ) - t) by
        rw [htz]; field_simp, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 47)]
      calc (2 : ℝ) ^ 47 * |(R : ℝ) - t| ≤ 2 ^ 47 * (1 / 2) := by gcongr
        _ = 2 ^ 46 := by norm_num
    rw [← Int.cast_abs] at h1
    have h2 : |R * 2 ^ 47 - (|z|)| ≤ 2 ^ 46 := by exact_mod_cast h1
    have : ((R * 2 ^ 47 - (|z|)).natAbs : ℤ) = |R * 2 ^ 47 - (|z|)| := Int.natCast_natAbs _
    omega) (by norm_num)
  have hdv : value w2.toBits = (R : ℝ) - t := by
    rw [hw2v, htz, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_abs]
    field_simp
  obtain ⟨hdf, hdv'⟩ := fsub_exact (roundEven ((x - 0.5).abs * 128.0)) ((x - 0.5).abs * 128.0) w2
    hrf hx'f hw2f (by rw [hdv, hR, hxt]) (by
      rw [hR, hxt]; linarith [abs_le.mp hrd, (by norm_num : (1 / 2 : ℝ) < 2 ^ 1023)])
  rw [hR, hxt] at hdv'
  exact ⟨hdf, hdv', hrd⟩

#print axioms red54

end Library.Numerics.Float64.Lgamma.LgammaSinAccRed
