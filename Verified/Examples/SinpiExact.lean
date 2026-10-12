import Verified.Examples.SinpiWithin

/-!
The exact results of `Sinpi.sinpi` and `Sinpi.cospi` as bit equalities: `sinpi` of an integer is
`±0` with the sign of `x`, `cospi` of an integer plus `1/2` is `+0`, and the three functions give
the canonical NaN for an infinity or a NaN.
-/

namespace Verified.Examples.SinpiExact

open CodeLib.IEEE64 LeanExe.ProofKit TrigSinCos TanBigWords TanWith SinpiBits SinpiFloor
  SinpiPieces SinpiCommon SinpiReflect SinpiSin SinpiKernels SinpiTanKernel SinpiCos
  SinpiCosFloor SinpiTanpi SinpiTiny SinpiWithin

set_option exponentiation.threshold 1200

/-- A word of value 0 is `±0` by its sign. -/
theorem zero_word (w : UInt64) (h : value w = 0) :
    w = if Wasm.IEEE64.sign w = true then 0x8000000000000000 else 0 := by
  have h1 := (TrigSinCos.zero_iff w).mpr h
  have h2 := w.toNat_lt
  by_cases hs : Wasm.IEEE64.sign w = true
  · rw [if_pos hs]
    have hs' : 2 ^ 63 ≤ w.toNat := by
      simp only [Wasm.IEEE64.sign, decide_eq_true_eq] at hs
      exact hs
    apply UInt64.toNat_inj.mp
    show w.toNat = 9223372036854775808
    omega
  · rw [if_neg hs]
    have hs' : w.toNat < 2 ^ 63 := by
      simp only [Wasm.IEEE64.sign, decide_eq_true_eq, not_le] at hs
      exact hs
    apply UInt64.toNat_inj.mp
    show w.toNat = 0
    omega

/-- The sign choice between `±0`. -/
theorem signed_zero (c : Bool) :
    (if c = true then -(0.0 : Float) else 0.0).toBits =
      if c = true then 0x8000000000000000 else 0 := by
  obtain ⟨z1, z2⟩ := zero_bits'
  cases c
  · rw [if_neg (show ¬((false : Bool) = true) by decide),
      if_neg (show ¬((false : Bool) = true) by decide), z1]
  · rw [if_pos rfl, if_pos rfl, z2]

/-- A nonzero integer is at least 1 in magnitude. -/
theorem int_one_le (v : ℝ) (n : Int) (hn : v = n) (h0 : v ≠ 0) : 1 ≤ |v| := by
  have hn0 : n ≠ 0 := fun h => h0 (by rw [hn, h, Int.cast_zero])
  rw [hn, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hn0

/-- The integer part from `floor_frac` of an integer is the integer. -/
theorem not_frac (v : ℝ) (n : Int) (N : Nat) (hn : v = n) (h1 : N + 1 / 2 ^ 52 ≤ |v|)
    (h2 : |v| < N + 1) : False := by
  rw [hn, ← Int.cast_abs] at h1 h2
  have a1 : (N : ℤ) < |n| := by
    have : (N : ℝ) < ((|n| : ℤ) : ℝ) := by linarith [show (0 : ℝ) < 1 / 2 ^ 52 by positivity]
    exact_mod_cast this
  have a2 : |n| < (N : ℤ) + 1 := by exact_mod_cast h2
  omega

/-- `sinpi` of an integer is `±0` with the sign of `x`. -/
theorem sinpi_int (x : Float) (hxf : Finite x.toBits) (n : Int) (hn : value x.toBits = n) :
    (Sinpi.sinpi x).toBits =
      if Wasm.IEEE64.sign x.toBits = true then 0x8000000000000000 else 0 := by
  obtain ⟨c1, c29, c52, cinf⟩ := abs_thresholds x hxf
  obtain ⟨f0, v0⟩ := zero_float
  unfold Sinpi.sinpi
  dsimp only
  rw [ax_abs, neg_flag]
  by_cases h0 : value x.toBits = 0
  · have ha : |value x.toBits| = 0 := by rw [h0, abs_zero]
    rw [if_pos (c1.mpr (by rw [ha]; norm_num)), if_pos (c29.mpr (by rw [ha]; positivity)),
      if_pos ((feq_iff x 0.0 hxf f0).mpr (by rw [h0, v0]))]
    exact zero_word _ h0
  have h1 := int_one_le _ n hn h0
  rw [if_neg (fun h' => by linarith [c1.mp h'])]
  by_cases h52 : |value x.toBits| < 2 ^ 52
  · rw [if_pos (c52.mpr h52)]
    obtain ⟨N, -, -, -, -, -, -, -, hcase⟩ := floor_frac x hxf h1 h52
    generalize Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff) (x.toBits &&& 0xFFFFFFFF) = P
      at *
    obtain ⟨fl, j0⟩ := P
    dsimp only at *
    rcases hcase with ⟨-, hz⟩ | ⟨hgt, hlt, -⟩
    · rw [hz, show (0 : UInt64) >>> 32 = 0 by decide,
        if_pos (show ((0 : UInt64) == 0) = true by decide)]
      exact signed_zero _
    · exact (not_frac _ n N hn hgt hlt).elim
  · rw [if_neg (fun h' => h52 (c52.mp h')), if_neg cinf]
    exact signed_zero _

/-- `|x|` of an integer plus `1/2` is a natural number plus `1/2`. -/
theorem half_nat (v : ℝ) (n : Int) (hn : v = n + 1 / 2) : ∃ M : Nat, |v| = M + 1 / 2 := by
  rcases le_or_gt 0 n with h | h
  · refine ⟨n.toNat, ?_⟩
    have e : ((n.toNat : ℕ) : ℝ) = n := by exact_mod_cast Int.toNat_of_nonneg h
    have : (0 : ℝ) ≤ n := by exact_mod_cast h
    rw [hn, e, abs_of_nonneg (by linarith)]
  · refine ⟨(-n - 1).toNat, ?_⟩
    have e : (((-n - 1).toNat : ℕ) : ℝ) = -n - 1 := by
      exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ -n - 1 by omega)
    have : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
    rw [hn, e, abs_of_neg (by linarith)]
    ring

/-- A value of an integer plus `1/2` is below `2 ^ 52`. -/
theorem half_small (x : Float) (n : Int) (hn : value x.toBits = n + 1 / 2) :
    |value x.toBits| < 2 ^ 52 := by
  by_contra h
  obtain ⟨k, hk⟩ := big_integer x.toBits (not_lt.mp h)
  have : (2 * (k - n) : ℤ) = 1 := by
    have : (2 * ((k : ℝ) - n)) = 1 := by rw [← hk, hn]; ring
    exact_mod_cast this
  omega

/-- `cospi` of an integer plus `1/2` is `+0`. -/
theorem cospi_half (x : Float) (hxf : Finite x.toBits) (n : Int)
    (hn : value x.toBits = n + 1 / 2) : (Sinpi.cospi x).toBits = 0 := by
  obtain ⟨hs, hf, hv, -, hix, -⟩ := abs_facts x hxf
  obtain ⟨c1, -, c52, -⟩ := abs_thresholds x hxf
  obtain ⟨t1, t2, t3⟩ := thresholds x.abs _ |value x.toBits| hix hs hv
  obtain ⟨M, hM⟩ := half_nat _ n hn
  have h52 := half_small x n hn
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  unfold Sinpi.cospi
  dsimp only
  rw [ax_abs]
  by_cases h1 : |value x.toBits| < 1
  · have hM1 : M = 0 := by
      have : (M : ℝ) < 1 := by linarith
      have : M < 1 := by exact_mod_cast this
      omega
    rw [hM1, Nat.cast_zero, zero_add] at hM
    rw [if_pos (c1.mpr h1), if_neg (fun h' => by linarith [t1.mp h']),
      if_neg (fun h' => by linarith [t2.mp h']), if_pos (t3.mpr (by linarith)),
      if_pos ((beq_half _ hf).trans (by rw [hv, hM]; simp)), (zero_bits').1]
  · rw [if_neg (fun h' => h1 (c1.mp h')), if_pos (c52.mpr h52)]
    obtain ⟨N, -, -, -, -, -, hdf, hdv, hcase⟩ := floor_frac x hxf (not_lt.mp h1) h52
    generalize Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff) (x.toBits &&& 0xFFFFFFFF) = P
      at *
    obtain ⟨fl, j0⟩ := P
    dsimp only at *
    have hF : |value x.toBits| - N = 1 / 2 := by
      rcases hcase with ⟨heq, -⟩ | ⟨hgt, hlt, -⟩
      · exfalso
        rw [hM] at heq
        have : (2 * M + 1 : ℤ) = 2 * N := by
          have : (2 * (M : ℝ) + 1) = 2 * N := by linarith
          exact_mod_cast this
        omega
      · rw [hM] at hgt hlt
        have a1 : N < M + 1 := by
          have : (N : ℝ) < M + 1 := by linarith [show (0 : ℝ) < 1 / 2 ^ 52 by positivity]
          exact_mod_cast this
        have a2 : M < N + 1 := by
          have : (M : ℝ) < N + 1 := by linarith
          exact_mod_cast this
        have : M = N := by omega
        rw [hM, this]
        ring
    obtain ⟨-, t2', t3'⟩ := thresholds (x.abs - fl) ((x.abs - fl).toBits >>> 32)
      (|value x.toBits| - N) (by rw [TrigWords.shr_toNat]; rfl)
      (SinpiReflect.pos_toNat _ (by rw [hdv, hF]; norm_num)) hdv
    rw [beq_half _ hdf, hdv, hF,
      decide_eq_true (ge_of_not_lt _ _ (fun h' => by linarith [t2'.mp h'])),
      decide_eq_true (t3'.mpr (by rw [hF]; norm_num)),
      if_pos (show (true && true && decide ((1 : ℝ) / 2 = 1 / 2)) = true by simp),
      (zero_bits').1]

theorem nan_div : (0.0 / 0.0 : Float).toBits = Wasm.IEEE64.canonicalNaN := by
  rw [F64Bits.toBits_div, (zero_bits').1]
  decide +kernel

/-- `sinpi`, `cospi`, and `tanpi` of an infinity or a NaN are the canonical NaN. -/
theorem nonfinite (x : Float) (h : ¬ Finite x.toBits) :
    (Sinpi.sinpi x).toBits = Wasm.IEEE64.canonicalNaN ∧
      (Sinpi.cospi x).toBits = Wasm.IEEE64.canonicalNaN ∧
      (Sinpi.tanpi x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hix := TrigSinCos.high_word x.toBits
  have he := TrigTheorem.high_nonfinite x h
  refine ⟨?_, ?_, ?_⟩
  · unfold Sinpi.sinpi
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat]
    rw [if_neg (by omega), if_neg (by omega), if_pos he, nan_div]
  · unfold Sinpi.cospi
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat]
    rw [if_neg (by omega), if_neg (by omega), if_pos he, nan_div]
  · unfold Sinpi.tanpi
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat]
    rw [if_neg (by omega), if_neg (by omega), if_pos he, nan_div]

#print axioms sinpi_int
#print axioms cospi_half
#print axioms nonfinite

end Verified.Examples.SinpiExact
