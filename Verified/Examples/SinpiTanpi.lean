import Verified.Examples.SinpiCosFloor

/-!
`Sinpi.tanpi` from `2 ^ -29` on in magnitude: within one step of `tan (π x)` for every finite `x`
that is not an integer plus `1/2`.  Below 1 the tangent pieces run on `|x|`; from 1 below
`2 ^ 52` they run on the fraction of `|x|`, and an integer gives `±0`; from `2 ^ 52` on the result
is `±0`.  The sign of `x` negates the result.
-/

namespace Verified.Examples.SinpiTanpi

open CodeLib.IEEE64 LeanExe.ProofKit TrigSinCos TanBigWords TanTrunc TanWith SinpiBits
  SinpiFloor SinpiPieces SinpiCommon SinpiReflect SinpiSin SinpiKernels SinpiTanKernel SinpiCos
  SinpiCosFloor

set_option exponentiation.threshold 1200

theorem tan_shift (F : ℝ) (N : Nat) : Real.tan (Real.pi * (N + F)) = Real.tan (Real.pi * F) := by
  rw [show Real.pi * (N + F) = Real.pi * F + N * Real.pi by ring]
  exact Real.tan_periodic.nat_mul N (Real.pi * F)

theorem tan_int (n : Int) : Real.tan (Real.pi * n) = 0 := by
  rw [Real.tan_eq_sin_div_cos, show Real.pi * (n : ℝ) = n * Real.pi by ring, Real.sin_int_mul_pi,
    zero_div]

/-- The result of a choice between `±0` is within one step of 0. -/
theorem zero_prop (p : Prop) [Decidable p] :
    F64SignedRounding.WithinSteps 1 0 (if p then -(0.0 : Float) else 0.0).toBits := by
  obtain ⟨z1, z2⟩ := zero_bits'
  by_cases h : p
  · rw [if_pos h, z2]; exact F64SelfStep.zero_step _ (by decide)
  · rw [if_neg h, z1]; exact F64SelfStep.zero_step _ (by decide)

/-- A signed result from a nonnegative one: `tan (π x)` is odd. -/
theorem signed_tan (x : Float) (hxf : Finite x.toBits) (h0 : value x.toBits ≠ 0) (s : Float)
    (hs : F64SignedRounding.WithinSteps 1 (Real.tan (Real.pi * |value x.toBits|)) s.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.tan (Real.pi * value x.toBits))
      (if Wasm.IEEE64.sign x.toBits = true then -s else s).toBits := by
  rcases sign_cases x hxf h0 with ⟨hsg, hv⟩ | ⟨hsg, hv⟩
  · rw [if_pos hsg]
    have := neg_within _ _ hs
    rwa [show Real.pi * value x.toBits = -(Real.pi * |value x.toBits|) by
      conv_lhs => rw [hv]
      ring, Real.tan_neg]
  · rw [if_neg (by rw [hsg]; decide)]
    rwa [show Real.pi * value x.toBits = Real.pi * |value x.toBits| by rw [← hv]]

/-- `tanpi` from `2 ^ -29` below 1, away from `1/2`. -/
theorem tanpi_mid (x : Float) (hxf : Finite x.toBits) (h1 : 1 / 2 ^ 29 ≤ |value x.toBits|)
    (h2 : |value x.toBits| < 1) (hh : |value x.toBits| ≠ 1 / 2) :
    F64SignedRounding.WithinSteps 1 (Real.tan (Real.pi * value x.toBits))
      (Sinpi.tanpi x).toBits := by
  obtain ⟨hs, hf, hv, -, hix, -⟩ := abs_facts x hxf
  obtain ⟨c1, c29, -, -⟩ := abs_thresholds x hxf
  obtain ⟨-, t2, -⟩ := thresholds x.abs _ |value x.toBits| hix hs hv
  have h0 : value x.toBits ≠ 0 := by
    intro h; rw [h, abs_zero] at h1; linarith [show (0 : ℝ) < 1 / 2 ^ 29 by positivity]
  have hp := tan_pieces x.abs |value x.toBits| hs hf hv (le_trans (by norm_num) h1) h2
  unfold Sinpi.tanpi
  dsimp only
  rw [ax_abs, neg_flag, if_pos (c1.mpr h2), if_neg (fun h => by linarith [c29.mp h])]
  apply signed_tan x hxf h0
  by_cases hq : |value x.toBits| < 1 / 2
  · rw [if_pos (t2.mpr hq)]
    exact hp.1 hq
  · rw [if_neg (fun h' => hq (t2.mp h')), beq_half _ hf, hv, decide_eq_false hh,
      if_neg (show ¬((false : Bool) = true) by decide)]
    exact hp.2 (lt_of_le_of_ne (not_lt.mp hq) (Ne.symm hh))

/-- `tanpi` from 1 below `2 ^ 52`, away from an integer plus `1/2`. -/
theorem tanpi_floor (x : Float) (hxf : Finite x.toBits) (h1 : 1 ≤ |value x.toBits|)
    (h2 : |value x.toBits| < 2 ^ 52) (hh : ∀ n : Nat, |value x.toBits| ≠ n + 1 / 2) :
    F64SignedRounding.WithinSteps 1 (Real.tan (Real.pi * value x.toBits))
      (Sinpi.tanpi x).toBits := by
  obtain ⟨c1, -, c52, -⟩ := abs_thresholds x hxf
  obtain ⟨N, hN1, hN52, hNv, hflf, hj, hdf, hdv, hcase⟩ := floor_frac x hxf h1 h2
  have h0 : value x.toBits ≠ 0 := by intro h; rw [h, abs_zero] at h1; linarith
  unfold Sinpi.tanpi
  dsimp only
  rw [ax_abs, neg_flag, if_neg (fun h' => by linarith [c1.mp h']), if_pos (c52.mpr h2)]
  apply signed_tan x hxf h0
  generalize Sinpi.ffloor ((x.toBits >>> 32) &&& 0x7fffffff) (x.toBits &&& 0xFFFFFFFF) = P at *
  obtain ⟨fl, j0⟩ := P
  dsimp only at *
  rw [show |value x.toBits| = N + (|value x.toBits| - N) by ring, tan_shift]
  rcases hcase with ⟨heq, hz⟩ | ⟨hgt, hlt, ha63⟩
  · rw [hz, show (0 : UInt64) >>> 32 = 0 by decide,
      if_pos (show (0 : UInt64) < 0x3fe00000 by decide),
      if_pos (show ((0 : UInt64) == 0) = true by decide), heq, sub_self, mul_zero, Real.tan_zero]
    exact zero_prop _
  · set F := |value x.toBits| - N with hFdef
    have hF0 : 1 / 2 ^ 52 ≤ F := by rw [hFdef]; linarith
    have hF1 : F < 1 := by rw [hFdef]; linarith
    have hFh : F ≠ 1 / 2 := by
      intro hf'
      exact hh N (by rw [← hf', hFdef]; ring)
    have hp := tan_pieces (x.abs - fl) F ha63 hdf hdv (le_trans (by norm_num) hF0) hF1
    obtain ⟨-, t2, -⟩ := thresholds (x.abs - fl) ((x.abs - fl).toBits >>> 32) F
      (by rw [TrigWords.shr_toNat]; rfl) ha63 hdv
    by_cases hq : F < 1 / 2
    · rw [if_pos (t2.mpr hq), frac_high _ F ha63 hdv hF0,
        if_neg (show ¬((false : Bool) = true) by decide)]
      exact hp.1 hq
    · rw [if_neg (fun h' => hq (t2.mp h')), beq_half _ hdf, hdv, decide_eq_false hFh,
        if_neg (show ¬((false : Bool) = true) by decide)]
      exact hp.2 (lt_of_le_of_ne (not_lt.mp hq) (Ne.symm hFh))

#print axioms tanpi_mid
#print axioms tanpi_floor

end Verified.Examples.SinpiTanpi
