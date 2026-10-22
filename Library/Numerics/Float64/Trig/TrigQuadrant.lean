import Library.Numerics.Float64.Trig.TrigKernelSpec
import Library.Numerics.Float64.Trig.TrigCosKernel
import Library.Numerics.Float64.Trig.TrigReduce
import Library.Numerics.Float64.Trig.TrigStep

/-!
The reduced path of `sin` and `cos`: for a reduction `Reduced xa n y0 y1`, the sine and cosine
kernels on `y0 + y1` lie within one step of `sin r` and `cos r`, `r = xa - N π/2`, and the
quadrant `N mod 4` turns them into `sin xa` and `cos xa`.
-/

namespace Library.Numerics.Float64.Trig.TrigQuadrant

open CodeLib.IEEE64 LeanExe.ProofKit TrigKernelWords TrigKernelSpec TrigCosKernel TrigReduce
  TrigStep

local notation "𝐮" => unitRoundoff64

/-- The kernels on a reduced argument. -/
theorem reduced_kernels (xa n : UInt64) (y0 y1 : Float) (hR : Reduced xa n y0.toBits y1.toBits) :
    ∃ N : Int, ((n.toNat % 4 : Nat) : Int) = N % 4 ∧
      F64SignedRounding.WithinSteps 1 (Real.sin (value xa - N * (Real.pi / 2)))
        (Trig.kernelSin y0 y1 true).toBits ∧
      F64SignedRounding.WithinSteps 1 (Real.cos (value xa - N * (Real.pi / 2)))
        (Trig.kernelCos y0 y1).toBits := by
  obtain ⟨N, hN, f0, f1, hacc, htail, hrl, hru⟩ := hR
  set r := value xa - N * (Real.pi / 2) with hr
  refine ⟨N, by push_cast; exact hN, ?_, ?_⟩
  all_goals
    have hpi : Real.pi < 3.15 := Real.pi_lt_d2
    have hr1 : |r| ≤ 78541 / 100000 := by
      have : Real.pi < 3.1416 := Real.pi_lt_d4
      have h17 : (1 : ℝ) / 2 ^ 17 ≤ 1 / 100000 := by norm_num
      linarith
    have hr0 : 1 / 2 ^ 69 ≤ |r| := le_trans (by norm_num) hrl
    set X0 := |value y0.toBits| with hX0
    have hX0nn : 0 ≤ X0 := abs_nonneg _
    have hsum := abs_le.mp hacc
    have hrr : |r| / 2 ^ 60 ≤ |r| := div_le_self (abs_nonneg _) (by norm_num)
    -- `X0` lies within a relative `2 ^ -50` of `|r|`.
    have hup : X0 ≤ |r| * (1 + 1 / 2 ^ 50) := by
      have h1 := abs_add_le (value y0.toBits + value y1.toBits) (-(value y1.toBits))
      rw [show value y0.toBits + value y1.toBits + -value y1.toBits = value y0.toBits by ring,
        abs_neg] at h1
      have h2 : |value y0.toBits + value y1.toBits| ≤ |r| + |r| / 2 ^ 60 := by
        have := abs_sub_abs_le_abs_sub (value y0.toBits + value y1.toBits) r
        linarith
      have h3 : X0 * (1 - 1 / 2 ^ 52) ≤ |r| * (1 + 1 / 2 ^ 60) := by
        rw [← hX0] at h1
        nlinarith
      nlinarith [abs_nonneg r]
    have hlo : 1 / 2 ^ 70 ≤ X0 := by
      have h1 := abs_add_le (value y0.toBits) (value y1.toBits)
      have h2 : |r| - |r| / 2 ^ 60 ≤ |value y0.toBits + value y1.toBits| := by
        have := abs_sub_abs_le_abs_sub r (value y0.toBits + value y1.toBits)
        have hc : |r - (value y0.toBits + value y1.toBits)| =
            |value y0.toBits + value y1.toBits - r| := abs_sub_comm _ _
        linarith
      have h3 : |r| * (1 - 1 / 2 ^ 60) ≤ X0 * (1 + 1 / 2 ^ 52) := by
        rw [← hX0] at h1
        nlinarith
      nlinarith [abs_nonneg r]
    have hX1 : X0 ≤ 78541 / 100000 := by
      have : Real.pi < 3.1416 := Real.pi_lt_d4
      have h17 : (1 : ℝ) / 2 ^ 17 ≤ 1 / 100000 := by norm_num
      nlinarith [abs_nonneg r]
    have hy : |value y1.toBits| ≤ X0 / 2 ^ 52 := htail
    have har : |value y0.toBits + value y1.toBits - r| ≤ |r| / 2 ^ 59 :=
      hacc.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num))
  · obtain ⟨hcf, t, hct, hts⟩ := sinTail_spec y0.toBits y1.toBits X0 f0 f1 rfl hlo hX1 hy
    rw [kernelSin_tail_bits]
    exact sin_final _ t _ r X0 hcf hct hts har hX0nn hup hr0 hr1
  · obtain ⟨hcf, hc⟩ := cos_spec y0.toBits y1.toBits X0 f0 f1 rfl hlo hX1 hy
    rw [kernelCos_bits]
    exact cos_final _ _ r hcf hc har hr1

/-- `sin` and `cos` of `r + N π/2` by the quadrant `k = N mod 4`. -/
theorem quadrant (r : ℝ) (N : Int) (k : Nat) (hk : (k : Int) = N % 4) :
    (k = 0 → Real.sin (r + N * (Real.pi / 2)) = Real.sin r ∧
      Real.cos (r + N * (Real.pi / 2)) = Real.cos r) ∧
    (k = 1 → Real.sin (r + N * (Real.pi / 2)) = Real.cos r ∧
      Real.cos (r + N * (Real.pi / 2)) = -Real.sin r) ∧
    (k = 2 → Real.sin (r + N * (Real.pi / 2)) = -Real.sin r ∧
      Real.cos (r + N * (Real.pi / 2)) = -Real.cos r) ∧
    (k = 3 → Real.sin (r + N * (Real.pi / 2)) = -Real.cos r ∧
      Real.cos (r + N * (Real.pi / 2)) = Real.sin r) := by
  have hN : (N : ℝ) = k + ((N / 4 : Int) : ℝ) * 4 := by
    have h := Int.emod_add_ediv_mul N 4
    rw [← hk] at h
    have h' := congrArg (fun z : Int => (z : ℝ)) h
    push_cast at h'
    linarith
  have hs : r + N * (Real.pi / 2) = (r + k * (Real.pi / 2)) + ((N / 4 : Int) : ℝ) * (2 * Real.pi) := by
    rw [hN]
    ring
  rw [hs, Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]
  have h3 : r + 3 * (Real.pi / 2) = (r + Real.pi / 2) + Real.pi := by ring
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> subst h <;> push_cast
  · simp
  · simp [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
  · rw [show r + 2 * (Real.pi / 2) = r + Real.pi by ring, Real.sin_add_pi, Real.cos_add_pi]
    exact ⟨rfl, rfl⟩
  · rw [h3, Real.sin_add_pi, Real.cos_add_pi, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two]
    exact ⟨rfl, by ring⟩

#print axioms reduced_kernels
#print axioms quadrant

end Library.Numerics.Float64.Trig.TrigQuadrant
