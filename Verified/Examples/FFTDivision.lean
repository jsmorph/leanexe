import Verified.Examples.FourierTwiddle

namespace Verified.Examples.FFTDivision

open CodeLib.IEEE64 LeanExe.ProofKit F64Approx

set_option exponentiation.threshold 1200

theorem normalize_near (n : UInt64) (hn : 0 < n.toNat) (hsize : n.toNat ≤ 2 ^ 53)
    (y : Float) (R L E : ℝ) (hy : FApprox y R E) (hR : |R| ≤ L)
    (hsafe : L + E < (2 : ℝ) ^ 1022) :
    FApprox (y / n.toFloat) (R / (n.toNat : ℝ))
      ((E + unitRoundoff64 * (L + E)) / (n.toNat : ℝ) +
        multiplicationUnderflowEpsilon) := by
  have hnreal : (0 : ℝ) < n.toNat := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n.toNat := by exact_mod_cast (show 1 ≤ n.toNat from hn)
  have hden := FourierTwiddle.convert_near n hsize
  change FApprox n.toFloat (n.toNat : ℝ) 0 at hden
  have hL : 0 ≤ L := (abs_nonneg _).trans hR
  have hE : 0 ≤ E := (abs_nonneg _).trans hy.2
  have hM := add_nonneg hL hE
  have hcap : (L + E) / (n.toNat : ℝ) < (2 : ℝ) ^ 1022 :=
    (div_le_self hM hn1).trans_lt hsafe
  have hd := fapprox_div hy hden L (n.toNat : ℝ) hR
    (by rw [abs_of_pos hnreal]) hnreal ((L + E) / (n.toNat : ℝ))
    (by rw [sub_zero]) hcap
  simp only [mul_zero, zero_div, add_zero, sub_zero] at hd
  exact hd.mono (le_of_eq (by
    unfold unitRoundoff64 multiplicationUnderflowEpsilon
    ring))

#print axioms normalize_near

end Verified.Examples.FFTDivision
