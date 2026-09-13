import Project.ProofKit.F64ProductBound
import Project.ProofKit.F64ArithmeticBounds

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order

set_option exponentiation.threshold 4096

theorem courant_exact_bound (ratio alpha : UInt64)
    (hr : positiveBits ratio = true) (ha : positiveBits alpha = true)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (br : value ratio ≤ 1) (ba : value alpha ≤ 32 * M^2)
    (hc : positiveBits (Wasm.IEEE64.mul ratio alpha) = true)
    (hhalf : Wasm.IEEE64.mul ratio alpha ≤ 0x3FE0000000000000) :
    value ratio * value alpha ≤ 51 / 100 := by
  have hrp := positiveBits_spec ratio hr
  have hap := positiveBits_spec alpha ha
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hprod : 0 < value ratio * value alpha := mul_pos hrp.2 hap.2
  have hbound : |value ratio * value alpha| < (2 : ℝ)^1022 := by
    rw [abs_of_pos hprod]
    calc
      value ratio * value alpha ≤ 1 * value alpha := mul_le_mul_of_nonneg_right br hap.2.le
      _ ≤ 32 * M^2 := by simpa only [one_mul] using ba
      _ ≤ 32 * ((2 : ℝ)^100)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMmax 2) (by norm_num)
      _ < (2 : ℝ)^1022 := by norm_num
  exact Project.ProofKit.F64ProductBound.product_le_of_rounded_half ratio alpha hrp.1 hap.1
    hprod.le hbound hc hhalf

theorem selected_courant_bound (ratio left right : UInt64)
    (hr : positiveBits ratio = true) (hl : positiveBits left = true) (ht : positiveBits right = true)
    (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (br : value ratio ≤ 1) (bl : value left ≤ 32 * M^2) (bt : value right ≤ 32 * M^2) :
    let alpha := if left ≤ right then right else left
    positiveBits (Wasm.IEEE64.mul ratio alpha) = true →
    Wasm.IEEE64.mul ratio alpha ≤ 0x3FE0000000000000 →
    value ratio * (value left + value right) / 2 ≤ 51 / 100 := by
  let alpha := if left ≤ right then right else left
  dsimp only
  intro hc hhalf
  obtain ⟨ha, hmax⟩ := positive_max_value left right hl ht
  have ba : value alpha ≤ 32 * M^2 := by
    rw [show value alpha = max (value left) (value right) from hmax]
    exact max_le bl bt
  have hprod := courant_exact_bound ratio alpha hr ha M hM hMmax br ba hc hhalf
  have hrl := mul_le_mul_of_nonneg_left (le_max_left (value left) (value right))
    (positiveBits_spec ratio hr).2.le
  have hrr := mul_le_mul_of_nonneg_left (le_max_right (value left) (value right))
    (positiveBits_spec ratio hr).2.le
  change value alpha = max (value left) (value right) at hmax
  rw [← hmax] at hrl hrr
  nlinarith only [hrl, hrr, hprod]

#print axioms courant_exact_bound
#print axioms selected_courant_bound
end Project.EulerRiemann.Numerics
