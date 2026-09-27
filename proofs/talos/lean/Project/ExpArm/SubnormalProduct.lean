import Project.ProofKit.F64MulBounds
import Project.ProofKit.F64OneAdd

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem scale_product_bound (scale tmp : UInt64) (hs : Finite scale) (ht : Finite tmp)
    (hl : (2 : ℝ)^(-500 : Int) ≤ value scale) (hu : value scale ≤ (2 : ℝ)^500)
    (hsmall : |value tmp| ≤ 1/250) :
    let p := Wasm.IEEE64.mul scale tmp
    Finite p ∧ |value p| ≤ value scale/200 ∧
      |value p-value scale*value tmp| ≤ value scale/1000000000000000000 := by
  have hp : 0 < value scale := (by positivity : (0 : ℝ) < 2^(-500 : Int)).trans_le hl
  have hmul : |value scale*value tmp| ≤ value scale/250 := by
    rw [abs_mul, abs_of_pos hp]
    nlinarith only [hsmall, hp]
  have hb : |value scale*value tmp| < (2 : ℝ)^1022 := by
    apply hmul.trans_lt
    calc
      _ ≤ (2 : ℝ)^500/250 := div_le_div_of_nonneg_right hu (by norm_num)
      _ < _ := by norm_num
  have h := F64MulBounds.mul_real_mixed scale tmp hs ht hb
  have hunder : multiplicationUnderflowEpsilon ≤ value scale/100000000000000000000 := by
    calc
      _ ≤ (2 : ℝ)^(-500 : Int)/100000000000000000000 := by norm_num [multiplicationUnderflowEpsilon]
      _ ≤ _ := div_le_div_of_nonneg_right hl (by norm_num)
  have he : |value (Wasm.IEEE64.mul scale tmp)-value scale*value tmp| ≤
      value scale/1000000000000000000 := by
    apply h.2.trans
    have hround : unitRoundoff64*|value scale*value tmp| ≤ unitRoundoff64*(value scale/250) :=
      mul_le_mul_of_nonneg_left hmul (by norm_num [unitRoundoff64])
    dsimp [unitRoundoff64] at hround ⊢
    linarith
  refine ⟨h.1, ?_, he⟩
  have hsum := abs_add_le (value (Wasm.IEEE64.mul scale tmp)-value scale*value tmp)
    (value scale*value tmp)
  rw [sub_add_cancel] at hsum
  linarith

theorem scale_le_two_of_small_sum (scale p : UInt64) (hs : Finite scale) (hp : Finite p)
    (hsl : 0 < value scale) (hsu : value scale ≤ (2 : ℝ)^300)
    (hpm : |value p| ≤ value scale/200)
    (hy : Wasm.IEEE64.add scale p < 0x3FF0000000000000) : value scale ≤ 2 := by
  have habs := abs_le.mp hpm
  have hpos : 0 < value scale+value p := by linarith
  have hbound : |value scale+value p| < (2 : ℝ)^1023 := by
    rw [abs_of_pos hpos]
    calc
      _ ≤ (201/200)*value scale := by linarith
      _ ≤ (201/200)*(2 : ℝ)^300 := by nlinarith only [hsu]
      _ < _ := by norm_num
  have h := F64AddBounds.add_real_relative scale p hs hp hbound
  have herr := h.2
  rw [abs_of_pos hpos] at herr
  have he := (abs_le.mp herr).1
  have hu := F64OneAdd.below_one_value _ hy
  norm_num [unitRoundoff64] at he
  linarith

#print axioms scale_product_bound
#print axioms scale_le_two_of_small_sum
end Project.ExpArm
