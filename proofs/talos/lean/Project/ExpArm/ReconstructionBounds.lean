import Project.ExpArm.SubnormalProduct
import Project.ExpArm.NormalPath

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem reconstruction_bounds (scale tmp : UInt64) (hs : Finite scale) (ht : Finite tmp)
    (hl : (2 : ℝ)^(-500 : Int) ≤ value scale) (hu : value scale ≤ (2 : ℝ)^500)
    (hsmall : |value tmp| ≤ 1/250) :
    let r := normalReconstruction scale tmp
    Finite r ∧ value scale/2 ≤ value r ∧ value r ≤ 2*value scale := by
  have hp := scale_product_bound scale tmp hs ht hl hu hsmall
  have hsp : 0 < value scale := (by positivity : (0 : ℝ) < 2^(-500 : Int)).trans_le hl
  have hpm := abs_le.mp hp.2.1
  have hpos : 0 < value scale+value (Wasm.IEEE64.mul scale tmp) := by linarith
  have hbound : |value scale+value (Wasm.IEEE64.mul scale tmp)| < (2 : ℝ)^1023 := by
    rw [abs_of_pos hpos]
    calc
      _ ≤ (201/200)*value scale := by linarith
      _ ≤ (201/200)*(2 : ℝ)^500 := by nlinarith only [hu]
      _ < _ := by norm_num
  have h := F64AddBounds.add_real_relative scale (Wasm.IEEE64.mul scale tmp) hs hp.1 hbound
  have he := h.2
  rw [abs_of_pos hpos] at he
  have he' := abs_le.mp he
  dsimp [unitRoundoff64] at he'
  refine ⟨h.1, ?_, ?_⟩ <;>
    dsimp only [normalReconstruction] <;> linarith

theorem scaled_table_magnitude (word bits : UInt64) (c : Int)
    (he : 0 ≤ 1023+(shiftInteger word/128+c))
    (hs : value bits*(2 : ℝ)^1023 = value (tableScaleWord (word &&& 127).toNat)*
      (2 : ℝ)^(1023+(shiftInteger word/128+c)).toNat) :
    (2 : ℝ)^(shiftInteger word/128+c) ≤ value bits ∧
    value bits ≤ (199/100)*(2 : ℝ)^(shiftInteger word/128+c) := by
  let i := (word &&& 127).toNat
  have hi : i < 128 := by
    have h : i ≤ 127 := UInt64.le_iff_toNat_le.mp UInt64.and_le_right
    omega
  have ht := table_real_bounds i hi
  have hv : value bits = value (tableScaleWord i)*scaleFactor (shiftInteger word/128+c) := by
    dsimp [scaleFactor]
    rw [← mul_div_assoc]
    exact (eq_div_iff (by positivity)).mpr hs
  rw [scaleFactor_zpow _ he] at hv
  have hp : 0 < (2 : ℝ)^(shiftInteger word/128+c) := by positivity
  rw [hv]
  constructor
  · nlinarith [ht.2.2.1]
  · nlinarith [table_upper i hi]

#print axioms reconstruction_bounds
#print axioms scaled_table_magnitude
end Project.ExpArm
