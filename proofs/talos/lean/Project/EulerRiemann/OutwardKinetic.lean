import Project.EulerRiemann.OutwardSpeed
import Project.EulerRiemann.OutwardConstants
import Project.ProofKit.F64OutwardAccepted

namespace Project.EulerRiemann.OutwardSpeed
open CodeLib.IEEE64
open Project.ProofKit.F64Outward
set_option exponentiation.threshold 4096

theorem kinetic_lower (rho mx my : UInt64) (hr : 0 < value rho)
    (h : (kineticLower rho mx my).status = 0) :
    Finite (kineticLower rho mx my).value ∧
    value (kineticLower rho mx my).value ≤ ((value mx)^2+(value my)^2)/(2*value rho) := by
  let xx := mul false mx mx
  let yy := mul false my my
  let sum := add false xx.value yy.value
  let half := mul false 0x3FE0000000000000 sum.value
  unfold kineticLower at h ⊢
  dsimp only at h ⊢
  split_ifs at h with hxy hsum hhalf
  · simp only [hxy, hsum, hhalf, ite_true]
    have hxy : xx.status = 0 ∧ yy.status = 0 := by simpa [xx, yy] using hxy
    have hsum : sum.status = 0 := by simpa [sum, xx, yy] using hsum
    have hhalf : half.status = 0 := by simpa [half, sum, xx, yy] using hhalf
    change (div false half.value rho).status = 0 at h
    change Finite (div false half.value rho).value ∧
      value (div false half.value rho).value ≤ _
    have ex := sound_lower (mul_accepted false mx mx hxy.1).2.2
    have ey := sound_lower (mul_accepted false my my hxy.2).2.2
    have es := sound_lower (add_accepted false xx.value yy.value hsum).2.2
    have eh := sound_lower (mul_accepted false 0x3FE0000000000000 sum.value hhalf).2.2
    have ed := sound_lower (div_accepted false half.value rho h).2.2.2
    change Finite xx.value ∧ value xx.value ≤ value mx*value mx at ex
    change Finite yy.value ∧ value yy.value ≤ value my*value my at ey
    change Finite sum.value ∧ value sum.value ≤ value xx.value+value yy.value at es
    change Finite half.value ∧ value half.value ≤ value 0x3FE0000000000000*value sum.value at eh
    have hsumBound : value sum.value ≤ (value mx)^2+(value my)^2 := by
      nlinarith only [ex.2, ey.2, es.2]
    rw [half_value] at eh
    have hhalfBound : value half.value ≤ ((value mx)^2+(value my)^2)/2 := by
      linarith only [eh.2, hsumBound]
    refine ⟨ed.1, ed.2.trans ?_⟩
    calc
      value half.value/value rho ≤ (((value mx)^2+(value my)^2)/2)/value rho :=
        div_le_div_of_nonneg_right hhalfBound hr.le
      _ = ((value mx)^2+(value my)^2)/(2*value rho) := by ring
  all_goals exact False.elim ((by decide : (1:UInt64) ≠ 0) h)

#print axioms kinetic_lower
end Project.EulerRiemann.OutwardSpeed
