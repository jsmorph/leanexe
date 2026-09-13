import Project.EulerCellStep.Model
import Project.ProofKit.F64AffineUpdate
import Project.ProofKit.F64Order

namespace Project.EulerRiemann.Numerics
open CodeLib.IEEE64
open Project.ProofKit.F64Order

set_option exponentiation.threshold 4096

theorem update_error (ratio state fluxL fluxR : UInt64)
    (hr : positiveBits ratio = true) (hs : Finite state) (hl : Finite fluxL) (hh : Finite fluxR)
    (hr1 : value ratio ≤ 1) (M : ℝ) (hM : 1 ≤ M) (hMmax : M ≤ (2 : ℝ)^100)
    (bs : |value state| ≤ M) (bl : |value fluxL| ≤ 66 * M^5) (bh : |value fluxR| ≤ 66 * M^5) :
    let result := Project.EulerCellStep.Model.updateCheckedBits ratio state fluxL fluxR
    result.status = 0 ∧ Finite result.value ∧
    |value result.value - (value state - value ratio * (value fluxR - value fluxL))| ≤
      arithmeticEpsilon * M + 396 * arithmeticEpsilon * value ratio * M^5 +
        2 * multiplicationUnderflowEpsilon := by
  have hp := positiveBits_spec ratio hr
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hM5 : 1 ≤ M^5 := one_le_pow₀ hM
  have hM15 : M ≤ M^5 := by
    have h := mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M^4) hMpos.le
    nlinarith only [h]
  have hmax : M + 132 * M^5 ≤ (2 : ℝ)^1000 := by
    calc
      _ ≤ 133 * M^5 := by linarith only [hM15]
      _ ≤ 133 * ((2 : ℝ)^100)^5 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hMpos.le hMmax 5) (by norm_num)
      _ ≤ (2 : ℝ)^1000 := by norm_num
  have bd : |value fluxR - value fluxL| ≤ 132 * M^5 := by
    have h := abs_sub (value fluxR) (value fluxL)
    linarith only [h, bh, bl]
  obtain ⟨hd, hi, hv, herr⟩ := Project.ProofKit.F64AffineUpdate.difference_update ratio state fluxL fluxR
    hp.1 hs hl hh hp.2.le hr1 M (132 * M^5) hM (by linarith only [hM5]) hmax bs bd
  let difference := Wasm.IEEE64.sub fluxR fluxL
  let increment := Wasm.IEEE64.mul ratio difference
  let result := Wasm.IEEE64.sub state increment
  have hinput : (Project.EulerConservative.Model.positiveBits ratio && Project.EulerConservative.Model.finiteBits state &&
      Project.EulerConservative.Model.finiteBits fluxL && Project.EulerConservative.Model.finiteBits fluxR) = true := by
    change (positiveBits ratio && finiteBits state && finiteBits fluxL && finiteBits fluxR) = true
    simp only [Bool.and_eq_true_iff, finiteBits_iff]
    exact ⟨⟨⟨hr, hs⟩, hl⟩, hh⟩
  have houtput : (Project.EulerConservative.Model.finiteBits difference &&
      Project.EulerConservative.Model.finiteBits increment && Project.EulerConservative.Model.finiteBits result) = true := by
    change (finiteBits difference && finiteBits increment && finiteBits result) = true
    simp only [Bool.and_eq_true_iff, finiteBits_iff]
    exact ⟨⟨hd, hi⟩, hv⟩
  have hresult : Project.EulerCellStep.Model.updateCheckedBits ratio state fluxL fluxR = ⟨0, result⟩ := by
    unfold Project.EulerCellStep.Model.updateCheckedBits
    rw [ite_eq_left hinput, ite_eq_left houtput]
  dsimp only
  rw [hresult]
  exact ⟨rfl, hv, herr.trans_eq (by ring)⟩

#print axioms update_error
end Project.EulerRiemann.Numerics
