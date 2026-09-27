import Project.ExpArm.IntegerSelection

namespace Project.ExpArm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem high_product_exact (word : UInt64) (hf : Finite word) (k : Int)
    (hv : value word = (k : ℝ)) (hk : k.natAbs ≤ 180000) :
    Finite (Wasm.IEEE64.mul word 0xBF762E42FEFA0000) ∧
    value (Wasm.IEEE64.mul word 0xBF762E42FEFA0000) =
      (k : ℝ) * value 0xBF762E42FEFA0000 := by
  have hs : Wasm.IEEE64.scaledValue word = k * (2 : Int)^1074 := by
    have hr := (div_eq_iff (by positivity : (2 : ℝ)^1074 ≠ 0)).mp hv
    exact_mod_cast hr
  have hm : Wasm.IEEE64.scaledMagnitude word = k.natAbs * 2^1074 := by
    rw [← natAbs_scaledValue, hs, Int.natAbs_mul]
    rfl
  have hc : Wasm.IEEE64.scaledMagnitude 0xBF762E42FEFA0000 = 47632711549 * 2^1031 := by
    rfl
  have hn : k.natAbs * 47632711549 < 2^53 := by omega
  have hp : Wasm.IEEE64.scaledMagnitude word *
      Wasm.IEEE64.scaledMagnitude 0xBF762E42FEFA0000 =
      (k.natAbs * 47632711549) * 2^(1074+1031) := by
    rw [hm, hc, pow_add]
    ring
  have hmax : (k.natAbs * 47632711549) * 2^1031 < 2^2097 := by
    calc
      _ < 2^53 * 2^1031 := Nat.mul_lt_mul_of_pos_right hn (by positivity)
      _ < _ := by norm_num
  have h := F64ExactArithmetic.mul_exact_scaled word 0xBF762E42FEFA0000 hf (by rfl)
    (k.natAbs * 47632711549) 1031 hn hp hmax
  simpa only [hv] using h

theorem reduction_high_product (x : UInt64) (hf : Finite x) (hx : |value x| ≤ 800) :
    let kd := Wasm.IEEE64.sub (reductionWord x) 0x4338000000000000
    Finite (Wasm.IEEE64.mul kd 0xBF762E42FEFA0000) ∧
    value (Wasm.IEEE64.mul kd 0xBF762E42FEFA0000) =
      (reductionInteger x : ℝ) * value 0xBF762E42FEFA0000 := by
  have hx' : |value x| ≤ 1024 := hx.trans (by norm_num)
  have hs := integer_selection x hf hx'
  apply high_product_exact _ hs.2.2.1 _ hs.2.2.2.1
  have hk := reductionInteger_abs x hf hx'
  have hb : |(reductionInteger x : ℝ)| ≤ 180000 := by linarith
  have hi : |reductionInteger x| ≤ (180000 : Int) := by exact_mod_cast hb
  rw [Int.abs_eq_natAbs] at hi
  exact_mod_cast hi

#print axioms reduction_high_product
end Project.ExpArm
