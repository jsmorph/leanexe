import Project.ProofKit.F64Order

namespace Project.ProofKit.F64Order
set_option exponentiation.threshold 4096
set_option maxRecDepth 8192

private def magnitude (n : Nat) : Nat :=
  if n / 2 ^ 52 = 0 then n % 2 ^ 52
  else (2 ^ 52 + n % 2 ^ 52) * 2 ^ (n / 2 ^ 52 - 1)

private theorem magnitude_strict {left right : Nat} (hlt : left < right) :
    magnitude left < magnitude right := by
  let le := left / 2 ^ 52
  let re := right / 2 ^ 52
  let lf := left % 2 ^ 52
  let rf := right % 2 ^ 52
  have hlf : lf < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hrf : rf < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hld : left = le * 2 ^ 52 + lf := (Nat.div_add_mod' left (2 ^ 52)).symm
  have hrd : right = re * 2 ^ 52 + rf := (Nat.div_add_mod' right (2 ^ 52)).symm
  change (if le = 0 then lf else (2 ^ 52 + lf) * 2 ^ (le - 1)) <
    (if re = 0 then rf else (2 ^ 52 + rf) * 2 ^ (re - 1))
  by_cases heq : le = re
  · have hfrac : lf < rf := by omega
    rw [← heq]
    split
    · exact hfrac
    · exact Nat.mul_lt_mul_of_pos_right (Nat.add_lt_add_left hfrac _) (by positivity)
  · have hexp : le < re := by omega
    have hrnz : re ≠ 0 := by omega
    rw [ite_eq_right hrnz]
    by_cases hlz : le = 0
    · rw [ite_eq_left hlz]
      have hp : 1 ≤ 2 ^ (re - 1) := Nat.one_le_pow _ _ (by omega)
      calc
        lf < 2 ^ 52 := hlf
        _ ≤ (2 ^ 52 + rf) * 2 ^ (re - 1) := by nlinarith
    · rw [ite_eq_right hlz]
      have hsig : 2 ^ 52 + lf < 2 ^ 53 := by norm_num at hlf ⊢; omega
      have hpow : 2 ^ le ≤ 2 ^ (re - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      calc
        (2 ^ 52 + lf) * 2 ^ (le - 1) < 2 ^ 53 * 2 ^ (le - 1) :=
          Nat.mul_lt_mul_of_pos_right hsig (by positivity)
        _ = 2 ^ 52 * 2 ^ le := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        _ ≤ 2 ^ 52 * 2 ^ (re - 1) := Nat.mul_le_mul_left _ hpow
        _ ≤ (2 ^ 52 + rf) * 2 ^ (re - 1) :=
          Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-- Strict ordering of sign-cleared encodings orders decoded magnitudes. -/
theorem abs_value_lt (left right : UInt64) (hlt : absBits left < absBits right) :
    |CodeLib.IEEE64.value left| < |CodeLib.IEEE64.value right| := by
  have hscaled : Wasm.IEEE64.scaledMagnitude left < Wasm.IEEE64.scaledMagnitude right := by
    rw [scaledMagnitude_abs, scaledMagnitude_abs]
    exact magnitude_strict (UInt64.lt_iff_toNat_lt.mp hlt)
  have habs (x : UInt64) : |(Wasm.IEEE64.scaledValue x : ℝ)| =
      Wasm.IEEE64.scaledMagnitude x := by
    simp [Wasm.IEEE64.scaledValue]
    split <;> simp
  simp only [CodeLib.IEEE64.value, abs_div, habs]
  exact div_lt_div_of_pos_right (by exact_mod_cast hscaled) (by positivity)

#print axioms abs_value_lt
end Project.ProofKit.F64Order
