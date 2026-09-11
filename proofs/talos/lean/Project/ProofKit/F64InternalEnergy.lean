import Project.ProofKit.F64StrictOrder
import CodeLib.IEEE64.Operations

namespace Project.ProofKit.F64InternalEnergy
open CodeLib.IEEE64
open Project.ProofKit.F64Order

set_option exponentiation.threshold 4096

def residual (rho mx my energy : UInt64) : UInt64 :=
  let product := Wasm.IEEE64.mul rho energy
  let xx := Wasm.IEEE64.mul mx mx
  let yy := Wasm.IEEE64.mul my my
  let sum := Wasm.IEEE64.add xx yy
  let kinetic := Wasm.IEEE64.mul 0x3FE0000000000000 sum
  Wasm.IEEE64.sub product kinetic

theorem residual_error (rho mx my energy : UInt64)
    (hr : Finite rho) (hx : Finite mx) (hy : Finite my) (he : Finite energy)
    (br : |value rho| ≤ 1 / 2) (bx : |value mx| ≤ 1 / 2)
    (byy : |value my| ≤ 1 / 2) (be : |value energy| ≤ 1 / 2) :
    Finite (residual rho mx my energy) ∧
      |value (residual rho mx my energy) -
        (value rho * value energy - ((value mx)^2 + (value my)^2) / 2)| ≤
          5 * arithmeticEpsilon := by
  let ε := arithmeticEpsilon
  have eps_pos : 0 < ε := by norm_num [ε, arithmeticEpsilon]
  have eps_small : ε < 1 / 100 := by norm_num [ε, arithmeticEpsilon]
  have product_bound (a b : UInt64) (ha : |value a| ≤ 1 / 2)
      (hb : |value b| ≤ 1 / 2) : |value a * value b| ≤ 1 / 4 := by
    rw [abs_mul]
    calc
      _ ≤ (1 / 2 : ℝ) * (1 / 2) := mul_le_mul ha hb (abs_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have product_error (a b : UInt64) (ha : Finite a) (hb : Finite b)
      (ba : |value a| ≤ 1 / 2) (bb : |value b| ≤ 1 / 2) :
      Finite (Wasm.IEEE64.mul a b) ∧
        |value (Wasm.IEEE64.mul a b) - value a * value b| ≤ ε ∧
        |value (Wasm.IEEE64.mul a b)| ≤ 1 / 4 + ε := by
    obtain ⟨hf, herr⟩ := mul_real_error a b ha hb
      (ba.trans (by norm_num)) (bb.trans (by norm_num))
    change |value (Wasm.IEEE64.mul a b) - value a * value b| ≤ ε at herr
    refine ⟨hf, herr, ?_⟩
    calc
      _ = |(value (Wasm.IEEE64.mul a b) - value a * value b) + value a * value b| := by congr 1; ring
      _ ≤ |value (Wasm.IEEE64.mul a b) - value a * value b| + |value a * value b| := abs_add_le _ _
      _ ≤ ε + 1 / 4 := add_le_add herr (product_bound a b ba bb)
      _ = _ := by ring
  obtain ⟨hp, ep, bp⟩ := product_error rho energy hr he br be
  obtain ⟨hxx, exx, bxx⟩ := product_error mx mx hx hx bx bx
  obtain ⟨hyy, eyy, byy'⟩ := product_error my my hy hy byy byy
  let xx := Wasm.IEEE64.mul mx mx
  let yy := Wasm.IEEE64.mul my my
  let sum := Wasm.IEEE64.add xx yy
  have bxx1 : |value xx| ≤ 1 := by dsimp [xx]; linarith
  have byy1 : |value yy| ≤ 1 := by dsimp [yy]; linarith
  obtain ⟨hs, es⟩ := add_real_error xx yy hxx hyy bxx1 byy1
  change |value sum - (value xx + value yy)| ≤ ε at es
  have bs : |value sum| ≤ 1 / 2 + 3 * ε := by
    have triangle := abs_add_le (value xx) (value yy)
    have bridge := abs_add_le (value sum - (value xx + value yy)) (value xx + value yy)
    rw [sub_add_cancel] at bridge
    change |value xx| ≤ 1 / 4 + ε at bxx
    change |value yy| ≤ 1 / 4 + ε at byy'
    linarith
  have half_finite : Finite 0x3FE0000000000000 := by unfold CodeLib.IEEE64.Finite; decide
  have half_value : value 0x3FE0000000000000 = 1 / 2 := by
    change ((2^1073 : Nat) : ℝ) / (2 : ℝ)^1074 = 1 / 2
    norm_num
  have half_bound : |value 0x3FE0000000000000| ≤ 1 := by rw [half_value]; norm_num
  have bs1 : |value sum| ≤ 1 := by linarith
  let kinetic := Wasm.IEEE64.mul 0x3FE0000000000000 sum
  obtain ⟨hk, ek⟩ := mul_real_error 0x3FE0000000000000 sum half_finite hs half_bound bs1
  change |value kinetic - value 0x3FE0000000000000 * value sum| ≤ ε at ek
  rw [half_value] at ek
  have bk : |value kinetic| ≤ 1 := by
    have bridge := abs_add_le (value kinetic - (1 / 2) * value sum) ((1 / 2) * value sum)
    rw [sub_add_cancel, abs_mul] at bridge
    norm_num at bridge
    linarith
  have bp1 : |value (Wasm.IEEE64.mul rho energy)| ≤ 1 := by linarith
  obtain ⟨hd, ed⟩ := sub_real_error (Wasm.IEEE64.mul rho energy) kinetic hp hk bp1 bk
  refine ⟨hd, ?_⟩
  change |value (residual rho mx my energy) -
    (value (Wasm.IEEE64.mul rho energy) - value kinetic)| ≤ ε at ed
  change |value xx - value mx * value mx| ≤ ε at exx
  change |value yy - value my * value my| ≤ ε at eyy
  have hp' := abs_le.mp ep
  have hxx' := abs_le.mp exx
  have hyy' := abs_le.mp eyy
  have hs' := abs_le.mp es
  have hk' := abs_le.mp ek
  have hd' := abs_le.mp ed
  apply abs_le.mpr
  constructor <;> nlinarith

#print axioms residual_error
end Project.ProofKit.F64InternalEnergy
