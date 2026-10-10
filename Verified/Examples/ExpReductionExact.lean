import LeanExe.ProofKit.F64DyadicBounds
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64GridExact
import CodeLib.IEEE64.Operations
import LeanExe.ProofKit.F64AddBounds

namespace Verified.Examples.ExpReductionExact
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem high_scaled_value :
    Wasm.IEEE64.scaledValue 0x3F762E42FEFA0000 =
      (47632711549 : Int) * 2 ^ 1031 := by
  norm_num [Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.sign,
    Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem high_product_representable (k : Nat) (hk : k ≤ 189000) :
    roundedMagnitude ((47632711549 * k) * 2 ^ 1031) =
      (47632711549 * k) * 2 ^ 1031 := by
  exact F64GridExact.roundedMagnitude_shifted_small _ _ (by omega)

#print axioms high_scaled_value
#print axioms high_product_representable

theorem high_product_rounder (negative : Bool) (k : Nat) (hk : k ≤ 189000) :
    Wasm.IEEE64.roundDyadicMagnitude negative ((47632711549 * k) * 2 ^ 2105) 1074 =
      Wasm.IEEE64.roundScaledMagnitude negative ((47632711549 * k) * 2 ^ 1031) := by
  simpa only [show 1074 + 1031 = 2105 by decide] using
    F64PowerScale.dyadic_shifted_exact negative (47632711549 * k) 1031 (by omega)

theorem high_product_packing (negative : Bool) (k : Nat) (hk : k ≤ 189000) :
    Finite (Wasm.IEEE64.roundDyadicMagnitude negative ((47632711549 * k) * 2 ^ 2105) 1074) ∧
    Wasm.IEEE64.scaledMagnitude
        (Wasm.IEEE64.roundDyadicMagnitude negative ((47632711549 * k) * 2 ^ 2105) 1074) =
      (47632711549 * k) * 2 ^ 1031 ∧
    Wasm.IEEE64.sign
        (Wasm.IEEE64.roundDyadicMagnitude negative ((47632711549 * k) * 2 ^ 2105) 1074) =
      negative := by
  have hsmall : 47632711549 * k ≤ 2 ^ 53 := by omega
  have hmax : (47632711549 * k) * 2 ^ 1031 < 2 ^ 2097 := by
    calc
      _ ≤ 2 ^ 53 * 2 ^ 1031 := Nat.mul_le_mul_right _ hsmall
      _ = 2 ^ 1084 := by rw [← pow_add]
      _ < 2 ^ 2097 := by norm_num
  rw [high_product_rounder negative k hk]
  have hp := F64Packing.pack_spec negative _ hmax
  rw [high_product_representable k hk] at hp
  exact hp

theorem high_mul_exact (kd : UInt64) (k : Nat) (hkd : Finite kd)
    (hmag : Wasm.IEEE64.scaledMagnitude kd = k * 2 ^ 1074) (hk : k ≤ 189000) :
    Finite (Wasm.IEEE64.mul kd 0xBF762E42FEFA0000) ∧
    value (Wasm.IEEE64.mul kd 0xBF762E42FEFA0000) =
      value kd * value 0xBF762E42FEFA0000 := by
  have hf : Finite 0xBF762E42FEFA0000 := by
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  have hhm : Wasm.IEEE64.scaledMagnitude 0xBF762E42FEFA0000 =
      47632711549 * 2 ^ 1031 := by
    norm_num [Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent,
      Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  have hhs : Wasm.IEEE64.sign 0xBF762E42FEFA0000 = true := by decide +kernel
  have hprod : Wasm.IEEE64.scaledMagnitude kd *
      Wasm.IEEE64.scaledMagnitude 0xBF762E42FEFA0000 =
        (47632711549 * k) * 2 ^ 2105 := by
    rw [hmag, hhm, show (2 : Nat) ^ 2105 = 2 ^ 1074 * 2 ^ 1031 by rw [← pow_add]]
    ring
  rw [mul_finite_rounder kd _ hkd hf, hprod]
  have hp := high_product_packing (Wasm.IEEE64.sign kd != Wasm.IEEE64.sign 0xBF762E42FEFA0000)
    k hk
  refine ⟨hp.1, ?_⟩
  simp only [value, Wasm.IEEE64.scaledValue]
  rw [hp.2.2, hp.2.1, hmag, hhm, hhs]
  cases Wasm.IEEE64.sign kd <;> simp <;> ring

#print axioms high_product_rounder
#print axioms high_product_packing
#print axioms high_mul_exact

theorem integer_packing_exact (k : Int) (hk : k.natAbs ≤ 2 ^ 18) :
    Finite (Wasm.IEEE64.roundScaledMagnitude (k < 0) (k.natAbs * 2 ^ 1074)) ∧
    Wasm.IEEE64.scaledValue
        (Wasm.IEEE64.roundScaledMagnitude (k < 0) (k.natAbs * 2 ^ 1074)) =
      k * 2 ^ 1074 := by
  exact F64GridExact.signed_grid_packing_exact k 1074 (hk.trans (by norm_num)) (by norm_num)

#print axioms integer_packing_exact

end Verified.Examples.ExpReductionExact
