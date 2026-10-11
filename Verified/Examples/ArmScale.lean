import Verified.Examples.ExpSpecialScale
import LeanExe.ProofKit.F64Magnitude

/-!
The scale words of Arm's `exp2` and `exp10`.  The bits `ExpScaleBits.scaleBits ki` hold
`2 ^ q H j` for `k = 128 q + j`, and lowering the exponent field by one binade, as
`exp2SpecialCase` does for a positive `k`, gives `2 ^ (q - 1) H j`.  These extend
`ExpScaleEncoding.encoded_scale_value` to every normal exponent.
-/

namespace Verified.Examples.ArmScale
open CodeLib.IEEE64
open LeanExe.ProofKit F64Magnitude

set_option exponentiation.threshold 4096

/-- The table head's fraction with any normal exponent field `e` has value `2 ^ (e - 1023) H j`. -/
theorem scale_value (j : Fin 128) (e : Nat) (he0 : 0 < e) (he : e < 2047) :
    Finite (Wasm.IEEE64.encodeFinite false e
        (Wasm.IEEE64.fraction (ExpTableBounds.headBits j.val))) ∧
      value (Wasm.IEEE64.encodeFinite false e
        (Wasm.IEEE64.fraction (ExpTableBounds.headBits j.val))) =
        (2 : ℝ) ^ ((e : Int) - 1023) * value (ExpTableBounds.headBits j.val) := by
  let f := Wasm.IEEE64.fraction (ExpTableBounds.headBits j.val)
  have hf : f < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hs := sign_encodeFinite false e f (by omega) hf
  have hex := exponent_encodeFinite false e f (by omega) hf
  have hfr := fraction_encodeFinite false e f (by omega) hf
  obtain ⟨hhs, hhe, _⟩ := ExpScaleFacts.checked_head_fields j
  have hp : (2 : ℝ) ^ (e - 1) = (2 : ℝ) ^ ((e : Int) - 1023) * (2 : ℝ) ^ 1022 := by
    have h1 : ((e - 1 : Nat) : Int) = ((e : Int) - 1023) + ((1022 : Nat) : Int) := by omega
    rw [← zpow_natCast, h1, zpow_add₀ (by norm_num), zpow_natCast]
  refine ⟨finite_encodeFinite false e f he hf, ?_⟩
  change value (Wasm.IEEE64.encodeFinite false e f) = _
  rw [normal_value _ hs (by rw [hex]; exact he0), hex, hfr,
    normal_value _ hhs (by rw [hhe]; norm_num), hhe, hp]
  norm_num only [Nat.reduceSub]
  dsimp [f]
  ring

/-- The scale word holds `2 ^ q H j` for every normal binade. -/
theorem ordinary_scale (ki : UInt64) (k q : Int) (j : Fin 128)
    (hki : (ki.toNat : Int) = (0x4338000000000000 : Int) + k)
    (hk : k = 128 * q + j.val) (hj : (ki % 128).toNat = j.val)
    (hqlo : -1022 ≤ q) (hqhi : q ≤ 1023) :
    Finite (ExpScaleBits.scaleBits ki) ∧
      value (ExpScaleBits.scaleBits ki) = (2 : ℝ) ^ q * value (ExpTableBounds.headBits j.val) := by
  let e := (1023 + q).toNat
  have heq : 1023 + q + ((0 : Nat) : Int) = (e : Int) + 4096 * ((0 : Nat) : Int) := by
    dsimp [e]
    omega
  have h := ExpScaleBits.scale_bits_adjusted_encoding ki k q j 0 e 0 hki hk hj heq (by omega)
  have h' : ExpScaleBits.scaleBits ki = Wasm.IEEE64.encodeFinite false e
      (Wasm.IEEE64.fraction (ExpTableBounds.headBits j.val)) := by
    simpa using h
  obtain ⟨hf, hv⟩ := scale_value j e (by omega) (by omega)
  have hq : (e : Int) - 1023 = q := by dsimp [e]; omega
  rw [hq] at hv
  rw [h']
  exact ⟨hf, hv⟩

/-- The scale lowered by one binade. -/
def halfScale (ki : UInt64) : UInt64 :=
  ExpScaleBits.scaleBits ki - ((1 : UInt64) <<< (52 : UInt64))

theorem half_adjustment (w : UInt64) :
    w - ((1 : UInt64) <<< (52 : UInt64)) = w + UInt64.ofNat (4095 * 2 ^ 52) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat',
    UInt64.toNat_shiftLeft, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
  change (2 ^ 64 - 1 * 2 ^ 52 + w.toNat) % 2 ^ 64 =
    (w.toNat + ((4095 * 2 ^ 52) % 2 ^ 64)) % 2 ^ 64
  rw [Nat.mod_eq_of_lt (by decide : 4095 * 2 ^ 52 < 2 ^ 64)]
  congr 1
  omega

/-- The lowered scale holds `2 ^ (q - 1) H j`. -/
theorem half_scale (ki : UInt64) (k q : Int) (j : Fin 128)
    (hki : (ki.toNat : Int) = (0x4338000000000000 : Int) + k)
    (hk : k = 128 * q + j.val) (hj : (ki % 128).toNat = j.val)
    (hqlo : -1021 ≤ q) (hqhi : q ≤ 1024) :
    Finite (halfScale ki) ∧
      value (halfScale ki) = (2 : ℝ) ^ (q - 1) * value (ExpTableBounds.headBits j.val) := by
  let e := (1022 + q).toNat
  have heq : 1023 + q + ((4095 : Nat) : Int) = (e : Int) + 4096 * ((1 : Nat) : Int) := by
    dsimp [e]
    omega
  have h := ExpScaleBits.scale_bits_adjusted_encoding ki k q j 4095 e 1 hki hk hj heq (by omega)
  obtain ⟨hf, hv⟩ := scale_value j e (by omega) (by omega)
  have hq : (e : Int) - 1023 = q - 1 := by dsimp [e]; omega
  rw [hq] at hv
  rw [halfScale, half_adjustment, h]
  exact ⟨hf, hv⟩

#print axioms scale_value
#print axioms ordinary_scale
#print axioms half_adjustment
#print axioms half_scale

end Verified.Examples.ArmScale
