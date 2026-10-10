import Verified.Examples.ExpScaleEncoding
import Verified.Examples.ExpShiftedBits

namespace Verified.Examples.ExpScaleBits
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

def index (ki : UInt64) : UInt64 := 2 * (ki % 128)

def scaleBits (ki : UInt64) : UInt64 :=
  Exp.expTable[(index ki + 1).toNat]! + (ki <<< (45 : UInt64))

private theorem positive_encoding_toNat (e f : Nat) (he : e < 2048) (hf : f < 2 ^ 52) :
    (Wasm.IEEE64.encodeFinite false e f).toNat = e * 2 ^ 52 + f := by
  simp only [Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, zero_add,
    UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem index_values (ki : UInt64) (j : Fin 128) (hj : (ki % 128).toNat = j.val) :
    (index ki).toNat = 2 * j.val ∧ (index ki + 1).toNat = 2 * j.val + 1 := by
  have hi : (index ki).toNat = 2 * j.val := by
    simp only [index, UInt64.toNat_mul, UInt64.reduceToNat, hj]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨hi, ?_⟩
  simp only [UInt64.toNat_add, UInt64.reduceToNat, hi]
  exact Nat.mod_eq_of_lt (by omega)

theorem scale_bits_adjusted_encoding (ki : UInt64) (k q : Int) (j : Fin 128)
    (a e t : Nat)
    (hki : (ki.toNat : Int) = (0x4338000000000000 : Int) + k)
    (hk : k = 128 * q + j.val) (hj : (ki % 128).toNat = j.val)
    (heq : 1023 + q + (a : Int) = (e : Int) + 4096 * (t : Int))
    (he : e < 2048) :
    scaleBits ki + UInt64.ofNat (a * 2 ^ 52) =
      Wasm.IEEE64.encodeFinite false e
        (Wasm.IEEE64.fraction (ExpTableBounds.headBits j.val)) := by
  let B := Exp.expTable[2 * j.val + 1]!.toNat
  let f := Wasm.IEEE64.fraction (ExpTableBounds.headBits j.val)
  let M : Nat := 0x4338000000000000
  let L := M / 2 ^ 19
  have hf : f < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  obtain ⟨hhs, hhe, hB⟩ := ExpScaleFacts.checked_head_fields j
  have hc : Wasm.IEEE64.encodeFinite false 1023 f = ExpTableBounds.headBits j.val := by
    simpa only [hhs, hhe] using F64Packing.encode_fields (ExpTableBounds.headBits j.val)
  have hH : (ExpTableBounds.headBits j.val).toNat = 1023 * 2 ^ 52 + f := by
    rw [← hc]
    exact positive_encoding_toNat 1023 f (by decide) hf
  have hB' : (B : Int) + (j.val : Int) * (2 : Int) ^ 45 =
      1023 * (2 : Int) ^ 52 + (f : Int) := by
    have hn : B + j.val * 2 ^ 45 = 1023 * 2 ^ 52 + f := hB.trans hH
    exact_mod_cast hn
  have hm : M * 2 ^ 45 = L * 2 ^ 64 := by decide +kernel
  have hmI : (M : Int) * (2 : Int) ^ 45 = (L : Int) * (2 : Int) ^ 64 := by
    exact_mod_cast hm
  have hsumI : (B : Int) + (ki.toNat : Int) * (2 : Int) ^ 45 + (a : Int) * 2 ^ 52 =
      (e : Int) * (2 : Int) ^ 52 + (f : Int) +
        ((L : Int) + (t : Int)) * (2 : Int) ^ 64 := by
    rw [hki, hk]
    change (B : Int) + ((M : Int) + (128 * q + (j.val : Int))) * (2 : Int) ^ 45 +
      (a : Int) * 2 ^ 52 = _
    nlinarith only [hB', hmI, heq]
  have hsum : B + ki.toNat * 2 ^ 45 + a * 2 ^ 52 =
      e * 2 ^ 52 + f + (L + t) * 2 ^ 64 := by
    exact_mod_cast hsumI
  have hsmall : e * 2 ^ 52 + f < 2 ^ 64 := by omega
  apply UInt64.toNat_inj.mp
  rw [positive_encoding_toNat e f he hf]
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', scaleBits,
    (index_values ki j hj).2, UInt64.toNat_shiftLeft, UInt64.reduceToNat,
    Nat.reduceMod, Nat.shiftLeft_eq]
  change ((B + ((ki.toNat * 2 ^ 45) % 2 ^ 64)) % 2 ^ 64 +
    ((a * 2 ^ 52) % 2 ^ 64)) % 2 ^ 64 = e * 2 ^ 52 + f
  calc
    _ = (B + ki.toNat * 2 ^ 45 + a * 2 ^ 52) % 2 ^ 64 := by
      rw [Nat.add_mod_mod B (ki.toNat * 2 ^ 45) (2 ^ 64),
        Nat.add_mod_mod, Nat.mod_add_mod]
    _ = (e * 2 ^ 52 + f + (L + t) * 2 ^ 64) % 2 ^ 64 := by rw [hsum]
    _ = (e * 2 ^ 52 + f) % 2 ^ 64 :=
      Nat.add_mul_mod_self_right (e * 2 ^ 52 + f) (L + t) (2 ^ 64)
    _ = e * 2 ^ 52 + f := Nat.mod_eq_of_lt hsmall

theorem scale_bits_encoding (ki : UInt64) (k q : Int) (j : Fin 128)
    (hki : (ki.toNat : Int) = (0x4338000000000000 : Int) + k)
    (hk : k = 128 * q + j.val) (hj : (ki % 128).toNat = j.val)
    (hqlo : -1000 ≤ q) (hqhi : q ≤ 999) :
    scaleBits ki = ExpScaleEncoding.encodedScale j q := by
  let e := (1023 + q).toNat
  have he : e < 2048 := by dsimp [e]; omega
  have heq : 1023 + q + (0 : Nat) = (e : Int) + 4096 * (0 : Nat) := by
    dsimp [e]
    omega
  have h := scale_bits_adjusted_encoding ki k q j 0 e 0 hki hk hj heq he
  change scaleBits ki + 0 = ExpScaleEncoding.encodedScale j q at h
  simpa only [UInt64.add_zero] using h

#print axioms index_values
#print axioms scale_bits_adjusted_encoding
#print axioms scale_bits_encoding

end Verified.Examples.ExpScaleBits
