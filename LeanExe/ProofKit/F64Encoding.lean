import LeanExe.ProofKit.F64Source
import LeanExe.ProofKit.FloatCommon

namespace LeanExe.ProofKit.F64Encoding
open Float.Model Float.Model.UnpackedFloat FloatCommon

def sourceSign (x : UInt64) : Sign :=
  if Wasm.IEEE64.sign x then .negative else .positive

theorem unpackMantissa_eq (x : UInt64) :
    (unpackMantissa (spec := Format.binary64) x.toBitVec).toNat =
      Wasm.IEEE64.fraction x := by
  simp [unpackMantissa, Wasm.IEEE64.fraction]

theorem unpackExponent_eq (x : UInt64) :
    (unpackExponent (spec := Format.binary64) x.toBitVec).toNat =
      Wasm.IEEE64.exponent x := by
  simp [unpackExponent, Wasm.IEEE64.exponent, Nat.shiftRight_eq_div_pow]

theorem unpackSign_eq (x : UInt64) :
    Sign.ofBitVec (unpackSign (spec := Format.binary64) x.toBitVec) = sourceSign x := by
  have hx := x.toNat_lt
  have hv : (unpackSign (spec := Format.binary64) x.toBitVec).toNat = x.toNat / 2 ^ 63 := by
    simp [unpackSign, Nat.shiftRight_eq_div_pow]
    omega
  simp only [Sign.ofBitVec, sourceSign, Wasm.IEEE64.sign, decide_eq_true_eq]
  have he : unpackSign (spec := Format.binary64) x.toBitVec = 0#1 ↔ x.toNat < 2 ^ 63 := by
    rw [← BitVec.toNat_inj, hv]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  simp only [he]
  split <;> split <;> first | rfl | omega

def decode (x : UInt64) : UnpackedFloat :=
  let s := sourceSign x
  let e := Wasm.IEEE64.exponent x
  let f := Wasm.IEEE64.fraction x
  if e = 2047 then
    if f = 0 then .infinity s else .notANumber
  else if e = 0 then
    if h : f = 0 then .zero s else .finite s f (-1074) (Nat.pos_of_ne_zero h)
  else .finite s (2 ^ 52 + f) ((e : Int) - 1075) (by omega)

theorem unpack_eq (x : UInt64) :
    unpack Format.binary64 x.toBitVec = decode x := by
  unfold UnpackedFloat.unpack decode
  simp only [unpackSign_eq, unpackExponent_eq, unpackMantissa_eq]
  have he : unpackExponent (spec := Format.binary64) x.toBitVec = -1#11 ↔
      Wasm.IEEE64.exponent x = 2047 := by
    rw [← BitVec.toNat_inj, unpackExponent_eq]
    rfl
  have he0 : unpackExponent (spec := Format.binary64) x.toBitVec = 0#11 ↔
      Wasm.IEEE64.exponent x = 0 := by
    rw [← BitVec.toNat_inj, unpackExponent_eq]
    rfl
  have hf0 : unpackMantissa (spec := Format.binary64) x.toBitVec = 0#52 ↔
      Wasm.IEEE64.fraction x = 0 := by
    rw [← BitVec.toNat_inj, unpackMantissa_eq]
    rfl
  simp only [he, he0, hf0]
  split <;> split
  all_goals try rfl
  · split
    · rfl
    · simp_all [Format.exponentBias]
  · simp only [Format.exponentBias, Nat.reduceSub, Nat.reducePow, Nat.cast_ofNat,
      Int.reduceAdd, Nat.reducePow]
    congr 1
    rw [append_toNat]
    simp [unpackMantissa_eq]

theorem packComponents_eq (s : Sign) (e f : Nat) (he : e < 2048) (hf : f < 2 ^ 52) :
    UInt64.ofBitVec (packComponents Format.binary64 s (BitVec.ofNat 11 e) (BitVec.ofNat 52 f)) =
      Wasm.IEEE64.encodeFinite (negative s) e f := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofBitVec, packComponents, append_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hf]
  cases s <;>
    simp [Sign.toBitVec, negative, Wasm.IEEE64.encodeFinite, Nat.add_mul]
  all_goals omega

#print axioms unpack_eq
#print axioms packComponents_eq

end LeanExe.ProofKit.F64Encoding
