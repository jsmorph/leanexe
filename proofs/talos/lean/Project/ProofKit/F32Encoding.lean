import Project.ProofKit.F32Source

namespace Project.ProofKit.F32Encoding
open Float.Model Float.Model.UnpackedFloat

theorem append_toNat (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

def sourceSign (x : UInt32) : Sign :=
  if Wasm.IEEE32.sign x then .negative else .positive

theorem unpackMantissa_eq (x : UInt32) :
    (unpackMantissa (spec := Format.binary32) x.toBitVec).toNat =
      Wasm.IEEE32.fraction x := by
  simp [unpackMantissa, Wasm.IEEE32.fraction]

theorem unpackExponent_eq (x : UInt32) :
    (unpackExponent (spec := Format.binary32) x.toBitVec).toNat =
      Wasm.IEEE32.exponent x := by
  simp [unpackExponent, Wasm.IEEE32.exponent, Nat.shiftRight_eq_div_pow]

theorem unpackSign_eq (x : UInt32) :
    Sign.ofBitVec (unpackSign (spec := Format.binary32) x.toBitVec) = sourceSign x := by
  have hx := x.toNat_lt
  have hv : (unpackSign (spec := Format.binary32) x.toBitVec).toNat = x.toNat / 2 ^ 31 := by
    simp [unpackSign, Nat.shiftRight_eq_div_pow]
    omega
  simp only [Sign.ofBitVec, sourceSign, Wasm.IEEE32.sign, decide_eq_true_eq]
  have he : unpackSign (spec := Format.binary32) x.toBitVec = 0#1 ↔ x.toNat < 2 ^ 31 := by
    rw [← BitVec.toNat_inj, hv]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega
  simp only [he]
  split <;> split <;> first | rfl | omega

def decode (x : UInt32) : UnpackedFloat :=
  let s := sourceSign x
  let e := Wasm.IEEE32.exponent x
  let f := Wasm.IEEE32.fraction x
  if e = 255 then
    if f = 0 then .infinity s else .notANumber
  else if e = 0 then
    if h : f = 0 then .zero s else .finite s f (-149) (Nat.pos_of_ne_zero h)
  else .finite s (2 ^ 23 + f) ((e : Int) - 150) (by omega)

theorem unpack_eq (x : UInt32) :
    unpack Format.binary32 x.toBitVec = decode x := by
  unfold UnpackedFloat.unpack decode
  simp only [unpackSign_eq, unpackExponent_eq, unpackMantissa_eq]
  have he : unpackExponent (spec := Format.binary32) x.toBitVec = -1#8 ↔
      Wasm.IEEE32.exponent x = 255 := by
    rw [← BitVec.toNat_inj, unpackExponent_eq]
    rfl
  have he0 : unpackExponent (spec := Format.binary32) x.toBitVec = 0#8 ↔
      Wasm.IEEE32.exponent x = 0 := by
    rw [← BitVec.toNat_inj, unpackExponent_eq]
    rfl
  have hf0 : unpackMantissa (spec := Format.binary32) x.toBitVec = 0#23 ↔
      Wasm.IEEE32.fraction x = 0 := by
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

def negative (s : Sign) : Bool := match s with
  | .negative => true
  | .positive => false

theorem packComponents_eq (s : Sign) (e f : Nat) (he : e < 256) (hf : f < 2 ^ 23) :
    UInt32.ofBitVec (packComponents Format.binary32 s (BitVec.ofNat 8 e) (BitVec.ofNat 23 f)) =
      Wasm.IEEE32.encodeFinite (negative s) e f := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofBitVec, packComponents, append_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hf]
  cases s <;>
    simp [Sign.toBitVec, negative, Wasm.IEEE32.encodeFinite, Nat.add_mul]
  all_goals omega

#print axioms unpack_eq
#print axioms packComponents_eq

end Project.ProofKit.F32Encoding
