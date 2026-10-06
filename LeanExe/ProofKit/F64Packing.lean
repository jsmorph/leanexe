import LeanExe.ProofKit.F64Encoding
import CodeLib.IEEE32.Roundoff

namespace LeanExe.ProofKit.F64Packing
open Float.Model Float.Model.UnpackedFloat F64Encoding F64Source FloatCommon

theorem pack_nan : UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 .notANumber) =
    Wasm.IEEE64.canonicalNaN := by decide

theorem pack_infinity (s : Sign) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (.infinity s)) =
      Wasm.IEEE64.infinity (negative s) := by
  cases s <;> decide

theorem pack_zero (s : Sign) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (.zero s)) =
      Wasm.IEEE64.signMask (negative s) := by
  cases s <;> decide

theorem pack_finite (s : Sign) (m : Nat) (e : Int) (hm : 0 < m) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (.finite s m e hm)) =
      if 2047 ≤ (e + 1075).toNat then Wasm.IEEE64.infinity (negative s)
      else if m.log2 = 52 then
        Wasm.IEEE64.encodeFinite (negative s) (e + 1075).toNat (m % 2 ^ 52)
      else Wasm.IEEE64.encodeFinite (negative s) 0 (m % 2 ^ 52) := by
  have hmvec : BitVec.ofNat 52 m = BitVec.ofNat 52 (m % 2 ^ 52) := by
    apply BitVec.toNat_inj.mp
    simp only [BitVec.toNat_ofNat, Nat.mod_mod]
  have hf : m % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  simp only [UnpackedFloat.pack, Format.exponentBias, Format.mantissaBits,
    Nat.reducePow, Nat.reduceSub, Nat.cast_ofNat, Int.add_assoc, Int.reduceAdd]
  have he : 2048 ≤ (e + 1075).toNat + 1 ↔ 2047 ≤ (e + 1075).toNat := by omega
  simp only [he]
  split
  · exact pack_infinity s
  · rename_i he
    have hl : m.log2 + 1 = 53 ↔ m.log2 = 52 := by omega
    simp only [hl]
    split
    · rw [hmvec]
      exact packComponents_eq s _ _ (by omega) hf
    · rw [hmvec]
      exact packComponents_eq s 0 _ (by decide) hf

theorem negative_sourceSign (x : UInt64) : negative (sourceSign x) = Wasm.IEEE64.sign x := by
  unfold sourceSign
  cases Wasm.IEEE64.sign x <;> rfl

theorem encode_fields (x : UInt64) :
    Wasm.IEEE64.encodeFinite (Wasm.IEEE64.sign x)
      (Wasm.IEEE64.exponent x) (Wasm.IEEE64.fraction x) = x := by
  apply UInt64.toNat_inj.mp
  have hx := x.toNat_lt
  simp only [Wasm.IEEE64.encodeFinite, Wasm.IEEE64.sign, Wasm.IEEE64.exponent,
    Wasm.IEEE64.fraction, UInt64.toNat_ofNat', decide_eq_true_eq]
  split <;> omega

theorem signMask_eq_encode (b : Bool) :
    Wasm.IEEE64.signMask b = Wasm.IEEE64.encodeFinite b 0 0 := by
  cases b <;> decide

theorem pack_decode (x : UInt64) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (decode x)) =
      if Wasm.IEEE64.isNaN x then Wasm.IEEE64.canonicalNaN else x := by
  have he := exponent_lt x
  have hf := fraction_lt x
  norm_num at hf
  have hx := encode_fields x
  unfold decode
  dsimp only
  by_cases he255 : Wasm.IEEE64.exponent x = 2047
  · simp only [he255, ↓reduceIte]
    by_cases hf0 : Wasm.IEEE64.fraction x = 0
    · simp only [hf0, ↓reduceIte, pack_infinity, negative_sourceSign]
      simp [Wasm.IEEE64.isNaN, he255, hf0, infinity_eq_encodeFinite]
      simpa [he255, hf0] using hx
    · simp [hf0, pack_nan, Wasm.IEEE64.isNaN, he255]
  · simp only [he255, ↓reduceIte]
    by_cases he0 : Wasm.IEEE64.exponent x = 0
    · simp only [he0, ↓reduceIte]
      by_cases hf0 : Wasm.IEEE64.fraction x = 0
      · simp [hf0, pack_zero, negative_sourceSign, Wasm.IEEE64.isNaN, he0,
          signMask_eq_encode]
        simpa [he0, hf0] using hx
      · have hl : (Wasm.IEEE64.fraction x).log2 < 52 :=
          (Nat.log2_lt (by omega)).mpr hf
        simp [hf0, pack_finite, negative_sourceSign, Wasm.IEEE64.isNaN, he0,
          Nat.ne_of_lt hl, Nat.mod_eq_of_lt hf]
        simpa [he0] using hx
    · have hl : (2 ^ 52 + Wasm.IEEE64.fraction x).log2 = 52 := by
        apply (Nat.log2_eq_iff (by omega)).mpr
        constructor <;> omega
      norm_num at hl
      simp [he0, pack_finite, hl, negative_sourceSign, Wasm.IEEE64.isNaN,
        he255, show ¬2047 ≤ Wasm.IEEE64.exponent x by omega,
        Nat.mod_eq_of_lt hf]
      exact hx

theorem ofBits_toBits (x : UInt64) :
    (Float.Model.ofBits x).toBits =
      if Wasm.IEEE64.isNaN x then Wasm.IEEE64.canonicalNaN else x := by
  change UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    (UnpackedFloat.unpack Format.binary64 x.toBitVec)) = _
  rw [unpack_eq, pack_decode]

theorem decode_nan (x : UInt64) (hx : Wasm.IEEE64.isNaN x = true) :
    decode x = .notANumber := by
  simp only [Wasm.IEEE64.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hx
  simp [decode, hx.1, hx.2]

theorem unpack_ofBits (x : UInt64) : (Float.Model.ofBits x).unpack = decode x := by
  unfold Float.Model.unpack
  rw [ofBits_toBits]
  by_cases hx : Wasm.IEEE64.isNaN x = true
  · simp only [hx, ↓reduceIte, decode_nan x hx]
    rfl
  · simp [hx, unpack_eq]

theorem add_unpacked (a b : UInt64) :
    LeanExe.Float64.addBits a b =
      UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
        (UnpackedFloat.add Format.binary64 (decode a) (decode b))) := by
  change (Float.Model.pack (UnpackedFloat.add Format.binary64
    (Float.Model.ofBits a).unpack (Float.Model.ofBits b).unpack)).toBits = _
  rw [unpack_ofBits, unpack_ofBits]
  rfl

theorem sub_unpacked (a b : UInt64) :
    LeanExe.Float64.subBits a b =
      UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
        (UnpackedFloat.sub Format.binary64 (decode a) (decode b))) := by
  change (Float.Model.pack (UnpackedFloat.sub Format.binary64
    (Float.Model.ofBits a).unpack (Float.Model.ofBits b).unpack)).toBits = _
  rw [unpack_ofBits, unpack_ofBits]
  rfl

theorem mul_unpacked (a b : UInt64) :
    LeanExe.Float64.mulBits a b =
      UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
        (UnpackedFloat.mul Format.binary64 (decode a) (decode b))) := by
  change (Float.Model.pack (UnpackedFloat.mul Format.binary64
    (Float.Model.ofBits a).unpack (Float.Model.ofBits b).unpack)).toBits = _
  rw [unpack_ofBits, unpack_ofBits]
  rfl

theorem div_unpacked (a b : UInt64) :
    LeanExe.Float64.divBits a b =
      UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
        (UnpackedFloat.div Format.binary64 (decode a) (decode b))) := by
  change (Float.Model.pack (UnpackedFloat.div Format.binary64
    (Float.Model.ofBits a).unpack (Float.Model.ofBits b).unpack)).toBits = _
  rw [unpack_ofBits, unpack_ofBits]
  rfl

theorem sqrt_unpacked (x : UInt64) :
    LeanExe.Float64.sqrtBits x =
      UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
        (UnpackedFloat.sqrt Format.binary64 (decode x))) := by
  change (Float.Model.pack (UnpackedFloat.sqrt Format.binary64
    (Float.Model.ofBits x).unpack)).toBits = _
  rw [unpack_ofBits]
  rfl

#print axioms pack_decode
#print axioms unpack_ofBits
#print axioms add_unpacked
#print axioms sub_unpacked
#print axioms mul_unpacked
#print axioms div_unpacked
#print axioms sqrt_unpacked

end LeanExe.ProofKit.F64Packing
