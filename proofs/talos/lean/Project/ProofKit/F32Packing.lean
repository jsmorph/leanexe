import Project.ProofKit.F32Encoding
import CodeLib.IEEE32.SpecialValues

namespace Project.ProofKit.F32Packing
open Float.Model Float.Model.UnpackedFloat F32Encoding
open CodeLib.IEEE32

theorem pack_nan : UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 .notANumber) =
    Wasm.IEEE32.canonicalNaN := by decide

theorem pack_infinity (s : Sign) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 (.infinity s)) =
      Wasm.IEEE32.infinity (negative s) := by
  cases s <;> decide

theorem pack_zero (s : Sign) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 (.zero s)) =
      Wasm.IEEE32.signMask (negative s) := by
  cases s <;> decide

theorem pack_finite (s : Sign) (m : Nat) (e : Int) (hm : 0 < m) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 (.finite s m e hm)) =
      if 255 ≤ (e + 150).toNat then Wasm.IEEE32.infinity (negative s)
      else if m.log2 = 23 then
        Wasm.IEEE32.encodeFinite (negative s) (e + 150).toNat (m % 2 ^ 23)
      else Wasm.IEEE32.encodeFinite (negative s) 0 (m % 2 ^ 23) := by
  have hmvec : BitVec.ofNat 23 m = BitVec.ofNat 23 (m % 2 ^ 23) := by
    apply BitVec.toNat_inj.mp
    simp only [BitVec.toNat_ofNat, Nat.mod_mod]
  have hf : m % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (by decide)
  simp only [UnpackedFloat.pack, Format.exponentBias, Format.mantissaBits,
    Nat.reducePow, Nat.reduceSub, Nat.cast_ofNat, Int.add_assoc, Int.reduceAdd]
  have he : 256 ≤ (e + 150).toNat + 1 ↔ 255 ≤ (e + 150).toNat := by omega
  simp only [he]
  split
  · exact pack_infinity s
  · rename_i he
    have hl : m.log2 + 1 = 24 ↔ m.log2 = 23 := by omega
    simp only [hl]
    split
    · rw [hmvec]
      exact packComponents_eq s _ _ (by omega) hf
    · rw [hmvec]
      exact packComponents_eq s 0 _ (by decide) hf

theorem negative_sourceSign (x : UInt32) : negative (sourceSign x) = Wasm.IEEE32.sign x := by
  unfold sourceSign
  cases Wasm.IEEE32.sign x <;> rfl

theorem encode_fields (x : UInt32) :
    Wasm.IEEE32.encodeFinite (Wasm.IEEE32.sign x)
      (Wasm.IEEE32.exponent x) (Wasm.IEEE32.fraction x) = x := by
  apply UInt32.toNat_inj.mp
  have hx := x.toNat_lt
  simp only [Wasm.IEEE32.encodeFinite, Wasm.IEEE32.sign, Wasm.IEEE32.exponent,
    Wasm.IEEE32.fraction, UInt32.toNat_ofNat', decide_eq_true_eq]
  split <;> omega

theorem signMask_eq_encode (b : Bool) :
    Wasm.IEEE32.signMask b = Wasm.IEEE32.encodeFinite b 0 0 := by
  cases b <;> decide

theorem pack_decode (x : UInt32) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 (decode x)) =
      if Wasm.IEEE32.isNaN x then Wasm.IEEE32.canonicalNaN else x := by
  have he := exponent_lt x
  have hf := fraction_lt x
  norm_num at hf
  have hx := encode_fields x
  unfold decode
  dsimp only
  by_cases he255 : Wasm.IEEE32.exponent x = 255
  · simp only [he255, ↓reduceIte]
    by_cases hf0 : Wasm.IEEE32.fraction x = 0
    · simp only [hf0, ↓reduceIte, pack_infinity, negative_sourceSign]
      simp [Wasm.IEEE32.isNaN, he255, hf0, infinity_eq_encodeFinite]
      simpa [he255, hf0] using hx
    · simp [hf0, pack_nan, Wasm.IEEE32.isNaN, he255]
  · simp only [he255, ↓reduceIte]
    by_cases he0 : Wasm.IEEE32.exponent x = 0
    · simp only [he0, ↓reduceIte]
      by_cases hf0 : Wasm.IEEE32.fraction x = 0
      · simp [hf0, pack_zero, negative_sourceSign, Wasm.IEEE32.isNaN, he0,
          signMask_eq_encode]
        simpa [he0, hf0] using hx
      · have hl : (Wasm.IEEE32.fraction x).log2 < 23 :=
          (Nat.log2_lt (by omega)).mpr hf
        simp [hf0, pack_finite, negative_sourceSign, Wasm.IEEE32.isNaN, he0,
          Nat.ne_of_lt hl, Nat.mod_eq_of_lt hf]
        simpa [he0] using hx
    · have hl : (2 ^ 23 + Wasm.IEEE32.fraction x).log2 = 23 := by
        apply (Nat.log2_eq_iff (by omega)).mpr
        constructor <;> omega
      norm_num at hl
      simp [he0, pack_finite, hl, negative_sourceSign, Wasm.IEEE32.isNaN,
        he255, show ¬255 ≤ Wasm.IEEE32.exponent x by omega,
        Nat.mod_eq_of_lt hf]
      exact hx

theorem ofBits_toBits (x : UInt32) :
    (Float32.Model.ofBits x).toBits =
      if Wasm.IEEE32.isNaN x then Wasm.IEEE32.canonicalNaN else x := by
  change UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
    (UnpackedFloat.unpack Format.binary32 x.toBitVec)) = _
  rw [unpack_eq, pack_decode]

theorem decode_nan (x : UInt32) (hx : Wasm.IEEE32.isNaN x = true) :
    decode x = .notANumber := by
  simp only [Wasm.IEEE32.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hx
  simp [decode, hx.1, hx.2]

theorem unpack_ofBits (x : UInt32) : (Float32.Model.ofBits x).unpack = decode x := by
  unfold Float32.Model.unpack
  rw [ofBits_toBits]
  by_cases hx : Wasm.IEEE32.isNaN x = true
  · simp only [hx, ↓reduceIte, decode_nan x hx]
    rfl
  · simp [hx, unpack_eq]

theorem add_unpacked (a b : UInt32) :
    LeanExe.Float32.addBits a b =
      UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
        (UnpackedFloat.add Format.binary32 (decode a) (decode b))) := by
  change (Float32.Model.pack (UnpackedFloat.add Format.binary32
    (Float32.Model.ofBits a).unpack (Float32.Model.ofBits b).unpack)).toBits = _
  rw [unpack_ofBits, unpack_ofBits]
  rfl

theorem sub_unpacked (a b : UInt32) :
    LeanExe.Float32.subBits a b =
      UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
        (UnpackedFloat.sub Format.binary32 (decode a) (decode b))) := by
  change (Float32.Model.pack (UnpackedFloat.sub Format.binary32
    (Float32.Model.ofBits a).unpack (Float32.Model.ofBits b).unpack)).toBits = _
  rw [unpack_ofBits, unpack_ofBits]
  rfl

theorem mul_unpacked (a b : UInt32) :
    LeanExe.Float32.mulBits a b =
      UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
        (UnpackedFloat.mul Format.binary32 (decode a) (decode b))) := by
  change (Float32.Model.pack (UnpackedFloat.mul Format.binary32
    (Float32.Model.ofBits a).unpack (Float32.Model.ofBits b).unpack)).toBits = _
  rw [unpack_ofBits, unpack_ofBits]
  rfl

theorem div_unpacked (a b : UInt32) :
    LeanExe.Float32.divBits a b =
      UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
        (UnpackedFloat.div Format.binary32 (decode a) (decode b))) := by
  change (Float32.Model.pack (UnpackedFloat.div Format.binary32
    (Float32.Model.ofBits a).unpack (Float32.Model.ofBits b).unpack)).toBits = _
  rw [unpack_ofBits, unpack_ofBits]
  rfl

theorem sqrt_unpacked (x : UInt32) :
    LeanExe.Float32.sqrtBits x =
      UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
        (UnpackedFloat.sqrt Format.binary32 (decode x))) := by
  change (Float32.Model.pack (UnpackedFloat.sqrt Format.binary32
    (Float32.Model.ofBits x).unpack)).toBits = _
  rw [unpack_ofBits]
  rfl

#print axioms pack_decode
#print axioms unpack_ofBits
#print axioms add_unpacked
#print axioms sub_unpacked
#print axioms mul_unpacked
#print axioms div_unpacked
#print axioms sqrt_unpacked

end Project.ProofKit.F32Packing
