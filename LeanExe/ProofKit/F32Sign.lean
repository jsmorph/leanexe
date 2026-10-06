import LeanExe.ProofKit.F32Sub

/-!
Lean's negation and absolute value of binary32 values in terms of Talos's
`IEEE32` functions.  Negation equals subtraction from negative zero, which
canonicalizes NaN as Lean does, and the absolute value of a canonical bit
pattern is `IEEE32.abs`.
-/

namespace LeanExe.ProofKit.F32Sign
open Float.Model Float.Model.UnpackedFloat F32Encoding F32Packing FloatCommon
open CodeLib.IEEE32

theorem fields_negate (x : UInt32) :
    Wasm.IEEE32.exponent (Wasm.IEEE32.negate x) = Wasm.IEEE32.exponent x ∧
      Wasm.IEEE32.fraction (Wasm.IEEE32.negate x) = Wasm.IEEE32.fraction x ∧
      Wasm.IEEE32.sign (Wasm.IEEE32.negate x) = !Wasm.IEEE32.sign x :=
  ⟨exponent_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x),
    fraction_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x),
    sign_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x)⟩

theorem fields_abs (x : UInt32) :
    Wasm.IEEE32.exponent (Wasm.IEEE32.abs x) = Wasm.IEEE32.exponent x ∧
      Wasm.IEEE32.fraction (Wasm.IEEE32.abs x) = Wasm.IEEE32.fraction x ∧
      Wasm.IEEE32.sign (Wasm.IEEE32.abs x) = false :=
  ⟨exponent_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x),
    fraction_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x),
    sign_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x)⟩

theorem decode_abs (x : UInt32) : decode (Wasm.IEEE32.abs x) = (decode x).abs := by
  obtain ⟨he, hf, hs⟩ := fields_abs x
  have hs' : sourceSign (Wasm.IEEE32.abs x) = .positive := by simp [sourceSign, hs]
  by_cases he255 : Wasm.IEEE32.exponent x = 255 <;>
    by_cases he0 : Wasm.IEEE32.exponent x = 0 <;>
    by_cases hf0 : Wasm.IEEE32.fraction x = 0 <;>
    simp [decode, he, hf, hs', he255, he0, hf0, UnpackedFloat.abs]

theorem isNaN_negate (x : UInt32) : Wasm.IEEE32.isNaN (Wasm.IEEE32.negate x) = Wasm.IEEE32.isNaN x := by
  obtain ⟨he, hf, -⟩ := fields_negate x
  simp [Wasm.IEEE32.isNaN, he, hf]

theorem isNaN_abs (x : UInt32) : Wasm.IEEE32.isNaN (Wasm.IEEE32.abs x) = Wasm.IEEE32.isNaN x := by
  obtain ⟨he, hf, -⟩ := fields_abs x
  simp [Wasm.IEEE32.isNaN, he, hf]

theorem neg_bits (x : UInt32) :
    (Float32.Model.neg (Float32.Model.ofBits x)).toBits =
      if Wasm.IEEE32.isNaN x then Wasm.IEEE32.canonicalNaN else Wasm.IEEE32.negate x := by
  change UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 (Float32.Model.ofBits x).unpack.neg) = _
  rw [unpack_ofBits, ← F32Sub.decode_negate, pack_decode, isNaN_negate]

theorem abs_bits (x : UInt32) :
    (Float32.Model.abs (Float32.Model.ofBits x)).toBits =
      if Wasm.IEEE32.isNaN x then Wasm.IEEE32.canonicalNaN else Wasm.IEEE32.abs x := by
  change UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 (Float32.Model.ofBits x).unpack.abs) = _
  rw [unpack_ofBits, ← decode_abs, pack_decode, isNaN_abs]

/-- Subtracting from negative zero negates exactly and turns every NaN into the
canonical NaN. -/
theorem sub_negZero (x : UInt32) :
    Wasm.IEEE32.sub 0x80000000 x =
      if Wasm.IEEE32.isNaN x then Wasm.IEEE32.canonicalNaN else Wasm.IEEE32.negate x := by
  obtain ⟨he, hf, hs⟩ := fields_negate x
  have hMag : Wasm.IEEE32.scaledMagnitude (Wasm.IEEE32.negate x) =
      Wasm.IEEE32.scaledMagnitude x := by
    simp [Wasm.IEEE32.scaledMagnitude, he, hf]
  have hz : Wasm.IEEE32.scaledMagnitude (0x80000000 : UInt32) = 0 := by decide
  unfold Wasm.IEEE32.sub
  by_cases hn : Wasm.IEEE32.isNaN x = true
  · simp [Wasm.IEEE32.add, isNaN_negate, hn]
  have hn' := Bool.eq_false_iff.mpr hn
  by_cases hi : Wasm.IEEE32.isInfinite x = true
  · have hi' : Wasm.IEEE32.isInfinite (Wasm.IEEE32.negate x) = true := by
      simpa [Wasm.IEEE32.isInfinite, he, hf] using hi
    simp [Wasm.IEEE32.add, isNaN_negate, hn', hi', show
      Wasm.IEEE32.isNaN (0x80000000 : UInt32) = false by decide, show
      Wasm.IEEE32.isInfinite (0x80000000 : UInt32) = false by decide]
  have hi' := Bool.eq_false_iff.mpr hi
  have hne := F32Add.exponent_ne x hn' hi'
  by_cases hzx : Wasm.IEEE32.scaledMagnitude x = 0
  · obtain ⟨hex, hfx⟩ := F32Add.zero_fields x hzx
    have hv : Wasm.IEEE32.scaledValue (Wasm.IEEE32.negate x) = 0 := by
      simp [Wasm.IEEE32.scaledValue, hMag, hzx]
    have hnn : Wasm.IEEE32.isNaN (Wasm.IEEE32.negate x) = false := by rw [isNaN_negate]; exact hn'
    have hin : Wasm.IEEE32.isInfinite (Wasm.IEEE32.negate x) = false := by
      simpa [Wasm.IEEE32.isInfinite, he, hf] using hi'
    have hneg : Wasm.IEEE32.negate x = Wasm.IEEE32.encodeFinite (!Wasm.IEEE32.sign x) 0 0 := by
      simp [Wasm.IEEE32.negate, hex, hfx]
    simp only [Wasm.IEEE32.add, hnn, hin, hv, hs, hn',
      show Wasm.IEEE32.isNaN (0x80000000 : UInt32) = false by decide,
      show Wasm.IEEE32.isInfinite (0x80000000 : UInt32) = false by decide,
      show Wasm.IEEE32.scaledValue (0x80000000 : UInt32) = 0 by decide,
      show Wasm.IEEE32.sign (0x80000000 : UInt32) = true by decide]
    rw [hneg]
    cases Wasm.IEEE32.sign x <;> decide
  · rw [ite_eq_right (by simpa using hn)]
    exact (F32Add.talos_zero_nonzero _ _ hz (by rw [he]; exact hne) (by rw [hMag]; exact hzx)).1

end LeanExe.ProofKit.F32Sign
