import LeanExe.ProofKit.F64Sub

/-!
Lean's negation and absolute value of binary64 values in terms of Talos's
`IEEE64` functions.  Negation equals subtraction from negative zero, which
canonicalizes NaN as Lean does, and the absolute value of a canonical bit
pattern is `IEEE64.abs`.
-/

namespace LeanExe.ProofKit.F64Sign
open Float.Model Float.Model.UnpackedFloat F64Encoding F64Packing F64Source FloatCommon

theorem fields_negate (x : UInt64) :
    Wasm.IEEE64.exponent (Wasm.IEEE64.negate x) = Wasm.IEEE64.exponent x ∧
      Wasm.IEEE64.fraction (Wasm.IEEE64.negate x) = Wasm.IEEE64.fraction x ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.negate x) = !Wasm.IEEE64.sign x :=
  ⟨exponent_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x),
    fraction_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x),
    sign_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x)⟩

theorem fields_abs (x : UInt64) :
    Wasm.IEEE64.exponent (Wasm.IEEE64.abs x) = Wasm.IEEE64.exponent x ∧
      Wasm.IEEE64.fraction (Wasm.IEEE64.abs x) = Wasm.IEEE64.fraction x ∧
      Wasm.IEEE64.sign (Wasm.IEEE64.abs x) = false :=
  ⟨exponent_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x),
    fraction_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x),
    sign_encodeFinite _ _ _ (exponent_lt x) (fraction_lt x)⟩

theorem decode_abs (x : UInt64) : decode (Wasm.IEEE64.abs x) = (decode x).abs := by
  obtain ⟨he, hf, hs⟩ := fields_abs x
  have hs' : sourceSign (Wasm.IEEE64.abs x) = .positive := by simp [sourceSign, hs]
  by_cases he2047 : Wasm.IEEE64.exponent x = 2047 <;>
    by_cases he0 : Wasm.IEEE64.exponent x = 0 <;>
    by_cases hf0 : Wasm.IEEE64.fraction x = 0 <;>
    simp [decode, he, hf, hs', he2047, he0, hf0, UnpackedFloat.abs]

theorem isNaN_negate (x : UInt64) : Wasm.IEEE64.isNaN (Wasm.IEEE64.negate x) = Wasm.IEEE64.isNaN x := by
  obtain ⟨he, hf, -⟩ := fields_negate x
  simp [Wasm.IEEE64.isNaN, he, hf]

theorem isNaN_abs (x : UInt64) : Wasm.IEEE64.isNaN (Wasm.IEEE64.abs x) = Wasm.IEEE64.isNaN x := by
  obtain ⟨he, hf, -⟩ := fields_abs x
  simp [Wasm.IEEE64.isNaN, he, hf]

theorem neg_bits (x : UInt64) :
    (Float.Model.neg (Float.Model.ofBits x)).toBits =
      if Wasm.IEEE64.isNaN x then Wasm.IEEE64.canonicalNaN else Wasm.IEEE64.negate x := by
  change UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (Float.Model.ofBits x).unpack.neg) = _
  rw [unpack_ofBits, ← F64Sub.decode_negate, pack_decode, isNaN_negate]

theorem abs_bits (x : UInt64) :
    (Float.Model.abs (Float.Model.ofBits x)).toBits =
      if Wasm.IEEE64.isNaN x then Wasm.IEEE64.canonicalNaN else Wasm.IEEE64.abs x := by
  change UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (Float.Model.ofBits x).unpack.abs) = _
  rw [unpack_ofBits, ← decode_abs, pack_decode, isNaN_abs]

/-- Subtracting from negative zero negates exactly and turns every NaN into the
canonical NaN. -/
theorem sub_negZero (x : UInt64) :
    Wasm.IEEE64.sub 0x8000000000000000 x =
      if Wasm.IEEE64.isNaN x then Wasm.IEEE64.canonicalNaN else Wasm.IEEE64.negate x := by
  obtain ⟨he, hf, hs⟩ := fields_negate x
  have hMag : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.negate x) =
      Wasm.IEEE64.scaledMagnitude x := by
    simp [Wasm.IEEE64.scaledMagnitude, he, hf]
  have hz : Wasm.IEEE64.scaledMagnitude (0x8000000000000000 : UInt64) = 0 := by decide
  unfold Wasm.IEEE64.sub
  by_cases hn : Wasm.IEEE64.isNaN x = true
  · simp [Wasm.IEEE64.add, isNaN_negate, hn]
  have hn' := Bool.eq_false_iff.mpr hn
  by_cases hi : Wasm.IEEE64.isInfinite x = true
  · have hi' : Wasm.IEEE64.isInfinite (Wasm.IEEE64.negate x) = true := by
      simpa [Wasm.IEEE64.isInfinite, he, hf] using hi
    simp [Wasm.IEEE64.add, isNaN_negate, hn', hi', show
      Wasm.IEEE64.isNaN (0x8000000000000000 : UInt64) = false by decide, show
      Wasm.IEEE64.isInfinite (0x8000000000000000 : UInt64) = false by decide]
  have hi' := Bool.eq_false_iff.mpr hi
  have hne := F64Add.exponent_ne x hn' hi'
  by_cases hzx : Wasm.IEEE64.scaledMagnitude x = 0
  · obtain ⟨hex, hfx⟩ := F64Add.zero_fields x hzx
    have hv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.negate x) = 0 := by
      simp [Wasm.IEEE64.scaledValue, hMag, hzx]
    have hnn : Wasm.IEEE64.isNaN (Wasm.IEEE64.negate x) = false := by rw [isNaN_negate]; exact hn'
    have hin : Wasm.IEEE64.isInfinite (Wasm.IEEE64.negate x) = false := by
      simpa [Wasm.IEEE64.isInfinite, he, hf] using hi'
    have hneg : Wasm.IEEE64.negate x = Wasm.IEEE64.encodeFinite (!Wasm.IEEE64.sign x) 0 0 := by
      simp [Wasm.IEEE64.negate, hex, hfx]
    simp only [Wasm.IEEE64.add, hnn, hin, hv, hs, hn',
      show Wasm.IEEE64.isNaN (0x8000000000000000 : UInt64) = false by decide,
      show Wasm.IEEE64.isInfinite (0x8000000000000000 : UInt64) = false by decide,
      show Wasm.IEEE64.scaledValue (0x8000000000000000 : UInt64) = 0 by decide,
      show Wasm.IEEE64.sign (0x8000000000000000 : UInt64) = true by decide]
    rw [hneg]
    cases Wasm.IEEE64.sign x <;> decide
  · rw [ite_eq_right (by simpa using hn)]
    exact (F64Add.talos_zero_nonzero _ _ hz (by rw [he]; exact hne) (by rw [hMag]; exact hzx)).1

end LeanExe.ProofKit.F64Sign
