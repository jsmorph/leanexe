import LeanExe.ProofKit.F32Mul
import LeanExe.ProofKit.F32Sub
import LeanExe.ProofKit.F32Div
import LeanExe.ProofKit.F32Sqrt
import LeanExe.ProofKit.F32Compare
import LeanExe.ProofKit.F32Sign

/-!
Lean's `Float32` operations on bit patterns agree with Talos's `IEEE32`
functions, the semantics of WebAssembly's `f32` instructions in the
deterministic profile.
-/

namespace LeanExe.ProofKit.F32Bits
open Float.Model Float.Model.UnpackedFloat F32Encoding F32Packing

/-- Every NaN in Lean's model is the canonical NaN, so reading a float's bits
back gives the float. -/
theorem ofBits_toBits (x : Float32) : Float32.ofBits x.toBits = x := by
  obtain ⟨⟨bits, valid⟩⟩ := x
  have key : (Float32.Model.ofBits bits).toBits = bits := by
    rw [F32Packing.ofBits_toBits]
    split
    · rename_i hNaN
      simp only [Wasm.IEEE32.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hNaN
      have he : unpackExponent (spec := Format.binary32) bits.toBitVec = -1#8 := by
        rw [← BitVec.toNat_inj, unpackExponent_eq]
        exact hNaN.1
      have hf : unpackMantissa (spec := Format.binary32) bits.toBitVec ≠ 0#23 := by
        rw [ne_eq, ← BitVec.toNat_inj, unpackMantissa_eq]
        exact hNaN.2
      have hbits := valid.eq_packedNaN he hf
      rw [← pack_nan]
      apply UInt32.toBitVec_inj.mp
      rw [hbits]
      rfl
    · rfl
  show Float32.ofModel (Float32.Model.ofBits bits) = Float32.ofModel ⟨bits, valid⟩
  congr 1
  cases hModel : Float32.Model.ofBits bits with
  | mk b v =>
      rw [hModel] at key
      subst key
      rfl

theorem toBits_add (a b : Float32) : (a + b).toBits = Wasm.IEEE32.add a.toBits b.toBits := by
  rw [← F32Add.add_eq, LeanExe.Float32.addBits, ofBits_toBits, ofBits_toBits]

theorem toBits_sub (a b : Float32) : (a - b).toBits = Wasm.IEEE32.sub a.toBits b.toBits := by
  rw [← F32Sub.sub_eq, LeanExe.Float32.subBits, ofBits_toBits, ofBits_toBits]

theorem toBits_mul (a b : Float32) : (a * b).toBits = Wasm.IEEE32.mul a.toBits b.toBits := by
  rw [← F32Mul.mul_eq, LeanExe.Float32.mulBits, ofBits_toBits, ofBits_toBits]

theorem toBits_div (a b : Float32) : (a / b).toBits = Wasm.IEEE32.div a.toBits b.toBits := by
  rw [← F32Div.div_eq, LeanExe.Float32.divBits, ofBits_toBits, ofBits_toBits]

theorem toBits_sqrt (a : Float32) : a.sqrt.toBits = Wasm.IEEE32.sqrt a.toBits := by
  rw [← F32Sqrt.sqrt_eq, LeanExe.Float32.sqrtBits, ofBits_toBits]

theorem toModel_eq (x : Float32) : x.toModel = Float32.Model.ofBits x.toBits := by
  conv_lhs => rw [← ofBits_toBits x]
  rfl

/-- The bit pattern of a Lean float is canonical: its only NaN is the
canonical NaN. -/
theorem toBits_canonical (x : Float32) :
    (if Wasm.IEEE32.isNaN x.toBits then Wasm.IEEE32.canonicalNaN else x.toBits) = x.toBits := by
  rw [← F32Packing.ofBits_toBits, ← toModel_eq]
  rfl

theorem decide_lt (a b : Float32) : decide (a < b) = Wasm.IEEE32.lt a.toBits b.toBits := by
  rw [← F32Compare.lt_bits, ← toModel_eq, ← toModel_eq]
  show decide (a.lt b = true) = _
  simp only [Float32.lt, decide_eq_true_eq]
  show decide (a.toModel.lt b.toModel = true) = _
  cases a.toModel.lt b.toModel <;> rfl

theorem decide_le (a b : Float32) : decide (a ≤ b) = Wasm.IEEE32.le a.toBits b.toBits := by
  rw [← F32Compare.le_bits, ← toModel_eq, ← toModel_eq]
  show decide (a.le b = true) = _
  simp only [Float32.le, decide_eq_true_eq]
  show decide (a.toModel.le b.toModel = true) = _
  cases a.toModel.le b.toModel <;> rfl

theorem lt_iff (a b : Float32) : a < b ↔ Wasm.IEEE32.lt a.toBits b.toBits = true := by
  rw [← decide_lt, decide_eq_true_iff]

theorem le_iff (a b : Float32) : a ≤ b ↔ Wasm.IEEE32.le a.toBits b.toBits = true := by
  rw [← decide_le, decide_eq_true_iff]

theorem beq_eq (a b : Float32) : (a == b) = Wasm.IEEE32.eq a.toBits b.toBits := by
  rw [← F32Compare.beq_bits, ← toModel_eq, ← toModel_eq]
  rfl

theorem toBits_neg (x : Float32) : (-x).toBits = Wasm.IEEE32.sub 0x80000000 x.toBits := by
  rw [F32Sign.sub_negZero]
  show (Float32.Model.neg x.toModel).toBits = _
  rw [toModel_eq, F32Sign.neg_bits]

theorem toBits_abs (x : Float32) : x.abs.toBits = Wasm.IEEE32.abs x.toBits := by
  show (Float32.Model.abs x.toModel).toBits = _
  rw [toModel_eq, F32Sign.abs_bits]
  split
  · rename_i hNaN
    have h := toBits_canonical x
    rw [ite_eq_left hNaN] at h
    rw [← h]
    decide
  · rfl

/-- Two words with equal scaled magnitudes have the same exponent and fraction fields. -/
theorem fields_of_scaledMagnitude_eq {x y : UInt32}
    (h : Wasm.IEEE32.scaledMagnitude x = Wasm.IEEE32.scaledMagnitude y) :
    Wasm.IEEE32.exponent x = Wasm.IEEE32.exponent y ∧
      Wasm.IEEE32.fraction x = Wasm.IEEE32.fraction y := by
  have hfx := CodeLib.IEEE32.fraction_lt x
  have hfy := CodeLib.IEEE32.fraction_lt y
  have below : ∀ {f g d : Nat}, f < 2 ^ 23 → f < (2 ^ 23 + g) * 2 ^ d := fun hf =>
    Nat.lt_of_lt_of_le hf
      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))
  have step : ∀ {f g d e : Nat}, f < 2 ^ 23 → d < e →
      (2 ^ 23 + f) * 2 ^ d < (2 ^ 23 + g) * 2 ^ e := by
    intro f g d e hf hde
    calc (2 ^ 23 + f) * 2 ^ d < 2 ^ 24 * 2 ^ d :=
          Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
      _ = 2 ^ 23 * 2 ^ (d + 1) := by rw [← pow_add, ← pow_add]; congr 1; omega
      _ ≤ 2 ^ 23 * 2 ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hde)
      _ ≤ (2 ^ 23 + g) * 2 ^ e := Nat.mul_le_mul_right _ (by omega)
  simp only [Wasm.IEEE32.scaledMagnitude, beq_iff_eq] at h
  by_cases hx : Wasm.IEEE32.exponent x = 0 <;> by_cases hy : Wasm.IEEE32.exponent y = 0 <;>
    simp only [hx, hy, ↓reduceIte] at h
  · exact ⟨by omega, h⟩
  · exact absurd h (Nat.ne_of_lt (below hfx))
  · exact absurd h.symm (Nat.ne_of_lt (below hfy))
  · rcases Nat.lt_trichotomy (Wasm.IEEE32.exponent x - 1) (Wasm.IEEE32.exponent y - 1) with
      hl | he | hl
    · exact absurd h (Nat.ne_of_lt (step hfx hl))
    · refine ⟨by omega, ?_⟩
      rw [he] at h
      have := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h
      omega
    · exact absurd h.symm (Nat.ne_of_lt (step hfy hl))

/-- Two words with equal scaled values are equal unless the value is zero. -/
theorem eq_of_scaledValue_eq {x y : UInt32}
    (h : Wasm.IEEE32.scaledValue x = Wasm.IEEE32.scaledValue y)
    (hz : Wasm.IEEE32.scaledMagnitude x ≠ 0) : x = y := by
  obtain ⟨hme, hse⟩ : Wasm.IEEE32.scaledMagnitude x = Wasm.IEEE32.scaledMagnitude y ∧
      Wasm.IEEE32.sign x = Wasm.IEEE32.sign y := by
    simp only [Wasm.IEEE32.scaledValue] at h
    cases hsx : Wasm.IEEE32.sign x <;> cases hsy : Wasm.IEEE32.sign y <;>
      simp only [hsx, hsy, Bool.false_eq_true, ↓reduceIte] at h <;>
      first | exact absurd h (by omega) | exact ⟨by omega, rfl⟩
  obtain ⟨he, hf⟩ := fields_of_scaledMagnitude_eq hme
  calc x = Wasm.IEEE32.encodeFinite (Wasm.IEEE32.sign x) (Wasm.IEEE32.exponent x)
        (Wasm.IEEE32.fraction x) := (F32Packing.encode_fields x).symm
    _ = Wasm.IEEE32.encodeFinite (Wasm.IEEE32.sign y) (Wasm.IEEE32.exponent y)
        (Wasm.IEEE32.fraction y) := by rw [hse, he, hf]
    _ = y := F32Packing.encode_fields y

/-- A word that is not a NaN pattern decodes to a value other than NaN. -/
theorem decode_ne_nan {x : UInt32} (hx : Wasm.IEEE32.isNaN x = false) :
    decode x ≠ .notANumber := by
  intro h
  have := (F32Compare.decode_canonical x hx).1
  rw [h] at this
  exact this

theorem decode_zero_iff {x : UInt32} (hx : Wasm.IEEE32.isNaN x = false) :
    (∃ s, decode x = .zero s) ↔ Wasm.IEEE32.scaledMagnitude x = 0 := by
  constructor
  · rintro ⟨s, hs⟩
    have hv := (F32Compare.decode_canonical x hx).2
    rw [hs] at hv
    simp only [F32Compare.value, Wasm.IEEE32.scaledValue] at hv
    split at hv <;> omega
  · intro hz
    exact ⟨_, F32Add.decode_zero x hz⟩

theorem decode_le (x y : UInt32) : (decode x).le (decode y) = Wasm.IEEE32.le x y := by
  have h := F32Compare.le_bits x y
  simpa only [Float32.Model.le, F32Packing.unpack_ofBits] using h

/-- Lean's IEEE 754-2019 `minimum` and `maximum` of two decoded words are Talos's `min` and
`max` of the words. -/
theorem minmax_bits (x y : UInt32) :
    UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 ((decode x).minimum (decode y))) =
        Wasm.IEEE32.min x y ∧
      UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 ((decode x).maximum (decode y))) =
        Wasm.IEEE32.max x y := by
  by_cases hx : Wasm.IEEE32.isNaN x = true
  · rw [F32Packing.decode_nan x hx]
    simp [UnpackedFloat.minimum, UnpackedFloat.maximum, Wasm.IEEE32.min, Wasm.IEEE32.max, hx,
      F32Packing.pack_nan]
  have hx' := Bool.eq_false_iff.mpr hx
  by_cases hy : Wasm.IEEE32.isNaN y = true
  · rw [F32Packing.decode_nan y hy]
    have hu := decode_ne_nan hx'
    have hmin : (decode x).minimum .notANumber = .notANumber := by
      cases decode x <;> simp_all [UnpackedFloat.minimum]
    have hmax : (decode x).maximum .notANumber = .notANumber := by
      cases decode x <;> simp_all [UnpackedFloat.maximum]
    simp [hmin, hmax, Wasm.IEEE32.min, Wasm.IEEE32.max, hy, F32Packing.pack_nan]
  have hy' := Bool.eq_false_iff.mpr hy
  by_cases hz : Wasm.IEEE32.scaledMagnitude x = 0 ∧ Wasm.IEEE32.scaledMagnitude y = 0
  · rw [F32Add.decode_zero x hz.1, F32Add.decode_zero y hz.2]
    simp only [Wasm.IEEE32.min, Wasm.IEEE32.max, hx', hy', hz.1, hz.2, Bool.or_false,
      beq_self_eq_true, Bool.and_self, ↓reduceIte, Bool.false_eq_true]
    rw [← F32Packing.negative_sourceSign x, ← F32Packing.negative_sourceSign y]
    cases sourceSign x <;> cases sourceSign y <;>
      simp [UnpackedFloat.minimum, UnpackedFloat.maximum, F32Packing.pack_zero,
        FloatCommon.negative]
  have hzu : ¬((∃ s, decode x = .zero s) ∧ ∃ s, decode y = .zero s) := by
    rw [decode_zero_iff hx', decode_zero_iff hy']
    exact hz
  obtain ⟨hmin, hmax⟩ :=
    FloatCommon.minimum_maximum_eq _ _ (decode_ne_nan hx') (decode_ne_nan hy') hzu
  rw [hmin, hmax, decode_le]
  have px := F32Packing.pack_decode x
  have py := F32Packing.pack_decode y
  simp only [hx', hy', Bool.false_eq_true, ↓reduceIte] at px py
  have hz' :
      (Wasm.IEEE32.scaledMagnitude x == 0 && Wasm.IEEE32.scaledMagnitude y == 0) = false := by
    simpa using hz
  simp only [Wasm.IEEE32.min, Wasm.IEEE32.max, hx', hy', hz', Bool.or_self, Bool.false_eq_true,
    ↓reduceIte, apply_ite (fun u => UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 u)), px, py]
  by_cases hlt : Wasm.IEEE32.lt x y = true
  · have hle : Wasm.IEEE32.le x y = true := by
      simp only [Wasm.IEEE32.lt, Wasm.IEEE32.le, hx', hy', Bool.or_self, Bool.false_eq_true,
        ↓reduceIte, decide_eq_true_eq] at hlt ⊢
      omega
    simp [hlt, hle]
  · by_cases hle : Wasm.IEEE32.le x y = true
    · have heq : Wasm.IEEE32.scaledValue x = Wasm.IEEE32.scaledValue y := by
        simp only [Wasm.IEEE32.lt, Wasm.IEEE32.le, hx', hy', Bool.or_self, Bool.false_eq_true,
          ↓reduceIte, decide_eq_true_eq] at hlt hle
        omega
      have hnz : Wasm.IEEE32.scaledMagnitude x ≠ 0 := by
        intro h0
        apply hz
        refine ⟨h0, ?_⟩
        have hv := F32Add.zero_value x h0
        rw [heq] at hv
        simp only [Wasm.IEEE32.scaledValue] at hv
        split at hv <;> omega
      have hxy := eq_of_scaledValue_eq heq hnz
      subst hxy
      simp
    · simp [hlt, hle]

/-- `min` is IEEE 754-2019's `minimum`: a NaN operand gives the canonical NaN, and `-0` is below
`+0`, as Talos's `IEEE32.min` and WebAssembly's `f32.min` compute. -/
theorem toBits_min (a b : Float32) : (min a b).toBits = Wasm.IEEE32.min a.toBits b.toBits := by
  show (Float32.Model.minimum a.toModel b.toModel).toBits = _
  rw [toModel_eq, toModel_eq]
  show UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
    ((Float32.Model.ofBits a.toBits).unpack.minimum (Float32.Model.ofBits b.toBits).unpack)) = _
  rw [F32Packing.unpack_ofBits, F32Packing.unpack_ofBits]
  exact (minmax_bits a.toBits b.toBits).1

/-- `max` is IEEE 754-2019's `maximum`: a NaN operand gives the canonical NaN, and `+0` is above
`-0`, as Talos's `IEEE32.max` and WebAssembly's `f32.max` compute. -/
theorem toBits_max (a b : Float32) : (max a b).toBits = Wasm.IEEE32.max a.toBits b.toBits := by
  show (Float32.Model.maximum a.toModel b.toModel).toBits = _
  rw [toModel_eq, toModel_eq]
  show UInt32.ofBitVec (UnpackedFloat.pack Format.binary32
    ((Float32.Model.ofBits a.toBits).unpack.maximum (Float32.Model.ofBits b.toBits).unpack)) = _
  rw [F32Packing.unpack_ofBits, F32Packing.unpack_ofBits]
  exact (minmax_bits a.toBits b.toBits).2

/-- Lean's model replaces every NaN with the canonical NaN, so a float built from
bits keeps them unless they are a NaN pattern. -/
theorem toBits_ofBits (w : UInt32) :
    (Float32.ofBits w).toBits = if Wasm.IEEE32.isNaN w then Wasm.IEEE32.canonicalNaN else w :=
  F32Packing.ofBits_toBits w

end LeanExe.ProofKit.F32Bits
