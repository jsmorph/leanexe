module

public import LeanExe.ProofKit.F64Mul
public import LeanExe.ProofKit.F64Sub
public import LeanExe.ProofKit.F64Div
public import LeanExe.ProofKit.F64Sqrt
public import LeanExe.ProofKit.F64Compare
public import LeanExe.ProofKit.F64Sign

@[expose] public section

/-!
Lean's `Float` operations on bit patterns agree with Talos's `IEEE64`
functions, the semantics of WebAssembly's `f64` instructions in the
deterministic profile.
-/

namespace LeanExe.ProofKit.F64Bits
open Float.Model Float.Model.UnpackedFloat F64Encoding F64Packing

/-- Every NaN in Lean's model is the canonical NaN, so reading a float's bits
back gives the float. -/
theorem ofBits_toBits (x : Float) : Float.ofBits x.toBits = x := by
  obtain ⟨⟨bits, valid⟩⟩ := x
  have key : (Float.Model.ofBits bits).toBits = bits := by
    rw [F64Packing.ofBits_toBits]
    split
    · rename_i hNaN
      simp only [Wasm.IEEE64.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hNaN
      have he : unpackExponent (spec := Format.binary64) bits.toBitVec = -1#11 := by
        rw [← BitVec.toNat_inj, unpackExponent_eq]
        exact hNaN.1
      have hf : unpackMantissa (spec := Format.binary64) bits.toBitVec ≠ 0#52 := by
        rw [ne_eq, ← BitVec.toNat_inj, unpackMantissa_eq]
        exact hNaN.2
      have hbits := valid.eq_packedNaN he hf
      rw [← pack_nan]
      apply UInt64.toBitVec_inj.mp
      rw [hbits]
      rfl
    · rfl
  show Float.ofModel (Float.Model.ofBits bits) = Float.ofModel ⟨bits, valid⟩
  congr 1
  cases hModel : Float.Model.ofBits bits with
  | mk b v =>
      rw [hModel] at key
      subst key
      rfl

theorem toBits_add (a b : Float) : (a + b).toBits = Wasm.IEEE64.add a.toBits b.toBits := by
  rw [← F64Add.add_eq, LeanExe.ProofKit.Float64.addBits, ofBits_toBits, ofBits_toBits]

theorem toBits_sub (a b : Float) : (a - b).toBits = Wasm.IEEE64.sub a.toBits b.toBits := by
  rw [← F64Sub.sub_eq, LeanExe.ProofKit.Float64.subBits, ofBits_toBits, ofBits_toBits]

theorem toBits_mul (a b : Float) : (a * b).toBits = Wasm.IEEE64.mul a.toBits b.toBits := by
  rw [← F64Mul.mul_eq, LeanExe.ProofKit.Float64.mulBits, ofBits_toBits, ofBits_toBits]

theorem toBits_div (a b : Float) : (a / b).toBits = Wasm.IEEE64.div a.toBits b.toBits := by
  rw [← F64Div.div_eq, LeanExe.ProofKit.Float64.divBits, ofBits_toBits, ofBits_toBits]

theorem toBits_sqrt (a : Float) : a.sqrt.toBits = Wasm.IEEE64.sqrt a.toBits := by
  rw [← F64Sqrt.sqrt_eq, LeanExe.ProofKit.Float64.sqrtBits, ofBits_toBits]

theorem toModel_eq (x : Float) : x.toModel = Float.Model.ofBits x.toBits := by
  conv_lhs => rw [← ofBits_toBits x]
  rfl

/-- The bit pattern of a Lean float is canonical: its only NaN is the
canonical NaN. -/
theorem toBits_canonical (x : Float) :
    (if Wasm.IEEE64.isNaN x.toBits then Wasm.IEEE64.canonicalNaN else x.toBits) = x.toBits := by
  rw [← F64Packing.ofBits_toBits, ← toModel_eq]
  rfl

theorem decide_lt (a b : Float) : decide (a < b) = Wasm.IEEE64.lt a.toBits b.toBits := by
  rw [← F64Compare.lt_bits, ← toModel_eq, ← toModel_eq]
  show decide (a.lt b = true) = _
  simp only [Float.lt, decide_eq_true_eq]
  show decide (a.toModel.lt b.toModel = true) = _
  cases a.toModel.lt b.toModel <;> rfl

theorem decide_le (a b : Float) : decide (a ≤ b) = Wasm.IEEE64.le a.toBits b.toBits := by
  rw [← F64Compare.le_bits, ← toModel_eq, ← toModel_eq]
  show decide (a.le b = true) = _
  simp only [Float.le, decide_eq_true_eq]
  show decide (a.toModel.le b.toModel = true) = _
  cases a.toModel.le b.toModel <;> rfl

theorem lt_iff (a b : Float) : a < b ↔ Wasm.IEEE64.lt a.toBits b.toBits = true := by
  rw [← decide_lt, decide_eq_true_iff]

theorem le_iff (a b : Float) : a ≤ b ↔ Wasm.IEEE64.le a.toBits b.toBits = true := by
  rw [← decide_le, decide_eq_true_iff]

theorem beq_eq (a b : Float) : (a == b) = Wasm.IEEE64.eq a.toBits b.toBits := by
  rw [← F64Compare.beq_bits, ← toModel_eq, ← toModel_eq]
  rfl

theorem toBits_neg (x : Float) : (-x).toBits = Wasm.IEEE64.sub 0x8000000000000000 x.toBits := by
  rw [F64Sign.sub_negZero]
  show (Float.Model.neg x.toModel).toBits = _
  rw [toModel_eq, F64Sign.neg_bits]

theorem toBits_abs (x : Float) : x.abs.toBits = Wasm.IEEE64.abs x.toBits := by
  show (Float.Model.abs x.toModel).toBits = _
  rw [toModel_eq, F64Sign.abs_bits]
  split
  · rename_i hNaN
    have h := toBits_canonical x
    rw [ite_eq_left hNaN] at h
    rw [← h]
    decide
  · rfl

/-- Two words with equal scaled magnitudes have the same exponent and fraction fields. -/
theorem fields_of_scaledMagnitude_eq {x y : UInt64}
    (h : Wasm.IEEE64.scaledMagnitude x = Wasm.IEEE64.scaledMagnitude y) :
    Wasm.IEEE64.exponent x = Wasm.IEEE64.exponent y ∧
      Wasm.IEEE64.fraction x = Wasm.IEEE64.fraction y := by
  have hfx := F64Source.fraction_lt x
  have hfy := F64Source.fraction_lt y
  have below : ∀ {f g d : Nat}, f < 2 ^ 52 → f < (2 ^ 52 + g) * 2 ^ d := fun hf =>
    Nat.lt_of_lt_of_le hf
      (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)))
  have step : ∀ {f g d e : Nat}, f < 2 ^ 52 → d < e →
      (2 ^ 52 + f) * 2 ^ d < (2 ^ 52 + g) * 2 ^ e := by
    intro f g d e hf hde
    calc (2 ^ 52 + f) * 2 ^ d < 2 ^ 53 * 2 ^ d :=
          Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
      _ = 2 ^ 52 * 2 ^ (d + 1) := by rw [← pow_add, ← pow_add]; congr 1; omega
      _ ≤ 2 ^ 52 * 2 ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hde)
      _ ≤ (2 ^ 52 + g) * 2 ^ e := Nat.mul_le_mul_right _ (by omega)
  simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq] at h
  by_cases hx : Wasm.IEEE64.exponent x = 0 <;> by_cases hy : Wasm.IEEE64.exponent y = 0 <;>
    simp only [hx, hy, ↓reduceIte] at h
  · exact ⟨by omega, h⟩
  · exact absurd h (Nat.ne_of_lt (below hfx))
  · exact absurd h.symm (Nat.ne_of_lt (below hfy))
  · rcases Nat.lt_trichotomy (Wasm.IEEE64.exponent x - 1) (Wasm.IEEE64.exponent y - 1) with
      hl | he | hl
    · exact absurd h (Nat.ne_of_lt (step hfx hl))
    · refine ⟨by omega, ?_⟩
      rw [he] at h
      have := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h
      omega
    · exact absurd h.symm (Nat.ne_of_lt (step hfy hl))

/-- Two words with equal scaled values are equal unless the value is zero. -/
theorem eq_of_scaledValue_eq {x y : UInt64}
    (h : Wasm.IEEE64.scaledValue x = Wasm.IEEE64.scaledValue y)
    (hz : Wasm.IEEE64.scaledMagnitude x ≠ 0) : x = y := by
  obtain ⟨hme, hse⟩ : Wasm.IEEE64.scaledMagnitude x = Wasm.IEEE64.scaledMagnitude y ∧
      Wasm.IEEE64.sign x = Wasm.IEEE64.sign y := by
    simp only [Wasm.IEEE64.scaledValue] at h
    cases hsx : Wasm.IEEE64.sign x <;> cases hsy : Wasm.IEEE64.sign y <;>
      simp only [hsx, hsy, Bool.false_eq_true, ↓reduceIte] at h <;>
      first | exact absurd h (by omega) | exact ⟨by omega, rfl⟩
  obtain ⟨he, hf⟩ := fields_of_scaledMagnitude_eq hme
  calc x = Wasm.IEEE64.encodeFinite (Wasm.IEEE64.sign x) (Wasm.IEEE64.exponent x)
        (Wasm.IEEE64.fraction x) := (F64Packing.encode_fields x).symm
    _ = Wasm.IEEE64.encodeFinite (Wasm.IEEE64.sign y) (Wasm.IEEE64.exponent y)
        (Wasm.IEEE64.fraction y) := by rw [hse, he, hf]
    _ = y := F64Packing.encode_fields y

/-- A word that is not a NaN pattern decodes to a value other than NaN. -/
theorem decode_ne_nan {x : UInt64} (hx : Wasm.IEEE64.isNaN x = false) :
    decode x ≠ .notANumber := by
  intro h
  have := (F64Compare.decode_canonical x hx).1
  rw [h] at this
  exact this

theorem decode_zero_iff {x : UInt64} (hx : Wasm.IEEE64.isNaN x = false) :
    (∃ s, decode x = .zero s) ↔ Wasm.IEEE64.scaledMagnitude x = 0 := by
  constructor
  · rintro ⟨s, hs⟩
    have hv := (F64Compare.decode_canonical x hx).2
    rw [hs] at hv
    simp only [F64Compare.value, Wasm.IEEE64.scaledValue] at hv
    split at hv <;> omega
  · intro hz
    exact ⟨_, F64Add.decode_zero x hz⟩

theorem decode_le (x y : UInt64) : (decode x).le (decode y) = Wasm.IEEE64.le x y := by
  have h := F64Compare.le_bits x y
  simpa only [Float.Model.le, F64Packing.unpack_ofBits] using h

/-- Lean's IEEE 754-2019 `minimum` and `maximum` of two decoded words are Talos's `min` and
`max` of the words. -/
theorem minmax_bits (x y : UInt64) :
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 ((decode x).minimum (decode y))) =
        Wasm.IEEE64.min x y ∧
      UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 ((decode x).maximum (decode y))) =
        Wasm.IEEE64.max x y := by
  by_cases hx : Wasm.IEEE64.isNaN x = true
  · rw [F64Packing.decode_nan x hx]
    simp [UnpackedFloat.minimum, UnpackedFloat.maximum, Wasm.IEEE64.min, Wasm.IEEE64.max, hx,
      F64Packing.pack_nan]
  have hx' := Bool.eq_false_iff.mpr hx
  by_cases hy : Wasm.IEEE64.isNaN y = true
  · rw [F64Packing.decode_nan y hy]
    have hu := decode_ne_nan hx'
    have hmin : (decode x).minimum .notANumber = .notANumber := by
      cases decode x <;> simp_all [UnpackedFloat.minimum]
    have hmax : (decode x).maximum .notANumber = .notANumber := by
      cases decode x <;> simp_all [UnpackedFloat.maximum]
    simp [hmin, hmax, Wasm.IEEE64.min, Wasm.IEEE64.max, hy, F64Packing.pack_nan]
  have hy' := Bool.eq_false_iff.mpr hy
  by_cases hz : Wasm.IEEE64.scaledMagnitude x = 0 ∧ Wasm.IEEE64.scaledMagnitude y = 0
  · rw [F64Add.decode_zero x hz.1, F64Add.decode_zero y hz.2]
    simp only [Wasm.IEEE64.min, Wasm.IEEE64.max, hx', hy', hz.1, hz.2, Bool.or_false,
      beq_self_eq_true, Bool.and_self, ↓reduceIte, Bool.false_eq_true]
    rw [← F64Packing.negative_sourceSign x, ← F64Packing.negative_sourceSign y]
    cases sourceSign x <;> cases sourceSign y <;>
      simp [UnpackedFloat.minimum, UnpackedFloat.maximum, F64Packing.pack_zero,
        FloatCommon.negative]
  have hzu : ¬((∃ s, decode x = .zero s) ∧ ∃ s, decode y = .zero s) := by
    rw [decode_zero_iff hx', decode_zero_iff hy']
    exact hz
  obtain ⟨hmin, hmax⟩ :=
    FloatCommon.minimum_maximum_eq _ _ (decode_ne_nan hx') (decode_ne_nan hy') hzu
  rw [hmin, hmax, decode_le]
  have px := F64Packing.pack_decode x
  have py := F64Packing.pack_decode y
  simp only [hx', hy', Bool.false_eq_true, ↓reduceIte] at px py
  have hz' :
      (Wasm.IEEE64.scaledMagnitude x == 0 && Wasm.IEEE64.scaledMagnitude y == 0) = false := by
    simpa using hz
  simp only [Wasm.IEEE64.min, Wasm.IEEE64.max, hx', hy', hz', Bool.or_self, Bool.false_eq_true,
    ↓reduceIte, apply_ite (fun u => UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 u)), px, py]
  by_cases hlt : Wasm.IEEE64.lt x y = true
  · have hle : Wasm.IEEE64.le x y = true := by
      simp only [Wasm.IEEE64.lt, Wasm.IEEE64.le, hx', hy', Bool.or_self, Bool.false_eq_true,
        ↓reduceIte, decide_eq_true_eq] at hlt ⊢
      omega
    simp [hlt, hle]
  · by_cases hle : Wasm.IEEE64.le x y = true
    · have heq : Wasm.IEEE64.scaledValue x = Wasm.IEEE64.scaledValue y := by
        simp only [Wasm.IEEE64.lt, Wasm.IEEE64.le, hx', hy', Bool.or_self, Bool.false_eq_true,
          ↓reduceIte, decide_eq_true_eq] at hlt hle
        omega
      have hnz : Wasm.IEEE64.scaledMagnitude x ≠ 0 := by
        intro h0
        apply hz
        refine ⟨h0, ?_⟩
        have hv := F64Add.zero_value x h0
        rw [heq] at hv
        simp only [Wasm.IEEE64.scaledValue] at hv
        split at hv <;> omega
      have hxy := eq_of_scaledValue_eq heq hnz
      subst hxy
      simp
    · simp [hlt, hle]

/-- `min` is IEEE 754-2019's `minimum`: a NaN operand gives the canonical NaN, and `-0` is below
`+0`, as Talos's `IEEE64.min` and WebAssembly's `f64.min` compute. -/
theorem toBits_min (a b : Float) : (min a b).toBits = Wasm.IEEE64.min a.toBits b.toBits := by
  show (Float.Model.minimum a.toModel b.toModel).toBits = _
  rw [toModel_eq, toModel_eq]
  show UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    ((Float.Model.ofBits a.toBits).unpack.minimum (Float.Model.ofBits b.toBits).unpack)) = _
  rw [F64Packing.unpack_ofBits, F64Packing.unpack_ofBits]
  exact (minmax_bits a.toBits b.toBits).1

/-- `max` is IEEE 754-2019's `maximum`: a NaN operand gives the canonical NaN, and `+0` is above
`-0`, as Talos's `IEEE64.max` and WebAssembly's `f64.max` compute. -/
theorem toBits_max (a b : Float) : (max a b).toBits = Wasm.IEEE64.max a.toBits b.toBits := by
  show (Float.Model.maximum a.toModel b.toModel).toBits = _
  rw [toModel_eq, toModel_eq]
  show UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    ((Float.Model.ofBits a.toBits).unpack.maximum (Float.Model.ofBits b.toBits).unpack)) = _
  rw [F64Packing.unpack_ofBits, F64Packing.unpack_ofBits]
  exact (minmax_bits a.toBits b.toBits).2

/-- Lean's model replaces every NaN with the canonical NaN, so a float built from
bits keeps them unless they are a NaN pattern. -/
theorem toBits_ofBits (w : UInt64) :
    (Float.ofBits w).toBits = if Wasm.IEEE64.isNaN w then Wasm.IEEE64.canonicalNaN else w :=
  F64Packing.ofBits_toBits w

/-- A word shifted left by 52 has a zero fraction field, so it is not a NaN pattern. -/
theorem shiftLeft_52_not_nan (v : UInt64) : Wasm.IEEE64.isNaN (v <<< 52) = false := by
  have hFraction : Wasm.IEEE64.fraction (v <<< 52) = 0 := by
    unfold Wasm.IEEE64.fraction
    rw [UInt64.toNat_shiftLeft]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 52 ∣ 2 ^ 64), Nat.mul_mod_left]
  simp [Wasm.IEEE64.isNaN, hFraction]

end LeanExe.ProofKit.F64Bits
