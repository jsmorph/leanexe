module

public import LeanExe.ProofKit.F64Bits
public import LeanExe.ProofKit.F32Bits

@[expose] public section

/-!
From Lean v4.36.0 on, `min` and `max` on `Float` and `Float32` are IEEE 754-2019's `minimum` and
`maximum`: a NaN operand gives NaN, and `-0` is below `+0`.  `min_eq`, `max_eq`, `min32_eq`, and
`max32_eq` write them with `<`, `==`, and the unsigned order of the operands' bit patterns.  When
neither operand is below the other and they are equal, they are the same word or two zeros, and of
two zeros `-0`, whose sign bit is set, has the larger bit pattern.  Otherwise one operand is a NaN,
and the result is the canonical NaN, the only NaN of Lean's model.  The verified compiler's
reflector compiles `min` and `max` on floats through these equations, so every back end, the GPU
kernels' included, compiles them from operations that it compiles with proofs.
-/

namespace LeanExe.ProofKit.FloatMinMax

section Binary64
open Wasm.IEEE64

theorem toBits_inj {a b : Float} (h : a.toBits = b.toBits) : a = b := by
  rw [← F64Bits.ofBits_toBits a, ← F64Bits.ofBits_toBits b, h]

/-- A zero's bit pattern is its sign bit. -/
theorem zero_signMask {x : UInt64} (hx : scaledMagnitude x = 0) : x = signMask (sign x) :=
  calc x = encodeFinite (sign x) (exponent x) (fraction x) := (F64Packing.encode_fields x).symm
    _ = encodeFinite (sign x) 0 0 := by
      rw [(F64Add.zero_fields x hx).1, (F64Add.zero_fields x hx).2]
    _ = signMask (sign x) := (F64Packing.signMask_eq_encode _).symm

theorem lt_true {x y : UInt64} (h : lt x y = true) :
    isNaN x = false ∧ isNaN y = false ∧ scaledValue x < scaledValue y := by
  unfold lt at h
  cases hx : isNaN x <;> cases hy : isNaN y <;> simp_all

theorem eq_true {x y : UInt64} (h : eq x y = true) :
    isNaN x = false ∧ isNaN y = false ∧ scaledValue x = scaledValue y := by
  unfold eq at h
  cases hx : isNaN x <;> cases hy : isNaN y <;> simp_all

/-- Two words that no comparison orders include a NaN pattern. -/
theorem nan_of_unordered {x y : UInt64} (h1 : lt x y = false) (h2 : lt y x = false)
    (h3 : eq x y = false) : (isNaN x || isNaN y) = true := by
  unfold lt at h1 h2
  unfold eq at h3
  cases hx : isNaN x <;> cases hy : isNaN y <;> simp_all
  omega

/-- Two words whose order puts one below the other are not both zeros. -/
theorem not_zeros_of_lt {x y : UInt64} (h : lt x y = true) :
    (scaledMagnitude x == 0 && scaledMagnitude y == 0) = false := by
  obtain ⟨-, -, hv⟩ := lt_true h
  cases hz : (scaledMagnitude x == 0 && scaledMagnitude y == 0)
  · rfl
  · simp only [Bool.and_eq_true, beq_iff_eq] at hz
    rw [F64Add.zero_value x hz.1, F64Add.zero_value y hz.2] at hv
    exact absurd hv (lt_irrefl 0)

/-- Equal words that are not NaN patterns: two zeros, or one word twice. -/
theorem eq_cases {x y : UInt64} (h : eq x y = true) :
    (scaledMagnitude x = 0 ∧ scaledMagnitude y = 0) ∨ (scaledMagnitude x ≠ 0 ∧ x = y) := by
  obtain ⟨-, -, hv⟩ := eq_true h
  by_cases hz : scaledMagnitude x = 0
  · refine Or.inl ⟨hz, ?_⟩
    rw [F64Add.zero_value x hz] at hv
    simp only [scaledValue] at hv
    split at hv <;> omega
  · exact Or.inr ⟨hz, F64Bits.eq_of_scaledValue_eq hv hz⟩

theorem min_bits (x y : UInt64) :
    Wasm.IEEE64.min x y =
      if lt x y then x else if lt y x then y else if eq x y then (if x ≤ y then y else x)
      else canonicalNaN := by
  cases h1 : lt x y
  · cases h2 : lt y x
    · cases h3 : eq x y
      · simp only [Wasm.IEEE64.min, nan_of_unordered h1 h2 h3, ↓reduceIte, Bool.false_eq_true]
      · obtain ⟨hx, hy, -⟩ := eq_true h3
        simp only [Bool.false_eq_true, ↓reduceIte, Wasm.IEEE64.min, hx, hy, Bool.or_self]
        rcases eq_cases h3 with ⟨hzx, hzy⟩ | ⟨hz, rfl⟩
        · simp only [hzx, hzy, beq_self_eq_true, Bool.and_self, ↓reduceIte]
          conv_rhs => rw [zero_signMask hzx, zero_signMask hzy]
          cases sign x <;> cases sign y <;> decide
        · have hz' : (scaledMagnitude x == 0 && scaledMagnitude x == 0) = false := by
            simpa using hz
          simp only [hz', h1, Bool.false_eq_true, ↓reduceIte, ite_self]
    · obtain ⟨hy, hx, -⟩ := lt_true h2
      have hz : (scaledMagnitude x == 0 && scaledMagnitude y == 0) = false := by
        rw [Bool.and_comm]; exact not_zeros_of_lt h2
      simp only [Wasm.IEEE64.min, hx, hy, hz, h1, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨hx, hy, -⟩ := lt_true h1
    simp only [Wasm.IEEE64.min, hx, hy, not_zeros_of_lt h1, h1, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte]

theorem max_bits (x y : UInt64) :
    Wasm.IEEE64.max x y =
      if lt x y then y else if lt y x then x else if eq x y then (if x ≤ y then x else y)
      else canonicalNaN := by
  cases h1 : lt x y
  · cases h2 : lt y x
    · cases h3 : eq x y
      · simp only [Wasm.IEEE64.max, nan_of_unordered h1 h2 h3, ↓reduceIte, Bool.false_eq_true]
      · obtain ⟨hx, hy, -⟩ := eq_true h3
        simp only [Bool.false_eq_true, ↓reduceIte, Wasm.IEEE64.max, hx, hy, Bool.or_self]
        rcases eq_cases h3 with ⟨hzx, hzy⟩ | ⟨hz, rfl⟩
        · simp only [hzx, hzy, beq_self_eq_true, Bool.and_self, ↓reduceIte]
          conv_rhs => rw [zero_signMask hzx, zero_signMask hzy]
          cases sign x <;> cases sign y <;> decide
        · have hz' : (scaledMagnitude x == 0 && scaledMagnitude x == 0) = false := by
            simpa using hz
          simp only [hz', h1, Bool.false_eq_true, ↓reduceIte, ite_self]
    · obtain ⟨hy, hx, -⟩ := lt_true h2
      have hz : (scaledMagnitude x == 0 && scaledMagnitude y == 0) = false := by
        rw [Bool.and_comm]; exact not_zeros_of_lt h2
      simp only [Wasm.IEEE64.max, hx, hy, hz, h1, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨hx, hy, -⟩ := lt_true h1
    simp only [Wasm.IEEE64.max, hx, hy, not_zeros_of_lt h1, h1, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte]

theorem canonicalNaN_toBits :
    (Float.ofBits 0x7FF8000000000000).toBits = canonicalNaN := by
  rw [F64Bits.toBits_ofBits]
  rfl

/-- IEEE 754-2019's `minimum`, which `min` on `Float` computes, from comparisons, `==`, and the
order of the bit patterns of two equal operands. -/
theorem min_eq (a b : Float) :
    (if a < b then a else if b < a then b else if a == b then (if a.toBits ≤ b.toBits then b else a)
      else Float.ofBits 0x7FF8000000000000) = min a b := by
  apply toBits_inj
  rw [F64Bits.toBits_min, min_bits, ← F64Bits.decide_lt, ← F64Bits.decide_lt, ← F64Bits.beq_eq]
  by_cases h1 : a < b
  · simp only [h1, decide_true, ↓reduceIte]
  · by_cases h2 : b < a
    · simp only [h1, h2, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
    · by_cases h3 : (a == b) = true
      · simp only [h1, h2, h3, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases h4 : a.toBits ≤ b.toBits <;> simp [h4]
      · simp only [h1, h2, h3, decide_false, Bool.false_eq_true, ↓reduceIte, canonicalNaN_toBits]

/-- IEEE 754-2019's `maximum`, which `max` on `Float` computes, from comparisons, `==`, and the
order of the bit patterns of two equal operands. -/
theorem max_eq (a b : Float) :
    (if a < b then b else if b < a then a else if a == b then (if a.toBits ≤ b.toBits then a else b)
      else Float.ofBits 0x7FF8000000000000) = max a b := by
  apply toBits_inj
  rw [F64Bits.toBits_max, max_bits, ← F64Bits.decide_lt, ← F64Bits.decide_lt, ← F64Bits.beq_eq]
  by_cases h1 : a < b
  · simp only [h1, decide_true, ↓reduceIte]
  · by_cases h2 : b < a
    · simp only [h1, h2, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
    · by_cases h3 : (a == b) = true
      · simp only [h1, h2, h3, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases h4 : a.toBits ≤ b.toBits <;> simp [h4]
      · simp only [h1, h2, h3, decide_false, Bool.false_eq_true, ↓reduceIte, canonicalNaN_toBits]

end Binary64

section Binary32
open Wasm.IEEE32

theorem toBits_inj32 {a b : Float32} (h : a.toBits = b.toBits) : a = b := by
  rw [← F32Bits.ofBits_toBits a, ← F32Bits.ofBits_toBits b, h]

theorem zero_signMask32 {x : UInt32} (hx : scaledMagnitude x = 0) : x = signMask (sign x) :=
  calc x = encodeFinite (sign x) (exponent x) (fraction x) := (F32Packing.encode_fields x).symm
    _ = encodeFinite (sign x) 0 0 := by
      rw [(F32Add.zero_fields x hx).1, (F32Add.zero_fields x hx).2]
    _ = signMask (sign x) := (F32Packing.signMask_eq_encode _).symm

theorem lt_true32 {x y : UInt32} (h : lt x y = true) :
    isNaN x = false ∧ isNaN y = false ∧ scaledValue x < scaledValue y := by
  unfold lt at h
  cases hx : isNaN x <;> cases hy : isNaN y <;> simp_all

theorem eq_true32 {x y : UInt32} (h : eq x y = true) :
    isNaN x = false ∧ isNaN y = false ∧ scaledValue x = scaledValue y := by
  unfold eq at h
  cases hx : isNaN x <;> cases hy : isNaN y <;> simp_all

theorem nan_of_unordered32 {x y : UInt32} (h1 : lt x y = false) (h2 : lt y x = false)
    (h3 : eq x y = false) : (isNaN x || isNaN y) = true := by
  unfold lt at h1 h2
  unfold eq at h3
  cases hx : isNaN x <;> cases hy : isNaN y <;> simp_all
  omega

theorem not_zeros_of_lt32 {x y : UInt32} (h : lt x y = true) :
    (scaledMagnitude x == 0 && scaledMagnitude y == 0) = false := by
  obtain ⟨-, -, hv⟩ := lt_true32 h
  cases hz : (scaledMagnitude x == 0 && scaledMagnitude y == 0)
  · rfl
  · simp only [Bool.and_eq_true, beq_iff_eq] at hz
    rw [F32Add.zero_value x hz.1, F32Add.zero_value y hz.2] at hv
    exact absurd hv (lt_irrefl 0)

theorem eq_cases32 {x y : UInt32} (h : eq x y = true) :
    (scaledMagnitude x = 0 ∧ scaledMagnitude y = 0) ∨ (scaledMagnitude x ≠ 0 ∧ x = y) := by
  obtain ⟨-, -, hv⟩ := eq_true32 h
  by_cases hz : scaledMagnitude x = 0
  · refine Or.inl ⟨hz, ?_⟩
    rw [F32Add.zero_value x hz] at hv
    simp only [scaledValue] at hv
    split at hv <;> omega
  · exact Or.inr ⟨hz, F32Bits.eq_of_scaledValue_eq hv hz⟩

theorem min_bits32 (x y : UInt32) :
    Wasm.IEEE32.min x y =
      if lt x y then x else if lt y x then y else if eq x y then (if x ≤ y then y else x)
      else canonicalNaN := by
  cases h1 : lt x y
  · cases h2 : lt y x
    · cases h3 : eq x y
      · simp only [Wasm.IEEE32.min, nan_of_unordered32 h1 h2 h3, ↓reduceIte, Bool.false_eq_true]
      · obtain ⟨hx, hy, -⟩ := eq_true32 h3
        simp only [Bool.false_eq_true, ↓reduceIte, Wasm.IEEE32.min, hx, hy, Bool.or_self]
        rcases eq_cases32 h3 with ⟨hzx, hzy⟩ | ⟨hz, rfl⟩
        · simp only [hzx, hzy, beq_self_eq_true, Bool.and_self, ↓reduceIte]
          conv_rhs => rw [zero_signMask32 hzx, zero_signMask32 hzy]
          cases sign x <;> cases sign y <;> decide
        · have hz' : (scaledMagnitude x == 0 && scaledMagnitude x == 0) = false := by
            simpa using hz
          simp only [hz', h1, Bool.false_eq_true, ↓reduceIte, ite_self]
    · obtain ⟨hy, hx, -⟩ := lt_true32 h2
      have hz : (scaledMagnitude x == 0 && scaledMagnitude y == 0) = false := by
        rw [Bool.and_comm]; exact not_zeros_of_lt32 h2
      simp only [Wasm.IEEE32.min, hx, hy, hz, h1, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨hx, hy, -⟩ := lt_true32 h1
    simp only [Wasm.IEEE32.min, hx, hy, not_zeros_of_lt32 h1, h1, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte]

theorem max_bits32 (x y : UInt32) :
    Wasm.IEEE32.max x y =
      if lt x y then y else if lt y x then x else if eq x y then (if x ≤ y then x else y)
      else canonicalNaN := by
  cases h1 : lt x y
  · cases h2 : lt y x
    · cases h3 : eq x y
      · simp only [Wasm.IEEE32.max, nan_of_unordered32 h1 h2 h3, ↓reduceIte, Bool.false_eq_true]
      · obtain ⟨hx, hy, -⟩ := eq_true32 h3
        simp only [Bool.false_eq_true, ↓reduceIte, Wasm.IEEE32.max, hx, hy, Bool.or_self]
        rcases eq_cases32 h3 with ⟨hzx, hzy⟩ | ⟨hz, rfl⟩
        · simp only [hzx, hzy, beq_self_eq_true, Bool.and_self, ↓reduceIte]
          conv_rhs => rw [zero_signMask32 hzx, zero_signMask32 hzy]
          cases sign x <;> cases sign y <;> decide
        · have hz' : (scaledMagnitude x == 0 && scaledMagnitude x == 0) = false := by
            simpa using hz
          simp only [hz', h1, Bool.false_eq_true, ↓reduceIte, ite_self]
    · obtain ⟨hy, hx, -⟩ := lt_true32 h2
      have hz : (scaledMagnitude x == 0 && scaledMagnitude y == 0) = false := by
        rw [Bool.and_comm]; exact not_zeros_of_lt32 h2
      simp only [Wasm.IEEE32.max, hx, hy, hz, h1, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨hx, hy, -⟩ := lt_true32 h1
    simp only [Wasm.IEEE32.max, hx, hy, not_zeros_of_lt32 h1, h1, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte]

theorem canonicalNaN_toBits32 :
    (Float32.ofBits (UInt64.toUInt32 0x7FC00000)).toBits = canonicalNaN := by
  rw [F32Bits.toBits_ofBits]
  rfl

/-- IEEE 754-2019's `minimum`, which `min` on `Float32` computes, from comparisons, `==`, and the
order of the bit patterns of two equal operands, widened to words as the reflector reads them. -/
theorem min32_eq (a b : Float32) :
    (if a < b then a else if b < a then b
      else if a == b then (if a.toBits.toUInt64 ≤ b.toBits.toUInt64 then b else a)
      else Float32.ofBits (UInt64.toUInt32 0x7FC00000)) = min a b := by
  apply toBits_inj32
  rw [F32Bits.toBits_min, min_bits32, ← F32Bits.decide_lt, ← F32Bits.decide_lt, ← F32Bits.beq_eq]
  by_cases h1 : a < b
  · simp only [h1, decide_true, ↓reduceIte]
  · by_cases h2 : b < a
    · simp only [h1, h2, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
    · by_cases h3 : (a == b) = true
      · simp only [h1, h2, h3, decide_false, Bool.false_eq_true, ↓reduceIte, UInt32.toUInt64_le]
        by_cases h4 : a.toBits ≤ b.toBits <;> simp [h4]
      · simp only [h1, h2, h3, decide_false, Bool.false_eq_true, ↓reduceIte,
          canonicalNaN_toBits32]

/-- IEEE 754-2019's `maximum`, which `max` on `Float32` computes, from comparisons, `==`, and the
order of the bit patterns of two equal operands, widened to words. -/
theorem max32_eq (a b : Float32) :
    (if a < b then b else if b < a then a
      else if a == b then (if a.toBits.toUInt64 ≤ b.toBits.toUInt64 then a else b)
      else Float32.ofBits (UInt64.toUInt32 0x7FC00000)) = max a b := by
  apply toBits_inj32
  rw [F32Bits.toBits_max, max_bits32, ← F32Bits.decide_lt, ← F32Bits.decide_lt, ← F32Bits.beq_eq]
  by_cases h1 : a < b
  · simp only [h1, decide_true, ↓reduceIte]
  · by_cases h2 : b < a
    · simp only [h1, h2, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
    · by_cases h3 : (a == b) = true
      · simp only [h1, h2, h3, decide_false, Bool.false_eq_true, ↓reduceIte, UInt32.toUInt64_le]
        by_cases h4 : a.toBits ≤ b.toBits <;> simp [h4]
      · simp only [h1, h2, h3, decide_false, Bool.false_eq_true, ↓reduceIte,
          canonicalNaN_toBits32]

end Binary32

end LeanExe.ProofKit.FloatMinMax
