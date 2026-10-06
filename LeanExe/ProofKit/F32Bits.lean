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

theorem toBits_min (a b : Float32) :
    (min a b).toBits = if Wasm.IEEE32.le a.toBits b.toBits then a.toBits else b.toBits := by
  rw [← decide_le]
  show (if a ≤ b then a else b).toBits = _
  split <;> simp_all

theorem toBits_max (a b : Float32) :
    (max a b).toBits = if Wasm.IEEE32.le a.toBits b.toBits then b.toBits else a.toBits := by
  rw [← decide_le]
  show (if a ≤ b then b else a).toBits = _
  split <;> simp_all

/-- Lean's model replaces every NaN with the canonical NaN, so a float built from
bits keeps them unless they are a NaN pattern. -/
theorem toBits_ofBits (w : UInt32) :
    (Float32.ofBits w).toBits = if Wasm.IEEE32.isNaN w then Wasm.IEEE32.canonicalNaN else w :=
  F32Packing.ofBits_toBits w

end LeanExe.ProofKit.F32Bits
