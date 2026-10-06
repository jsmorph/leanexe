import LeanExe.ProofKit.F64Mul
import LeanExe.ProofKit.F64Sub
import LeanExe.ProofKit.F64Div
import LeanExe.ProofKit.F64Sqrt
import LeanExe.ProofKit.F64Compare
import LeanExe.ProofKit.F64Sign

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

theorem toBits_min (a b : Float) :
    (min a b).toBits = if Wasm.IEEE64.le a.toBits b.toBits then a.toBits else b.toBits := by
  rw [← decide_le]
  show (if a ≤ b then a else b).toBits = _
  split <;> simp_all

theorem toBits_max (a b : Float) :
    (max a b).toBits = if Wasm.IEEE64.le a.toBits b.toBits then b.toBits else a.toBits := by
  rw [← decide_le]
  show (if a ≤ b then b else a).toBits = _
  split <;> simp_all

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
