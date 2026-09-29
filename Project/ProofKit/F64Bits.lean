import Project.ProofKit.F64Mul
import Project.ProofKit.F64Sub
import Project.ProofKit.F64Div
import Project.ProofKit.F64Sqrt

/-!
Lean's `Float` operations on bit patterns agree with Talos's `IEEE64`
functions, the semantics of WebAssembly's `f64` instructions in the
deterministic profile.
-/

namespace Project.ProofKit.F64Bits
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
  rw [← F64Add.add_eq, LeanExe.Float64.addBits, ofBits_toBits, ofBits_toBits]

theorem toBits_sub (a b : Float) : (a - b).toBits = Wasm.IEEE64.sub a.toBits b.toBits := by
  rw [← F64Sub.sub_eq, LeanExe.Float64.subBits, ofBits_toBits, ofBits_toBits]

theorem toBits_mul (a b : Float) : (a * b).toBits = Wasm.IEEE64.mul a.toBits b.toBits := by
  rw [← F64Mul.mul_eq, LeanExe.Float64.mulBits, ofBits_toBits, ofBits_toBits]

theorem toBits_div (a b : Float) : (a / b).toBits = Wasm.IEEE64.div a.toBits b.toBits := by
  rw [← F64Div.div_eq, LeanExe.Float64.divBits, ofBits_toBits, ofBits_toBits]

theorem toBits_sqrt (a : Float) : a.sqrt.toBits = Wasm.IEEE64.sqrt a.toBits := by
  rw [← F64Sqrt.sqrt_eq, LeanExe.Float64.sqrtBits, ofBits_toBits]

end Project.ProofKit.F64Bits
