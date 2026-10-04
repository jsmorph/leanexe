import Project.ProofKit.F32Mul
import Project.ProofKit.F32Sub
import Project.ProofKit.F32Div
import Project.ProofKit.F32Sqrt

/-!
Lean's `Float32` operations on bit patterns agree with Talos's `IEEE32`
functions, the semantics of WebAssembly's `f32` instructions in the
deterministic profile.
-/

namespace Project.ProofKit.F32Bits
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

end Project.ProofKit.F32Bits
