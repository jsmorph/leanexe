import LeanExe.WGSL.F32Canonical
import LeanExe.IR.Expr
import LeanExe.ProofKit.F32Bits
import LeanExe.ProofKit.F32Nearest

namespace LeanExe.WGSL

open LeanExe.ProofKit

theorem canonical32_nan : canonical32 Wasm.IEEE32.canonicalNaN = Wasm.IEEE32.canonicalNaN := by
  decide +kernel

theorem canonical32_of_toBits (x : Float32) (bits : UInt32) (h : x.toBits = bits) :
    canonical32 bits = bits :=
  (congrArg canonical32 h).symm.trans ((F32Bits.toBits_canonical x).trans h)

theorem canonical_f32_bin (op : LeanExe.IR.F32Op) (a b : UInt32) :
    canonical32 (op.apply a b) = op.apply a b := by
  by_cases ha : Wasm.IEEE32.isNaN a = true
  · have h : op.apply a b = Wasm.IEEE32.canonicalNaN := by
      cases op <;> simp [LeanExe.IR.F32Op.apply, Wasm.IEEE32.sub, Wasm.IEEE32.add,
        Wasm.IEEE32.mul, Wasm.IEEE32.div, ha]
    rw [h, canonical32_nan]
  by_cases hb : Wasm.IEEE32.isNaN b = true
  · have h : op.apply a b = Wasm.IEEE32.canonicalNaN := by
      cases op <;> simp [LeanExe.IR.F32Op.apply, Wasm.IEEE32.sub, Wasm.IEEE32.add,
        Wasm.IEEE32.mul, Wasm.IEEE32.div, hb, F32Sign.isNaN_negate]
    rw [h, canonical32_nan]
  have hA : (Float32.ofBits a).toBits = a := by simp [F32Bits.toBits_ofBits, ha]
  have hB : (Float32.ofBits b).toBits = b := by simp [F32Bits.toBits_ofBits, hb]
  cases op with
  | add =>
      exact canonical32_of_toBits (Float32.ofBits a + Float32.ofBits b) _ (by
        rw [F32Bits.toBits_add, hA, hB]; rfl)
  | sub =>
      exact canonical32_of_toBits (Float32.ofBits a - Float32.ofBits b) _ (by
        rw [F32Bits.toBits_sub, hA, hB]; rfl)
  | mul =>
      exact canonical32_of_toBits (Float32.ofBits a * Float32.ofBits b) _ (by
        rw [F32Bits.toBits_mul, hA, hB]; rfl)
  | div =>
      exact canonical32_of_toBits (Float32.ofBits a / Float32.ofBits b) _ (by
        rw [F32Bits.toBits_div, hA, hB]; rfl)

theorem canonical_f32_sqrt (a : UInt32) : canonical32 (Wasm.IEEE32.sqrt a) = Wasm.IEEE32.sqrt a := by
  by_cases ha : Wasm.IEEE32.isNaN a = true
  · have h : Wasm.IEEE32.sqrt a = Wasm.IEEE32.canonicalNaN := by simp [Wasm.IEEE32.sqrt, ha]
    rw [h, canonical32_nan]
  have hA : (Float32.ofBits a).toBits = a := by simp [F32Bits.toBits_ofBits, ha]
  simpa only [canonical32, F32Bits.toBits_sqrt, hA] using
    F32Bits.toBits_canonical (Float32.ofBits a).sqrt

theorem canonical_f32_nearest (a : UInt32) :
    canonical32 (Wasm.IEEE32.nearest a) = Wasm.IEEE32.nearest a := by
  unfold canonical32
  split
  · rename_i h
    exact (F32Nearest.nearest_nan a h).symm
  · rfl

end LeanExe.WGSL
