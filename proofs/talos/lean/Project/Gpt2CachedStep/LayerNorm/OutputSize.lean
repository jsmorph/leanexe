import Project.Gpt2CachedStep.LayerNorm.Size

namespace Project.Gpt2CachedStep.LayerNorm
open Wasm Project.ProofKit PackedFloatFrame

def outputSizeFrame (frame : Locals) (rows : Nat) : Locals :=
  { frame with
    locals := (((((frame.locals.set 63 (.i64 (UInt64.ofNat rows))).set 64 (.i64 768)).set
      61 (.i64 (UInt64.ofNat (rows * 768)))).set 62 (.i64 4)).set
      35 (.i64 (UInt64.ofNat (4 * (rows * 768))))).set 61 (.i64 (UInt64.ofNat (4 * (rows * 768))))
    values := [] }

set_option maxRecDepth 32768 in
theorem outputSize_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (rows : Nat) (hParams : frame.params.length = 9) (hLocals : frame.locals.length = 74)
    (hValues : frame.values = []) (hRows : frame.params[8]? = some (.i64 (UInt64.ofNat rows)))
    (hCount : 4 * (rows * 768) ≤ 2^32)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (outputSizeFrame frame rows) env) :
    wp «module» ((func20.drop 98).take 18 ++ rest) Q store frame env := by
  have hSplit : (func20.drop 98).take 18 =
      [.localGet 8, .localSet 72, .constI64 768, .localSet 73] ++
      CheckedNatMul.program 72 73 ++ [.localSet 70, .constI64 4, .localSet 71] ++
      CheckedNatMul.program 70 71 ++ [.localSet 44, .localGet 44, .localSet 70] := rfl
  have hProduct : UInt64.ofNat rows * 768 = UInt64.ofNat (rows * 768) := by simp
  have hBytes : UInt64.ofNat (rows * 768) * 4 = UInt64.ofNat (4 * (rows * 768)) := by
    rw [Nat.mul_comm 4 (rows * 768)]
    simp only [UInt64.ofNat_mul]
    rfl
  have hElements : rows * 768 < UInt64.size := by
    change rows * 768 < 18446744073709551616
    omega
  rw [hSplit]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues, hRows]
  apply CheckedNatMul.program_spec 72 73 «module» env store _ (UInt64.ofNat rows) 768 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · simp only [UInt64.toNat_ofNat', UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    change _ < 18446744073709551616
    omega
  wp_packed_frame [hParams, hLocals, hProduct]
  apply CheckedNatMul.program_spec 70 71 «module» env store _ (UInt64.ofNat (rows * 768)) 4 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · rw [UInt64.toNat_ofNat_of_lt' hElements]
    change (rows * 768) * 4 < 18446744073709551616
    omega
  wp_packed_frame [hParams, hLocals, hBytes]
  exact hNext

@[simp] theorem layerNorm_size (weights input : ByteArray) (scaleOffset biasOffset rows : Nat) :
    (LeanExe.Models.Gpt2.layerNorm weights input scaleOffset biasOffset rows).size = 4 * (rows * 768) := by
  rw [layerNorm_eq, PackedSource.generate_size]

#print axioms outputSize_spec

end Project.Gpt2CachedStep.LayerNorm
