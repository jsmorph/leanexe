import Project.Gpt2CachedStep.CachedAttention.FrozenFixedSize

namespace Project.Gpt2CachedStep.Frozen.CachedAttention
open Wasm Project.ProofKit PackedFloatFrame

def matrixSizeCode (byteLocal : Nat) : Wasm.Program :=
  [.constI64 12, .localSet 111, .localGet 8, .localSet 112] ++
    CheckedNatMul.program 111 112 ++ [.localSet 109, .constI64 4, .localSet 110] ++
    CheckedNatMul.program 109 110 ++ [.localSet byteLocal, .localGet byteLocal, .localSet 109]

def matrixSizeFrame (frame : Locals) (size byteLocal : Nat) : Locals :=
  { frame with
    locals := (((((frame.locals.set 103 (.i64 12)).set 104 (.i64 (UInt64.ofNat size))).set
      101 (.i64 (UInt64.ofNat (12 * size)))).set 102 (.i64 4)).set
      (byteLocal - 8) (.i64 (UInt64.ofNat (4 * (12 * size))))).set 101 (.i64 (UInt64.ofNat (4 * (12 * size))))
    values := [] }

theorem matrixSize_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (size byteLocal : Nat) (hParams : frame.params.length = 8) (hLocals : frame.locals.length = 114)
    (hValues : frame.values = []) (hSize : frame.locals[0]? = some (.i64 (UInt64.ofNat size)))
    (hLow : 8 ≤ byteLocal) (hHigh : byteLocal < 109) (hCount : 4 * (12 * size) ≤ 2^32)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (matrixSizeFrame frame size byteLocal) env) :
    wp «module» (matrixSizeCode byteLocal ++ rest) Q store frame env := by
  have hProduct : 12 * UInt64.ofNat size = UInt64.ofNat (12 * size) := by simp
  have hBytes : UInt64.ofNat (12 * size) * 4 = UInt64.ofNat (4 * (12 * size)) := by
    rw [Nat.mul_comm 4 (12 * size)]
    simp
  have hElements : 12 * size < UInt64.size := by
    change 12 * size < 18446744073709551616
    omega
  have hNotParam : ¬ byteLocal < 8 := by omega
  have hValid : byteLocal < 8 + 114 := by omega
  have hSlot : byteLocal - 8 < 114 := by omega
  simp only [matrixSizeCode, List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues, hSize]
  apply CheckedNatMul.program_spec 111 112 «module» env store _ 12 (UInt64.ofNat size) []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · simp only [UInt64.toNat_ofNat', UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    change _ < 18446744073709551616
    omega
  wp_packed_frame [hParams, hLocals, hProduct]
  apply CheckedNatMul.program_spec 109 110 «module» env store _ (UInt64.ofNat (12 * size)) 4 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · rw [UInt64.toNat_ofNat_of_lt' hElements]
    change (12 * size) * 4 < 18446744073709551616
    omega
  wp_packed_frame [hParams, hLocals, hBytes, hNotParam, hValid, hSlot]
  exact hNext

set_option maxRecDepth 32768 in
theorem emitted_matrix_sizes :
    (func29.drop 117).take 18 = matrixSizeCode 36 ∧
    (func29.drop 222).take 18 = matrixSizeCode 62 := by
  constructor <;> rfl

#print axioms matrixSize_spec

end Project.Gpt2CachedStep.Frozen.CachedAttention
