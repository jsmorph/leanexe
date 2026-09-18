import Project.Gpt2CachedStep.LayerNorm.OutputLoop
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.PackedCapacity
import Project.ProofKit.PackedAllocationFrame

namespace Project.Gpt2CachedStep.LayerNorm
open Wasm Project.ProofKit PackedFloatFrame

def sizeCode (byteLocal : Nat) : Wasm.Program :=
  [.localGet 8, .localSet 70, .constI64 4, .localSet 71] ++ CheckedNatMul.program 70 71 ++
    [.localSet byteLocal, .localGet byteLocal, .localSet 70]

def sizeFrame (frame : Locals) (byteLocal rows : Nat) : Locals :=
  { frame with
    locals := (((frame.locals.set 61 (.i64 (UInt64.ofNat rows))).set 62 (.i64 4)).set
      (byteLocal - 9) (.i64 (UInt64.ofNat (4 * rows)))).set 61 (.i64 (UInt64.ofNat (4 * rows)))
    values := [] }

theorem sizeCode_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (byteLocal rows : Nat) (hParams : frame.params.length = 9) (hLocals : frame.locals.length = 74)
    (hValues : frame.values = []) (hRows : frame.params[8]? = some (.i64 (UInt64.ofNat rows)))
    (hLow : 9 ≤ byteLocal) (hHigh : byteLocal < 70) (hCount : 4 * rows ≤ 2^32)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (sizeFrame frame byteLocal rows) env) :
    wp «module» (sizeCode byteLocal ++ rest) Q store frame env := by
  have hBytes : UInt64.ofNat rows * 4 = UInt64.ofNat (4 * rows) := by simp [Nat.mul_comm]
  have hNotParam : ¬ byteLocal < 9 := by omega
  have hValid : byteLocal < 9 + 74 := by omega
  have hSlot : byteLocal - 9 < 74 := by omega
  simp only [sizeCode, List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues, hRows]
  apply CheckedNatMul.program_spec 70 71 «module» env store _ (UInt64.ofNat rows) 4 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · simp only [UInt64.toNat_ofNat', UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    change _ < 18446744073709551616
    omega
  wp_packed_frame [hParams, hLocals, hBytes, hNotParam, hValid, hSlot]
  exact hNext

set_option maxRecDepth 32768 in
theorem emitted_sizes : func20.take 11 = sizeCode 9 ∧ (func20.drop 49).take 11 = sizeCode 19 := by
  constructor <;> rfl

set_option maxRecDepth 32768 in
theorem emitted_capacities :
    (func20.drop 11).take 12 = PackedCapacity.program 70 72 ∧
    (func20.drop 60).take 12 = PackedCapacity.program 70 72 ∧
    (func20.drop 116).take 12 = PackedCapacity.program 70 72 := by
  constructor <;> first | rfl | (constructor <;> rfl)

set_option maxRecDepth 32768 in
theorem emitted_allocations :
    (func20.drop 23).take 15 = PackedAllocation.program 72 ∧
    (func20.drop 72).take 15 = PackedAllocation.program 72 ∧
    (func20.drop 128).take 15 = PackedAllocation.program 72 := by
  constructor <;> first | rfl | (constructor <;> rfl)

#print axioms sizeCode_spec

end Project.Gpt2CachedStep.LayerNorm
