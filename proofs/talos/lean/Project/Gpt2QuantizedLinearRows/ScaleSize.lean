import Project.Gpt2QuantizedLinearRows.ScaleLoop
import Project.ProofKit.PackedCapacity
import Project.ProofKit.PackedAllocationFrame

namespace Project.Gpt2QuantizedLinearRows.QuantizeRows
open Wasm Project.ProofKit PackedFloatFrame

def scaleSizeCode : Wasm.Program :=
  [.localGet 4, .localSet 40, .constI64 4, .localSet 41] ++ CheckedNatMul.program 40 41 ++
    [.localSet 5, .localGet 5, .localSet 40]

def scaleSizeFrame (frame : Locals) (rows : Nat) : Locals :=
  { frame with locals := (((frame.locals.set 35 (.i64 (UInt64.ofNat rows))).set 36 (.i64 4)).set
      0 (.i64 (UInt64.ofNat (4 * rows)))).set 35 (.i64 (UInt64.ofNat (4 * rows))), values := [] }

theorem scaleSizeCode_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (rows : Nat)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 43)
    (hValues : frame.values = []) (hRows : frame.params[4]? = some (.i64 (UInt64.ofNat rows)))
    (hCount : 4 * rows ≤ 2^32) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (scaleSizeFrame frame rows) env) :
    wp «module» (scaleSizeCode ++ rest) Q store frame env := by
  have hBytes : UInt64.ofNat rows * 4 = UInt64.ofNat (4 * rows) := by simp [Nat.mul_comm]
  simp only [scaleSizeCode, List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues, hRows]
  apply CheckedNatMul.program_spec 40 41 «module» env store _ (UInt64.ofNat rows) 4 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · simp only [UInt64.toNat_ofNat', UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    change _ < 18446744073709551616
    omega
  wp_packed_frame [hParams, hLocals, hBytes]
  exact hNext

theorem emitted_scaleSize : func3.take 11 = scaleSizeCode := rfl

#print axioms scaleSizeCode_spec

end Project.Gpt2QuantizedLinearRows.QuantizeRows
