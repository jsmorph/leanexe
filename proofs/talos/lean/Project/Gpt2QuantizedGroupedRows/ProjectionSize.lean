import Project.Gpt2QuantizedGroupedRows.ProjectionState
import Project.ProofKit.CheckedNatMul

namespace Project.Gpt2QuantizedGroupedRows.Projection
open Wasm Project.ProofKit PackedFloatFrame

def sizeCode : Wasm.Program :=
  [.localGet 9, .localSet 95, .localGet 8, .localSet 96] ++ CheckedNatMul.program 95 96 ++
    [.localSet 93, .constI64 4, .localSet 94] ++ CheckedNatMul.program 93 94 ++
    [.localSet 29, .localGet 29, .localSet 93]

def sizeFrame (frame : Locals) (outputWidth rows : Nat) : Locals :=
  { frame with
    locals := frame.locals
      |>.set 84 (.i64 (UInt64.ofNat rows))
      |>.set 85 (.i64 (UInt64.ofNat outputWidth))
      |>.set 82 (.i64 (UInt64.ofNat (rows * outputWidth)))
      |>.set 83 (.i64 4)
      |>.set 18 (.i64 (UInt64.ofNat (4 * (rows * outputWidth))))
      |>.set 82 (.i64 (UInt64.ofNat (4 * (rows * outputWidth))))
    values := [] }

theorem sizeCode_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (outputWidth rows : Nat)
    (hParams : frame.params.length = 11) (hLocals : frame.locals.length = 100)
    (hValues : frame.values = []) (hRows : frame.params[9]? = some (.i64 (UInt64.ofNat rows)))
    (hWidth : frame.params[8]? = some (.i64 (UInt64.ofNat outputWidth)))
    (hCount : 4 * (rows * outputWidth) ≤ 2^32)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (sizeFrame frame outputWidth rows) env) :
    wp «module» (sizeCode ++ rest) Q store frame env := by
  have hFit : (UInt64.ofNat rows).toNat * (UInt64.ofNat outputWidth).toNat < UInt64.size := by
    apply lt_of_le_of_lt (Nat.mul_le_mul (Nat.mod_le ..) (Nat.mod_le ..))
    change rows * outputWidth < 18446744073709551616
    omega
  have hFour : UInt64.ofNat (rows * outputWidth) * 4 = UInt64.ofNat (4 * (rows * outputWidth)) := by
    rw [Nat.mul_comm 4 (rows * outputWidth), UInt64.ofNat_mul (rows * outputWidth) 4,
      show UInt64.ofNat 4 = 4 from rfl]
  simp only [sizeCode, List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues, hRows, hWidth]
  apply CheckedNatMul.program_spec 95 96 «module» env store _
    (UInt64.ofNat rows) (UInt64.ofNat outputWidth) []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · exact hFit
  wp_packed_frame [hParams, hLocals, ← UInt64.ofNat_mul]
  apply CheckedNatMul.program_spec 93 94 «module» env store _ (UInt64.ofNat (rows * outputWidth)) 4 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · apply lt_of_le_of_lt (Nat.mul_le_mul_right 4 (Nat.mod_le (rows * outputWidth) UInt64.size))
    change rows * outputWidth * 4 < 18446744073709551616
    omega
  wp_packed_frame [hParams, hLocals, hFour]
  exact hNext

theorem emitted_size : (func8.drop 50).take 18 = sizeCode := rfl

#print axioms sizeCode_spec

end Project.Gpt2QuantizedGroupedRows.Projection
