import Project.Gpt2QuantizedLinearRows.ScaleSize

namespace Project.Gpt2QuantizedLinearRows.QuantizeRows
open Wasm Project.ProofKit PackedFloatFrame

def byteSizeCode : Wasm.Program :=
  [.localGet 4, .localSet 42, .localGet 3, .localSet 43] ++ CheckedNatMul.program 42 43 ++
    [.localSet 40, .constI64 1, .localSet 41] ++ CheckedNatMul.program 40 41 ++
    [.localSet 16, .localGet 16, .localSet 40]

def byteSizeFrame (frame : Locals) (width rows : Nat) : Locals :=
  { frame with
    locals := frame.locals
      |>.set 37 (.i64 (UInt64.ofNat rows))
      |>.set 38 (.i64 (UInt64.ofNat width))
      |>.set 35 (.i64 (UInt64.ofNat (rows * width)))
      |>.set 36 (.i64 1)
      |>.set 11 (.i64 (UInt64.ofNat (rows * width)))
      |>.set 35 (.i64 (UInt64.ofNat (rows * width)))
    values := [] }

theorem byteSizeCode_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (width rows : Nat)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 43)
    (hValues : frame.values = []) (hRows : frame.params[4]? = some (.i64 (UInt64.ofNat rows)))
    (hWidth : frame.params[3]? = some (.i64 (UInt64.ofNat width))) (hCount : rows * width ≤ 2^32)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (byteSizeFrame frame width rows) env) :
    wp «module» (byteSizeCode ++ rest) Q store frame env := by
  have hFit : (UInt64.ofNat rows).toNat * (UInt64.ofNat width).toNat < UInt64.size := by
    apply lt_of_le_of_lt (Nat.mul_le_mul (Nat.mod_le ..) (Nat.mod_le ..))
    change rows * width < 18446744073709551616
    omega
  simp only [byteSizeCode, List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues, hRows, hWidth]
  apply CheckedNatMul.program_spec 42 43 «module» env store _
    (UInt64.ofNat rows) (UInt64.ofNat width) []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · exact hFit
  wp_packed_frame [hParams, hLocals, ← UInt64.ofNat_mul]
  apply CheckedNatMul.program_spec 40 41 «module» env store _ (UInt64.ofNat (rows * width)) 1 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · simpa using (UInt64.ofNat (rows * width)).toNat_lt
  wp_packed_frame [hParams, hLocals, UInt64.mul_one]
  exact hNext

theorem emitted_byteSize : (func3.drop 49).take 18 = byteSizeCode := rfl

#print axioms byteSizeCode_spec

end Project.Gpt2QuantizedLinearRows.QuantizeRows
