import Project.Gpt2QuantizedCached.Program
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2QuantizedCached.Embedding
open Wasm Project.ProofKit PackedFloatFrame

def sizeFrame (frame : Locals) : Locals :=
  { frame with
    locals := (((frame.locals.set 7 (.i64 768)).set 8 (.i64 4)).set
      1 (.i64 3072)).set 7 (.i64 3072)
    values := [] }

set_option maxRecDepth 32768 in
theorem emitted_size : (func30.drop 28).take 11 =
    [.constI64 768, .localSet 12, .constI64 4, .localSet 13] ++
      CheckedNatMul.program 12 13 ++ [.localSet 6, .localGet 6, .localSet 12] := rfl

theorem size_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 22)
    (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (sizeFrame frame) env) :
    wp «module» ((func30.drop 28).take 11 ++ rest) Q store frame env := by
  rw [emitted_size]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues]
  apply CheckedNatMul.program_spec 12 13 «module» env store _ 768 4 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · decide
  wp_packed_frame [hParams, hLocals]
  exact hNext

#print axioms size_spec

end Project.Gpt2QuantizedCached.Embedding
