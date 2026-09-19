import Project.Gpt2CachedStep.Program
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.Vocabulary
open Wasm Project.ProofKit PackedFloatFrame

def sizeFrame (frame : Locals) : Locals :=
  { frame with
    locals := (((frame.locals.set 22 (.i64 50257)).set 23 (.i64 4)).set 0 (.i64 201028)).set 22 (.i64 201028)
    values := [] }

set_option maxRecDepth 32768 in
theorem emitted_size : func37.take 11 =
    [.constI64 50257, .localSet 28, .constI64 4, .localSet 29] ++
    CheckedNatMul.program 28 29 ++ [.localSet 6, .localGet 6, .localSet 28] := rfl

theorem size_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (hParams : frame.params.length = 6) (hLocals : frame.locals.length = 35) (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program) (hNext : wp «module» rest Q store (sizeFrame frame) env) :
    wp «module» (func37.take 11 ++ rest) Q store frame env := by
  rw [emitted_size]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues]
  apply CheckedNatMul.program_spec 28 29 «module» env store _ 50257 4 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · decide
  wp_packed_frame [hParams, hLocals]
  exact hNext

#print axioms size_spec

end Project.Gpt2CachedStep.Vocabulary
