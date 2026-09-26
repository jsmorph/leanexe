import Project.Gpt2CachedStep.Program
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.CachedHidden
open Wasm Project.ProofKit PackedFloatFrame

def embeddingSizeFrame (frame : Locals) : Locals :=
  { frame with
    locals := (((frame.locals.set 95 (.i64 768)).set 96 (.i64 4)).set
      0 (.i64 3072)).set 95 (.i64 3072)
    values := [] }

set_option maxRecDepth 32768 in
theorem emitted_embeddingSize : func36.take 11 =
    [.constI64 768, .localSet 103, .constI64 4, .localSet 104] ++
      CheckedNatMul.program 103 104 ++ [.localSet 8, .localGet 8, .localSet 103] := rfl

theorem embeddingSize_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (hParams : frame.params.length = 8) (hLocals : frame.locals.length = 124)
    (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (embeddingSizeFrame frame) env) :
    wp «module» (func36.take 11 ++ rest) Q store frame env := by
  rw [emitted_embeddingSize]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues]
  apply CheckedNatMul.program_spec 103 104 «module» env store _ 768 4 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · decide
  wp_packed_frame [hParams, hLocals]
  exact hNext

#print axioms embeddingSize_spec

end Project.Gpt2CachedStep.CachedHidden
