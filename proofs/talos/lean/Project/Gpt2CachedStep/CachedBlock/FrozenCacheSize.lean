import Project.Gpt2CachedStep.FrozenProgram
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.Frozen.CachedBlock
open Wasm Project.ProofKit PackedFloatFrame

theorem emitted_block_signature : func33Def.params.length = 11 ∧ func33Def.locals.length = 164 := by
  constructor <;> rfl

def cacheSizeFrame (frame : Locals) : Locals :=
  { frame with
    locals := (((frame.locals.set 156 (.i64 1536)).set 157 (.i64 4)).set
      143 (.i64 6144)).set 156 (.i64 6144)
    values := [] }

set_option maxRecDepth 32768 in
theorem emitted_cache_size : (func33.drop 484).take 11 =
    [.constI64 1536, .localSet 167, .constI64 4, .localSet 168] ++
      CheckedNatMul.program 167 168 ++ [.localSet 154, .localGet 154, .localSet 167] := rfl

theorem cacheSize_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (hParams : frame.params.length = 11) (hLocals : frame.locals.length = 164)
    (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (cacheSizeFrame frame) env) :
    wp «module» ((func33.drop 484).take 11 ++ rest) Q store frame env := by
  rw [emitted_cache_size]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues]
  apply CheckedNatMul.program_spec 167 168 «module» env store _ 1536 4 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · decide
  wp_packed_frame [hParams, hLocals]
  exact hNext

#print axioms cacheSize_spec

end Project.Gpt2CachedStep.Frozen.CachedBlock
