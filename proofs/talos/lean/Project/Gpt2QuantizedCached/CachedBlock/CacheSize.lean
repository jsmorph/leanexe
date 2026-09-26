import Project.Gpt2QuantizedCached.CachedBlock.Structure
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.ProofKit PackedFloatFrame

theorem emitted_block_signature : func54Def.params.length = 11 ∧ func54Def.locals.length = 193 := by
  constructor <;> rfl

def cacheSizeFrame (frame : Locals) : Locals :=
  { frame with
    locals := (((frame.locals.set 185 (.i64 1536)).set 186 (.i64 4)).set
      171 (.i64 6144)).set 185 (.i64 6144)
    values := [] }

set_option maxRecDepth 32768 in
theorem emitted_cache_size : (activatedSuccess.drop 109).take 11 =
    [.constI64 1536, .localSet 196, .constI64 4, .localSet 197] ++
      CheckedNatMul.program 196 197 ++ [.localSet 182, .localGet 182, .localSet 196] := rfl

theorem cacheSize_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (hParams : frame.params.length = 11) (hLocals : frame.locals.length = 193)
    (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q store (cacheSizeFrame frame) env) :
    wp «module» ((activatedSuccess.drop 109).take 11 ++ rest) Q store frame env := by
  rw [emitted_cache_size]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLocals, hValues]
  apply CheckedNatMul.program_spec 196 197 «module» env store _ 1536 4 []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · decide
  wp_packed_frame [hParams, hLocals]
  exact hNext

#print axioms cacheSize_spec

end Project.Gpt2QuantizedCached.CachedBlock
