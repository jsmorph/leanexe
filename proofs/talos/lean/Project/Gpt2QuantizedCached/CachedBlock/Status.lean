import Project.Gpt2QuantizedCached.CachedBlock.Completion

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.ProofKit PackedFloatFrame

def successFrame (frame : Locals) : Locals :=
  { frame with locals := frame.locals.set 178 (.i64 0) }

theorem successFrame_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (hParams : frame.params.length = 11) (hLength : frame.locals.length = 193)
    (hValues : frame.values = []) (Q : Assertion Unit) (rest : Program)
    (hNext : wp «module» rest Q initial (successFrame frame) env) :
    wp «module» ([.constI64 0, .localSet 189] ++ rest) Q initial frame env := by
  simp only [List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  simpa only [successFrame, hValues] using hNext

#print axioms successFrame_spec
end Project.Gpt2QuantizedCached.CachedBlock
