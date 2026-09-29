import Project.Encoding
import Project.Encoding.Decode
import Project.Encoding.DecodeCorrect.Modules

namespace Wasm.Encoding

/-- The decoder reads every successful encoding back as the encoded module.  The
decoder, which the official testsuite exercises, then defines what the encoder's
output means.  `Decoder.maxLocals` is the decoder's per-function limit on locals. -/
theorem decode_encode (m : Wasm.Module) (bytes : ByteArray)
    (locals : ∀ f ∈ m.funcs, f.locals.length ≤ Decoder.maxLocals)
    (success : encode m = .ok bytes) : decode bytes = .ok m := by
  have hEncodes := encode_correct m bytes success
  unfold decode
  rw [Decoder.moduleParser_run hEncodes locals]

end Wasm.Encoding
