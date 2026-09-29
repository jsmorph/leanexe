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

/-- `encode` succeeds on `m`, and the decoder reads the bytes back as `m`.  For a
concrete module, the premise that the encoder's result is `ok` holds by
evaluation. -/
theorem round_trip (m : Wasm.Module)
    (locals : ∀ f ∈ m.funcs, f.locals.length ≤ Decoder.maxLocals)
    (ok : (encode m).isOk = true) :
    ∃ bytes, encode m = .ok bytes ∧ decode bytes = .ok m := by
  cases success : encode m with
  | error message => simp [success, Except.isOk, Except.toBool] at ok
  | ok bytes => exact ⟨bytes, rfl, decode_encode m bytes locals success⟩

end Wasm.Encoding
