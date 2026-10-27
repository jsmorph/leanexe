import Verified.Wasi.PureInstructionsInteger
import Verified.Wasi.PureInstructionsFloat
import Verified.Wasi.PureInstructionsState

namespace Verified.Wasi.PureTransport

open Wasm

theorem atomic_transport {World : Type} {source target : Module}
    (hMemory64 : target.memIs64 = source.memIs64)
    (hMemoryCap : target.memoryCap = source.memoryCap)
    {inst : Instruction} (hForm : Encoding.InstructionForm inst) (hAtomic : atomic inst = true)
    (fuel : Nat) (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    execOne fuel target (restore world initial) locals inst targetHost =
        liftContinuation world (execOne fuel source initial locals inst sourceHost) ∧
      NoReturnCall (execOne fuel source initial locals inst sourceHost) := by
  rcases atomic_cases hForm hAtomic with hInteger | hFloat | hState
  · exact integer_transport source target hForm hInteger fuel initial world locals sourceHost targetHost
  · exact float_transport source target hForm hFloat fuel initial world locals sourceHost targetHost
  · exact state_transport hMemory64 hMemoryCap hForm hState fuel initial world locals sourceHost targetHost

end Verified.Wasi.PureTransport
