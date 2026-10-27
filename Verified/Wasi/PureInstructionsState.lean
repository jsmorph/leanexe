import Verified.Wasi.PureInstructionsLocals
import Verified.Wasi.PureInstructionsMemory
import Verified.Wasi.PureInstructionsGrowth

namespace Verified.Wasi.PureTransport

open Wasm

theorem state_transport {World : Type} {source target : Module}
    (hMemory64 : target.memIs64 = source.memIs64)
    (hMemoryCap : target.memoryCap = source.memoryCap)
    {inst : Instruction} (hForm : Encoding.InstructionForm inst) (hState : stateAtomic inst = true)
    (fuel : Nat) (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    execOne fuel target (restore world initial) locals inst targetHost =
        liftContinuation world (execOne fuel source initial locals inst sourceHost) ∧
      NoReturnCall (execOne fuel source initial locals inst sourceHost) := by
  rcases state_cases hForm hState with hLocal | hMemory | hGrowth
  · exact local_transport source target hForm hLocal fuel initial world locals sourceHost targetHost
  · exact memory_transport source target hForm hMemory fuel initial world locals sourceHost targetHost
  · exact growth_transport hMemory64 hMemoryCap hForm hGrowth fuel initial world locals sourceHost targetHost

end Verified.Wasi.PureTransport
