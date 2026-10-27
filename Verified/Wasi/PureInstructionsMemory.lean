import Verified.Wasi.PureInstructionsLoad
import Verified.Wasi.PureInstructionsStore

namespace Verified.Wasi.PureTransport

open Wasm

theorem memory_transport {World : Type} (source target : Module)
    {inst : Instruction} (hForm : Encoding.InstructionForm inst)
    (hMemory : memoryAtomic inst = true)
    (fuel : Nat) (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    execOne fuel target (restore world initial) locals inst targetHost =
        liftContinuation world (execOne fuel source initial locals inst sourceHost) ∧
      NoReturnCall (execOne fuel source initial locals inst sourceHost) := by
  cases hForm <;> simp_all only [memoryAtomic, Bool.false_eq_true]
  case load32 offset =>
    exact load32_transport source target offset fuel initial world locals sourceHost targetHost
  case load64 offset =>
    exact load64_transport source target offset fuel initial world locals sourceHost targetHost
  case load8U offset =>
    exact load8_transport source target offset fuel initial world locals sourceHost targetHost
  case store32 offset =>
    exact store32_transport source target offset fuel initial world locals sourceHost targetHost
  case store64 offset =>
    exact store64_transport source target offset fuel initial world locals sourceHost targetHost
  case store8 offset =>
    exact store8_transport source target offset fuel initial world locals sourceHost targetHost

end Verified.Wasi.PureTransport
