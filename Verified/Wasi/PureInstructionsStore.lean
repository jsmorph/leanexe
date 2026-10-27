import Verified.Wasi.PureInstructionsMemoryStep

namespace Verified.Wasi.PureTransport

open Wasm

theorem store8_transport {World : Type} (source target : Module) (offset : UInt32)
    (fuel : Nat) (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    execOne fuel target (restore world initial) locals (.store8 offset) targetHost =
        liftContinuation world
          (execOne fuel source initial locals (.store8 offset) sourceHost) ∧
      NoReturnCall (execOne fuel source initial locals (.store8 offset) sourceHost) := by
  cases fuel with
  | zero => simp only [execOne.eq_def, liftContinuation, NoReturnCall, and_self]
  | succ fuel =>
    constructor
    · rw [store8_step, store8_step]
      repeat' first | rfl | contradiction | split
    · apply (noReturnCall_iff_flag _).2
      simp only [store8_step]
      repeat' first | rfl | split

theorem store32_transport {World : Type} (source target : Module) (offset : UInt32)
    (fuel : Nat) (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    execOne fuel target (restore world initial) locals (.store32 offset) targetHost =
        liftContinuation world
          (execOne fuel source initial locals (.store32 offset) sourceHost) ∧
      NoReturnCall (execOne fuel source initial locals (.store32 offset) sourceHost) := by
  cases fuel with
  | zero => simp only [execOne.eq_def, liftContinuation, NoReturnCall, and_self]
  | succ fuel =>
    constructor
    · rw [store32_step, store32_step]
      repeat' first | rfl | contradiction | split
    · apply (noReturnCall_iff_flag _).2
      simp only [store32_step]
      repeat' first | rfl | split

theorem store64_transport {World : Type} (source target : Module) (offset : UInt32)
    (fuel : Nat) (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    execOne fuel target (restore world initial) locals (.store64 offset) targetHost =
        liftContinuation world
          (execOne fuel source initial locals (.store64 offset) sourceHost) ∧
      NoReturnCall (execOne fuel source initial locals (.store64 offset) sourceHost) := by
  cases fuel with
  | zero => simp only [execOne.eq_def, liftContinuation, NoReturnCall, and_self]
  | succ fuel =>
    constructor
    · rw [store64_step, store64_step]
      repeat' first | rfl | contradiction | split
    · apply (noReturnCall_iff_flag _).2
      simp only [store64_step]
      repeat' first | rfl | split

end Verified.Wasi.PureTransport
