import Verified.Wasi.PureInstructionsMemoryStep

namespace Verified.Wasi.PureTransport

open Wasm

theorem load8_transport {World : Type} (source target : Module) (offset : UInt32)
    (fuel : Nat) (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    execOne fuel target (restore world initial) locals (.load8U offset) targetHost =
        liftContinuation world
          (execOne fuel source initial locals (.load8U offset) sourceHost) ∧
      NoReturnCall (execOne fuel source initial locals (.load8U offset) sourceHost) := by
  cases fuel with
  | zero => simp only [execOne.eq_def, liftContinuation, NoReturnCall, and_self]
  | succ fuel =>
    constructor
    · rw [load8_step, load8_step]
      repeat' first | rfl | contradiction | split
    · apply (noReturnCall_iff_flag _).2
      simp only [load8_step]
      repeat' first | rfl | split

theorem load32_transport {World : Type} (source target : Module) (offset : UInt32)
    (fuel : Nat) (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    execOne fuel target (restore world initial) locals (.load32 offset) targetHost =
        liftContinuation world
          (execOne fuel source initial locals (.load32 offset) sourceHost) ∧
      NoReturnCall (execOne fuel source initial locals (.load32 offset) sourceHost) := by
  cases fuel with
  | zero => simp only [execOne.eq_def, liftContinuation, NoReturnCall, and_self]
  | succ fuel =>
    constructor
    · rw [load32_step, load32_step]
      repeat' first | rfl | contradiction | split
    · apply (noReturnCall_iff_flag _).2
      simp only [load32_step]
      repeat' first | rfl | split

theorem load64_transport {World : Type} (source target : Module) (offset : UInt32)
    (fuel : Nat) (initial : Store Unit) (world : World) (locals : Locals)
    (sourceHost : HostEnv Unit) (targetHost : HostEnv World) :
    execOne fuel target (restore world initial) locals (.load64 offset) targetHost =
        liftContinuation world
          (execOne fuel source initial locals (.load64 offset) sourceHost) ∧
      NoReturnCall (execOne fuel source initial locals (.load64 offset) sourceHost) := by
  cases fuel with
  | zero => simp only [execOne.eq_def, liftContinuation, NoReturnCall, and_self]
  | succ fuel =>
    constructor
    · rw [load64_step, load64_step]
      repeat' first | rfl | contradiction | split
    · apply (noReturnCall_iff_flag _).2
      simp only [load64_step]
      repeat' first | rfl | split

end Verified.Wasi.PureTransport
