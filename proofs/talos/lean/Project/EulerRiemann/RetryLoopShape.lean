import Project.EulerRiemann.StepReserve
import Project.EulerRiemann.ExecutionProposal

namespace Project.EulerRiemann.Execution
open Wasm

def retryLoop : Wasm.Program :=
  match (func74[4]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def retryTrial : Wasm.Program :=
  match (retryLoop[22]? : Option Wasm.Instruction) with
  | some (.iff _ _ body _ _ _) => body
  | _ => []

theorem retry_loop_shape : func74 =
    func74.take 4 ++ [.block 0 0 [.loop 0 0 retryLoop]] ++ func74.drop 5 := rfl

theorem retry_trial_shape : retryLoop[22]? =
    some (.iff 0 0 retryTrial
      (match (retryLoop[22]? : Option Wasm.Instruction) with
        | some (.iff _ _ _ no _ _) => no | _ => [])) := rfl

def retryTrialFrame (frame : Locals) (n : Nat) (ratio source result : UInt64)
    (accepted : Bool) : Locals :=
  let locals := frame.locals.set 9 (.i64 (UInt64.ofNat n))
  let locals := locals.set 10 (.i64 (UInt64.ofNat n))
  let locals := locals.set 11 (.i64 ratio)
  let locals := locals.set 12 (.i64 source)
  let locals := locals.set 13 (.i64 source)
  let locals := locals.set 15 (.i64 result)
  let locals := locals.set 14 (.i64 result)
  let locals := locals.set 16 (.i64 result)
  let locals := locals.set 17 (.i64 result)
  let locals := locals.set 18 (.i64 result)
  let locals := locals.set 19 (.i64 result)
  let locals := locals.set 20 (.i64 (boolWord accepted))
  { frame with locals, values := [] }

#print axioms retry_loop_shape
#print axioms retry_trial_shape

end Project.EulerRiemann.Execution
