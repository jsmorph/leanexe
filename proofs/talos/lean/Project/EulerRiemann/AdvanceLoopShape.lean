import Project.EulerRiemann.ExecutionRetry
import Project.EulerRiemann.ControlAdvanceStep
import Project.EulerRiemann.ExecutionScan

namespace Project.EulerRiemann.Execution
open Wasm

def advanceLoop : Wasm.Program :=
  match (func78[4]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def advanceWorkBody : Wasm.Program :=
  match (advanceLoop[19]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ body _ _) => body
  | _ => []

def advanceTrialBody : Wasm.Program :=
  match (advanceWorkBody[23]? : Option Wasm.Instruction) with
  | some (.iff _ _ body _ _ _) => body
  | _ => []

def advanceContinueBody : Wasm.Program :=
  match (advanceTrialBody[64]? : Option Wasm.Instruction) with
  | some (.iff _ _ body _ _ _) => body
  | _ => []

def advanceFinishBody : Wasm.Program :=
  match (advanceLoop[19]? : Option Wasm.Instruction) with
  | some (.iff _ _ body _ _ _) => body
  | _ => []

theorem advance_loop_shape : func78 =
    func78.take 4 ++ [.block 0 0 [.loop 0 0 advanceLoop]] ++ func78.drop 5 := rfl

theorem advance_work_shape : advanceWorkBody = advanceWorkBody.take 13 ++
    [.localGet 16, .constI64 0, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 1, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 0, .eqI64, .eqz,
      .iff 0 0 advanceTrialBody
        (match (advanceWorkBody[23]? : Option Wasm.Instruction) with
          | some (.iff _ _ _ body _ _) => body | _ => [])] := rfl

theorem advance_trial_shape : advanceTrialBody = advanceTrialBody.take 54 ++
    [.localGet 33, .constI64 0, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 1, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 0, .eqI64, .eqz,
      .iff 0 0 advanceContinueBody
        (match (advanceTrialBody[64]? : Option Wasm.Instruction) with
          | some (.iff _ _ _ body _ _) => body | _ => [])] := rfl

def advanceTimeFrame (frame : Locals) : Locals :=
  { frame with locals := frame.locals.set 6 (.i64 Time.endTime), values := [] }

def advanceScanFrame (frame : Locals) (source : UInt64) (stats : Traversal.Scan) : Locals :=
  let locals := frame.locals.set 7 (.i64 source)
  let locals := locals.set 8 (.i64 source)
  let locals := locals.set 10 (.i64 stats.alpha)
  let locals := locals.set 9 (.i64 stats.status)
  let locals := locals.set 11 (.i64 stats.status)
  let locals := locals.set 12 (.i64 stats.alpha)
  { frame with locals, values := [] }

def advanceTrialFrame (frame : Locals) (n : Nat) (time source alpha dt trialDt result : UInt64) : Locals :=
  let locals := frame.locals.set 13 (.i64 (UInt64.ofNat n))
  let locals := locals.set 14 (.i64 time)
  let locals := locals.set 15 (.i64 alpha)
  let locals := locals.set 16 (.i64 dt)
  let locals := locals.set 17 (.i64 dt)
  let locals := locals.set 42 (.i64 dt)
  let locals := locals.set 43 (.i64 1)
  let locals := locals.set 44 (.i64 (dt + 1))
  let locals := locals.set 18 (.i64 (dt + 1))
  let locals := locals.set 19 (.i64 (UInt64.ofNat n))
  let locals := locals.set 20 (.i64 time)
  let locals := locals.set 21 (.i64 dt)
  let locals := locals.set 22 (.i64 source)
  let locals := locals.set 23 (.i64 source)
  let locals := locals.set 27 (.i64 result)
  let locals := locals.set 26 (.i64 result)
  let locals := locals.set 25 (.i64 trialDt)
  let locals := locals.set 24 (.i64 0)
  let locals := locals.set 28 (.i64 0)
  let locals := locals.set 29 (.i64 trialDt)
  let locals := locals.set 30 (.i64 result)
  let locals := locals.set 31 (.i64 result)
  { frame with locals, values := [] }

#print axioms advance_loop_shape
#print axioms advance_work_shape
#print axioms advance_trial_shape

end Project.EulerRiemann.Execution
