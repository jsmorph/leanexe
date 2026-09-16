import Project.EulerCertificate.ExecutionRetryTotal
import Project.EulerCertificate.SolverMemory

namespace Project.EulerCertificate.Execution
open Wasm Project.EulerRiemann
open Project.ProofKit.F64Outward (Checked)
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768

def advanceLoop : Wasm.Program :=
  match (func184[4]? : Option Wasm.Instruction) with
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
  match (advanceTrialBody[106]? : Option Wasm.Instruction) with
  | some (.iff _ _ body _ _ _) => body
  | _ => []

def advanceFinishBody : Wasm.Program :=
  match (advanceLoop[19]? : Option Wasm.Instruction) with
  | some (.iff _ _ body _ _ _) => body
  | _ => []

def advanceScanFailureBody : Wasm.Program :=
  match (advanceWorkBody[23]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ body _ _) => body
  | _ => []

def advanceTrialFailureBody : Wasm.Program :=
  match (advanceTrialBody[106]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ body _ _) => body
  | _ => []

theorem advance_loop_shape : func184 =
    func184.take 4 ++ [.block 0 0 [.loop 0 0 advanceLoop]] ++ func184.drop 5 := rfl

theorem advance_work_shape : advanceWorkBody = advanceWorkBody.take 13 ++
    [.localGet 41, .constI64 0, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 1, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 0, .eqI64, .eqz,
      .iff 0 0 advanceTrialBody advanceScanFailureBody] := rfl

theorem advance_trial_shape : advanceTrialBody = advanceTrialBody.take 96 ++
    [.localGet 72, .constI64 0, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 1, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64], .constI64 0, .eqI64, .eqz,
      .iff 0 0 advanceContinueBody advanceTrialFailureBody] := rfl

def advanceTimeFrame (frame : Locals) : Locals :=
  { frame with locals := frame.locals.set 18 (.i64 Time.endTime), values := [] }

def advanceParams (fuel : UInt64) (n : Nat) (trials time source : UInt64) (boundary : Vector) : List Wasm.Value :=
  [.i64 fuel, .i64 (UInt64.ofNat n), .i64 trials, .i64 time, .i64 source, .i64 source,
    .i64 boundary.mass.status, .i64 boundary.mass.lower, .i64 boundary.mass.upper,
    .i64 boundary.momentum.status, .i64 boundary.momentum.lower, .i64 boundary.momentum.upper,
    .i64 boundary.transverse.status, .i64 boundary.transverse.lower, .i64 boundary.transverse.upper,
    .i64 boundary.energy.status, .i64 boundary.energy.lower, .i64 boundary.energy.upper]

def advanceScanFrame (frame : Locals) (source : UInt64) (stats : Checked) : Locals :=
  let locals := frame.locals.set 19 (.i64 source)
  let locals := locals.set 20 (.i64 source)
  let locals := locals.set 22 (.i64 stats.value)
  let locals := locals.set 21 (.i64 stats.status)
  let locals := locals.set 23 (.i64 stats.status)
  let locals := locals.set 24 (.i64 stats.value)
  { frame with locals, values := [] }

def advanceTrialFrame (frame : Locals) (n : Nat) (trials time source alpha dt trialDt result : UInt64)
    (boundary : Vector) (status : UInt64 := 0) : Locals :=
  let locals := frame.locals.set 25 (.i64 (UInt64.ofNat n))
  let locals := locals.set 26 (.i64 (time))
  let locals := locals.set 27 (.i64 (alpha))
  let locals := locals.set 28 (.i64 (dt))
  let locals := locals.set 29 (.i64 (dt))
  let locals := locals.set 154 (.i64 (dt))
  let locals := locals.set 155 (.i64 (1))
  let locals := locals.set 156 (.i64 (dt + 1))
  let locals := locals.set 30 (.i64 (dt + 1))
  let locals := locals.set 31 (.i64 (UInt64.ofNat n))
  let locals := locals.set 32 (.i64 (trials))
  let locals := locals.set 33 (.i64 (time))
  let locals := locals.set 34 (.i64 (dt))
  let locals := locals.set 35 (.i64 (alpha))
  let locals := locals.set 36 (.i64 (source))
  let locals := locals.set 37 (.i64 (source))
  let locals := locals.set 53 (.i64 (boundary.energy.upper))
  let locals := locals.set 52 (.i64 (boundary.energy.lower))
  let locals := locals.set 51 (.i64 (boundary.energy.status))
  let locals := locals.set 50 (.i64 (boundary.transverse.upper))
  let locals := locals.set 49 (.i64 (boundary.transverse.lower))
  let locals := locals.set 48 (.i64 (boundary.transverse.status))
  let locals := locals.set 47 (.i64 (boundary.momentum.upper))
  let locals := locals.set 46 (.i64 (boundary.momentum.lower))
  let locals := locals.set 45 (.i64 (boundary.momentum.status))
  let locals := locals.set 44 (.i64 (boundary.mass.upper))
  let locals := locals.set 43 (.i64 (boundary.mass.lower))
  let locals := locals.set 42 (.i64 (boundary.mass.status))
  let locals := locals.set 41 (.i64 (result))
  let locals := locals.set 40 (.i64 (result))
  let locals := locals.set 39 (.i64 (trialDt))
  let locals := locals.set 38 (.i64 (status))
  let locals := locals.set 54 (.i64 (status))
  let locals := locals.set 55 (.i64 (trialDt))
  let locals := locals.set 56 (.i64 (result))
  let locals := locals.set 57 (.i64 (result))
  let locals := locals.set 58 (.i64 (boundary.mass.status))
  let locals := locals.set 59 (.i64 (boundary.mass.lower))
  let locals := locals.set 60 (.i64 (boundary.mass.upper))
  let locals := locals.set 61 (.i64 (boundary.momentum.status))
  let locals := locals.set 62 (.i64 (boundary.momentum.lower))
  let locals := locals.set 63 (.i64 (boundary.momentum.upper))
  let locals := locals.set 64 (.i64 (boundary.transverse.status))
  let locals := locals.set 65 (.i64 (boundary.transverse.lower))
  let locals := locals.set 66 (.i64 (boundary.transverse.upper))
  let locals := locals.set 67 (.i64 (boundary.energy.status))
  let locals := locals.set 68 (.i64 (boundary.energy.lower))
  let locals := locals.set 69 (.i64 (boundary.energy.upper))
  { frame with locals, values := [] }

#print axioms advance_loop_shape
#print axioms advance_work_shape
#print axioms advance_trial_shape

end Project.EulerCertificate.Execution
