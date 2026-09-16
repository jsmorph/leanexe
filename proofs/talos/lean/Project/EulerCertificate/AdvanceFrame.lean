import Project.EulerCertificate.AdvanceLoopShape

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerRiemann.Execution (boolWord)
open Project.ProofKit.F64Outward (Checked)
open Project.EulerCertificate.Flux (Vector)
open Project.EulerCertificateFlux.Execution (vectorValues boundsValues)

set_option maxRecDepth 32768

structure AdvanceFrameAt (frame : Locals) (fuel : UInt64) (n : Nat)
    (trials time source tracker outputTime outputRoot : UInt64) (done : Bool) (boundary : Vector) : Prop where
  params : frame.params = advanceParams fuel n trials time source boundary
  locals : frame.locals.length = 157
  values : frame.values = []
  tracker : frame.locals[0]? = some (.i64 tracker)
  status : frame.locals[1]? = some (.i64 0)
  outputTime : frame.locals[2]? = some (.i64 outputTime)
  outputOwner : frame.locals[3]? = some (.i64 outputRoot)
  outputPointer : frame.locals[4]? = some (.i64 outputRoot)
  done : frame.locals[17]? = some (.i64 (boolWord done))

def advanceReturnedFrame (frame : Locals) (status time source : UInt64) (boundary : Vector) : Locals :=
  let locals := frame.locals.set 1 (.i64 (status))
  let locals := locals.set 2 (.i64 (time))
  let locals := locals.set 3 (.i64 (source))
  let locals := locals.set 4 (.i64 (source))
  let locals := locals.set 5 (.i64 (boundary.mass.status))
  let locals := locals.set 6 (.i64 (boundary.mass.lower))
  let locals := locals.set 7 (.i64 (boundary.mass.upper))
  let locals := locals.set 8 (.i64 (boundary.momentum.status))
  let locals := locals.set 9 (.i64 (boundary.momentum.lower))
  let locals := locals.set 10 (.i64 (boundary.momentum.upper))
  let locals := locals.set 11 (.i64 (boundary.transverse.status))
  let locals := locals.set 12 (.i64 (boundary.transverse.lower))
  let locals := locals.set 13 (.i64 (boundary.transverse.upper))
  let locals := locals.set 14 (.i64 (boundary.energy.status))
  let locals := locals.set 15 (.i64 (boundary.energy.lower))
  let locals := locals.set 16 (.i64 (boundary.energy.upper))
  let locals := locals.set 17 (.i64 (1))
  { frame with locals, values := [] }

def advanceAccumulatedFrame (frame : Locals) (boundary stepBoundary : Vector) : Locals :=
  let total := Vectors.add boundary stepBoundary
  let locals := frame.locals.set 70 (.i64 (boundary.mass.status))
  let locals := locals.set 71 (.i64 (boundary.mass.lower))
  let locals := locals.set 72 (.i64 (boundary.mass.upper))
  let locals := locals.set 73 (.i64 (boundary.momentum.status))
  let locals := locals.set 74 (.i64 (boundary.momentum.lower))
  let locals := locals.set 75 (.i64 (boundary.momentum.upper))
  let locals := locals.set 76 (.i64 (boundary.transverse.status))
  let locals := locals.set 77 (.i64 (boundary.transverse.lower))
  let locals := locals.set 78 (.i64 (boundary.transverse.upper))
  let locals := locals.set 79 (.i64 (boundary.energy.status))
  let locals := locals.set 80 (.i64 (boundary.energy.lower))
  let locals := locals.set 81 (.i64 (boundary.energy.upper))
  let locals := locals.set 82 (.i64 (stepBoundary.mass.status))
  let locals := locals.set 83 (.i64 (stepBoundary.mass.lower))
  let locals := locals.set 84 (.i64 (stepBoundary.mass.upper))
  let locals := locals.set 85 (.i64 (stepBoundary.momentum.status))
  let locals := locals.set 86 (.i64 (stepBoundary.momentum.lower))
  let locals := locals.set 87 (.i64 (stepBoundary.momentum.upper))
  let locals := locals.set 88 (.i64 (stepBoundary.transverse.status))
  let locals := locals.set 89 (.i64 (stepBoundary.transverse.lower))
  let locals := locals.set 90 (.i64 (stepBoundary.transverse.upper))
  let locals := locals.set 91 (.i64 (stepBoundary.energy.status))
  let locals := locals.set 92 (.i64 (stepBoundary.energy.lower))
  let locals := locals.set 93 (.i64 (stepBoundary.energy.upper))
  let locals := locals.set 105 (.i64 (total.energy.upper))
  let locals := locals.set 104 (.i64 (total.energy.lower))
  let locals := locals.set 103 (.i64 (total.energy.status))
  let locals := locals.set 102 (.i64 (total.transverse.upper))
  let locals := locals.set 101 (.i64 (total.transverse.lower))
  let locals := locals.set 100 (.i64 (total.transverse.status))
  let locals := locals.set 99 (.i64 (total.momentum.upper))
  let locals := locals.set 98 (.i64 (total.momentum.lower))
  let locals := locals.set 97 (.i64 (total.momentum.status))
  let locals := locals.set 96 (.i64 (total.mass.upper))
  let locals := locals.set 95 (.i64 (total.mass.lower))
  let locals := locals.set 94 (.i64 (total.mass.status))
  let locals := locals.set 106 (.i64 (total.mass.status))
  let locals := locals.set 107 (.i64 (total.mass.lower))
  let locals := locals.set 108 (.i64 (total.mass.upper))
  let locals := locals.set 109 (.i64 (total.momentum.status))
  let locals := locals.set 110 (.i64 (total.momentum.lower))
  let locals := locals.set 111 (.i64 (total.momentum.upper))
  let locals := locals.set 112 (.i64 (total.transverse.status))
  let locals := locals.set 113 (.i64 (total.transverse.lower))
  let locals := locals.set 114 (.i64 (total.transverse.upper))
  let locals := locals.set 115 (.i64 (total.energy.status))
  let locals := locals.set 116 (.i64 (total.energy.lower))
  let locals := locals.set 117 (.i64 (total.energy.upper))
  { frame with locals, values := [] }

def advanceContinuedFrame (frame : Locals) (fuel : UInt64) (n : Nat)
    (trials nextTime result : UInt64) (total : Vector) : Locals :=
  let locals := frame.locals.set 118 (.i64 (UInt64.ofNat n))
  let locals := locals.set 119 (.i64 (trials))
  let locals := locals.set 120 (.i64 (nextTime))
  let locals := locals.set 121 (.i64 (result))
  let locals := locals.set 122 (.i64 (result))
  let locals := locals.set 123 (.i64 (total.mass.status))
  let locals := locals.set 124 (.i64 (total.mass.lower))
  let locals := locals.set 125 (.i64 (total.mass.upper))
  let locals := locals.set 126 (.i64 (total.momentum.status))
  let locals := locals.set 127 (.i64 (total.momentum.lower))
  let locals := locals.set 128 (.i64 (total.momentum.upper))
  let locals := locals.set 129 (.i64 (total.transverse.status))
  let locals := locals.set 130 (.i64 (total.transverse.lower))
  let locals := locals.set 131 (.i64 (total.transverse.upper))
  let locals := locals.set 132 (.i64 (total.energy.status))
  let locals := locals.set 133 (.i64 (total.energy.lower))
  let locals := locals.set 134 (.i64 (total.energy.upper))
  let locals := locals.set 135 (.i64 (UInt64.ofNat n))
  let locals := locals.set 136 (.i64 (trials))
  let locals := locals.set 137 (.i64 (nextTime))
  let locals := locals.set 138 (.i64 (result))
  let locals := locals.set 139 (.i64 (result))
  let locals := locals.set 140 (.i64 (total.mass.status))
  let locals := locals.set 141 (.i64 (total.mass.lower))
  let locals := locals.set 142 (.i64 (total.mass.upper))
  let locals := locals.set 143 (.i64 (total.momentum.status))
  let locals := locals.set 144 (.i64 (total.momentum.lower))
  let locals := locals.set 145 (.i64 (total.momentum.upper))
  let locals := locals.set 146 (.i64 (total.transverse.status))
  let locals := locals.set 147 (.i64 (total.transverse.lower))
  let locals := locals.set 148 (.i64 (total.transverse.upper))
  let locals := locals.set 149 (.i64 (total.energy.status))
  let locals := locals.set 150 (.i64 (total.energy.lower))
  let locals := locals.set 151 (.i64 (total.energy.upper))
  let locals := locals.set 152 (.i64 (result))
  let locals := locals.set 0 (.i64 (result))
  { params := advanceParams (fuel - 1) n trials nextTime result total
    locals
    values := [] }

theorem AdvanceFrameAt.time {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time source tracker outputTime outputRoot : UInt64} {done : Bool} {boundary : Vector}
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot done boundary) :
    AdvanceFrameAt (advanceTimeFrame frame) fuel n trials time source tracker outputTime outputRoot done boundary := by
  cases h
  constructor <;> simp_all [advanceTimeFrame]

theorem AdvanceFrameAt.scan {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time source tracker outputTime outputRoot : UInt64} {done : Bool} {boundary : Vector}
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot done boundary) (stats : Checked) :
    AdvanceFrameAt (advanceScanFrame frame source stats) fuel n trials time source tracker outputTime outputRoot done boundary := by
  cases h
  constructor <;> simp_all [advanceScanFrame]

theorem AdvanceFrameAt.trial {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time source tracker outputTime outputRoot : UInt64} {done : Bool} {boundary : Vector}
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot done boundary) (alpha dt trialDt result : UInt64) (stepBoundary : Vector) (status : UInt64 := 0) :
    AdvanceFrameAt (advanceTrialFrame frame n trials time source alpha dt trialDt result stepBoundary status) fuel n trials time source tracker outputTime outputRoot done boundary := by
  cases h
  constructor <;> simp_all [advanceTrialFrame]

theorem AdvanceFrameAt.accumulated {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time source tracker outputTime outputRoot : UInt64} {done : Bool} {boundary : Vector}
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot done boundary) (stepBoundary : Vector) :
    AdvanceFrameAt (advanceAccumulatedFrame frame boundary stepBoundary) fuel n trials time source tracker outputTime outputRoot done boundary := by
  cases h
  constructor <;> simp_all [advanceAccumulatedFrame]

theorem AdvanceFrameAt.continued {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time source tracker outputTime outputRoot : UInt64} {done : Bool} {boundary : Vector}
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot done boundary)
    (nextTime result : UInt64) (total : Vector) :
    AdvanceFrameAt (advanceContinuedFrame frame fuel n trials nextTime result total)
      (fuel - 1) n trials nextTime result result outputTime outputRoot done total := by
  cases h
  constructor <;> simp_all [advanceContinuedFrame]

def advanceMeasure (frame : Locals) : Nat :=
  if frame.locals[17]? = some (.i64 1) then 0
  else match (frame.params[0]? : Option Wasm.Value) with
    | some (.i64 fuel) => fuel.toNat + 1 | _ => 0

theorem AdvanceFrameAt.measure {frame : Locals} {fuel : UInt64} {n : Nat}
    {trials time source tracker outputTime outputRoot : UInt64} {done : Bool} {boundary : Vector}
    (h : AdvanceFrameAt frame fuel n trials time source tracker outputTime outputRoot done boundary) :
    advanceMeasure frame = if done then 0 else fuel.toNat + 1 := by
  cases done <;> simp [advanceMeasure, h.done, h.params, boolWord, advanceParams]

#print axioms AdvanceFrameAt.time
#print axioms AdvanceFrameAt.scan
#print axioms AdvanceFrameAt.trial
#print axioms AdvanceFrameAt.accumulated
#print axioms AdvanceFrameAt.continued
#print axioms AdvanceFrameAt.measure
end Project.EulerCertificate.Execution
