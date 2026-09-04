import Project.EulerRusanov.InterfaceData

/-!
# Pure binary64 model for the fixed Euler--Rusanov quarter-step

This module mirrors the fixed source entry without using Lean's native
`Float` evaluator.  The three guarded flux calls use the already proved pure
Euler--Rusanov model.  Each conservative update then uses Talos's pure
`Wasm.IEEE64` operations in the exact source association:

`round(U - round((1/4) * round(F_right - F_left)))`.
-/

namespace Project.EulerRusanovStep.Model

open Wasm

set_option maxRecDepth 1048576
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 4096

/-- Seven public words in source structure order. -/
structure CheckedSodQuarterStepBits where
  status : UInt64
  leftDensity : UInt64
  leftMomentum : UInt64
  leftEnergy : UInt64
  rightDensity : UInt64
  rightMomentum : UInt64
  rightEnergy : UInt64
  deriving DecidableEq, Inhabited, Repr

def zeroBits : UInt64 := 0x0000000000000000
def oneBits : UInt64 := 0x3FF0000000000000
def eighthBits : UInt64 := 0x3FC0000000000000
def tenthBits : UInt64 := 0x3FB999999999999A
def quarterBits : UInt64 := 0x3FD0000000000000
def fiveHalvesBits : UInt64 := 0x4004000000000000
def signMask : UInt64 := 0x8000000000000000

/-- Pure binary64 meaning of one source update component. -/
def quarterUpdateComponentBits
    (state fluxLeft fluxRight : UInt64) : UInt64 :=
  let fluxDifference :=
    IEEE64.add fluxRight (fluxLeft ^^^ signMask)
  let scaledDifference :=
    IEEE64.mul quarterBits fluxDifference
  IEEE64.add state (scaledDifference ^^^ signMask)

/-- Fixed left-boundary flux call, directly mirroring the source arguments. -/
def sodLLFlux : Project.EulerRusanov.Model.CheckedFluxBits :=
  Project.EulerRusanov.Model.checkedFluxBitsModel
    oneBits zeroBits oneBits oneBits zeroBits oneBits

/-- Fixed interior flux call, directly mirroring the source arguments. -/
def sodLRFlux : Project.EulerRusanov.Model.CheckedFluxBits :=
  Project.EulerRusanov.Model.checkedFluxBitsModel
    oneBits zeroBits oneBits eighthBits zeroBits tenthBits

/-- Fixed right-boundary flux call, directly mirroring the source arguments. -/
def sodRRFlux : Project.EulerRusanov.Model.CheckedFluxBits :=
  Project.EulerRusanov.Model.checkedFluxBitsModel
    eighthBits zeroBits tenthBits eighthBits zeroBits tenthBits

/-- Total pure result of the fixed three-call source entry. -/
def sodQuarterStepCheckedBitsModel : CheckedSodQuarterStepBits :=
  let leftLeft := sodLLFlux
  let leftRight := sodLRFlux
  let rightRight := sodRRFlux
  if leftLeft.status == zeroBits &&
      leftRight.status == zeroBits &&
      rightRight.status == zeroBits then
    { status := zeroBits
      leftDensity := quarterUpdateComponentBits
        oneBits leftLeft.mass leftRight.mass
      leftMomentum := quarterUpdateComponentBits
        zeroBits leftLeft.momentum leftRight.momentum
      leftEnergy := quarterUpdateComponentBits
        fiveHalvesBits leftLeft.energy leftRight.energy
      rightDensity := quarterUpdateComponentBits
        eighthBits leftRight.mass rightRight.mass
      rightMomentum := quarterUpdateComponentBits
        zeroBits leftRight.momentum rightRight.momentum
      rightEnergy := quarterUpdateComponentBits
        quarterBits leftRight.energy rightRight.energy }
  else
    { status := 1
      leftDensity := zeroBits
      leftMomentum := zeroBits
      leftEnergy := zeroBits
      rightDensity := zeroBits
      rightMomentum := zeroBits
      rightEnergy := zeroBits }

/-- Frozen expected output of the pure model and future exact artifact. -/
def expectedSodQuarterStepBits : CheckedSodQuarterStepBits :=
  { status := 0x0000000000000000
    leftDensity := 0x3FE9E00000000000
    leftMomentum := 0x3FBCCCCCCCCCCCCC
    leftEnergy := 0x4000100000000000
    rightDensity := 0x3FD4400000000000
    rightMomentum := 0x3FBCCCCCCCCCCCCE
    rightEnergy := 0x3FE7C00000000000 }

/-- Public words in source structure order. -/
def resultWords : List UInt64 :=
  let result := sodQuarterStepCheckedBitsModel
  [result.status,
    result.leftDensity, result.leftMomentum, result.leftEnergy,
    result.rightDensity, result.rightMomentum, result.rightEnergy]

/-- Talos operand stacks are top-first, so source result order is reversed. -/
def resultValues : List Wasm.Value :=
  let result := sodQuarterStepCheckedBitsModel
  [.i64 result.rightEnergy,
    .i64 result.rightMomentum,
    .i64 result.rightDensity,
    .i64 result.leftEnergy,
    .i64 result.leftMomentum,
    .i64 result.leftDensity,
    .i64 result.status]

private theorem sodLLFlux_expected :
    sodLLFlux = Project.EulerRusanov.InterfaceData.sodLL.expected := by
  simpa [sodLLFlux, zeroBits, oneBits,
    Project.EulerRusanov.InterfaceData.modelResult,
    Project.EulerRusanov.InterfaceData.sodLL] using
    Project.EulerRusanov.InterfaceData.sodLL_model

private theorem sodLRFlux_expected :
    sodLRFlux = Project.EulerRusanov.InterfaceData.sodLR.expected := by
  simpa [sodLRFlux, zeroBits, oneBits, eighthBits, tenthBits,
    Project.EulerRusanov.InterfaceData.modelResult,
    Project.EulerRusanov.InterfaceData.sodLR] using
    Project.EulerRusanov.InterfaceData.sodLR_model

private theorem sodRRFlux_expected :
    sodRRFlux = Project.EulerRusanov.InterfaceData.sodRR.expected := by
  simpa [sodRRFlux, zeroBits, eighthBits, tenthBits,
    Project.EulerRusanov.InterfaceData.modelResult,
    Project.EulerRusanov.InterfaceData.sodRR] using
    Project.EulerRusanov.InterfaceData.sodRR_model

/-- The independent pure model computes the seven frozen words exactly. -/
theorem sodQuarterStepCheckedBitsModel_exact :
    sodQuarterStepCheckedBitsModel = expectedSodQuarterStepBits := by
  simp only [sodQuarterStepCheckedBitsModel,
    sodLLFlux_expected, sodLRFlux_expected, sodRRFlux_expected]
  decide

#print axioms sodQuarterStepCheckedBitsModel_exact

end Project.EulerRusanovStep.Model
