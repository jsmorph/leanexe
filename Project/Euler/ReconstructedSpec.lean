import LeanExe.Examples.EulerReconstructed
import Project.Euler.Spec

/-! Properties of the reconstructed Euler solver's Lean definitions. -/

namespace Project.Euler

open LeanExe.Examples.Euler

/-- `reconstructedAdvanceWith` with its loop's test and step named. -/
theorem reconstructedAdvanceWith_loop (n trials : UInt64) (time dt alpha : Float)
    (grid : Array Cell) :
    ∃ (cond : UInt64 × Float × Array Cell → Bool)
      (step : UInt64 × Float × Array Cell → UInt64 × Float × Array Cell),
      (∀ x, cond x = (x.1 == 9)) ∧
      (∀ x, step x = reconstructedAttempt n trials time alpha grid x.2.1 x.2.2) ∧
      reconstructedAdvanceWith n trials time dt alpha grid =
        match LeanExe.repeatWhile 2048 ((9 : UInt64), dt, (#[] : Array Cell)) cond step with
        | (status, dt, trial) =>
          if status == 0 then ((0 : UInt64), time + dt, trial)
          else (if status == 9 then 4 else status, time, grid) := by
  refine ⟨_, _, ?_, ?_, rfl⟩ <;> intro _ <;> rfl

/-- `reconstructedRunFrom` with its loop's test and step named. -/
theorem reconstructedRunFrom_loop (n trials : UInt64) :
    ∃ (cond : UInt64 × Float × Array Cell → Bool)
      (step : UInt64 × Float × Array Cell → UInt64 × Float × Array Cell),
      (∀ x, cond x = (x.1 == 0 && x.2.1.toBits != endTime.toBits)) ∧
      (∀ x, step x = reconstructedAdvanceStep n trials x.2.1 x.2.2) ∧
      reconstructedRunFrom n trials =
        match LeanExe.repeatWhile 4294967296 ((0 : UInt64), (0 : Float), initialCells n) cond
          step with
        | (status, time, grid) =>
          if status == 0 && time.toBits != endTime.toBits then (5, time, grid)
          else (status, time, grid) := by
  refine ⟨_, _, ?_, ?_, rfl⟩ <;> intro _ <;> rfl

end Project.Euler
