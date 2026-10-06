import Examples.Euler.Verify
import Examples.Euler.RealState
import Examples.Euler.Equations.CharacteristicSpeed

/-! The first-order solver's signal speed can underestimate the exact characteristic speed.  At the
admissible state of density 1, zero momenta, and total energy 1, `side` accepts and returns a speed
whose value is below the exact sound speed `√(14/25)`, so the exact speed `|u| + c` exceeds it.
The reconstructed solver computes its speeds with outward rounding instead, which `speedUpper_ge`
proves to bound the exact speed.  The compiled `side` export returns these words on every run. -/

namespace Examples.Euler.SpeedCounterexample

open Examples.Euler LeanExe.Pipeline
open CodeLib.IEEE64 (value)

set_option exponentiation.threshold 4096

/-- The side computation at the state `(1, 0, 0, 1)`. -/
def result : Side := side 1.0 0.0 0.0 1.0

theorem accepted : result.status = 0 := by decide +kernel

theorem speed_word : result.speed.toBits = 0x3FE7F254DAB9CC3A := by decide +kernel

noncomputable def state : Equations.Vec4 := ![1, 0, 0, 1]

theorem state_admissible : Equations.Admissible state := by
  change 0 < (1 : ℝ) ∧ 0 < (2/5 : ℝ) * (1 - (0^2 + 0^2) / (2 * 1))
  norm_num

theorem state_eq_vec : state = vec ⟨1.0, 0.0, 0.0, 1.0⟩ := by
  have hOne : value (1.0 : Float).toBits = (1 : ℝ) := by
    rw [show (1.0 : Float).toBits = 0x3FF0000000000000 by decide +kernel]
    change ((2^1074 : Nat) : ℝ) / (2 : ℝ)^1074 = 1
    norm_num
  have hZero : value (0.0 : Float).toBits = (0 : ℝ) := by
    rw [show (0.0 : Float).toBits = 0 by decide +kernel]
    change ((0 : Int) : ℝ) / (2 : ℝ)^1074 = 0
    norm_num
  funext i
  fin_cases i
  · exact hOne.symm
  · exact hZero.symm
  · exact hZero.symm
  · exact hOne.symm

theorem sound_speed : Equations.soundSpeed state = Real.sqrt (14/25 : ℝ) := by
  apply congrArg Real.sqrt
  change (7/5 : ℝ) * ((2/5) * (1 - (0^2 + 0^2) / (2 * 1))) / 1 = 14/25
  norm_num

/-- The accepted speed is below the exact sound speed, and so below the exact characteristic
speed in the x direction. -/
theorem speed_below_sound : real result.speed < Equations.soundSpeed state := by
  rw [real, speed_word, sound_speed]
  apply Real.lt_sqrt_of_sq_lt
  change ((((0x17F254DAB9CC3A * 2^1021 : Nat) : ℝ) / (2 : ℝ)^1074)^2 < 14/25)
  norm_num

theorem speed_below_characteristic :
    real result.speed < Equations.characteristicSpeed ![1, 0] state :=
  speed_below_sound.trans_le (le_add_of_nonneg_left (abs_nonneg _))

/-- The bytes of `euler.module` decode to a module whose `side` export, function 4, returns the
words of `result` on every run, without a trap. -/
theorem module_side : ∃ bytes, Wasm.Encoding.encode euler.module = .ok bytes ∧
    ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ ImplementsPureA false m 4 sideTuple := by
  obtain ⟨bytes, success, decoded⟩ := euler_round_trip
  exact ⟨bytes, success, euler.module, decoded, side_implements⟩

end Examples.Euler.SpeedCounterexample
