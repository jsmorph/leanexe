import Project.EulerRiemann.Numerics
import Project.Euler2DConservative.RealCharacteristicSpeed

namespace Project.EulerRiemann.SpeedCounterexample
open CodeLib.IEEE64
open Project.Euler2DConservative

set_option exponentiation.threshold 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def side := Numerics.sideCheckedBits 0x3FF0000000000000 0 0 0x3FF0000000000000

theorem accepted : side.status = 0 := by decide +kernel

theorem speed_word : side.speed = 0x3FE7F254DAB9CC3A := by decide +kernel

noncomputable def state : Guard.Vec4 := ![1, 0, 0, 1]

theorem state_admissible : Guard.Admissible state := by
  change 0 < (1 : ℝ) ∧ 0 < (2/5 : ℝ)*(1-(0^2+0^2)/(2*1))
  norm_num

theorem sound_speed : RealFlux.soundSpeed state = Real.sqrt (14/25 : ℝ) := by
  apply congrArg Real.sqrt
  change (7/5 : ℝ)*((2/5)*(1-(0^2+0^2)/(2*1)))/1 = 14/25
  norm_num

theorem state_eq_decoded :
    state = Guard.decodedState 0x3FF0000000000000 0 0 0x3FF0000000000000 := by
  have hOne : value 0x3FF0000000000000 = (1 : ℝ) := by
    change ((2^1074 : Nat) : ℝ)/(2 : ℝ)^1074 = 1
    norm_num
  have hZero : value 0 = (0 : ℝ) := by
    change ((0 : Int) : ℝ)/(2 : ℝ)^1074 = 0
    norm_num
  funext i
  fin_cases i
  · exact hOne.symm
  · exact hZero.symm
  · exact hZero.symm
  · exact hOne.symm

theorem speed_below_sound : value side.speed < RealFlux.soundSpeed state := by
  rw [speed_word, sound_speed]
  apply Real.lt_sqrt_of_sq_lt
  change ((((0x17F254DAB9CC3A * 2^1021 : Nat) : ℝ) / (2 : ℝ)^1074)^2 < 14/25)
  norm_num

#print axioms accepted
#print axioms speed_word
#print axioms speed_below_sound
end Project.EulerRiemann.SpeedCounterexample
