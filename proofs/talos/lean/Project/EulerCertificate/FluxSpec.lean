import Project.EulerCertificate.Flux
import Project.ProofKit.F64IntervalComposition
import Project.EulerRiemann.RealRusanov
import Project.EulerRiemann.OutwardConstants

namespace Project.EulerCertificate.Flux
open Project.ProofKit.F64Interval
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DConservative.Guard (decodedState)
open Project.EulerRiemann
open Project.EulerRiemann.OutwardSpeed (half_value)
open CodeLib.IEEE64
set_option exponentiation.threshold 4096

private theorem two_value : value 0x4000000000000000 = (2 : ℝ) := by
  change ((2^1075 : Nat) : ℝ) / (2 : ℝ)^1074 = 2
  norm_num

private theorem five_value : value 0x4014000000000000 = (5 : ℝ) := by
  change ((5 * 2^1074 : Nat) : ℝ) / (2 : ℝ)^1074 = 5
  norm_num

theorem pressure_valid (q : State) : Valid (pressure q)
    (Project.Euler2DConservative.Guard.pressure (decodedState q.density q.mx q.my q.energy)) := by
  have h := (((point_valid q.energy).sub
    ((((point_valid q.mx).scale q.mx).add ((point_valid q.my).scale q.my)).divPositive
      q.density |>.scale 0x3FE0000000000000)).scale 0x4000000000000000).divPositive
        0x4014000000000000
  rw [half_value, two_value, five_value] at h
  have he : (value q.energy - (value q.mx * value q.mx + value q.my * value q.my) /
      value q.density * (1 / 2)) * 2 / 5 =
      Project.Euler2DConservative.Guard.pressure (decodedState q.density q.mx q.my q.energy) := by
    simp only [Project.Euler2DConservative.Guard.pressure,
      Project.Euler2DConservative.Guard.internalEnergy, decodedState, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    ring
  rw [he] at h
  exact h

def get (v : Vector) (i : Fin 4) : Bounds := ![v.mass, v.momentum, v.transverse, v.energy] i

def words (q : State) (i : Fin 4) : UInt64 := ![q.density, q.mx, q.my, q.energy] i

theorem words_value (q : State) (i : Fin 4) :
    value (words q i) = decodedState q.density q.mx q.my q.energy i := by
  fin_cases i <;> rfl

theorem physical_valid (q : State) (i : Fin 4) :
    Valid (get (physical q) i)
      (RealRusanov.physicalFlux (decodedState q.density q.mx q.my q.energy) i) := by
  fin_cases i <;> simp only [get, physical, RealRusanov.physicalFlux, decodedState,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  · exact point_valid q.mx
  · have h := (((point_valid q.mx).scale q.mx).divPositive q.density).add (pressure_valid q)
    simpa [get, physical, RealRusanov.physicalFlux, decodedState, pow_two] using h
  · exact ((point_valid q.mx).scale q.my).divPositive q.density
  · have h := ((point_valid q.energy).add (pressure_valid q) |>.scale q.mx).divPositive q.density
    rw [mul_div_assoc] at h
    exact h

theorem component_valid (alpha left right : UInt64) (leftFlux rightFlux : Bounds)
    (x y : ℝ) (hl : Valid leftFlux x) (hr : Valid rightFlux y) :
    Valid (component alpha left right leftFlux rightFlux)
      ((x + y) / 2 - value alpha * (value right - value left) / 2) := by
  have h := ((hl.add hr).scale 0x3FE0000000000000).sub
    ((((point_valid right).sub (point_valid left)).scale alpha).scale 0x3FE0000000000000)
  rw [half_value] at h
  have he : (x + y) * (1 / 2) - (value right - value left) * value alpha * (1 / 2) =
      (x + y) / 2 - value alpha * (value right - value left) / 2 := by ring
  rw [he] at h
  exact h

theorem get_interface (alpha : UInt64) (left right : State) (i : Fin 4) :
    get (interface alpha left right) i = component alpha (words left i) (words right i)
      (get (physical left) i) (get (physical right) i) := by
  fin_cases i <;> simp only [get, interface, words, Matrix.cons_val_zero',
    Matrix.cons_val_succ']

theorem interface_valid (alpha : UInt64) (left right : State) (i : Fin 4) :
    Valid (get (interface alpha left right) i)
      (RealRusanov.interfaceFlux (value alpha)
        (decodedState left.density left.mx left.my left.energy)
        (decodedState right.density right.mx right.my right.energy) i) := by
  rw [get_interface]
  have h := component_valid alpha (words left i) (words right i)
    (get (physical left) i) (get (physical right) i) _ _
    (physical_valid left i) (physical_valid right i)
  simpa only [words_value, RealRusanov.interfaceFlux] using h

#print axioms pressure_valid
#print axioms physical_valid
#print axioms component_valid
#print axioms interface_valid
end Project.EulerCertificate.Flux
