import Project.EulerCertificate.Vectors
import Project.EulerCertificate.FluxSpec
import Project.ProofKit.F64NonnegativeMaximum

namespace Project.EulerCertificate.Vectors
open Project.EulerCertificate.Flux (Vector get words words_value)
open Project.Euler2DCellStep.Sweep (State)
open Project.Euler2DConservative.Guard (decodedState)

def Valid (a : Vector) (x : Fin 4 → ℝ) : Prop :=
  ∀ i, Project.ProofKit.F64Interval.Valid (get a i) (x i)

theorem get_state (q : State) (i : Fin 4) :
    get (state q) i = Project.ProofKit.F64Interval.point (words q i) := by
  fin_cases i <;> simp only [Flux.get, state, words, Matrix.cons_val_zero', Matrix.cons_val_succ']

theorem get_add (a b : Vector) (i : Fin 4) :
    get (add a b) i = Project.ProofKit.F64Interval.add (get a i) (get b i) := by
  fin_cases i <;> simp only [Flux.get, add, Matrix.cons_val_zero', Matrix.cons_val_succ']

theorem get_sub (a b : Vector) (i : Fin 4) :
    get (sub a b) i = Project.ProofKit.F64Interval.sub (get a i) (get b i) := by
  fin_cases i <;> simp only [Flux.get, sub, Matrix.cons_val_zero', Matrix.cons_val_succ']

theorem get_scale (a : Vector) (word : UInt64) (i : Fin 4) :
    get (scale a word) i = Project.ProofKit.F64Interval.scale (get a i) word := by
  fin_cases i <;> simp only [Flux.get, scale, Matrix.cons_val_zero', Matrix.cons_val_succ']

theorem get_divPositive (a : Vector) (word : UInt64) (i : Fin 4) :
    get (divPositive a word) i = Project.ProofKit.F64Interval.divPositive (get a i) word := by
  fin_cases i <;> simp only [Flux.get, divPositive, Matrix.cons_val_zero', Matrix.cons_val_succ']

theorem zero_valid : Valid zero (fun _ => 0) := by
  intro i
  have h := Project.ProofKit.F64Interval.point_valid (0 : UInt64)
  rw [Project.ProofKit.F64Order.zero_value] at h
  have hp : Project.ProofKit.F64Interval.point 0 = ⟨0, 0, 0⟩ := by decide
  rw [hp] at h
  fin_cases i <;> exact h

theorem state_valid (q : State) :
    Valid (state q) (decodedState q.density q.mx q.my q.energy) := by
  intro i
  rw [get_state, ← words_value]
  exact Project.ProofKit.F64Interval.point_valid (words q i)

theorem Valid.add {a b : Vector} {x y : Fin 4 → ℝ}
    (ha : Valid a x) (hb : Valid b y) : Valid (add a b) (fun i => x i + y i) := by
  intro i
  rw [get_add]
  exact (ha i).add (hb i)

theorem Valid.sub {a b : Vector} {x y : Fin 4 → ℝ}
    (ha : Valid a x) (hb : Valid b y) : Valid (sub a b) (fun i => x i - y i) := by
  intro i
  rw [get_sub]
  exact (ha i).sub (hb i)

theorem Valid.scale {a : Vector} {x : Fin 4 → ℝ}
    (ha : Valid a x) (word : UInt64) :
    Valid (scale a word) (fun i => x i * CodeLib.IEEE64.value word) := by
  intro i
  rw [get_scale]
  exact (ha i).scale word

theorem Valid.divPositive {a : Vector} {x : Fin 4 → ℝ}
    (ha : Valid a x) (word : UInt64) :
    Valid (divPositive a word) (fun i => x i / CodeLib.IEEE64.value word) := by
  intro i
  rw [get_divPositive]
  exact (ha i).divPositive word

#print axioms zero_valid
#print axioms state_valid
#print axioms Valid.add
#print axioms Valid.sub
#print axioms Valid.scale
#print axioms Valid.divPositive
end Project.EulerCertificate.Vectors
