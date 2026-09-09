import Project.Euler2DCellStep.Sweep

namespace Project.Euler2DCellStep.Runner
open Sweep

/-- First-order x then y splitting. Reject the proposed complete time step if either sweep rejects. -/
def step {nx ny : Nat} (ratio : UInt64) (grid : Grid nx ny) : Option (Grid nx ny) :=
  let x := outputs ratio false grid
  if Accepted x then
    let middle := nextGrid false x
    let y := outputs ratio true middle
    if Accepted y then some (nextGrid true y) else none
  else none

noncomputable def Transition {nx ny : Nat} (m : Wasm.Module) (ratio : UInt64)
    (before after : Grid nx ny) : Prop :=
  ∃ middle,
    middle = nextGrid false (outputs ratio false before) ∧
    after = nextGrid true (outputs ratio true middle) ∧
    Accepted (outputs ratio false before) ∧ Accepted (outputs ratio true middle) ∧
    GridSafe middle ∧ GridSafe after ∧
    Executes m ratio false before ∧ Executes m ratio true middle

theorem step_exact_safe {m : Wasm.Module} (hSpec : Spec.SafeSpecFor m)
    {nx ny : Nat} (ratio : UInt64) (before after : Grid nx ny)
    (h : step ratio before = some after) : Transition m ratio before after := by
  unfold step at h
  dsimp only at h
  split at h
  · rename_i hx
    split at h
    · rename_i hy
      have heq := Option.some.inj h
      subst after
      exact ⟨nextGrid false (outputs ratio false before), rfl, rfl, hx, hy,
        nextGrid_safe ratio false before hx, nextGrid_safe ratio true _ hy,
        executes hSpec ratio false before hx, executes hSpec ratio true _ hy⟩
    · contradiction
  · contradiction

def run {nx ny : Nat} : List UInt64 → Grid nx ny → Option (List (Grid nx ny))
  | [], _ => some []
  | ratio :: ratios, input =>
    match step ratio input with
    | none => none
    | some next => (run ratios next).map (next :: ·)

inductive Trace {nx ny : Nat} (m : Wasm.Module) :
    Grid nx ny → List UInt64 → List (Grid nx ny) → Prop
  | nil (input) : Trace m input [] []
  | cons {input next ratio ratios rest}
      (transition : Transition m ratio input next)
      (tail : Trace m next ratios rest) :
      Trace m input (ratio :: ratios) (next :: rest)

theorem run_exact_safe {m : Wasm.Module} (hSpec : Spec.SafeSpecFor m)
    {nx ny : Nat} (ratios : List UInt64) (input : Grid nx ny)
    (results : List (Grid nx ny)) (h : run ratios input = some results) :
    Trace m input ratios results := by
  induction ratios generalizing input results with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst results
    exact .nil input
  | cons ratio ratios ih =>
    simp only [run] at h
    split at h
    · contradiction
    · rename_i next hstep
      obtain ⟨tail, ht, heq⟩ := Option.map_eq_some_iff.mp h
      subst results
      exact .cons (step_exact_safe hSpec ratio input next hstep) (ih next tail ht)

/-- Stationary four-quadrant problem on the unit square; rho=p initially.
The stored energies are the rounded products 2.5*rho used by the native runner. -/
def initial (nx ny : Nat) : Grid nx ny := fun j i =>
  if i.val < nx/2 then
    if j.val < ny/2 then ⟨0x3FD0000000000000, 0, 0, 0x3FE4000000000000⟩
    else ⟨0x3FD999999999999A, 0, 0, 0x3FF0000000000000⟩
  else
    if j.val < ny/2 then ⟨0x3FE6666666666666, 0, 0, 0x3FFC000000000000⟩
    else ⟨0x3FF0000000000000, 0, 0, 0x4004000000000000⟩

theorem initial_safe (nx ny : Nat) : GridSafe (initial nx ny) := by
  have guarded (rho energy : UInt64)
      (h : Project.Euler2DConservative.Model.stateGuard rho 0 0 energy = true) :
      StateSafe ⟨rho, 0, 0, energy⟩ :=
    ⟨Project.Euler2DConservative.Guard.stateGuard_spec _ _ _ _ h,
      Project.Euler2DConservative.Guard.stateGuard_admissible _ _ _ _ h⟩
  intro j i
  dsimp only [initial]
  split <;> split <;> exact guarded _ _ (by decide)

noncomputable def RunnerSpecFor (m : Wasm.Module) : Prop :=
  ∀ nx ny ratios (input : Grid nx ny) results,
    run ratios input = some results → Trace m input ratios results

theorem runner_wat_exact_safe : RunnerSpecFor Project.Euler2DCellStep.«module» := by
  intro nx ny ratios input results h
  exact run_exact_safe Spec.cellCheckedBits_wat_safe ratios input results h

#print axioms initial_safe
#print axioms step_exact_safe
#print axioms run_exact_safe
#print axioms runner_wat_exact_safe
end Project.Euler2DCellStep.Runner
