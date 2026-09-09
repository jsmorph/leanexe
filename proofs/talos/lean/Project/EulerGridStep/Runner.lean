import Project.EulerGridStep.Spec

namespace Project.EulerGridStep.Runner
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Copy only the three conservative fields, never the status or diagnostics. -/
def nextGrid (cells : Nat) (output : Array UInt64) : Array UInt64 :=
  Array.ofFn (fun j : Fin (3 * cells) => output[1 + 6 * (j.val / 3) + j.val % 3]!)

@[simp] theorem nextGrid_size (cells : Nat) (output : Array UInt64) :
    (nextGrid cells output).size = 3 * cells := by simp [nextGrid]

theorem nextGrid_field (cells : Nat) (output : Array UInt64) (index field : Nat)
    (hi : index < cells) (hf : field < 3) :
    (nextGrid cells output)[3 * index + field]! = output[1 + 6 * index + field]! := by
  have hlt : 3 * index + field < 3 * cells := by omega
  have hd : (3 * index + field) / 3 = index := by omega
  have hm : (3 * index + field) % 3 = field := by omega
  simp [nextGrid, getElem!_pos, hlt, hd, hm]

noncomputable def GridSafe (cells : Nat) (grid : Array UInt64) : Prop :=
  grid.size = 3 * cells ∧ ∀ index < cells, ∃ pressure,
    Project.EulerCellStep.Safety.StateSafety grid[3 * index]! grid[3 * index + 1]!
      grid[3 * index + 2]! pressure

theorem nextGrid_safe (cells : Nat) (output : Array UInt64)
    (h : ∀ index < cells, Safety.OutputSafety output index) : GridSafe cells (nextGrid cells output) := by
  refine ⟨nextGrid_size _ _, ?_⟩
  intro index hi
  refine ⟨output[1 + 6 * index + 3]!, ?_⟩
  have hs := (h index hi).1
  have h0 := nextGrid_field cells output index 0 hi (by decide)
  simp only [Nat.add_zero] at h0
  have h1 := nextGrid_field cells output index 1 hi (by decide)
  have h2 := nextGrid_field cells output index 2 hi (by decide)
  simpa only [Nat.add_zero, h0, h1, h2] using hs

/-- A rejected output stops the run before its partial payload is copied. -/
def run : List UInt64 → Array UInt64 → Option (List (Array UInt64))
  | [], _ => some []
  | ratio :: ratios, input =>
    let output := Model.stepCheckedBits ratio input
    if output[0]! == 0 then
      (run ratios (nextGrid (input.size / 3) output)).map (output :: ·)
    else none

/-- Every accepted step records the exact IEEE output, its diagnostics, and
    the conservative grid supplied to the next step. -/
inductive SafeTrace : Nat → Array UInt64 → List UInt64 → List (Array UInt64) → Prop
  | nil (cells input) : SafeTrace cells input [] []
  | cons {cells input ratio ratios output outputs}
      (exactOutput : output = Model.stepCheckedBits ratio input)
      (accepted : output[0]! = 0)
      (size : output.size = 1 + 6 * cells)
      (safeOutput : ∀ index < cells, Safety.OutputSafety output index)
      (safeNext : GridSafe cells (nextGrid cells output))
      (rest : SafeTrace cells (nextGrid cells output) ratios outputs) :
      SafeTrace cells input (ratio :: ratios) (output :: outputs)

/-- Generic finite-run theorem; the list of raw time-step ratios is arbitrary. -/
theorem run_exact_safe (cells : Nat) (ratios : List UInt64) (input : Array UInt64)
    (hsize : input.size = 3 * cells) (outputs : List (Array UInt64))
    (h : run ratios input = some outputs) : SafeTrace cells input ratios outputs := by
  induction ratios generalizing input outputs with
  | nil =>
    simp only [run, Option.some.injEq] at h
    subst outputs
    exact .nil cells input
  | cons ratio ratios ih =>
    simp only [run] at h
    split at h
    · rename_i ha
      obtain ⟨tail, ht, heq⟩ := Option.map_eq_some_iff.mp h
      subst outputs
      have hdiv : input.size / 3 = cells := by omega
      have haccept : (Model.stepCheckedBits ratio input)[0]! = 0 := beq_iff_eq.mp ha
      have hs := Safety.step_accepted_safe ratio input haccept
      rw [hdiv] at hs
      apply SafeTrace.cons rfl haccept
      · simpa only [hdiv] using Safety.step_accepted_size ratio input haccept
      · exact hs
      · exact nextGrid_safe cells _ hs
      · apply ih _ (nextGrid_size cells _) _
        simpa only [hdiv] using ht
    · contradiction

#print axioms nextGrid_safe
#print axioms run_exact_safe
end Project.EulerGridStep.Runner
