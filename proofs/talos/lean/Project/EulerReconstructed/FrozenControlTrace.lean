import Project.EulerReconstructed.FrozenControlSafe

namespace Project.EulerReconstructed.Frozen.Control
open Project.EulerRiemann.Frozen
open Project.EulerRiemann.Frozen.Traversal (Cell initialCells)
open Project.EulerReconstructed.Frozen.Traversal (step)

def AcceptedStep (n trials : Nat) (dt : UInt64) (grid next : Array Cell) : Prop :=
  let stats := OutwardMaximum.gridUpper grid
  let ratio := OutwardCfl.gridRatioChecked n dt stats.value
  stats.status = 0 ∧ ratio.status = 0 ∧
    Project.EulerRiemann.Frozen.Traversal.accepted next = true ∧
    next = step n trials ratio.value grid

inductive NumericalTrace (n trials : Nat) :
    UInt64 → Array Cell → List UInt64 → UInt64 → Array Cell → Prop
  | nil (time grid) : NumericalTrace n trials time grid [] time grid
  | cons {time grid dt next dts finalTime finalGrid}
      (advance : Time.validAdvance time dt = true)
      (step : AcceptedStep n trials dt grid next)
      (tail : NumericalTrace n trials (Wasm.IEEE64.add time dt) next dts finalTime finalGrid) :
      NumericalTrace n trials time grid (dt :: dts) finalTime finalGrid

theorem NumericalTrace.length_le {n trials : Nat} {time finalTime : UInt64}
    {grid finalGrid : Array Cell} {dts : List UInt64}
    (h : NumericalTrace n trials time grid dts finalTime finalGrid) :
    dts.length + time.toNat ≤ finalTime.toNat := by
  induction h with
  | nil => simp
  | cons ha _ _ ih =>
    have hlt := (Time.validAdvance_bounds _ _ ha).1
    change UInt64.toNat _ < UInt64.toNat _ at hlt
    simp only [List.length_cons]
    omega

theorem advance_trace (fuel n trials : Nat) (time : UInt64) (grid : Array Cell) :
    ∃ dts, NumericalTrace n trials time grid dts
        (advance fuel n trials time grid).time (advance fuel n trials time grid).grid ∧
      dts.length ≤ fuel := by
  induction fuel generalizing time grid with
  | zero => exact ⟨[], .nil _ _, by simp⟩
  | succ fuel ih =>
    simp only [advance]
    split
    · exact ⟨[], .nil _ _, by simp⟩
    · split
      · split
        · rename_i ht hs ha
          let trial := retry
            ((Time.proposal n time (OutwardMaximum.gridUpper grid).value).toNat + 1)
            n trials time (Time.proposal n time (OutwardMaximum.gridUpper grid).value)
            (OutwardMaximum.gridUpper grid).value grid
          have hat : trial.status = 0 := by simpa only [trial, beq_iff_eq] using ha
          obtain ⟨hTime, hRatio, hAccepted, hGrid⟩ := retry_success _ _ _ _ _ _ _ hat
          obtain ⟨dts, hTrace, hLength⟩ := ih (Wasm.IEEE64.add time trial.dt) trial.grid
          refine ⟨trial.dt :: dts, .cons hTime ?_ hTrace, by simpa using Nat.succ_le_succ hLength⟩
          exact ⟨by simpa only [beq_iff_eq] using hs, hRatio, hAccepted, hGrid⟩
        · exact ⟨[], .nil _ _, by simp⟩
      · exact ⟨[], .nil _ _, by simp⟩

theorem run_trace (n trials : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    ∃ dts, NumericalTrace n trials 0 (initialCells n) dts (run n trials).time (run n trials).grid ∧
      dts.length ≤ (run n trials).time.toNat := by
  obtain ⟨dts, ht, _⟩ := advance_trace (Time.endTime.toNat + 1) n trials 0 (initialCells n)
  have he : run n trials = advance (Time.endTime.toNat + 1) n trials 0 (initialCells n) := by
    unfold run
    rw [if_pos hn]
  rw [← he] at ht
  exact ⟨dts, ht, by simpa using ht.length_le⟩

#print axioms NumericalTrace.length_le
#print axioms advance_trace
#print axioms run_trace
end Project.EulerReconstructed.Frozen.Control
