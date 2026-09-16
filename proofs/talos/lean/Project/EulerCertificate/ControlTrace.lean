import Project.EulerCertificate.ControlBoundary

namespace Project.EulerCertificate.Control
open Project.EulerRiemann
open Project.EulerRiemann.Traversal (Cell Indexed)
open Project.EulerReconstructed.Control (NumericalTrace)
open Project.EulerReconstructed.Conservation (traceRatio durationSum stepPhysicalBoundary)
open Project.EulerCertificate.Flux (Vector)

theorem advance_trace {n : Nat} (hn : 0 < n) (hmax : n ≤ 800) (fuel trials : Nat)
    (time : UInt64) (grid : Array Cell) (acc : Vector) (x : Fin 4 → ℝ)
    (hg : Indexed n grid) (hx : Vectors.Valid acc x) :
    let out := advance fuel n trials time grid acc
    ∃ dts, NumericalTrace n trials time grid dts out.time out.grid ∧
      Vectors.Valid out.boundary (fun i => x i +
        durationSum n trials (stepPhysicalBoundary hn trials) grid dts i) := by
  induction fuel generalizing time grid acc x with
  | zero => exact ⟨[], .nil _ _, by simpa only [advance, durationSum, add_zero] using hx⟩
  | succ fuel ih =>
    simp only [advance]
    split
    · exact ⟨[], .nil _ _, by simpa only [durationSum, add_zero] using hx⟩
    · split
      · split
        · rename_i ht hs ha
          let trial := retry
            ((Time.proposal n time (OutwardMaximum.gridUpper grid).value).toNat + 1)
            n trials time (Time.proposal n time (OutwardMaximum.gridUpper grid).value)
            (OutwardMaximum.gridUpper grid).value grid
          have hat : trial.status = 0 := by simpa only [trial, beq_iff_eq] using ha
          obtain ⟨hTime, hRatio, hAccepted, hGrid⟩ := retry_success _ _ _ _ _ _ _ hat
          have hb := retry_boundary_valid hn hmax _ trials time _ grid hg hat
          have hnxt : Indexed n trial.grid := by
            rw [hGrid]
            exact Project.EulerReconstructed.Traversal.step_indexed n trials _ grid hg
          obtain ⟨dts, hTrace, hValid⟩ := ih (Wasm.IEEE64.add time trial.dt) trial.grid
            (Vectors.add acc trial.boundary) (fun i => x i + stepPhysicalBoundary hn trials trial.dt grid i)
            hnxt (hx.add hb)
          refine ⟨trial.dt :: dts, .cons hTime ?_ hTrace, ?_⟩
          · exact ⟨by simpa only [beq_iff_eq] using hs, hRatio, hAccepted, hGrid⟩
          · have he : trial.grid = Project.EulerReconstructed.Traversal.step n trials
                (traceRatio n trial.dt grid) grid := hGrid
            intro i
            simp only [durationSum]
            rw [← he]
            simpa only [add_assoc] using hValid i
        · exact ⟨[], .nil _ _, by simpa only [durationSum, add_zero] using hx⟩
      · exact ⟨[], .nil _ _, by simpa only [durationSum, add_zero] using hx⟩

#print axioms advance_trace
end Project.EulerCertificate.Control
