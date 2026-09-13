import Project.EulerRiemann.ControlTime

namespace Project.EulerRiemann.Control
open Traversal
open Project.Euler2DCellStep.Sweep (Grid)

inductive NumericalTrace (n : Nat) :
    UInt64 → Grid n n → List UInt64 → UInt64 → Grid n n → Prop
  | nil (time grid) : NumericalTrace n time grid [] time grid
  | cons {time grid dt next dts finalTime finalGrid}
      (advance : Time.validAdvance time dt = true)
      (step : Numerics.step
        (Wasm.IEEE64.div dt (Time.spacing n)) grid = some next)
      (tail : NumericalTrace n (Wasm.IEEE64.add time dt) next dts finalTime finalGrid) :
      NumericalTrace n time grid (dt :: dts) finalTime finalGrid

theorem NumericalTrace.length_le {n : Nat} {time finalTime : UInt64}
    {grid finalGrid : Grid n n} {dts : List UInt64}
    (h : NumericalTrace n time grid dts finalTime finalGrid) :
    dts.length + time.toNat ≤ finalTime.toNat := by
  induction h with
  | nil => simp
  | cons ha _ _ ih =>
    have hlt := (Time.validAdvance_bounds _ _ ha).1
    change UInt64.toNat _ < UInt64.toNat _ at hlt
    simp only [List.length_cons]
    omega

theorem advance_trace (fuel n : Nat) (time : UInt64) (grid : Array Cell)
    (hg : Indexed n grid) :
    ∃ dts, NumericalTrace n time (asGrid n grid) dts
        (advance fuel n time grid).time (asGrid n (advance fuel n time grid).grid) ∧
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
            ((Time.proposal n time (scan grid).alpha).toNat + 1)
            n time (Time.proposal n time (scan grid).alpha) grid
          have hat : trial.status = 0 := by simpa only [trial, beq_iff_eq] using ha
          have hi := retry_indexed _ _ _ _ _ hg hat
          obtain ⟨dts, htrace, hlen⟩ := ih (Wasm.IEEE64.add time trial.dt) trial.grid hi
          exact ⟨trial.dt :: dts,
            .cons (retry_success _ _ _ _ _ hat).1 (retry_asGrid _ _ _ _ _ hg hat) htrace,
            by simpa using Nat.succ_le_succ hlen⟩
        · exact ⟨[], .nil _ _, by simp⟩
      · exact ⟨[], .nil _ _, by simp⟩

theorem run_trace (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) :
    ∃ dts, NumericalTrace n 0 (Initial.initial n) dts
        (run n).time (asGrid n (run n).grid) ∧
      dts.length ≤ (run n).time.toNat := by
  obtain ⟨dts, ht, _⟩ := advance_trace (Time.endTime.toNat + 1) n 0
    (initialCells n) (initialCells_indexed n hn)
  have he : run n = advance (Time.endTime.toNat + 1) n 0 (initialCells n) := by
    unfold run
    rw [if_pos hn]
  rw [initialCells_asGrid n hn, ← he] at ht
  exact ⟨dts, ht, by simpa using ht.length_le⟩

#print axioms NumericalTrace.length_le
#print axioms advance_trace
#print axioms run_trace

end Project.EulerRiemann.Control
