import Project.EulerReconstructed.FrozenSolveInitial
import Project.EulerReconstructed.FrozenTraceSafety
import Project.EulerReconstructed.FrozenPhysicalTrace

namespace Project.EulerReconstructed.Frozen.Spec
open Wasm
open Project.EulerRiemann.Frozen.Control (CellsSafe)
open Project.EulerRiemann.Frozen.Hyperbolicity (CellsHyperbolic cells_hyperbolic)
open Project.EulerRiemann.Frozen

def ResultAt (n trials : Nat) (final : Store Unit) (values : List Value) : Prop :=
  ∃ pointer : UInt64, values = [.i64 pointer] ∧
    Project.ProofKit.UInt64Array.At final pointer (Control.solve n trials) ∧
    final.mem.pages * 65536 ≤ 536870912

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (n : Nat) (trials : UInt64), 2 ≤ n ∧ n ≤ 800 →
    TerminatesWith env m 148 (m.initialStore (α := Unit)) [.i64 trials, .i64 (UInt64.ofNat n)]
      (ResultAt n trials.toNat)

def Successful (n trials : Nat) : Prop :=
  (Control.solve n trials)[0]? = some 0 →
    (Control.run n trials).time = Time.endTime ∧
    ∃ dts, Control.NumericalTrace n trials 0 (Project.EulerRiemann.Frozen.Traversal.initialCells n)
      dts Time.endTime (Control.run n trials).grid ∧ dts.length ≤ Time.endTime.toNat

theorem source_success (n trials : Nat) (hn : 2 ≤ n ∧ n ≤ 800) : Successful n trials := by
  have hStatusWord : (Control.solve n trials)[0]? = some (Control.run n trials).status := by
    simp [Control.solve, Output.pack]
  intro hZero
  have hStatus : (Control.run n trials).status = 0 := by
    rw [hStatusWord] at hZero
    exact Option.some.inj hZero
  have hTime := Control.run_terminal n trials hStatus
  obtain ⟨dts, hTrace, hLength⟩ := Control.run_trace n trials hn
  rw [hTime] at hTrace hLength
  exact ⟨hTime, dts, hTrace, hLength⟩

noncomputable def SafeSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (n : Nat) (trials : UInt64), 2 ≤ n ∧ n ≤ 800 →
    TerminatesWith env m 148 (m.initialStore (α := Unit)) [.i64 trials, .i64 (UInt64.ofNat n)]
      (fun final values => ResultAt n trials.toNat final values ∧
        CellsSafe (Control.run n trials.toNat).grid ∧ Successful n trials.toNat)

theorem solve_exact : ExactSpecFor module := by
  intro env n trials hn
  refine TerminatesWith.mono (Execution.solve_initial_exact env n trials hn) ?_
  rintro final values ⟨heap, result, hValues, _, hOwner, hPages⟩
  exact ⟨result.root, hValues, hOwner.buffer.values, by omega⟩

theorem solve_success : SafeSpecFor module := by
  intro env n trials hn
  refine TerminatesWith.mono (solve_exact env n trials hn) ?_
  intro final values hResult
  exact ⟨hResult, Control.run_safe n trials.toNat hn, source_success n trials.toNat hn⟩

noncomputable def HyperbolicSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (n : Nat) (trials : UInt64), 2 ≤ n ∧ n ≤ 800 →
    TerminatesWith env m 148 (m.initialStore (α := Unit)) [.i64 trials, .i64 (UInt64.ofNat n)]
      (fun final values => ResultAt n trials.toNat final values ∧
        CellsSafe (Control.run n trials.toNat).grid ∧ Successful n trials.toNat ∧
        CellsHyperbolic (Control.run n trials.toNat).grid ∧ Numerics.TraceFacts n trials.toNat)

theorem solve_hyperbolic : HyperbolicSpecFor module := by
  intro env n trials hn
  refine TerminatesWith.mono (solve_success env n trials hn) ?_
  rintro final values ⟨hResult, hSafe, hSuccess⟩
  exact ⟨hResult, hSafe, hSuccess, cells_hyperbolic _ hSafe,
    Numerics.initial_trace_facts n trials.toNat hn⟩

noncomputable def BalanceSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (n : Nat) (trials : UInt64) (hn : 2 ≤ n ∧ n ≤ 800),
    TerminatesWith env m 148 (m.initialStore (α := Unit)) [.i64 trials, .i64 (UInt64.ofNat n)]
      (fun final values => ResultAt n trials.toNat final values ∧
        CellsSafe (Control.run n trials.toNat).grid ∧ Successful n trials.toNat ∧
        CellsHyperbolic (Control.run n trials.toNat).grid ∧ Numerics.TraceFacts n trials.toNat ∧
        Conservation.RunBalance n trials.toNat (by omega) ∧
        Conservation.PhysicalRunBalance n trials.toNat (by omega))

theorem solve_balance : BalanceSpecFor module := by
  intro env n trials hn
  refine TerminatesWith.mono (solve_hyperbolic env n trials hn) ?_
  rintro final values ⟨hResult, hSafe, hSuccess, hHyperbolic, hTrace⟩
  exact ⟨hResult, hSafe, hSuccess, hHyperbolic, hTrace,
    Conservation.run_balance n trials.toNat (by omega) hn,
    Conservation.physical_run_balance n trials.toNat (by omega) hn⟩

#print axioms source_success
#print axioms solve_exact
#print axioms solve_success
#print axioms solve_hyperbolic
#print axioms solve_balance
end Project.EulerReconstructed.Frozen.Spec
