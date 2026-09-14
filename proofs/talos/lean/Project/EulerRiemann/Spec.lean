import Project.EulerRiemann.SolveInitial
import Project.EulerRiemann.ControlSafe
import Project.EulerRiemann.ControlTrace
import Project.EulerRiemann.Hyperbolicity
import Project.EulerRiemann.NumericsTraceBalance

namespace Project.EulerRiemann.Spec
open Wasm

def ResultAt (n : Nat) (final : Store Unit) (values : List Value) : Prop :=
  ∃ pointer : UInt64, values = [.i64 pointer] ∧
    Project.ProofKit.UInt64Array.At final pointer (Control.solve n) ∧
    final.mem.pages * 65536 ≤ 536870912

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (n : Nat), 2 ≤ n ∧ n ≤ 800 →
    TerminatesWith env m 103 (m.initialStore (α := Unit)) [.i64 (UInt64.ofNat n)] (ResultAt n)

def Successful (n : Nat) : Prop :=
  (Control.solve n)[0]? = some 0 →
    (Control.run n).time = Time.endTime ∧
    ∃ dts, Control.NumericalTrace n 0 (Initial.initial n) dts Time.endTime
      (Traversal.asGrid n (Control.run n).grid) ∧ dts.length ≤ Time.endTime.toNat

theorem source_success (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800) : Successful n := by
  have hStatusWord : (Control.solve n)[0]? = some (Control.run n).status := by
    simp [Control.solve, Output.pack]
  intro hZero
  have hStatus : (Control.run n).status = 0 := by
    rw [hStatusWord] at hZero
    exact Option.some.inj hZero
  have hTime := Control.run_terminal n hStatus
  obtain ⟨dts, hTrace, hLength⟩ := Control.run_trace n hn
  rw [hTime] at hTrace hLength
  exact ⟨hTime, dts, hTrace, hLength⟩

noncomputable def SafeSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (n : Nat), 2 ≤ n ∧ n ≤ 800 →
    TerminatesWith env m 103 (m.initialStore (α := Unit)) [.i64 (UInt64.ofNat n)]
      (fun final values => ResultAt n final values ∧
        Control.CellsSafe (Control.run n).grid ∧ Successful n)

theorem solve_exact : ExactSpecFor module := by
  intro env n hn
  refine TerminatesWith.mono (Execution.solve_initial_exact env n hn) ?_
  rintro final values ⟨heap, result, hValues, _, hOwner, hPages⟩
  exact ⟨result.root, hValues, hOwner.buffer.values, by omega⟩

theorem solve_success : SafeSpecFor module := by
  intro env n hn
  refine TerminatesWith.mono (solve_exact env n hn) ?_
  intro final values hResult
  exact ⟨hResult, Control.run_safe n hn, source_success n hn⟩

noncomputable def HyperbolicSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (n : Nat), 2 ≤ n ∧ n ≤ 800 →
    TerminatesWith env m 103 (m.initialStore (α := Unit)) [.i64 (UInt64.ofNat n)]
      (fun final values => ResultAt n final values ∧
        Control.CellsSafe (Control.run n).grid ∧ Successful n ∧
        Hyperbolicity.CellsHyperbolic (Control.run n).grid ∧
        Hyperbolicity.TraceHyperbolic n)

theorem solve_hyperbolic : HyperbolicSpecFor module := by
  intro env n hn
  refine TerminatesWith.mono (solve_success env n hn) ?_
  rintro final values ⟨hResult, hSafe, hSuccess⟩
  exact ⟨hResult, hSafe, hSuccess, Hyperbolicity.cells_hyperbolic _ hSafe,
    Hyperbolicity.initial_trace_hyperbolic n⟩

noncomputable def BalanceSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (n : Nat) (hn : 2 ≤ n ∧ n ≤ 800),
    TerminatesWith env m 103 (m.initialStore (α := Unit)) [.i64 (UInt64.ofNat n)]
      (fun final values => ResultAt n final values ∧
        Control.CellsSafe (Control.run n).grid ∧ Successful n ∧
        Conservation.RunBalance n (by omega))

theorem solve_balance : BalanceSpecFor module := by
  intro env n hn
  refine TerminatesWith.mono (solve_success env n hn) ?_
  rintro final values ⟨hResult, hSafe, hSuccess⟩
  exact ⟨hResult, hSafe, hSuccess, Conservation.run_balance n (by omega) hn⟩

#print axioms source_success
#print axioms solve_exact
#print axioms solve_success
#print axioms solve_hyperbolic
#print axioms solve_balance

end Project.EulerRiemann.Spec
