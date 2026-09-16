import Project.EulerCertificate.SolveInitial
import Project.EulerCertificate.OutputSpec
import Project.EulerCertificate.ResidualBounds

namespace Project.EulerCertificate.Spec
open Wasm
open Project.EulerRiemann.Traversal (initialCells)
open Project.EulerReconstructed.Control (NumericalTrace)
open Project.EulerReconstructed.Conservation
open CodeLib.IEEE64 (value)

def ResultAt (n trials : Nat) (final : Store Unit) (values : List Value) : Prop :=
  ∃ pointer : UInt64, values = [.i64 pointer] ∧
    Project.ProofKit.UInt64Array.At final pointer (Solve.solve n trials) ∧
    final.mem.pages * 65536 ≤ 536870912

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (n : Nat) (trials : UInt64), 2 ≤ n ∧ n ≤ 800 →
    TerminatesWith env m 190 (m.initialStore (α := Unit)) [.i64 trials, .i64 (UInt64.ofNat n)]
      (ResultAt n trials.toNat)

noncomputable def EnclosureFacts (n trials : Nat) (hn : 2 ≤ n ∧ n ≤ 800) : Prop :=
  ∃ dts, NumericalTrace n trials 0 (initialCells n) dts (Solve.run n trials).time (Solve.run n trials).grid ∧
    Vectors.Valid (Solve.run n trials).residual
      (durationSum n trials (stepPhysicalResidual (by omega : 0 < n) trials) (initialCells n) dts) ∧
    ∀ i : Fin 4, (Flux.get (Solve.run n trials).residual i).status = 0 →
      |durationSum n trials (stepPhysicalResidual (by omega : 0 < n) trials) (initialCells n) dts i| ≤
        max (-value (Flux.get (Solve.run n trials).residual i).lower)
          (value (Flux.get (Solve.run n trials).residual i).upper)

def NumericalOutputUnchanged (n trials : Nat) : Prop :=
  (Solve.run n trials).base = Project.EulerReconstructed.Control.run n trials ∧
    (Solve.solve n trials).toList = (Project.EulerReconstructed.Control.solve n trials).toList ++
      Solve.certificateWords (Solve.run n trials).residual

noncomputable def EnclosedSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (n : Nat) (trials : UInt64) (hn : 2 ≤ n ∧ n ≤ 800),
    TerminatesWith env m 190 (m.initialStore (α := Unit)) [.i64 trials, .i64 (UInt64.ofNat n)]
      (fun final values => ResultAt n trials.toNat final values ∧
        NumericalOutputUnchanged n trials.toNat ∧ EnclosureFacts n trials.toNat hn)

theorem solve_exact : ExactSpecFor module := by
  intro env n trials hn
  refine (Execution.solve_initial_exact env n trials hn).mono ?_
  rintro final values ⟨heap, result, hValues, _, hOwner, hPages⟩
  exact ⟨result.root, hValues, hOwner.buffer.values, by omega⟩

theorem solve_enclosure : EnclosedSpecFor module := by
  intro env n trials hn
  refine (solve_exact env n trials hn).mono ?_
  intro final values hResult
  obtain ⟨dts, hTrace, hValid⟩ := Solve.run_enclosure n trials.toNat hn
  exact ⟨hResult, ⟨Solve.run_base n trials.toNat, Solve.solve_toList n trials.toNat⟩,
    dts, hTrace, hValid, fun i hi => (hValid i).absolute_bound hi⟩

#print axioms solve_exact
#print axioms solve_enclosure
end Project.EulerCertificate.Spec
