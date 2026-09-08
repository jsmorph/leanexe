import Project.EulerGridStep.WriterReleaseShape

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow

def writerSavedFrame (base : Locals) (pointer : UInt64) : Locals :=
  { base with locals := (((base.locals.set 51 (.i64 pointer)).set 50 (.i64 pointer)).set
      55 (.i64 pointer)).set 56 (.i64 pointer), values := [] }

def writerReleaseFrame (roots : Nat → UInt64) (unused : UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) : Locals :=
  writerSavedFrame (writerStageFrame roots unused index cell 5) (roots 6)

theorem writer_release_setup_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (base : Locals) (pointer : UInt64)
    (hParams : base.params.length = 10) (hLocals : base.locals.length = 72)
    (hValues : base.values = [.i64 pointer, .i64 pointer])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial (writerSavedFrame base pointer) env) :
    wp m (writerReleaseSetup ++ rest) Q initial base env := by
  wp_alloc_window_lists [writerReleaseSetup, hParams, hLocals, hValues]
  simpa [writerSavedFrame] using hNext

@[simp] theorem writerReleaseFrame_values (roots : Nat → UInt64) (unused : UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) :
    (writerReleaseFrame roots unused index cell).values = [] := rfl

theorem writerReleaseFrame_pointer (roots : Nat → UInt64) (unused : UInt64) (index count : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) (hLo : 1 ≤ count) (hHi : count ≤ 5) :
    (writerReleaseFrame roots unused index cell).get (9 * count + 6) = some (.i64 (roots count)) := by
  interval_cases count <;>
    simp [writerReleaseFrame, writerSavedFrame, writerStageFrame, writerNextFrame,
      writerFirstFrame, writerEntryFrame, writerParameters, Locals.get]

theorem writerReleaseFrame_output (roots : Nat → UInt64) (unused : UInt64) (index : Nat)
    (cell : Project.EulerCellStep.Model.CheckedCell) :
    (writerReleaseFrame roots unused index cell).get 65 = some (.i64 (roots 6)) ∧
    (writerReleaseFrame roots unused index cell).get 66 = some (.i64 (roots 6)) := by
  simp [writerReleaseFrame, writerSavedFrame, Locals.get, writerParameters]

#print axioms writer_release_setup_spec
#print axioms writerReleaseFrame_pointer
#print axioms writerReleaseFrame_output
end Project.EulerGridStep.Execution
