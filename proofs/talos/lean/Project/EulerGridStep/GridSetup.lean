import Project.EulerGridStep.InitialArena
import Project.EulerGridStep.GridLoopFrame
import Project.EulerGridStep.RejectedEntryExecution

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
open Project.ProofKit.FixedArrayAllocatorWindow
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def gridValidEntryFrame (ratio pointer : UInt64) (length : Nat) : Locals :=
  { gridGuardFrame ratio pointer length with values := [] }

def gridSetupFrame (frame : Locals) (root : UInt64) : Locals :=
  { frame with
    locals := ((((((frame.locals.set 5 (.i64 root)).set 6 (.i64 root)).set 7 (.i64 0)).set
      8 (.i64 root)).set 9 (.i64 root)).set 10 (.i64 0)).set 38 (.i64 0)
    values := [] }

/-- Exact fourteen-instruction handoff from zero fill to the outer loop. -/
theorem grid_setup_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (root : UInt64)
    (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 43)
    (hValues : frame.values = []) (hRoot : frame.locals[32]? = some (.i64 root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial (gridSetupFrame frame root) env) :
    wp m ((gridValidBody.drop 78).take 14 ++ rest) Q initial frame env := by
  have hRootGet := (List.getElem?_eq_some_iff.mp hRoot).choose_spec
  wp_alloc_window_lists [gridValidBody, func36, List.drop, List.take,
    hParams, hLocals, hValues, hRootGet]
  simpa only [gridSetupFrame, hValues] using hNext

def gridInitialScratch (ratio : UInt64) (base length : Nat) : GridScratch :=
  let cells := length / 3
  let count := 1 + 6 * cells
  let heap := arenaHeap base count 0
  let root := arenaRoot base count 0
  { l2 := ratio
    l5 := UInt64.ofNat count
    l8 := root
    l33 := UInt64.ofNat count
    l34 := root
    l35 := UInt64.ofNat count
    l37 := UInt64.ofNat cells
    l39 := FixedArrayCapacity.normalizedCapacity (UInt64.ofNat count) 1
    l42 := heap + 48 + fieldRequest count
    l43 := (heap + 48 + fieldRequest count - 1) / 65536 + 1
    l44 := root }

theorem initial_grid_setup_frame (ratio pointer : UInt64) (base length : Nat) :
    gridSetupFrame (initialGridFrame (gridValidEntryFrame ratio pointer length) pointer base length)
      (arenaRoot base (1 + 6 * (length / 3)) 0) =
      gridLoopFrame ratio pointer (arenaRoot base (1 + 6 * (length / 3)) 0)
        (arenaRoot base (1 + 6 * (length / 3)) 0) (length / 3) 0 (gridInitialScratch ratio base length) := by
  cases hp : Project.EulerConservative.Model.positiveBits ratio <;> by_cases he : length = 0
  all_goals
    simp [gridSetupFrame, initialGridFrame, initialOutputFrame, initialFreshAllocFrame,
      initialFreshBumpFrame, initialCapacityFrame, initialDimensionsFrame,
      gridValidEntryFrame, gridGuardFrame, gridEntryFrame, gridInitialScratch,
      gridLoopFrame, hp, he, arena_root_eq_heap]

#print axioms grid_setup_spec
#print axioms initial_grid_setup_frame
end Project.EulerGridStep.Execution
