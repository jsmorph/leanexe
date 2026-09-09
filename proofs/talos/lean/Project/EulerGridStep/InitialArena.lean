import Project.EulerGridStep.InitialOutput
import Project.EulerGridStep.InitialDimensions
import Project.EulerGridStep.ArenaBounds

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def initialGridFrame (frame : Locals) (pointer : UInt64) (base length : Nat) : Locals :=
  initialOutputFrame (initialDimensionsFrame frame pointer length)
    (arenaHeap base (1 + 6 * (length / 3)) 0) (1 + 6 * (length / 3))

theorem initial_arena_shape : gridValidBody.take 78 =
    gridValidBody.take 36 ++ (gridValidBody.drop 36).take 42 := rfl

/-- The valid entry initializes slot zero using the same cells+6 arena budget as the loop. -/
theorem initial_arena_spec (m : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (pointer allocs releases frees : UInt64) (base : Nat) (input : Array UInt64)
    (hParams : frame.params.length = 2) (hLocals : frame.locals.length = 43)
    (hValues : frame.values = []) (hPointer : frame.params[1]? = some (.i64 pointer))
    (hInput : UInt64Array.At initial pointer input) (hCells : 0 < input.size / 3)
    (hPages : initial.mem.pages ≤ 65536) (hMemory32 : m.memIs64 = false)
    (hBudget : base + (input.size / 3 + 6) * arenaObjectSize (1 + 6 * (input.size / 3)) ≤ initial.mem.pages * 65536)
    (hHeap : initial.globals.globals[0]? = some (.i64 (arenaHeap base (1 + 6 * (input.size / 3)) 0)))
    (hFree : initial.globals.globals[1]? = some (.i64 0))
    (hAllocs : initial.globals.globals[2]? = some (.i64 allocs))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees))
    (hSeparate : ObjectsSeparate (arenaRoot base (1 + 6 * (input.size / 3)) 0)
      (1 + 6 * (input.size / 3)) pointer input.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final,
      BufferState final (1 + 6 * (input.size / 3))
        [⟨arenaRoot base (1 + 6 * (input.size / 3)) 0, Array.replicate (1 + 6 * (input.size / 3)) 0⟩]
        [] (allocs + 1) releases frees →
      final.globals.globals[0]? = some (.i64 (arenaHeap base (1 + 6 * (input.size / 3)) 1)) →
      final.mem.pages = initial.mem.pages → UInt64Array.At final pointer input →
      wp m rest Q final (initialGridFrame frame pointer base input.size) env) :
    wp m (gridValidBody.take 78 ++ rest) Q initial frame env := by
  have hBudget32 : base + (input.size / 3 + 6) * arenaObjectSize (1 + 6 * (input.size / 3)) ≤ 4294967296 := by omega
  have hSlot := arena_slot_fit_of_lt base (1 + 6 * (input.size / 3)) 0 (input.size / 3 + 6)
    (initial.mem.pages * 65536) (by omega) hBudget
  have hHeapNat := arena_heap_toNat_of_le base (1 + 6 * (input.size / 3)) 0
    (input.size / 3 + 6) (by omega) hBudget32
  have hSize : 1 + 6 * (input.size / 3) < 4294967296 := by
    simp only [Nat.zero_mul, Nat.add_zero] at hSlot
    omega
  rw [initial_arena_shape, List.append_assoc]
  apply initial_dimensions_spec m env initial frame pointer input hParams hLocals hValues hPointer hInput hCells hSize
  apply initial_output_spec m env initial (initialDimensionsFrame frame pointer input.size)
    (arenaHeap base (1 + 6 * (input.size / 3)) 0) pointer allocs releases frees (1 + 6 * (input.size / 3)) input
    hParams (by simp [initialDimensionsFrame, hLocals]) rfl
    (by simp [initialDimensionsFrame, hLocals]) (by simp [initialDimensionsFrame, hLocals])
    (by simpa only [hHeapNat] using hSlot) hPages hMemory32 hHeap hFree hAllocs hReleases hFrees hInput
    (by simpa only [arena_root_eq_heap] using hSeparate)
  intro final hState hFinalHeap hFinalPages hFinalInput
  apply hNext final
    (by simpa only [arena_root_eq_heap] using hState)
    (by rw [arena_heap_succ base (1 + 6 * (input.size / 3)) 0]; exact hFinalHeap)
    hFinalPages hFinalInput

#print axioms initial_arena_shape
#print axioms initial_arena_spec
end Project.EulerGridStep.Execution
