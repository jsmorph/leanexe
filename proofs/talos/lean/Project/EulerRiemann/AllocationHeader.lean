import Project.ProofKit.FixedArrayHeaderExec
import Project.EulerRiemann.AllocationGrowth

namespace Project.EulerRiemann.Execution
open Wasm Project.Clob Project.ProofKit.FixedArrayHeader

theorem sweep_header_shape : sweepBump.drop 28 = program 52 47 7 := rfl

def sweepSearch : Wasm.Program :=
  match (func70[30]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def sweepFit : Wasm.Program :=
  match (sweepSearch[23]? : Option Wasm.Instruction) with
  | some (.iff _ _ body _ _ _) => body
  | _ => []

theorem sweep_search_shape :
    func70[30]? = some (.block 0 0 [.loop 0 0 sweepSearch]) := rfl

theorem sweep_fit_shape : sweepSearch[23]? = some (.iff 0 0 sweepFit
    [.localGet 49, .localSet 48, .localGet 51, .localSet 49]) := rfl

theorem sweep_fit_header_shape : (sweepFit.drop 4).take 36 = program 49 50 7 := rfl

theorem sweep_header_spec (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (base capacity : UInt64) (hValues : frame.values = [])
    (hPointer : frame.get 52 = some (.i64 (base + 48)))
    (hCapacity : frame.get 47 = some (.i64 capacity))
    (hFit32 : base.toNat + 48 ≤ 4294967296)
    (hFit : base.toNat + 48 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q
      { store with mem := fixedArrayHeaderMem store.mem base capacity 7 } frame env) :
    wp Project.EulerRiemann.«module» (sweepBump.drop 28 ++ rest) Q store frame env := by
  rw [sweep_header_shape]
  exact program_spec _ env store frame 52 47 base capacity 7 hValues hPointer hCapacity
    hFit32 hFit Q rest hNext

theorem gridAt_header (store : Store Unit) (base capacity stride pointer : UInt64)
    (grid : Array Traversal.Cell) (hGrid : Memory.GridAt store pointer grid)
    (hFit32 : base.toNat + 48 ≤ 4294967296)
    (hDisjoint : pointer.toNat + 8 * (7 * grid.size + 1) ≤ base.toNat ∨
      base.toNat + 48 ≤ pointer.toNat) :
    Memory.GridAt { store with mem := fixedArrayHeaderMem store.mem base capacity stride }
      pointer grid := by
  apply hGrid.frame
  · exact Nat.le_of_eq (fixedArrayHeaderMem_pages store.mem base capacity stride).symm
  · intro address hLow hHigh
    exact bytes_outside store.mem base capacity stride hFit32 address (by omega)

#print axioms sweep_header_shape
#print axioms sweep_search_shape
#print axioms sweep_fit_shape
#print axioms sweep_fit_header_shape
#print axioms sweep_header_spec
#print axioms gridAt_header

end Project.EulerRiemann.Execution
