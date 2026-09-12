import Project.ProofKit.MemoryEnsure
import Project.EulerRiemann.Program
import Project.EulerRiemann.Memory

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit.MemoryGrowth

def sweepBump : Wasm.Program :=
  match (func70[34]? : Option Wasm.Instruction) with
  | some (.iff _ _ body _ _ _) => body
  | _ => []

theorem sweep_bump_shape : func70[34]? = some (.iff 0 0 sweepBump []) := rfl

theorem sweep_growth_shape : (sweepBump.drop 17).take 5 = ensureProgram 51 := rfl

theorem sweep_growth_spec (env : HostEnv Unit) (store : Store Unit)
    (frame : Locals) (required : Nat) (hValues : frame.values = [])
    (hLocal : frame.get 51 = some (.i64 (UInt64.ofNat required)))
    (hCurrent : store.mem.pages ≤ 65536) (hBound : required ≤ 65536)
    (hCap : required ≤ store.memoryCap Project.EulerRiemann.«module» 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q (ensured store required) frame env) :
    wp Project.EulerRiemann.«module» ((sweepBump.drop 17).take 5 ++ rest) Q store frame env := by
  rw [sweep_growth_shape]
  exact ensureProgram_spec _ env store frame 51 required rfl hValues hLocal
    hCurrent hBound hCap Q rest hNext

theorem gridAt_ensured (store : Store Unit) (required : Nat)
    (pointer : UInt64) (grid : Array Traversal.Cell) (hGrid : Memory.GridAt store pointer grid) :
    Memory.GridAt (ensured store required) pointer grid := by
  apply hGrid.frame
  · rw [ensured_pages]
    exact Nat.le_max_left ..
  · intro address _ _
    rw [ensured_bytes]

#print axioms sweep_bump_shape
#print axioms sweep_growth_shape
#print axioms sweep_growth_spec
#print axioms gridAt_ensured

end Project.EulerRiemann.Execution
