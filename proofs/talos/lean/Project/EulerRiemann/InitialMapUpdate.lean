import Project.EulerRiemann.InitialMapFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

theorem initial_map_update_shape : (initialMapLoop.drop 4).take 206 =
    (initialMapLoop.drop 4).take 84 ++ (initialMapLoop.drop 88).take 38 ++
      (initialMapLoop.drop 126).take 84 := by
  rfl

theorem initial_map_update_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n offset index : Nat) (source target : UInt64) (grid : Array Traversal.Cell)
    (hn : n ≤ 800) (hi : index < grid.size) (hSum : grid[index].index + offset < 1048576)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = [])
    (hN : frame.get 1 = some (.i64 (UInt64.ofNat n)))
    (hOffset : frame.get 10 = some (.i64 (UInt64.ofNat offset)))
    (hSource : frame.get 48 = some (.i64 source))
    (hTarget : frame.get 50 = some (.i64 target))
    (hIndex : frame.get 51 = some (.i64 (UInt64.ofNat index)))
    (hGrid : Memory.GridAt store source grid)
    (hFit32 : target.toNat + 8 * (7 * grid.size + 1) ≤ 4294967296)
    (hFitMemory : target.toNat + 8 * (7 * grid.size + 1) ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q
      (Memory.writeCell store target index (Traversal.initialCell n (grid[index].index + offset)))
      (initialMappedFrame frame n offset grid[index]) env) :
    wp module ((initialMapLoop.drop 4).take 206 ++ rest) Q store frame env := by
  rw [initial_map_update_shape]
  simp only [List.append_assoc]
  apply initial_map_load_spec env store frame source grid index
    hParams hLocals hValues hSource hIndex hGrid hi
  apply initial_map_call_spec env store (initialLoadedFrame frame grid[index])
    n grid[index].index offset hn hSum
  · exact hParams
  · simpa using hLocals
  · rfl
  · rw [initial_loaded_get_other _ _ _ hParams (by decide)]
    exact hN
  · rw [initial_loaded_get_other _ _ _ hParams (by decide)]
    exact hOffset
  · exact initial_loaded_index frame grid[index] hParams hLocals
  change wp module (_ ++ rest) Q store (initialMappedFrame frame n offset grid[index]) env
  apply initial_map_store_spec env store (initialMappedFrame frame n offset grid[index])
    target grid.size index (Traversal.initialCell n (grid[index].index + offset))
  · rfl
  · rw [initial_mapped_get_other _ _ _ _ _ hParams (by decide) (by decide)]
    exact hTarget
  · rw [initial_mapped_get_other _ _ _ _ _ hParams (by decide) (by decide)]
    exact hIndex
  · intro field hf
    exact initial_called_data _ _ _ _ field hParams (by simpa using hLocals) hf
  · exact hFit32
  · exact hFitMemory
  · exact hi
  · exact hNext

#print axioms initial_map_update_shape
#print axioms initial_map_update_spec

end Project.EulerRiemann.Execution
