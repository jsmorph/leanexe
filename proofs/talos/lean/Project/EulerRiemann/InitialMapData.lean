import Project.EulerRiemann.InitialMapDataShape
import Project.EulerRiemann.InitialMapReady

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayResult

theorem initial_map_data_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (n offset : Nat) (source target : UInt64) (grid : Array Traversal.Cell)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hCounter : frame.validIndex 51)
    (hn : n ≤ 800)
    (hSum : ∀ i : Nat, (h : i < grid.size) → grid[i].index + offset < 1048576)
    (hN : frame.get 1 = some (.i64 (UInt64.ofNat n)))
    (hOffset : frame.get 10 = some (.i64 (UInt64.ofNat offset)))
    (hSource : frame.get 48 = some (.i64 source))
    (hCount : frame.get 49 = some (.i64 (UInt64.ofNat grid.size)))
    (hTarget : frame.get 59 = some (.i64 target))
    (hGrid : Memory.GridAt store source grid)
    (hTarget32 : target.toNat + 8 * (7 * grid.size + 1) ≤ 4294967296)
    (hTargetFit : target.toNat + 8 * (7 * grid.size + 1) ≤ store.mem.pages * 65536)
    (hDisjoint : source.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * grid.size + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      Memory.GridAt final source grid →
      Memory.GridAt final target (initialMapOutput n offset grid) →
      Memory.WritesGrid store final target grid.size →
      InitialMapFrameAt (initialMapReadyFrame frame target hCounter) grid.size resultFrame →
      wp module rest Q final resultFrame env) :
    wp module (initialMapDataProgram ++ rest) Q store frame env := by
  have hLengthBound : target.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega
  have hOutSize : (initialMapOutput n offset grid).size = grid.size := by
    simp only [initialMapOutput, Array.size_map]
  have hPrefix : Memory.PrefixAt (writeLength store target (UInt64.ofNat grid.size))
      target (initialMapOutput n offset grid) 0 := by
    simpa only [hOutSize] using Memory.writeLength_prefix store target (initialMapOutput n offset grid)
      (by simpa only [hOutSize] using hTarget32) (by simpa only [hOutSize] using hTargetFit)
  have hSourceGrid : Memory.GridAt (writeLength store target (UInt64.ofNat grid.size)) source grid :=
    hGrid.writeLength_disjoint _ (by omega) (by omega)
  rw [initial_map_data_shape, List.append_assoc]
  apply initial_install_spec .map env store frame target (UInt64.ofNat grid.size)
    hParams hLocals hValues hTarget hCount hLengthBound
  refine FixedArrayCopy.initializeCounter_spec (counter := 0) ?_ rfl Q _ ?_
  · simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hCounter
  change wp module ([.block 0 0 [.loop 0 0 initialMapLoop]] ++ rest) Q
    (writeLength store target (UInt64.ofNat grid.size)) (initialMapReadyFrame frame target hCounter) env
  apply initial_map_loop_spec env _ _ n offset 0 source target grid hn (by omega) hSum
    (initial_map_ready_frame frame target hCounter hParams hLocals)
  · exact (initial_map_ready_get frame target hCounter hParams 1 (by decide) (by decide)).trans hN
  · exact (initial_map_ready_get frame target hCounter hParams 10 (by decide) (by decide)).trans hOffset
  · exact (initial_map_ready_get frame target hCounter hParams 48 (by decide) (by decide)).trans hSource
  · exact (initial_map_ready_get frame target hCounter hParams 49 (by decide) (by decide)).trans hCount
  · exact initial_map_ready_target frame target hCounter hParams
  · exact hSourceGrid
  · exact hPrefix
  · exact hDisjoint
  · intro final resultFrame hSourceFinal hTargetFinal hWrites hFrame
    exact hNext final resultFrame hSourceFinal hTargetFinal
      ((Memory.writeLength_frame store target grid.size (by omega)).trans hWrites) hFrame

#print axioms initial_map_data_spec

end Project.EulerRiemann.Execution
