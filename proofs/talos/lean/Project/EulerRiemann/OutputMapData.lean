import Project.EulerRiemann.OutputMapReady

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayResult

def outputMapDataProgram (pressure : Bool) : Wasm.Program :=
  (func99.drop (if pressure then 91 else 39)).take 9

theorem output_map_data_shape (pressure : Bool) : outputMapDataProgram pressure =
    [.localGet 47, .localSet 38] ++ lengthStoreLocalProgram 38 37 ++
      [.constI64 0, .localSet 39, .block 0 0 [.loop 0 0 (outputMapLoop pressure)]] := by
  cases pressure <;> rfl

theorem output_map_data_spec (pressure : Bool) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (source target : UInt64) (grid : Array Traversal.Cell)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 52)
    (hValues : frame.values = []) (hCounter : frame.validIndex 39)
    (hSource : frame.get 36 = some (.i64 source))
    (hCount : frame.get 37 = some (.i64 (UInt64.ofNat grid.size)))
    (hTarget : frame.get 47 = some (.i64 target))
    (hGrid : Memory.GridAt store source grid)
    (hTarget32 : target.toNat + 8 * (grid.size + 1) ≤ 4294967296)
    (hTargetFit : target.toNat + 8 * (grid.size + 1) ≤ store.mem.pages * 65536)
    (hDisjoint : source.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (grid.size + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final resultFrame,
      Memory.GridAt final source grid →
      UInt64Array.At final target (outputMapResult pressure grid) →
      ProofKit.Memory.WritesRange store final target.toNat (target.toNat + 8 * (grid.size + 1)) →
      OutputMapFrameAt pressure (outputMapReadyFrame frame target hCounter) grid.size resultFrame →
      wp module rest Q final resultFrame env) :
    wp module (outputMapDataProgram pressure ++ rest) Q store frame env := by
  have hPointer : target.toUInt32.toNat = target.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have hLengthBound : target.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [hPointer]
    omega
  have hOutSize : (outputMapResult pressure grid).size = grid.size := Array.size_map ..
  have hLengthWrites : ProofKit.Memory.WritesRange
      store (writeLength store target (UInt64.ofNat grid.size)) target.toNat
      (target.toNat + 8 * (grid.size + 1)) :=
    ProofKit.Memory.WritesRange.write64 store target.toUInt32 (UInt64.ofNat grid.size)
      _ _ (by rw [hPointer]) (by rw [hPointer]; omega)
  have hPrefix : UInt64Array.PrefixAt (writeLength store target (UInt64.ofNat grid.size))
      target (outputMapResult pressure grid) 0 := by
    apply UInt64Array.PrefixAt.empty
    · simpa only [hOutSize] using hTarget32
    · simpa only [hOutSize, writeLength_pages] using hTargetFit
    · rw [hOutSize]
      exact ProofKit.Memory.read64_write64 ..
  have hSourceGrid := hGrid.frame hLengthWrites.2.1.ge
    (fun _ hLow hHigh => hLengthWrites.2.2 _ (by omega))
  rw [output_map_data_shape]
  simp only [List.append_assoc]
  apply output_map_install_spec env store frame target (UInt64.ofNat grid.size)
    hParams hLocals hValues hTarget hCount hLengthBound
  refine FixedArrayCopy.initializeCounter_spec (counter := 0) ?_ rfl Q _ ?_
  · simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hCounter
  change wp module ([.block 0 0 [.loop 0 0 (outputMapLoop pressure)]] ++ rest) Q
    (writeLength store target (UInt64.ofNat grid.size)) (outputMapReadyFrame frame target hCounter) env
  apply output_map_loop_spec pressure env _ _ 0 source target grid (by omega)
    (output_map_ready_frame pressure frame target hCounter hParams hLocals)
  · exact (output_map_ready_get frame target hCounter hParams 36 (by decide) (by decide)).trans hSource
  · exact (output_map_ready_get frame target hCounter hParams 37 (by decide) (by decide)).trans hCount
  · exact output_map_ready_target frame target hCounter hParams
  · exact hSourceGrid
  · exact hPrefix
  · exact hDisjoint
  · intro final resultFrame hSourceFinal hTargetFinal hWrites hFrame
    exact hNext final resultFrame hSourceFinal hTargetFinal (hLengthWrites.trans hWrites) hFrame

#print axioms output_map_data_shape
#print axioms output_map_data_spec

end Project.EulerRiemann.Execution
