import Project.EulerRiemann.InitialArrayInstall
import Project.EulerRiemann.MemoryLength
import Project.ProofKit.FixedArrayFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayResult FixedArrayCopy

def initialExtractDataProgram : Wasm.Program := (initialExtractBody.drop 61).take 9

theorem initial_extract_data_shape : initialExtractDataProgram =
    InitialAllocationSite.extract.installProgram ++ initialExtractCopy := by
  rfl

theorem initial_extract_data_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (source target : UInt64) (grid : Array Traversal.Cell) (size : Nat)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hCounter : (resultFrame frame 56 target).validIndex 57)
    (hSource : frame.get 48 = some (.i64 source))
    (hTarget : frame.get 65 = some (.i64 target))
    (hLength : frame.get 53 = some (.i64 (UInt64.ofNat size)))
    (hOffset : frame.get 54 = some (.i64 0))
    (hCount : frame.get 55 = some (.i64 (UInt64.ofNat (7 * size))))
    (hGrid : Memory.GridAt store source grid) (hSize : size ≤ grid.size)
    (hTarget32 : target.toNat + 8 * (7 * size + 1) ≤ 4294967296)
    (hTargetFit : target.toNat + 8 * (7 * size + 1) ≤ store.mem.pages * 65536)
    (hSeparate : source.toNat + 8 * (7 * grid.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * size + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final,
      Memory.WritesGrid store final target size →
      Memory.GridAt final source grid → Memory.GridAt final target (grid.extract 0 size) →
      wp module rest Q final (counterFrame (resultFrame frame 56 target) 57 (7 * size) hCounter) env) :
    wp module (initialExtractDataProgram ++ rest) Q store frame env := by
  have hLengthBound : target.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega
  have hSourceGrid : Memory.GridAt (writeLength store target (UInt64.ofNat size)) source grid :=
    hGrid.writeLength_disjoint _ (by omega) (by omega)
  rw [initial_extract_data_shape, List.append_assoc]
  apply initial_install_spec .extract env store frame target (UInt64.ofNat size)
    hParams hLocals hValues hTarget hLength hLengthBound
  apply initial_extract_copy_spec env _ (resultFrame frame 56 target) source target grid size
    hCounter rfl
  · exact (resultFrame_get_ne frame 56 48 target (by omega) (by decide)).trans hSource
  · apply resultFrame_get_result frame 56 target (by omega)
    simp only [Locals.validIndex, hParams, hLocals]
    decide
  · exact (resultFrame_get_ne frame 56 54 target (by omega) (by decide)).trans hOffset
  · exact (resultFrame_get_ne frame 56 55 target (by omega) (by decide)).trans hCount
  · exact hSourceGrid
  · exact hSize
  · exact hTarget32
  · exact hTargetFit
  · exact Project.ProofKit.Memory.read64_write64 ..
  · exact hSeparate
  · intro final hWrites hSourceFinal hTargetFinal
    exact hNext final ((Memory.writeLength_frame store target size (by omega)).trans hWrites)
      hSourceFinal hTargetFinal

#print axioms initial_extract_data_shape
#print axioms initial_extract_data_spec

end Project.EulerRiemann.Execution
