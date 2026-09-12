import Project.EulerRiemann.InitialArrayInstall
import Project.EulerRiemann.InitialAppendCopy
import Project.EulerRiemann.MemoryLength
import Project.ProofKit.FixedArrayFrame

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayResult FixedArrayCopy

theorem initial_append_install_eq : initialGrowBody.drop 119 =
    InitialAllocationSite.append.installProgram ++ initialGrowBody.drop 125 := by
  rfl

theorem initial_append_data_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (source upper target : UInt64) (left right : Array Traversal.Cell)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = []) (hCounter : (resultFrame frame 55 target).validIndex 56)
    (hSource : frame.get 48 = some (.i64 source))
    (hUpper : frame.get 49 = some (.i64 upper))
    (hTarget : frame.get 64 = some (.i64 target))
    (hLength : frame.get 52 = some (.i64 (UInt64.ofNat (left.size + right.size))))
    (hLeftCount : frame.get 53 = some (.i64 (UInt64.ofNat (7 * left.size))))
    (hRightCount : frame.get 54 = some (.i64 (UInt64.ofNat (7 * right.size))))
    (hLeft : Memory.GridAt store source left) (hRight : Memory.GridAt store upper right)
    (hTarget32 : target.toNat + 8 * (7 * (left.size + right.size) + 1) ≤ 4294967296)
    (hTargetFit : target.toNat + 8 * (7 * (left.size + right.size) + 1) ≤ store.mem.pages * 65536)
    (hSeparateLeft : source.toNat + 8 * (7 * left.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * (left.size + right.size) + 1) ≤ source.toNat)
    (hSeparateRight : upper.toNat + 8 * (7 * right.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (7 * (left.size + right.size) + 1) ≤ upper.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final,
      Memory.WritesGrid store final target (left.size + right.size) →
      Memory.GridAt final source left → Memory.GridAt final upper right →
      Memory.GridAt final target (left ++ right) →
      wp module (initialGrowBody.drop 131 ++ rest) Q final
        (counterFrame (resultFrame frame 55 target) 56 (7 * right.size) hCounter) env) :
    wp module (initialGrowBody.drop 119 ++ rest) Q store frame env := by
  have hLengthBound : target.toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
    omega
  have hLeftGrid : Memory.GridAt
      (writeLength store target (UInt64.ofNat (left.size + right.size))) source left :=
    hLeft.writeLength_disjoint _ (by omega) (by omega)
  have hRightGrid : Memory.GridAt
      (writeLength store target (UInt64.ofNat (left.size + right.size))) upper right :=
    hRight.writeLength_disjoint _ (by omega) (by omega)
  rw [initial_append_install_eq, List.append_assoc]
  apply initial_install_spec .append env store frame target (UInt64.ofNat (left.size + right.size))
    hParams hLocals hValues hTarget hLength hLengthBound
  apply initial_append_copy_spec env _ (resultFrame frame 55 target) source upper target left right
    hCounter rfl
  · exact (resultFrame_get_ne frame 55 48 target (by omega) (by decide)).trans hSource
  · exact (resultFrame_get_ne frame 55 49 target (by omega) (by decide)).trans hUpper
  · apply resultFrame_get_result frame 55 target (by omega)
    simp only [Locals.validIndex, hParams, hLocals]
    decide
  · exact (resultFrame_get_ne frame 55 53 target (by omega) (by decide)).trans hLeftCount
  · exact (resultFrame_get_ne frame 55 54 target (by omega) (by decide)).trans hRightCount
  · exact hLeftGrid
  · exact hRightGrid
  · exact hTarget32
  · exact hTargetFit
  · exact Project.ProofKit.Memory.read64_write64 ..
  · exact hSeparateLeft
  · exact hSeparateRight
  · intro final hWrites hLeftFinal hRightFinal hTargetFinal
    exact hNext final
      ((Memory.writeLength_frame store target (left.size + right.size) (by omega)).trans hWrites)
      hLeftFinal hRightFinal hTargetFinal

#print axioms initial_append_install_eq
#print axioms initial_append_data_spec

end Project.EulerRiemann.Execution
