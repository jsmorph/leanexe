import Project.EulerRiemann.InitialAllocationShape
import Project.ProofKit.FixedArrayResult

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit FixedArrayFold FixedArrayResult

def InitialAllocationSite.targetLocal : InitialAllocationSite → Nat
  | .map => 50
  | .append => 55
  | .extract => 56

def InitialAllocationSite.installProgram : InitialAllocationSite → Wasm.Program
  | .map => (initialGrowBody.drop 45).take 6
  | .append => (initialGrowBody.drop 119).take 6
  | .extract => (initialExtractBody.drop 61).take 6

theorem initial_install_shape (site : InitialAllocationSite) :
    site.installProgram = resultProgram (site.capacityLocal + 5) site.targetLocal ++
      lengthStoreLocalProgram site.targetLocal site.lengthLocal := by
  cases site <;> rfl

theorem initial_done_install_shape : (initialDoneBody.drop 61).take 6 =
    InitialAllocationSite.extract.installProgram := by
  rfl

theorem initial_install_spec (site : InitialAllocationSite)
    (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (root length : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = [])
    (hRoot : frame.get (site.capacityLocal + 5) = some (.i64 root))
    (hLength : frame.get site.lengthLocal = some (.i64 length))
    (hBound : root.toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (writeLength store root length)
      (resultFrame frame site.targetLocal root) env) :
    wp module (site.installProgram ++ rest) Q store frame env := by
  have hTargetLower : frame.params.length ≤ site.targetLocal := by
    cases site <;> simp [InitialAllocationSite.targetLocal, hParams]
  have hTargetValid : frame.validIndex site.targetLocal := by
    cases site <;> simp [Locals.validIndex, InitialAllocationSite.targetLocal, hParams, hLocals]
  have hLengthLower : frame.params.length ≤ site.lengthLocal := by
    cases site <;> simp [InitialAllocationSite.lengthLocal, hParams]
  have hLengthValid : frame.validIndex site.lengthLocal := by
    cases site <;> simp [Locals.validIndex, InitialAllocationSite.lengthLocal, hParams, hLocals]
  have hDistinct : site.lengthLocal ≠ site.targetLocal := by
    cases site <;> decide
  rw [initial_install_shape, List.append_assoc]
  apply resultProgram_spec (site.capacityLocal + 5) site.targetLocal module env store frame root
    hValues hRoot hTargetLower hTargetValid
  exact lengthStoreLocal_spec module env store (resultFrame frame site.targetLocal root)
    root length site.targetLocal site.lengthLocal
    (resultFrame_get_result frame site.targetLocal root hTargetLower hTargetValid)
    (resultFrame_get_of_ne frame site.targetLocal site.lengthLocal root _
      hTargetLower hLengthLower hLengthValid hDistinct hLength) hBound Q rest hNext

#print axioms initial_install_shape
#print axioms initial_done_install_shape
#print axioms initial_install_spec

end Project.EulerRiemann.Execution
