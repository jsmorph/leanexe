import Project.EulerRiemann.InitialAllocationSearchShape
import Project.ProofKit.FixedArrayAllocateNone

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def InitialAllocationSite.allocationProgram : InitialAllocationSite → Wasm.Program
  | .map => (initialGrowBody.drop 30).take 15
  | .append => (initialGrowBody.drop 104).take 15
  | .extract => (initialExtractBody.drop 46).take 15

theorem initial_allocation_parts (site : InitialAllocationSite) :
    site.allocationProgram = FixedArrayAllocateNone.initializeProgram site.capacityLocal ++
      [.block 0 0 [.loop 0 0 site.searchBody]] ++
      [.localGet (site.capacityLocal + 5), .constI64 0, .eqI64, .iff 0 0 site.bumpProgram []] ++
      FixedArrayAllocateNone.countProgram := by
  cases site <;> rfl

theorem initial_allocation_shape (site : InitialAllocationSite) :
    site.allocationProgram = FixedArrayAllocateNone.program site.capacityLocal site.fitProgram 7 := by
  rw [initial_allocation_parts, initial_search_body, initial_bump_shape]
  rfl

theorem initial_done_allocation_shape : (initialDoneBody.drop 46).take 15 =
    InitialAllocationSite.extract.allocationProgram := by
  rfl

#print axioms initial_allocation_parts
#print axioms initial_allocation_shape
#print axioms initial_done_allocation_shape

end Project.EulerRiemann.Execution
