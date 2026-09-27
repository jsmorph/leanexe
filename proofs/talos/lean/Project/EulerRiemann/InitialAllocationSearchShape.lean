import Project.EulerRiemann.InitialAllocationBump
import Project.ProofKit.FixedArraySearchNone

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit Project.Runtime

def InitialAllocationSite.searchInstruction : InitialAllocationSite → Option Wasm.Instruction
  | .map => initialGrowBody[36]?
  | .append => initialGrowBody[110]?
  | .extract => initialExtractBody[52]?

def InitialAllocationSite.searchBody (site : InitialAllocationSite) : Wasm.Program :=
  match site.searchInstruction with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def InitialAllocationSite.fitProgram (site : InitialAllocationSite) : Wasm.Program :=
  match (site.searchBody[23]? : Option Wasm.Instruction) with
  | some (.iff _ _ body _ _ _) => body
  | _ => []

theorem initial_search_instruction (site : InitialAllocationSite) :
    site.searchInstruction = some (.block 0 0 [.loop 0 0 site.searchBody]) := by
  cases site <;> rfl

theorem initial_search_body (site : InitialAllocationSite) :
    site.searchBody = FixedArraySearch.body site.capacityLocal site.fitProgram := by
  cases site <;> rfl

theorem initial_search_shape (site : InitialAllocationSite) :
    site.searchInstruction =
      some (.block 0 0 [.loop 0 0 (FixedArraySearch.body site.capacityLocal site.fitProgram)]) := by
  rw [initial_search_instruction, initial_search_body]

theorem initial_done_search_shape : initialDoneBody[52]? = InitialAllocationSite.extract.searchInstruction := by
  rfl
#print axioms initial_search_instruction
#print axioms initial_search_body
#print axioms initial_search_shape
#print axioms initial_done_search_shape

end Project.EulerRiemann.Execution
