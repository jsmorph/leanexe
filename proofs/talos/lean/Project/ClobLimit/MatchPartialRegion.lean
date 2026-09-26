import Project.ClobLimit.MatchLocals
import Project.ClobLimit.SearchRegion
import Project.ClobMatchFuel.PartialBranch
import Project.ProofKit.Annotation

namespace Project.ClobLimit.MatchPartialRegion
open Project.FunctionRegion Project.LocalRegion Project.ProofKit.Annotation

def program : Wasm.Program :=
  LocalRegion.renameProgram MatchLocals.rename
    (FunctionRegion.renameProgram SearchRegion.searchRename
      Project.ClobMatchFuel.PartialBranch.partialBranchProg)

set_option maxRecDepth 1048576 in
theorem region :
    resolve func17
      [{ instructionIndex := 6, field := .block },
       { instructionIndex := 0, field := .loop },
       { instructionIndex := 17, field := .elseBranch },
       { instructionIndex := 27, field := .elseBranch },
       { instructionIndex := 58, field := .elseBranch }] = some program := by
  rfl

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 800000 in
theorem portable : PortableProgram SearchRegion.SearchDomain
    Project.ClobMatchFuel.PartialBranch.partialBranchProg := by
  prove_portable

set_option maxRecDepth 1048576 in
theorem allowed : AllowsProgram MatchLocals.Domain
    Project.ClobMatchFuel.PartialBranch.partialBranchProg := by
  decide

#print axioms region
end Project.ClobLimit.MatchPartialRegion
