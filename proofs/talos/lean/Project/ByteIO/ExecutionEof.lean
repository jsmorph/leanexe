import Project.ByteIO.Execution
import Project.ByteIO.ExecutionCasesModel

namespace Project.ByteIO
open Wasm
set_option maxRecDepth 65536
set_option cbv.maxSteps 2000000

/-- EOF frees the unused read buffer and the empty write succeeds. -/
theorem echo_eof :
    TerminatesWith partialHost Artifact.module 6 eofInitial [] (CasePost 0 [] []) := by
  apply terminates_of_check partialHost Artifact.module 6 eofInitial [] 32
    (caseCheck 0 [] []) (CasePost 0 [] [])
  · cbv
  · exact caseCheck_sound 0 [] []

#print axioms echo_eof
end Project.ByteIO
