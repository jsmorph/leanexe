import Project.ByteIO.Execution
import Project.ByteIO.ExecutionCasesModel

namespace Project.ByteIO
open Wasm
set_option maxRecDepth 65536
set_option cbv.maxSteps 2000000

/-- AGAIN followed by readiness retries the original read, then completes
four partial writes and balances allocation and free counts. -/
theorem echo_retry_ready :
    TerminatesWith retryHost Artifact.module 6 echoInitial [] (CasePost 0 [] exampleInput) := by
  apply terminates_of_check retryHost Artifact.module 6 echoInitial [] 32
    (caseCheck 0 [] exampleInput) (CasePost 0 [] exampleInput)
  · cbv
  · exact caseCheck_sound 0 [] exampleInput

#print axioms echo_retry_ready
end Project.ByteIO
