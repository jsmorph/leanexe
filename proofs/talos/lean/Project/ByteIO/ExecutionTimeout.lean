import Project.ByteIO.Execution
import Project.ByteIO.ExecutionCasesModel

namespace Project.ByteIO
open Wasm
set_option maxRecDepth 65536
set_option cbv.maxSteps 2000000

/-- AGAIN followed by the absolute clock event returns TIMEDOUT without
consuming input, and frees the allocated read buffer. -/
theorem echo_poll_timeout :
    TerminatesWith timeoutHost Artifact.module 6 echoInitial [] (CasePost 73 exampleInput []) := by
  apply terminates_of_check timeoutHost Artifact.module 6 echoInitial [] 32
    (caseCheck 73 exampleInput []) (CasePost 73 exampleInput [])
  · cbv
  · exact caseCheck_sound 73 exampleInput []

#print axioms echo_poll_timeout
end Project.ByteIO
