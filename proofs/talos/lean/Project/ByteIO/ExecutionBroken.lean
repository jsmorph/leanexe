import Project.ByteIO.Execution
import Project.ByteIO.ExecutionCasesModel

namespace Project.ByteIO
open Wasm
set_option maxRecDepth 65536
set_option cbv.maxSteps 2000000

/-- A fatal write error retains the two bytes already emitted and releases
its input owner; it does not claim successful complete output. -/
theorem echo_broken_prefix :
    TerminatesWith brokenHost Artifact.module 6 echoInitial [] (CasePost 64 [] [0, 255]) := by
  apply terminates_of_check brokenHost Artifact.module 6 echoInitial [] 32
    (caseCheck 64 [] [0, 255]) (CasePost 64 [] [0, 255])
  · cbv
  · exact caseCheck_sound 64 [] [0, 255]

#print axioms echo_broken_prefix
end Project.ByteIO
