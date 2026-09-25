import Project.RunningSum.ArtifactCache
import Lean.Elab.Tactic.Cbv

namespace Project.RunningSum.Artifact

set_option maxRecDepth 32768 in
set_option cbv.maxSteps 2000000 in
theorem validated : Project.ByteIO.Binary.validate raw = .ok () := by cbv

theorem valid : Project.ByteIO.Binary.Valid raw := Project.ByteIO.Binary.validate_sound validated

#print axioms validated
#print axioms valid

end Project.RunningSum.Artifact
