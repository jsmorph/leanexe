import Project.ByteIO.ArtifactCache
import Lean.Elab.Tactic.Cbv

namespace Project.ByteIO.Artifact

set_option maxRecDepth 32768 in
set_option cbv.maxSteps 2000000 in
theorem validated : Binary.validate raw = .ok () := by cbv

theorem valid : Binary.Valid raw := Binary.validate_sound validated

#print axioms validated
#print axioms valid

end Project.ByteIO.Artifact
