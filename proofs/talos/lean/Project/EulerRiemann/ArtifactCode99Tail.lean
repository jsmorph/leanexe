import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactByteLookup
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.Evaluate
import Lean.Elab.Tactic.Cbv

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072 in
@[cbv_eval] theorem code99_tail349_decoded :
    instructionSequenceAt 2432 false
      { bytes := artifactBytes, pos := 20791, limit := 20820 } =
      .ok (((Cache.raw.codes[99]!).body.drop 349, .end),
        { bytes := artifactBytes, pos := 20820, limit := 20820 }) := by
  cbv

#print axioms code99_tail349_decoded

end Project.EulerRiemann.Artifact
