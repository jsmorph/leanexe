import Project.EulerRiemann.ArtifactBytes
import Project.EulerRiemann.ArtifactCache
import Project.Artifact.Binary.Decode
import Lean.Elab.Tactic.Cbv

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

set_option maxRecDepth 131072 in
@[cbv_eval] theorem code99_tail349_decoded :
    instructionSequence 2432 false { bytes := artifactBytes, pos := 20791, limit := 20820 } =
      .ok (((Cache.raw.codes[99]!).body.drop 349, .end),
        { bytes := artifactBytes, pos := 20820, limit := 20820 }) := by
  cbv

#print axioms code99_tail349_decoded

end Project.EulerRiemann.Artifact
