import Project.EulerRiemann.ArtifactCode99Part333

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072 in
set_option cbv.maxSteps 1000000 in
@[cbv_eval] theorem code99_tail283_decoded :
    instructionSequenceAt 2498 false { bytes := artifactBytes, pos := 20257, limit := 20820 } =
      .ok (((Cache.raw.codes[99]!).body.drop 283, .end),
        { bytes := artifactBytes, pos := 20820, limit := 20820 }) := by
  cbv

#print axioms code99_tail283_decoded

end Project.EulerRiemann.Artifact
