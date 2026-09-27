import Project.EulerRiemann.ArtifactCode99Part283

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072 in
set_option cbv.maxSteps 1000000 in
@[cbv_eval] theorem code99_tail210_decoded :
    instructionSequenceAt 2571 false { bytes := artifactBytes, pos := 19985, limit := 20820 } =
      .ok (((Cache.raw.codes[99]!).body.drop 210, .end),
        { bytes := artifactBytes, pos := 20820, limit := 20820 }) := by
  cbv

#print axioms code99_tail210_decoded

end Project.EulerRiemann.Artifact
