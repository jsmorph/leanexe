import Project.EulerRiemann.ArtifactCode99Tail

namespace Project.EulerRiemann.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072 in
@[cbv_eval] theorem code99_tail333_decoded :
    instructionSequenceAt 2448 false
      { bytes := artifactBytes, pos := 20657, limit := 20820 } =
      .ok (((Cache.raw.codes[99]!).body.drop 333, .end),
        { bytes := artifactBytes, pos := 20820, limit := 20820 }) := by
  cbv

#print axioms code99_tail333_decoded

end Project.EulerRiemann.Artifact
