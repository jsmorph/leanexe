import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem type64_decoded :
    funcType { bytes := artifactBytes, pos := 525, limit := 534 } =
      .ok (Cache.raw.types[64]!, { bytes := artifactBytes, pos := 530, limit := 534 }) := by cbv

#print axioms type64_decoded

theorem type65_decoded :
    funcType { bytes := artifactBytes, pos := 530, limit := 534 } =
      .ok (Cache.raw.types[65]!, { bytes := artifactBytes, pos := 534, limit := 534 }) := by cbv

#print axioms type65_decoded


end Project.Gpt2QuantizedCached.Artifact
