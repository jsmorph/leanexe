import Project.Gpt2QuantizedCached.ArtifactByteLookup
import Project.Gpt2QuantizedCached.ArtifactCache
import Project.Artifact.Binary.CodeParts


namespace Project.Gpt2QuantizedCached.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

theorem function64_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 601, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[64]!, { bytes := artifactBytes, pos := 602, limit := 603 }) := by cbv

theorem function65_decoded :
    Leb.u32 { bytes := artifactBytes, pos := 602, limit := 603 } =
      .ok (Cache.raw.functionTypeIndices[65]!, { bytes := artifactBytes, pos := 603, limit := 603 }) := by cbv


end Project.Gpt2QuantizedCached.Artifact
