import Project.TinyGpt2Hidden.ArtifactBody28
import Project.TinyGpt2Hidden.ArtifactBody29
import Project.TinyGpt2Hidden.ArtifactByteLookup
import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.CodeParts

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem code28_decoded :
    code { bytes := artifactBytes, pos := 3815, limit := 16006 } =
      .ok (Cache.raw.codes[28]!, { bytes := artifactBytes, pos := 3989, limit := 16006 }) := by
  exact code28_decoded_parts

#print axioms code28_decoded

theorem code29_decoded :
    code { bytes := artifactBytes, pos := 3989, limit := 16006 } =
      .ok (Cache.raw.codes[29]!, { bytes := artifactBytes, pos := 4299, limit := 16006 }) := by
  exact code29_decoded_parts

#print axioms code29_decoded

theorem code30_decoded :
    code { bytes := artifactBytes, pos := 4299, limit := 16006 } =
      .ok (Cache.raw.codes[30]!, { bytes := artifactBytes, pos := 4311, limit := 16006 }) := by
  cbv

#print axioms code30_decoded

theorem code31_decoded :
    code { bytes := artifactBytes, pos := 4311, limit := 16006 } =
      .ok (Cache.raw.codes[31]!, { bytes := artifactBytes, pos := 4323, limit := 16006 }) := by
  cbv

#print axioms code31_decoded

end Project.TinyGpt2Hidden.Artifact
