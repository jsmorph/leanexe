import Project.EulerCertificate.ArtifactByteLookup
import Project.EulerCertificate.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerCertificate.ArtifactCodeVector
import Project.EulerCertificate.ArtifactMetadata
import Project.Artifact.Binary.ModuleParts
import Project.Artifact.Binary.SectionParts

namespace Project.EulerCertificate.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

set_option maxRecDepth 131072
set_option cbv.maxSteps 1000000

def afterTypes : RawModule :=
  { (default : RawModule) with
    types := Cache.raw.types,
    sections := [.type] }

def afterFunctions : RawModule :=
  { afterTypes with
    functionTypeIndices := Cache.raw.functionTypeIndices,
    sections := [.type, .function] }

def afterMemory : RawModule :=
  { afterFunctions with
    memories := Cache.raw.memories,
    sections := [.type, .function, .memory] }

def afterGlobals : RawModule :=
  { afterMemory with
    globals := Cache.raw.globals,
    sections := [.type, .function, .memory, .global] }

def afterExports : RawModule :=
  { afterGlobals with
    exports := Cache.raw.exports,
    sections := [.type, .function, .memory, .global, .export] }

theorem sections_from6 :
    sectionLoop 45630 6 Cache.raw { bytes := artifactBytes, pos := 45644, limit := 45644 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 45644, limit := 45644 }) := by rfl

#print axioms sections_from6

end Project.EulerCertificate.Artifact
