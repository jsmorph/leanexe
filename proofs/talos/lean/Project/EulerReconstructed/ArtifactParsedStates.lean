import Project.EulerReconstructed.ArtifactByteLookup
import Project.EulerReconstructed.ArtifactCache
import Project.Artifact.Binary.CodeParts
import Project.EulerReconstructed.ArtifactCodeVector
import Project.EulerReconstructed.ArtifactMetadata
import Project.Artifact.Binary.ModuleParts
import Project.Artifact.Binary.SectionParts

namespace Project.EulerReconstructed.Artifact
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
    sectionLoop 30712 6 Cache.raw { bytes := artifactBytes, pos := 30726, limit := 30726 } =
      .ok (Cache.raw, { bytes := artifactBytes, pos := 30726, limit := 30726 }) := by rfl

#print axioms sections_from6

end Project.EulerReconstructed.Artifact
