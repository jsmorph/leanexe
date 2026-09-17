import Project.TinyGpt2Hidden.ArtifactCache
import Project.Artifact.Binary.ValidationParts
import Lean.Elab.Tactic.Cbv

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

def resolvedFunctions : List FuncType :=
  Cache.raw.functionTypeIndices.map (fun i => Cache.raw.types[i.toNat]!)

theorem types_resolved : Validator.resolveFunctionTypes Cache.raw = .ok resolvedFunctions := by cbv

#print axioms types_resolved
end Project.TinyGpt2Hidden.Artifact
