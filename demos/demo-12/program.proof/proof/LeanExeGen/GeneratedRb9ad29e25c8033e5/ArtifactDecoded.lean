import LeanExeGen.GeneratedRb9ad29e25c8033e5.ArtifactBytes
import Project.Artifact.Binary.Decode

set_option maxRecDepth 1048576

namespace LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact

open Wasm.Binary

def decodedRaw? : Option RawModule :=
  (decode artifactBytes).toOption

theorem decodedRaw_isSome : decodedRaw?.isSome = true := by
  native_decide

def decodedRaw : RawModule :=
  decodedRaw?.getD default

theorem decode_eq_decodedRaw : decode artifactBytes = .ok decodedRaw := by
  cases hdecode : decode artifactBytes with
  | error error =>
      have h := decodedRaw_isSome
      unfold decodedRaw? at h
      rw [hdecode] at h
      change (none : Option RawModule).isSome = true at h
      cases h
  | ok raw =>
      unfold decodedRaw decodedRaw?
      rw [hdecode]
      rfl

end LeanExeGen.GeneratedRb9ad29e25c8033e5.Artifact
