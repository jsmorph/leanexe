import Project.EulerReconstruction.ArtifactParsed

set_option maxRecDepth 1048576

namespace Project.EulerReconstruction.Artifact

open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem decode_eq_cache_computed : decode artifactBytes = .ok Cache.raw := by
  exact decode_eq_cache_parts

def decodedRaw? : Option RawModule :=
  (decode artifactBytes).toOption

theorem decodedRaw_isSome : decodedRaw?.isSome = true := by
  unfold decodedRaw?
  rw [decode_eq_cache_computed]
  rfl

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

#print axioms decode_eq_cache_computed
#print axioms decode_eq_decodedRaw
end Project.EulerReconstruction.Artifact
