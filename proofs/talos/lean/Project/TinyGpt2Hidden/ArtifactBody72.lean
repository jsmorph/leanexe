import Project.TinyGpt2Hidden.ArtifactBody72Part2

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem body72Tail0_eq : body72Tail0 = Cache.raw.codes[72]!.body := by
  exact Equality.instrListEqualFuel_sound 4096 _ _ (by decide +kernel)

theorem code72_decoded_parts :
    code { bytes := artifactBytes, pos := 9349, limit := 16006 } = .ok (Cache.raw.codes[72]!, { bytes := artifactBytes, pos := 9983, limit := 16006 }) := by
  refine code_eq_of_parts (size := 632)
    (payload := { bytes := artifactBytes, pos := 9351, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 9355, limit := 9983 })
    (bodyFinish := { bytes := artifactBytes, pos := 9983, limit := 9983 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence72_tail0.trans (congrArg
      (fun body : List Instr => Except.ok ((body, Terminator.end),
        ({ bytes := artifactBytes, pos := 9983, limit := 9983 } : Cursor))) body72Tail0_eq)
  · rfl

#print axioms code72_decoded_parts
end Project.TinyGpt2Hidden.Artifact
