import Project.TinyGpt2Hidden.ArtifactBody57Part4

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem body57Tail0_eq : body57Tail0 = Cache.raw.codes[57]!.body := by
  exact Equality.instrListEqualFuel_sound 4096 _ _ (by decide +kernel)

theorem code57_decoded_parts :
    code { bytes := artifactBytes, pos := 6675, limit := 16006 } = .ok (Cache.raw.codes[57]!, { bytes := artifactBytes, pos := 7739, limit := 16006 }) := by
  refine code_eq_of_parts (size := 1062)
    (payload := { bytes := artifactBytes, pos := 6677, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 6681, limit := 7739 })
    (bodyFinish := { bytes := artifactBytes, pos := 7739, limit := 7739 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence57_tail0.trans (congrArg
      (fun body : List Instr => Except.ok ((body, Terminator.end),
        ({ bytes := artifactBytes, pos := 7739, limit := 7739 } : Cursor))) body57Tail0_eq)
  · rfl

#print axioms code57_decoded_parts
end Project.TinyGpt2Hidden.Artifact
