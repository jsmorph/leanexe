import Project.TinyGpt2Hidden.ArtifactBody77Part0

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem body77Tail0_eq : body77Tail0 = Cache.raw.codes[77]!.body := by
  exact Equality.instrListEqualFuel_sound 4096 _ _ (by decide +kernel)

theorem code77_decoded_parts :
    code { bytes := artifactBytes, pos := 15572, limit := 16006 } = .ok (Cache.raw.codes[77]!, { bytes := artifactBytes, pos := 15653, limit := 16006 }) := by
  refine code_eq_of_parts (size := 80)
    (payload := { bytes := artifactBytes, pos := 15573, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 15576, limit := 15653 })
    (bodyFinish := { bytes := artifactBytes, pos := 15653, limit := 15653 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence77_tail0.trans (congrArg
      (fun body : List Instr => Except.ok ((body, Terminator.end),
        ({ bytes := artifactBytes, pos := 15653, limit := 15653 } : Cursor))) body77Tail0_eq)
  · rfl

#print axioms code77_decoded_parts
end Project.TinyGpt2Hidden.Artifact
