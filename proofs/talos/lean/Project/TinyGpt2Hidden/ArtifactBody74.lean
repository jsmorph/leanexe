import Project.TinyGpt2Hidden.ArtifactBody74Part16

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem body74Tail0_eq : body74Tail0 = Cache.raw.codes[74]!.body := by
  exact Equality.instrListEqualFuel_sound 4096 _ _ (by decide +kernel)

theorem code74_decoded_parts :
    code { bytes := artifactBytes, pos := 9995, limit := 16006 } = .ok (Cache.raw.codes[74]!, { bytes := artifactBytes, pos := 15177, limit := 16006 }) := by
  refine code_eq_of_parts (size := 5180)
    (payload := { bytes := artifactBytes, pos := 9997, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 10001, limit := 15177 })
    (bodyFinish := { bytes := artifactBytes, pos := 15177, limit := 15177 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence74_tail0.trans (congrArg
      (fun body : List Instr => Except.ok ((body, Terminator.end),
        ({ bytes := artifactBytes, pos := 15177, limit := 15177 } : Cursor))) body74Tail0_eq)
  · rfl

#print axioms code74_decoded_parts
end Project.TinyGpt2Hidden.Artifact
