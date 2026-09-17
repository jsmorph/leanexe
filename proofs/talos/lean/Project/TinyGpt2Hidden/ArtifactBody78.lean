import Project.TinyGpt2Hidden.ArtifactBody78Part2

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem body78Tail0_eq : body78Tail0 = Cache.raw.codes[78]!.body := by
  exact Equality.instrListEqualFuel_sound 4096 _ _ (by decide +kernel)

theorem code78_decoded_parts :
    code { bytes := artifactBytes, pos := 15653, limit := 16006 } = .ok (Cache.raw.codes[78]!, { bytes := artifactBytes, pos := 16006, limit := 16006 }) := by
  refine code_eq_of_parts (size := 351)
    (payload := { bytes := artifactBytes, pos := 15655, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 15658, limit := 16006 })
    (bodyFinish := { bytes := artifactBytes, pos := 16006, limit := 16006 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence78_tail0.trans (congrArg
      (fun body : List Instr => Except.ok ((body, Terminator.end),
        ({ bytes := artifactBytes, pos := 16006, limit := 16006 } : Cursor))) body78Tail0_eq)
  · rfl

#print axioms code78_decoded_parts
end Project.TinyGpt2Hidden.Artifact
