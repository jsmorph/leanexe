import Project.TinyGpt2Hidden.ArtifactBody69Part11

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem body69Tail0_eq : body69Tail0 = Cache.raw.codes[69]!.body := by
  exact Equality.instrListEqualFuel_sound 4096 _ _ (by decide +kernel)

theorem code69_decoded_parts :
    code { bytes := artifactBytes, pos := 8354, limit := 16006 } = .ok (Cache.raw.codes[69]!, { bytes := artifactBytes, pos := 9325, limit := 16006 }) := by
  refine code_eq_of_parts (size := 969)
    (payload := { bytes := artifactBytes, pos := 8356, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 8359, limit := 9325 })
    (bodyFinish := { bytes := artifactBytes, pos := 9325, limit := 9325 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence69_tail0.trans (congrArg
      (fun body : List Instr => Except.ok ((body, Terminator.end),
        ({ bytes := artifactBytes, pos := 9325, limit := 9325 } : Cursor))) body69Tail0_eq)
  · rfl

#print axioms code69_decoded_parts
end Project.TinyGpt2Hidden.Artifact
