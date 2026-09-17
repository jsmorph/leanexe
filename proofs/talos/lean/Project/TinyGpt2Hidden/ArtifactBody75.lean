import Project.TinyGpt2Hidden.ArtifactBody75Part2

namespace Project.TinyGpt2Hidden.Artifact
open Wasm.Binary

attribute [local cbv_opaque] artifactBytes artifactData
attribute [local cbv_eval] artifactBytes_data artifactBytes_size

theorem body75Tail0_eq : body75Tail0 = Cache.raw.codes[75]!.body := by
  exact Equality.instrListEqualFuel_sound 4096 _ _ (by decide +kernel)

theorem code75_decoded_parts :
    code { bytes := artifactBytes, pos := 15177, limit := 16006 } = .ok (Cache.raw.codes[75]!, { bytes := artifactBytes, pos := 15544, limit := 16006 }) := by
  refine code_eq_of_parts (size := 365)
    (payload := { bytes := artifactBytes, pos := 15179, limit := 16006 }) (bodyStart := { bytes := artifactBytes, pos := 15182, limit := 15544 })
    (bodyFinish := { bytes := artifactBytes, pos := 15544, limit := 15544 }) ?_ ?_ ?_ ?_ ?_ ?_
  · cbv
  · decide
  · cbv
  · cbv
  · exact sequence75_tail0.trans (congrArg
      (fun body : List Instr => Except.ok ((body, Terminator.end),
        ({ bytes := artifactBytes, pos := 15544, limit := 15544 } : Cursor))) body75Tail0_eq)
  · rfl

#print axioms code75_decoded_parts
end Project.TinyGpt2Hidden.Artifact
