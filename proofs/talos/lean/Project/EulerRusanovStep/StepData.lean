import Project.EulerRusanovStep.ArtifactTranslation
import Project.EulerRusanovStep.Spec

/-!
# Fixed Euler step raw-data certificate

The public dataset contains the seven words below, in source ABI order.
The exact-artifact theorem carries the existing decoded-real certificate to
those same words.  CSV and plotting remain host presentation.
-/
namespace Project.EulerRusanovStep.StepData

open Wasm

/-- Status and the two conservative cells, in the public dataset's order. -/
def publishedWords : List UInt64 :=
  [0x0000000000000000,
   0x3FE9E00000000000, 0x3FBCCCCCCCCCCCCC, 0x4000100000000000,
   0x3FD4400000000000, 0x3FBCCCCCCCCCCCCE, 0x3FE7C00000000000]

theorem model_words_published : Model.resultWords = publishedWords := by
  unfold Model.resultWords
  rw [Model.sodQuarterStepCheckedBitsModel_exact]
  rfl

/-- Exact words, complete store preservation, and the decoded-real numerical
certificate for the fixed two-cell Sod quarter step. -/
noncomputable def StepV1SpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit),
    TerminatesWith env m 6 initial []
      (fun final values =>
        final = initial ∧
          values = publishedWords.reverse.map Wasm.Value.i64 ∧
          Numerical.RealCertificate Model.expectedSodQuarterStepBits)

theorem stepV1_generated :
    StepV1SpecFor Project.EulerRusanovStep.«module» := by
  intro env initial
  refine TerminatesWith.mono
    (Spec.sodQuarterStepCheckedBits_wat_real env initial) ?_
  rintro final values ⟨hfinal, hvalues, hreal⟩
  refine ⟨hfinal, ?_, ?_⟩
  · simpa only [Model.resultValues, Model.sodQuarterStepCheckedBitsModel_exact,
      Model.expectedSodQuarterStepBits, publishedWords, List.reverse_cons,
      List.reverse_nil, List.append_assoc, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil] using hvalues
  · simpa only [Model.sodQuarterStepCheckedBitsModel_exact] using hreal

/-- The frozen, decoded and validated bytes realize the published dataset. -/
theorem artifact_stepV1 :
    ∃ raw validated,
      Wasm.Binary.decode Artifact.artifactBytes = .ok raw ∧
      Wasm.Binary.validate raw = .ok validated ∧
      Wasm.Binary.CoreValid raw ∧
      StepV1SpecFor validated.toTalos := by
  apply Artifact.artifact_correct_of StepV1SpecFor
  simpa [Artifact.executionCache] using stepV1_generated

#print axioms model_words_published
#print axioms stepV1_generated
#print axioms artifact_stepV1

end Project.EulerRusanovStep.StepData
