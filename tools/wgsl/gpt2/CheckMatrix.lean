import Project.Gpt2.MatrixArithmetic

open LeanExe.WGSL Project.Gpt2.Matrix

#print axioms exact_from_dispatch
#print axioms vocabulary_left_layout
#print axioms vocabulary_right_layout
#print axioms vocabulary_from_dispatch
#print axioms vocabulary_exact
#print axioms layer_shape
#print axioms layer_matrix_injective
#print axioms head_shapes
#print axioms fifty_matrices
#print axioms attention_input_range
#print axioms fusion_from_dispatch
#print axioms vocabulary_fusion_choices
#print axioms Project.WGSL.ArithmeticChoice.fusion_iff_choices
#print axioms Project.WGSL.ArithmeticChoice.separate_evaluate

namespace ArithmeticRegression
open Project.WGSL Project.WGSL.MatrixView

private def x : WordBuffer := fun k => if k = 0 then 0xbf800000 else 0x3f800001
private def w : MatrixView.Matrix := fun k _ => if k = 0 then 0x3f800000 else 0x3f7ffffe

theorem separate_word : ArithmeticChoice.evaluate (fun _ => false) x w 0 2 = 0 := by decide +kernel
theorem fused_word : ArithmeticChoice.evaluate (fun _ => true) x w 0 2 = 0xa8800000 := by decide +kernel

/-- Both distinct words are admitted, each by its explicit computation. -/
theorem both_admitted : ColumnRun Binary32.semantics fusion x w 0 2 0 ∧
    ColumnRun Binary32.semantics fusion x w 0 2 0xa8800000 :=
  ⟨ArithmeticChoice.fusion_iff_choices.mpr ⟨fun _ => false, separate_word.symm⟩,
   ArithmeticChoice.fusion_iff_choices.mpr ⟨fun _ => true, fused_word.symm⟩⟩

#print axioms separate_word
#print axioms fused_word
#print axioms both_admitted
end ArithmeticRegression

private def unwrap (result : Except String α) : IO α := do
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

/-- Check the demo's fifty descriptors against the proved layer/head mapping.
This checks their interpretation, not checkpoint provenance or runner code. -/
def main (args : List String) : IO Unit := do
  let [manifestPath] := args | throw (IO.userError "expected demo manifest")
  let manifest ← unwrap (Lean.Json.parse (← IO.FS.readFile manifestPath))
  let actual ← unwrap (manifest.getObjVal? "matrices")
  unless actual == Lean.toJson bindings do
    throw (IO.userError "GPT-2 matrix assignments differ from the Lean layer/head plan")
  IO.println "GPT2_MATRIX_PLAN 50"
