import Project.Gpt2.Matrix

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
