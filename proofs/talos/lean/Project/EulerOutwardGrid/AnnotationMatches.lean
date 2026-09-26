import Project.EulerOutwardGrid.Program
import Project.ProofKit.Annotation
















set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.EulerOutwardGrid.AnnotationMatches

def function_45_array_fold_0_program : Wasm.Program :=
  (Project.ProofKit.Annotation.region Project.EulerOutwardGrid.func45 [] 0 28).getD []

theorem function_45_array_fold_0_eq :
    Project.ProofKit.Annotation.region Project.EulerOutwardGrid.func45 [] 0 28 = some function_45_array_fold_0_program := by
  rfl

theorem function_45_array_fold_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve Project.EulerOutwardGrid.func45 []).getD []).drop 0 =
      Project.EulerOutwardGrid.AnnotationMatches.function_45_array_fold_0_program ++ ((Project.ProofKit.Annotation.resolve Project.EulerOutwardGrid.func45 []).getD []).drop 28 := by
  rfl









end Project.EulerOutwardGrid.AnnotationMatches
