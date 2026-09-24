import LeanExe.Extract.ScalarEntryCorrectness

/-! Focused audit of the current extraction proofs. The independent TypeSafety
library keeps its own stricter policy; it does not import these modules. -/
#print axioms LeanExe.Extract.Core.ScalarPrimitive.lower_correct
#print axioms LeanExe.Extract.Core.extractScalarExpr_correct
#print axioms LeanExe.Extract.Core.extractScalarExpr_accepts
#print axioms LeanExe.Extract.Core.extractScalarExpr_supported
#print axioms LeanExe.Extract.Core.extractScalarExpr_total_correct
#print axioms LeanExe.Extract.Core.extractScalarFunc_correct
#print axioms LeanExe.Extract.Core.extractScalarFunc_accepts
#print axioms LeanExe.Extract.Core.compileEnvironment_scalar_total_correct
