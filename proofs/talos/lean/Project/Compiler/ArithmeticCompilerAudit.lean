import Project.Compiler.SourceCorrectness
import LeanExe.Source.ScalarReannotationEvaluation

#print axioms LeanExe.Extract.Arithmetic.compileEnvironment_accepts
#print axioms LeanExe.Extract.Arithmetic.compileEnvironment_success
#print axioms Project.Compiler.ArithmeticModule.retain_valid
#print axioms Project.Compiler.ArithmeticModule.alloc_valid
#print axioms Project.Compiler.ArithmeticModule.release_valid
#print axioms Project.Compiler.ArithmeticModule.extracted_module_valid
#print axioms Project.Compiler.ArithmeticModule.extracted_correct
#print axioms Project.Compiler.ArithmeticModule.compileEnvironment_correct
#print axioms Project.Compiler.ArithmeticModule.compileEnvironment_sound

#print axioms LeanExe.Source.Scalar.Reannotates.eval_iff
#print axioms LeanExe.Extract.Core.reannotation_sound
#print axioms LeanExe.Extract.Core.reannotation_accepts

#print axioms LeanExe.Extract.Core.guardDecision_sound
#print axioms LeanExe.Extract.Core.guardDecision_accepts

#print axioms LeanExe.Extract.Core.booleanFunctionApplication_sound
#print axioms LeanExe.Extract.Core.booleanFunctionApplication_accepts

#print axioms LeanExe.Extract.Core.predicateInputTypes_sound
#print axioms LeanExe.Extract.Core.predicateInputTypes_accepts

#print axioms LeanExe.Extract.Core.extractScalarFunc_boolean_correct

#print axioms LeanExe.Source.Scalar.StepMatcher.denote_cases
#print axioms LeanExe.Extract.Core.findStepMatcher_sound
#print axioms LeanExe.Extract.Core.findStepMatcher_accepts
#print axioms LeanExe.Extract.Core.expandStepMatchers_normalizes
#print axioms LeanExe.Extract.Core.expandStepMatchers_accepts
#print axioms LeanExe.Extract.Core.extractScalarEnvironmentFunc_accepts
#print axioms LeanExe.Extract.Core.extractScalarEnvironmentFunc_correct
#print axioms LeanExe.Extract.Arithmetic.compileEnvironment_environment_accepts
#print axioms Project.Compiler.ArithmeticModule.environment_extracted_correct
#print axioms Project.Compiler.ArithmeticModule.compileEnvironment_environment_correct

#print axioms LeanExe.Source.Scalar.BooleanScopeBindingForm.monadic_apply
#print axioms LeanExe.Extract.Core.booleanScopeBinding_sound
#print axioms LeanExe.Extract.Core.booleanScopeBinding_accepts

#print axioms LeanExe.Source.Scalar.BooleanScopeBindingForm.application_apply

#print axioms LeanExe.Source.Scalar.BooleanBinaryFunctionBinding.apply
#print axioms LeanExe.Extract.Core.booleanBinaryHelper_sound
#print axioms LeanExe.Extract.Core.booleanBinaryHelper_accepts
#print axioms LeanExe.Extract.Core.booleanBinaryCall_sound
#print axioms LeanExe.Extract.Core.booleanBinaryCall_accepts

#print axioms LeanExe.Source.Scalar.BooleanStep.UnitBooleanFunction.apply
#print axioms LeanExe.Extract.Core.booleanStepUnitTypes_sound
#print axioms LeanExe.Extract.Core.booleanStepUnitTypes_accepts
#print axioms LeanExe.Extract.Core.booleanStepUnitValue_sound
#print axioms LeanExe.Extract.Core.booleanStepUnitValue_accepts
#print axioms LeanExe.Extract.Core.booleanUnitStepFunction_sound
#print axioms LeanExe.Extract.Core.booleanUnitStepFunction_accepts
