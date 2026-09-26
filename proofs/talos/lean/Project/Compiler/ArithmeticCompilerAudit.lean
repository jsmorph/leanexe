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
