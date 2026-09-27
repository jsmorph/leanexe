import LeanExeGen.GeneratedRbade8cb1a4e3a423.Program
import Project.ProofKit.Annotation
import Project.ProofKit.FixedArrayPairResult
import Project.ProofKit.ScalarTransition





set_option maxRecDepth 1048576

namespace LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches

def function_0_while_loop_0_condition :
    Project.ProofKit.ScalarTransition.Expr .bool :=
  .and (.not (.eq (.get 0) (.const (0 : UInt64)))) (.eq (.get 5) (.const (0 : UInt64)))

def function_0_while_loop_0_body : Project.ProofKit.ScalarTransition.Stmt :=
  .ite (.leU (.get 1) (.const (1 : UInt64))) (.seq (.assign 4 (.get 3)) (.assign 5 (.const (1 : UInt64)))) (.ite (.ltU (.bin .divU (.get 1) (.get 2)) (.get 2)) (.seq (.assign 4 (.bin .add (.get 3) (.const (1 : UInt64)))) (.assign 5 (.const (1 : UInt64)))) (.ite (.not (.eq (.ite (.eq (.ite (.eq (.bin .remU (.get 1) (.get 2)) (.const (0 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (1 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (0 : UInt64)))) (.seq (.seq (.seq (.seq (.assign 6 (.bin .divU (.get 1) (.get 2))) (.assign 7 (.get 2))) (.assign 8 (.bin .add (.get 3) (.const (1 : UInt64))))) (.seq (.seq (.seq (.seq (.seq (.assign 9 (.get 6)) (.assign 10 (.get 7))) (.assign 11 (.get 8))) (.assign 1 (.get 9))) (.assign 2 (.get 10))) (.assign 3 (.get 11)))) (.assign 0 (.bin .sub (.get 0) (.const (1 : UInt64))))) (.seq (.seq (.seq (.seq (.assign 12 (.get 1)) (.assign 13 (.ite (.not (.eq (.ite (.eq (.ite (.eq (.get 2) (.const (2 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (1 : UInt64))) (.const (1 : UInt64)) (.const (0 : UInt64))) (.const (0 : UInt64)))) (.const (3 : UInt64)) (.bin .add (.get 2) (.const (2 : UInt64)))))) (.assign 14 (.get 3))) (.seq (.seq (.seq (.seq (.seq (.assign 15 (.get 12)) (.assign 16 (.get 13))) (.assign 17 (.get 14))) (.assign 1 (.get 15))) (.assign 2 (.get 16))) (.assign 3 (.get 17)))) (.assign 0 (.bin .sub (.get 0) (.const (1 : UInt64)))))))

def function_0_while_loop_0_program : Wasm.Program :=
  Project.ProofKit.ScalarTransition.whileProgram
    18 function_0_while_loop_0_condition function_0_while_loop_0_body

theorem function_0_while_loop_0_eq :
    Project.ProofKit.Annotation.region LeanExeGen.GeneratedRbade8cb1a4e3a423.func0
      [] 2
      3 = some function_0_while_loop_0_program := by
  rfl

end LeanExeGen.GeneratedRbade8cb1a4e3a423.AnnotationMatches
