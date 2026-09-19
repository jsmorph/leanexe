import LeanExe.WGSL.Examples.Body
open LeanExe.WGSL.Examples.Body
#compile_wgsl multiply 2 3 6 6 "/tmp/leanexe-wgsl-review/build/wgsl/body-check-tyz6A6/multiply"
#print axioms multiply.wgslSourceCorrect
#print axioms multiply.wgslShaderParsed
#print axioms multiply.wgslExecutionCorrect
