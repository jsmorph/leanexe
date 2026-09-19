import LeanExe.WGSL.Examples.Body
open LeanExe.WGSL.Examples.Body
#compile_wgsl matmul 2 3 8 12 "/tmp/leanexe-wgsl-review/build/wgsl/body-check-tyz6A6/matmul"
#print axioms matmul.wgslSourceCorrect
#print axioms matmul.wgslShaderParsed
#print axioms matmul.wgslExecutionCorrect
