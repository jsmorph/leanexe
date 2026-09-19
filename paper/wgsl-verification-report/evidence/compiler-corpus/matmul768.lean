import LeanExe.WGSL.Examples.Body
open LeanExe.WGSL.Examples.Body
#compile_wgsl matmul768 1 3 768 2304 "/tmp/leanexe-wgsl-review/build/wgsl/body-check-tyz6A6/matmul768"
#print axioms matmul768.wgslSourceCorrect
#print axioms matmul768.wgslShaderParsed
#print axioms matmul768.wgslExecutionCorrect
