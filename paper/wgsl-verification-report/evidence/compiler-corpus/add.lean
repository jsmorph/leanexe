import LeanExe.WGSL.Examples.Body
open LeanExe.WGSL.Examples.Body
#compile_wgsl add 2 3 6 6 "/tmp/leanexe-wgsl-review/build/wgsl/body-check-tyz6A6/add"
#print axioms add.wgslSourceCorrect
#print axioms add.wgslShaderParsed
#print axioms add.wgslExecutionCorrect
