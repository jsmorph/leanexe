import LeanExe.WGSL.Examples.Body
open LeanExe.WGSL.Examples.Body
#compile_wgsl zeroFold 2 3 1 1 "/tmp/leanexe-wgsl-review/build/wgsl/body-check-tyz6A6/zeroFold"
#print axioms zeroFold.wgslSourceCorrect
#print axioms zeroFold.wgslShaderParsed
#print axioms zeroFold.wgslExecutionCorrect
