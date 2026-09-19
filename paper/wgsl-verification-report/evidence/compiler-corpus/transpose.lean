import LeanExe.WGSL.Examples.Body
open LeanExe.WGSL.Examples.Body
#compile_wgsl transpose 2 3 6 6 "CHECKOUT/build/wgsl/body-check-tyz6A6/transpose"
#print axioms transpose.wgslSourceCorrect
#print axioms transpose.wgslShaderParsed
#print axioms transpose.wgslExecutionCorrect
