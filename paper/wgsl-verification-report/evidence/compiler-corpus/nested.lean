import LeanExe.WGSL.Examples.Body
open LeanExe.WGSL.Examples.Body
#compile_wgsl nested 2 3 12 9 "CHECKOUT/build/wgsl/body-check-tyz6A6/nested"
#print axioms nested.wgslSourceCorrect
#print axioms nested.wgslShaderParsed
#print axioms nested.wgslExecutionCorrect
