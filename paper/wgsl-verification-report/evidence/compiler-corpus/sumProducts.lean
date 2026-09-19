import LeanExe.WGSL.Examples.Body
open LeanExe.WGSL.Examples.Body
#compile_wgsl sumProducts 2 3 8 12 "/tmp/leanexe-wgsl-review/build/wgsl/body-check-tyz6A6/sumProducts"
#print axioms sumProducts.wgslSourceCorrect
#print axioms sumProducts.wgslShaderParsed
#print axioms sumProducts.wgslExecutionCorrect
