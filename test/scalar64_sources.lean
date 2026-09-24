import LeanExe.Correct.Scalar64.Prng
import LeanExe.Correct.Scalar64.Helper
import LeanExe.Correct.Scalar64.Gcd

open LeanExe.Correct.Scalar64

example (state : UInt64) : Runs [mixBody] mixBody (encodeArgs [state])
    (encodeWord (LeanExe.Examples.Prng.mix state)) := mixCertificate.computes state

example (x y : UInt64) : Runs [combineBody, helperBody] helperBody (encodeArgs [x, y])
    (encodeWord (LeanExe.Examples.ScalarHelper.caller x y)) := helperCertificate.computes (x, y)

#print axioms bitwise64_eq
#print axioms Runs.bitAnd
#print axioms Runs.bitOr
#print axioms Runs.bitXor
#print axioms Runs.shiftLeft
#print axioms Runs.shiftRight
#print axioms mixCertificate
#print axioms helperCertificate
#print axioms affineCertificate
#print axioms chooseCertificate
#print axioms gcdCertificate
