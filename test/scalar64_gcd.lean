import LeanExe.Correct.Scalar64.Gcd

open LeanExe.Correct.Scalar64

-- These invoke the universal source certificate, not sampled native equality.
example : Runs [gcdBody] gcdBody (encodeArgs [0, 0])
    (encodeWord (LeanExe.Examples.TalosGcd.gcd 0 0)) := gcdCertificate.computes (0, 0)
example (x : UInt64) : Runs [gcdBody] gcdBody (encodeArgs [x, 0])
    (encodeWord (LeanExe.Examples.TalosGcd.gcd x 0)) := gcdCertificate.computes (x, 0)
example (x y : UInt64) : Runs [gcdBody] gcdBody (encodeArgs [x, y])
    (encodeWord (LeanExe.Examples.TalosGcd.gcd x y)) := gcdCertificate.computes (x, y)

#print axioms remainder_decreases
#print axioms gcd_core
#print axioms Iterates.repeatM_eq
#print axioms gcd_original
#print axioms gcdCertificate
