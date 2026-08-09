# Euclidean UInt64 GCD loop

Use this entry after checked scalar-loop support has reduced an artifact proof to the Euclidean transition over two `UInt64` accumulators.  State the invariant as equality between the current natural-number GCD and the initial requested GCD.  Use the divisor's `toNat` value as the termination measure.

In the zero branch, the invariant and `Nat.gcd_zero_right` identify the returned first accumulator.  In the nonzero branch, `UInt64.toNat_mod` connects the generated remainder operation with natural-number remainder, while `Nat.gcd_rec` and GCD commutativity preserve the invariant.  `Nat.mod_lt` proves strict measure decrease from the nonzero divisor.

This entry supplies application mathematics and does not identify an artifact region.  Compose it with `scalar-post-test-loop`, generated body and condition equations, and a generated entry or termination adapter.  A different GCD algorithm or operand order may need a separate normalization step, which the proof journal should record before the entry receives broader automatic selection.
