# Orbit: lemmas about iterates

[The lemmas](Basic.lean) are the facts about iterates and orbits that [the LCG](../Lcg/README.md),
[Park and Miller's generator](../ParkMiller/README.md), and [xorshift64](../Xorshift/README.md)
share.  `loop_eq_iterate` states that `LeanExe.loop` with an unused index computes an iterate, so
`advance n x` is `step^[n.toNat] x`.  `minimalPeriod_eq_of_isPeriodicPt_iff` gives the minimal
period of a point as the `N` whose multiples are its periods.  `existsUnique_iterate` states that an
orbit that stays in a finite set with as many elements as the period reaches each element at
exactly one count below the period, and `natCard_uint64` counts the words.
