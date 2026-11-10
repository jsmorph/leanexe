import Demos.Rcv.Maine.Spec
import Demos.Rcv.Variants

/-!
The counts with which T11 and T12 of [the requirements](requirements.md), section "Theorems",
compare the count.  `countWithoutTest`, the count without the initial test, runs the rounds of the
count from `C₁ = K` whatever the first rankings, so that it is the count whenever the initial test
elects no one.  `singleCount`, the single count, is the count of the Oakland requirements without
its rule 3, with this module's interpretation: `Demos.Rcv.Variants.ruleSingle` decides each round,
naming a candidate that holds more than half of `Tᵣ`, ending without a winner when `Tᵣ` is 0, and
otherwise eliminating the candidate with the fewest votes, by the order on a tie.  Both run
`Demos.Rcv.Spec.run` from `K` with the count's fuel.
-/

namespace Demos.Rcv.Maine

open Demos.Rcv Demos.Rcv.Spec

/-- The count without the initial test: the rounds of the count from round 1 with `C₁ = K`. -/
def countWithoutTest (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) :
    Count :=
  run (interpret kinds) (decision order) ballots ((countedSet kinds).length + 1)
    (countedSet kinds)

/-- The single count: the rounds of the Oakland rules 1, 2, and 4 with this module's
interpretation, from round 1 with `C₁ = K`. -/
def singleCount (kinds : List Kind) (order : List Nat) (ballots : List (List UInt64)) : Count :=
  run (interpret kinds) (Variants.ruleSingle order) ballots ((countedSet kinds).length + 1)
    (countedSet kinds)

end Demos.Rcv.Maine
