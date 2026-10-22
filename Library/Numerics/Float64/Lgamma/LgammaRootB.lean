import Library.Numerics.Float64.Lgamma.LgammaRootB0
import Library.Numerics.Float64.Lgamma.LgammaRootB1
import Library.Numerics.Float64.Lgamma.LgammaRootB2

/-!
RootFact on the ranges 3, 4, 5 of `Library.Numerics.Float64.Lgamma.LgammaApprox.rootRanges` (`lgamma.c`, commit `ff2f71f6`).  On
each range, point values of `lgamma` at `A`, `B`, and the end away from the pole confine `|lgamma x|
≤ (1 + 2 ^ -40) afh` to `[A, B]` (`GammaRoot.root_domain_dec`, `root_domain_inc`).  A Taylor model
at 150 bits about the stored zero `-x0` bounds the polynomial absolutely within `2 ^ -120` where
`|lgamma| ≤ 2 ^ -24`, and models at 120 bits bound it within `2 ^ -63` relative on the pieces on
both sides (`GammaRoot.rootOk`).  The proofs of the three ranges are in `LgammaRootB0`,
`LgammaRootB1`, and `LgammaRootB2`, one module per range, since the module of all three passed the
20-minute limit of a build.
-/
