import Examples.KernelUnsoundness
import Examples.BogusArtifactClaim

/-!
# Isolated demonstrations

This library is not part of the verified `Project` library and nothing in
`Project` imports it.  `Examples.KernelUnsoundness` derives `False`, so
any module importing this library can prove anything.  It is built only
by explicit request: `defaultTargets` names `Project` alone.
-/
