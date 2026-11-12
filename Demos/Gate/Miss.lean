import Demos.Gate.GateSoundness
import Demos.Gate.Gaussian

/-!
The probability of a missed association.  When `gate nu s g` accepts, the real covariance `S` of
`s` is positive definite, so by `Model.gaussian_tail` an innovation distributed as
`multivariateGaussian 0 S` lies outside the gate with threshold `γ`, the real value of `g`, with
probability `Model.tail d γ`, where `d` is the size of `nu`.  `gate_miss` states that probability,
and `gate_miss_tail` adds that an accepted result of `tail k g` of the module `chisquare`, with
`k = d`, contains it.
-/

namespace Demos.Gate

open MeasureTheory ProbabilityTheory WithLp Library.Numerics.Interval
open CodeLib.IEEE64 (value)

/-- When `gate nu s g` returns status 0, an innovation distributed as `multivariateGaussian 0 S`,
with `S` the real covariance of `s`, has a squared Mahalanobis distance above the real value `γ`
of `g` with probability `Model.tail d γ`, where `d` is the size of `nu`. -/
theorem gate_miss {nu s : Array Float} {g : Float} (hsz : nu.size < 2 ^ 64 ∧ s.size < 2 ^ 64)
    (h : (gate nu s g).status = 0) :
    (multivariateGaussian 0 (covariance s nu.size)).real
        {ν | value g.toBits < Model.mahalanobis (covariance s nu.size) (ofLp ν)} =
      Model.tail nu.size (value g.toBits) := by
  obtain ⟨hd, -, -, -, -, hpd, -⟩ := gate_sound hsz h
  exact Model.gaussian_tail hd hpd _

/-- When `gate nu s g` and `tail k g` with `k = d`, the size of `nu`, both return status 0, the
interval of `tail k g` contains the probability that an innovation distributed as
`multivariateGaussian 0 S` lies outside the gate. -/
theorem gate_miss_tail {nu s : Array Float} {g : Float} {k : UInt64}
    (hsz : nu.size < 2 ^ 64 ∧ s.size < 2 ^ 64) (hk : k.toNat = nu.size)
    (h : (gate nu s g).status = 0) (ht : (tail k g).status = 0) :
    Contains (tail k g) ((multivariateGaussian 0 (covariance s nu.size)).real
      {ν | value g.toBits < Model.mahalanobis (covariance s nu.size) (ofLp ν)}) := by
  rw [gate_miss hsz h, ← hk]
  exact (tail_sound ht).2.2.2

#print axioms gate_miss
#print axioms gate_miss_tail

end Demos.Gate
