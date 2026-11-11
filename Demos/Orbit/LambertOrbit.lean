import Mathlib.Tactic

/-!
Draft toward review open item 1: the two scalar identities behind the statement that Izzo's
velocities at `r1` and `r2` belong to one orbit for every `x`.  In normalized variables, with
`c = s(1 - λ²)`, `n1 = s N1`, `n2 = s N2`, and `P = n1 n2 - (1 - ρ²) c²/2`, the components of
`v2 - v1 - β ((w × r2)/n2 - (w × r1)/n1)` along `r1` and `r2` vanish when
`y² = 1 - λ² + λ² x²`.
-/

namespace Demos.Orbit.LambertOrbit

theorem core_one {s L ρ x y γ c n1 n2 P κ β a1 : ℝ} (hs : s ≠ 0) (hL : L ≠ 0)
    (hL1 : 1 - L ^ 2 ≠ 0) (hρ1 : 1 - ρ ^ 2 ≠ 0) (hN1 : 1 + ρ + L ^ 2 * (1 - ρ) ≠ 0)
    (hq : y + L * x ≠ 0)
    (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2)
    (hc : c = s * (1 - L ^ 2)) (hn1 : n1 = s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2))
    (hn2 : n2 = s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) (hP : P = n1 * n2 - (1 - ρ ^ 2) * c ^ 2 / 2)
    (hκ : κ = γ * (y + L * x) / (L * c * s))
    (hβ : β = 2 * γ / (s ^ 2 * (y + L * x) * L * (1 - ρ ^ 2) * c))
    (ha : a1 = γ * ((L * y - x) - ρ * (L * y + x)) / n1 ^ 2) :
    -κ - (a1 - κ * P / n1 ^ 2) = β * (P / n1 - n2) := by
  subst hκ hβ ha hP hc hn1 hn2
  have key : -(γ * (y + L * x) / (L * (s * (1 - L ^ 2)) * s)) -
      (γ * ((L * y - x) - ρ * (L * y + x)) / (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) ^ 2 -
        γ * (y + L * x) / (L * (s * (1 - L ^ 2)) * s) *
          (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) -
            (1 - ρ ^ 2) * (s * (1 - L ^ 2)) ^ 2 / 2) / (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) ^ 2) -
      2 * γ / (s ^ 2 * (y + L * x) * L * (1 - ρ ^ 2) * (s * (1 - L ^ 2))) *
        ((s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) -
            (1 - ρ ^ 2) * (s * (1 - L ^ 2)) ^ 2 / 2) / (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) -
          s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) =
      -γ * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (y ^ 2 - (1 - L ^ 2 + L ^ 2 * x ^ 2)) /
        (L * (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) ^ 2 * (y + L * x)) := by
    field_simp
    ring
  rw [hy, sub_self, mul_zero, zero_div] at key
  linarith

theorem core_two {s L ρ x y γ c n1 n2 P κ β a2 : ℝ} (hs : s ≠ 0) (hL : L ≠ 0)
    (hL1 : 1 - L ^ 2 ≠ 0) (hρ1 : 1 - ρ ^ 2 ≠ 0) (hN2 : 1 - ρ + L ^ 2 * (1 + ρ) ≠ 0)
    (hq : y + L * x ≠ 0) (hy : y ^ 2 = 1 - L ^ 2 + L ^ 2 * x ^ 2)
    (hc : c = s * (1 - L ^ 2)) (hn1 : n1 = s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2))
    (hn2 : n2 = s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) (hP : P = n1 * n2 - (1 - ρ ^ 2) * c ^ 2 / 2)
    (hκ : κ = γ * (y + L * x) / (L * c * s))
    (hβ : β = 2 * γ / (s ^ 2 * (y + L * x) * L * (1 - ρ ^ 2) * c))
    (ha : a2 = -(γ * ((L * y - x) + ρ * (L * y + x))) / n2 ^ 2) :
    (a2 + κ * P / n2 ^ 2) - κ = β * (P / n2 - n1) := by
  subst hκ hβ ha hP hc hn1 hn2
  have key : (-(γ * ((L * y - x) + ρ * (L * y + x))) / (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) ^ 2 +
        γ * (y + L * x) / (L * (s * (1 - L ^ 2)) * s) *
          (s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) -
            (1 - ρ ^ 2) * (s * (1 - L ^ 2)) ^ 2 / 2) / (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) ^ 2) -
      γ * (y + L * x) / (L * (s * (1 - L ^ 2)) * s) -
      2 * γ / (s ^ 2 * (y + L * x) * L * (1 - ρ ^ 2) * (s * (1 - L ^ 2))) *
        ((s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2) * (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) -
            (1 - ρ ^ 2) * (s * (1 - L ^ 2)) ^ 2 / 2) / (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) -
          s * ((1 + ρ + L ^ 2 * (1 - ρ)) / 2)) =
      -γ * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2) * (y ^ 2 - (1 - L ^ 2 + L ^ 2 * x ^ 2)) /
        (L * (s * ((1 - ρ + L ^ 2 * (1 + ρ)) / 2)) ^ 2 * (y + L * x)) := by
    field_simp
    ring
  rw [hy, sub_self, mul_zero, zero_div] at key
  linarith


end Demos.Orbit.LambertOrbit
