import Mathlib

/-!
The error of the compensated reciprocal of `Tan.kernelTan`, in real numbers scaled by `w`: with
`α = a w ≈ -1`, `θ = t w`, `ζ = z / w`, `ω = W / w`, and `ν = v / w`, the result `t + m` times `w`
lies within `u / 2 ^ 12 + 3 η` of `-w / W`.
-/

namespace Verified.Examples.TanComp

theorem abs_mul_le {x y X Y : ℝ} (hx : |x| ≤ X) (hy : |y| ≤ Y) : |x * y| ≤ X * Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) ((abs_nonneg _).trans hx)

set_option maxHeartbeats 1000000 in
theorem comp_real (u η α θ ζ ω ν s q o M : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2 ^ 53)
    (hη0 : 0 ≤ η) (hη : η ≤ u / 2 ^ 100)
    (hα : |α + 1| ≤ u + η) (hθ : |θ - α| ≤ |α| / 2 ^ 20) (hζ : |ζ - 1| ≤ 1 / 2 ^ 20)
    (hω : |ω - 1| ≤ 2 * u) (hν : |ν - (ω - ζ)| ≤ u * |ω - ζ|)
    (hs : |s - (1 + θ * ζ)| ≤ u * |1 + θ * ζ|) (hq : |q - θ * ν| ≤ u * |θ * ν| + η)
    (ho : |o - (s + q)| ≤ u * |s + q|) (hM : |M - α * o| ≤ u * |α * o| + η) :
    |θ + M + 1 / ω| ≤ u / 2 ^ 12 + 3 * η := by
  have hu1 : u ≤ 1 / 2 ^ 53 := hu
  have hαb : |α| ≤ 1 + u + η := by
    have := abs_sub_abs_le_abs_sub α (-1)
    rw [sub_neg_eq_add, abs_neg, abs_one] at this
    linarith
  have hθb : |θ| ≤ 101 / 100 := by
    have := abs_sub_abs_le_abs_sub θ α
    have : |α| / 2 ^ 20 ≤ 1 / 2 ^ 19 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : u + η ≤ 1 / 2 := by linarith
      nlinarith
    linarith
  have hω0 : 1 / 2 ≤ ω := by
    have := (abs_le.mp hω).1
    linarith
  have hωζ : |ω - ζ| ≤ 1 / 2 ^ 19 := by
    have h := abs_sub_le ω 1 ζ
    rw [abs_sub_comm 1 ζ] at h
    have : 2 * u ≤ 1 / 2 ^ 20 := by linarith
    linarith
  -- `1 + θ ω` is small.
  have h1θω : |1 + θ * ω| ≤ 1 / 2 ^ 18 := by
    have hid : 1 + θ * ω = (α + 1) + α * (ω - 1) + (θ - α) * ω := by ring
    have e2 : |α * (ω - 1)| ≤ (1 + u + η) * (2 * u) := abs_mul_le hαb hω
    have hωb : |ω| ≤ 1 + 2 * u := by
      have := abs_sub_abs_le_abs_sub ω 1
      rw [abs_one] at this
      linarith
    have e3 : |(θ - α) * ω| ≤ (1 + u + η) / 2 ^ 20 * (1 + 2 * u) :=
      abs_mul_le (hθ.trans (div_le_div_of_nonneg_right hαb (by positivity))) hωb
    rw [hid]
    have := abs_add_le ((α + 1) + α * (ω - 1)) ((θ - α) * ω)
    have := abs_add_le (α + 1) (α * (ω - 1))
    have : (1 + u + η) * (2 * u) ≤ 3 * u := by nlinarith
    have : (1 + u + η) / 2 ^ 20 * (1 + 2 * u) ≤ 11 / 10 / 2 ^ 20 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  -- The pieces of `o`.
  have h1θζ : |1 + θ * ζ| ≤ 1 / 2 ^ 17 := by
    have hid : 1 + θ * ζ = (1 + θ * ω) - θ * (ω - ζ) := by ring
    have := abs_mul_le hθb hωζ
    rw [hid]
    have := abs_sub (1 + θ * ω) (θ * (ω - ζ))
    linarith
  have hθν : |θ * ν| ≤ 1 / 2 ^ 18 := by
    have hνb : |ν| ≤ (1 + u) * (1 / 2 ^ 19) := by
      have := abs_sub_abs_le_abs_sub ν (ω - ζ)
      have := mul_le_mul_of_nonneg_left hωζ hu0
      nlinarith
    have := abs_mul_le hθb hνb
    have : 101 / 100 * ((1 + u) * (1 / 2 ^ 19)) ≤ 1 / 2 ^ 18 := by nlinarith
    linarith
  have es := hs.trans (mul_le_mul_of_nonneg_left h1θζ hu0)
  have eq := hq.trans (add_le_add (mul_le_mul_of_nonneg_left hθν hu0) le_rfl)
  have hsq : |s + q| ≤ 1 / 2 ^ 16 := by
    have hid : s + q = (1 + θ * ζ) + θ * ν + (s - (1 + θ * ζ)) + (q - θ * ν) := by ring
    rw [hid]
    have h1 := abs_add_le ((1 + θ * ζ) + θ * ν + (s - (1 + θ * ζ))) (q - θ * ν)
    have h2 := abs_add_le ((1 + θ * ζ) + θ * ν) (s - (1 + θ * ζ))
    have h3 := abs_add_le (1 + θ * ζ) (θ * ν)
    have : u * (1 / 2 ^ 17) + (u * (1 / 2 ^ 18) + η) ≤ 1 / 2 ^ 18 := by nlinarith
    linarith
  have eo := ho.trans (mul_le_mul_of_nonneg_left hsq hu0)
  -- `o - (1 + θ ω)`.
  have hE : |o - (1 + θ * ω)| ≤ u / 2 ^ 14 + η := by
    have hid : o - (1 + θ * ω) = θ * (ν - (ω - ζ)) + (s - (1 + θ * ζ)) + (q - θ * ν) +
        (o - (s + q)) := by ring
    have hν' : |ν - (ω - ζ)| ≤ u * (1 / 2 ^ 19) :=
      hν.trans (mul_le_mul_of_nonneg_left hωζ hu0)
    have e1 := abs_mul_le hθb hν'
    rw [hid]
    have h1 := abs_add_le (θ * (ν - (ω - ζ)) + (s - (1 + θ * ζ)) + (q - θ * ν)) (o - (s + q))
    have h2 := abs_add_le (θ * (ν - (ω - ζ)) + (s - (1 + θ * ζ))) (q - θ * ν)
    have h3 := abs_add_le (θ * (ν - (ω - ζ))) (s - (1 + θ * ζ))
    have : 101 / 100 * (u * (1 / 2 ^ 19)) + u * (1 / 2 ^ 17) + (u * (1 / 2 ^ 18) + η) +
        u * (1 / 2 ^ 16) ≤ u / 2 ^ 14 + η := by nlinarith
    linarith
  have hob : |o| ≤ 1 / 2 ^ 17 := by
    have := abs_sub_abs_le_abs_sub o (1 + θ * ω)
    have : u / 2 ^ 14 + η ≤ 1 / 2 ^ 18 := by nlinarith
    linarith
  have eM := hM.trans (add_le_add (mul_le_mul_of_nonneg_left (abs_mul_le hαb hob) hu0) le_rfl)
  -- `α + 1/ω`.
  have hαω : |α + 1 / ω| ≤ 6 * u := by
    have hid : α + 1 / ω = (α + 1) + (1 - ω) / ω := by field_simp; ring
    rw [hid]
    have h1 := abs_add_le (α + 1) ((1 - ω) / ω)
    have h2 : |(1 - ω) / ω| ≤ 4 * u := by
      rw [abs_div, abs_of_pos (show 0 < ω by linarith), abs_sub_comm,
        div_le_iff₀ (show 0 < ω by linarith)]
      have : 2 * u ≤ 4 * u * ω := by nlinarith
      linarith
    linarith
  have hid : θ + M + 1 / ω = (α + 1 / ω) * (1 + θ * ω) + α * (o - (1 + θ * ω)) +
      (M - α * o) := by
    field_simp
    ring
  rw [hid]
  have e1 := abs_mul_le hαω h1θω
  have e2 := abs_mul_le hαb hE
  have h1 := abs_add_le ((α + 1 / ω) * (1 + θ * ω) + α * (o - (1 + θ * ω))) (M - α * o)
  have h2 := abs_add_le ((α + 1 / ω) * (1 + θ * ω)) (α * (o - (1 + θ * ω)))
  have e2 : 1 + u + η ≤ 2 := by linarith
  have e3 : (1 + u + η) * (u / 2 ^ 14 + η) ≤ 2 * (u / 2 ^ 14 + η) :=
    mul_le_mul_of_nonneg_right e2 (by positivity)
  have e4 : u * ((1 + u + η) * (1 / 2 ^ 17)) ≤ u * (2 * (1 / 2 ^ 17)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 (by positivity)) hu0
  linarith

#print axioms comp_real

end Verified.Examples.TanComp
