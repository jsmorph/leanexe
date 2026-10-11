import LeanExe.ProofKit.F64NearestSum
import LeanExe.ProofKit.F64GridExact

/-!
Rounded division gives the nearest binary64 value to the exact quotient.  `Wasm.IEEE64.div`
rounds the scaled quotient `N / D` by `roundQuotient` on the grid of `2 ^ s`, where `s` places
the integer part in `[2 ^ 52, 2 ^ 53)`, and packs the result exactly.  `roundQuotient_error`
bounds the rounding by half a unit, `grid_nearest` compares a point of the grid with every scaled
magnitude of a word, and `div_nearest` states that the quotient of two positive words with a
normal quotient below `2 ^ 1022` is `F64NearestNonnegative.Nearest` to the exact quotient.
-/

namespace LeanExe.ProofKit.F64NearestDiv
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem roundQuotient_error (n d : Nat) (hd : 0 < d) :
    |(Wasm.IEEE32.roundQuotient n d : ℝ) - (n : ℝ) / d| ≤ 1 / 2 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : n % d < d := Nat.mod_lt _ hd
  have hnd : (n : ℝ) = ((n / d : ℕ) : ℝ) * d + ((n % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod' n d).symm
  have hx : (n : ℝ) / d = ((n / d : ℕ) : ℝ) + ((n % d : ℕ) : ℝ) / d := by
    rw [hnd]; field_simp
  have hrd0 : (0 : ℝ) ≤ ((n % d : ℕ) : ℝ) / d := by positivity
  have hrd1 : ((n % d : ℕ) : ℝ) / d < 1 := by
    rw [div_lt_one hdR]; exact_mod_cast hr
  have hd0 : (d == 0) = false := by simpa using hd.ne'
  unfold Wasm.IEEE32.roundQuotient
  simp only [hd0, Bool.false_eq_true, ite_false]
  split_ifs with h1 h2 h3
  · have : ((n % d : ℕ) : ℝ) / d < 1 / 2 := by
      rw [div_lt_iff₀ hdR]
      have : ((2 * (n % d) : ℕ) : ℝ) < d := by exact_mod_cast h1
      push_cast at this
      linarith
    rw [hx, abs_le]; constructor <;> linarith
  · have : 1 / 2 < ((n % d : ℕ) : ℝ) / d := by
      rw [lt_div_iff₀ hdR]
      have : (d : ℝ) < ((2 * (n % d) : ℕ) : ℝ) := by exact_mod_cast h2
      push_cast at this
      linarith
    push_cast
    rw [hx, abs_le]; constructor <;> linarith
  · have heq : 2 * (n % d) = d := by omega
    have : ((n % d : ℕ) : ℝ) / d = 1 / 2 := by
      rw [div_eq_iff hdR.ne']
      have : ((2 * (n % d) : ℕ) : ℝ) = d := by exact_mod_cast heq
      push_cast at this
      linarith
    rw [hx, abs_le]; constructor <;> linarith
  · have heq : 2 * (n % d) = d := by omega
    have : ((n % d : ℕ) : ℝ) / d = 1 / 2 := by
      rw [div_eq_iff hdR.ne']
      have : ((2 * (n % d) : ℕ) : ℝ) = d := by exact_mod_cast heq
      push_cast at this
      linarith
    push_cast
    rw [hx, abs_le]; constructor <;> linarith

/-- A point `R 2 ^ s` within half a unit of `x` in the binade `[2 ^ (52 + s), 2 ^ (53 + s))` is
at least as close to `x` as any scaled magnitude on the grid of its own binade. -/
theorem grid_nearest (x : ℝ) (s R : Nat) (hlo : (2 : ℝ) ^ (52 + s) ≤ x)
    (hhi : x < (2 : ℝ) ^ (53 + s)) (hR : |(R : ℝ) * 2 ^ s - x| ≤ 2 ^ s / 2) (m : Nat)
    (hm : ∀ g : Nat, 2 ^ (52 + g) ≤ m → 2 ^ g ∣ m) :
    |(R : ℝ) * 2 ^ s - x| ≤ |(m : ℝ) - x| := by
  have hP : (0 : ℝ) < 2 ^ s := by positivity
  have hgrid : ∀ j : ℤ, |(R : ℝ) * 2 ^ s - x| ≤ |(j : ℝ) * 2 ^ s - x| := by
    intro j
    by_cases hj : j = R
    · rw [hj]
      push_cast
      exact le_rfl
    · have h1 : (1 : ℝ) ≤ |(j : ℝ) - R| := by
        have h1z : (1 : ℤ) ≤ |j - R| := Int.one_le_abs (sub_ne_zero.mpr hj)
        have : ((1 : ℤ) : ℝ) ≤ ((|j - R| : ℤ) : ℝ) := Int.cast_le.mpr h1z
        simpa using this
      have h2 : |(j : ℝ) * 2 ^ s - R * 2 ^ s| = |(j : ℝ) - R| * 2 ^ s := by
        rw [← sub_mul, abs_mul, abs_of_pos hP]
      have h3 := abs_sub_le ((j : ℝ) * 2 ^ s) x ((R : ℝ) * 2 ^ s)
      rw [h2, abs_sub_comm x] at h3
      have h4 : 2 ^ s ≤ |(j : ℝ) - R| * 2 ^ s := le_mul_of_one_le_left hP.le h1
      linarith
  have hlo' : (2 : ℝ) ^ 52 * 2 ^ s ≤ x := by rw [← pow_add]; exact hlo
  have hhi' : x < 2 ^ 53 * 2 ^ s := by rw [← pow_add]; exact hhi
  rcases lt_or_ge m (2 ^ (52 + s)) with hm1 | hm1
  · have h := hgrid (2 ^ 52)
    have hmr : (m : ℝ) < 2 ^ 52 * 2 ^ s := by
      rw [← pow_add]
      exact_mod_cast hm1
    simp only [Int.cast_pow, Int.cast_ofNat] at h
    rw [abs_of_nonpos (by linarith : (2 : ℝ) ^ 52 * 2 ^ s - x ≤ 0)] at h
    rw [abs_of_neg (by linarith : (m : ℝ) - x < 0)]
    linarith
  · rcases lt_or_ge m (2 ^ (53 + s)) with hm2 | hm2
    · obtain ⟨j, hj⟩ := hm s hm1
      have h := hgrid (j : ℤ)
      have hmj : (m : ℝ) = (j : ℝ) * 2 ^ s := by rw [hj]; push_cast; ring
      rw [hmj]
      simpa using h
    · have h := hgrid (2 ^ 53)
      have hmr : (2 : ℝ) ^ 53 * 2 ^ s ≤ m := by
        rw [← pow_add]
        exact_mod_cast hm2
      simp only [Int.cast_pow, Int.cast_ofNat] at h
      rw [abs_of_pos (by linarith : (0 : ℝ) < 2 ^ 53 * 2 ^ s - x)] at h
      rw [abs_of_pos (by linarith : (0 : ℝ) < (m : ℝ) - x)]
      linarith

/-- The rounding of a rational `N / D` in `[2 ^ 52, 2 ^ 2096)`: a point of the grid of its binade
within half a unit, packed exactly as a finite positive word. -/
theorem round_rational (N D : Nat) (hD : 0 < D) (hl : 2 ^ 52 * D ≤ N) (hu : N < 2 ^ 2096 * D) :
    ∃ R s : Nat, R ≤ 2 ^ 53 ∧ s ≤ 2043 ∧
      Wasm.IEEE64.roundRationalMagnitude false N D =
        Wasm.IEEE64.roundScaledMagnitude false (R * 2 ^ s) ∧
      (2 : ℝ) ^ (52 + s) ≤ (N : ℝ) / D ∧ (N : ℝ) / D < 2 ^ (53 + s) ∧
      |(R : ℝ) * 2 ^ s - (N : ℝ) / D| ≤ 2 ^ s / 2 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  set I := N / D with hI
  have hI52 : 2 ^ 52 ≤ I := (Nat.le_div_iff_mul_le hD).2 hl
  have hIu : I < 2 ^ 2096 := (Nat.div_lt_iff_lt_mul hD).2 hu
  have hI0 : I ≠ 0 := by positivity
  set L := Nat.log2 I with hL
  have hL52 : 52 ≤ L := (Nat.le_log2 hI0).2 hI52
  have hL2 : L < 2096 := (Nat.log2_lt hI0).2 hIu
  have hL1 : 2 ^ L ≤ I := Nat.log2_self_le hI0
  have hL3 : I < 2 ^ (L + 1) := Nat.lt_log2_self
  set s := L - 52 with hs
  have hsL : 52 + s = L := by omega
  have hx1 : (I : ℝ) ≤ (N : ℝ) / D := by
    rw [le_div_iff₀ hDR]; exact_mod_cast Nat.div_mul_le_self N D
  have hx2 : (N : ℝ) / D < I + 1 := by
    rw [div_lt_iff₀ hDR]
    have : N < (I + 1) * D := by
      have := Nat.lt_div_mul_add (a := N) hD
      rw [hI]; nlinarith
    exact_mod_cast this
  have hxlo : (2 : ℝ) ^ (52 + s) ≤ (N : ℝ) / D := by
    rw [hsL]
    have : ((2 ^ L : ℕ) : ℝ) ≤ I := by exact_mod_cast hL1
    push_cast at this
    linarith
  have hxhi : (N : ℝ) / D < 2 ^ (53 + s) := by
    rw [show 53 + s = L + 1 by omega]
    have : (I : ℝ) + 1 ≤ ((2 ^ (L + 1) : ℕ) : ℝ) := by exact_mod_cast hL3
    push_cast at this
    linarith
  set R := Wasm.IEEE32.roundQuotient N (D * 2 ^ s) with hR
  have hP : (0 : ℝ) < 2 ^ s := by positivity
  have hRe : |(R : ℝ) * 2 ^ s - (N : ℝ) / D| ≤ 2 ^ s / 2 := by
    have h := roundQuotient_error N (D * 2 ^ s) (by positivity)
    have h' : (R : ℝ) * 2 ^ s - (N : ℝ) / D = ((R : ℝ) - (N : ℝ) / ((D * 2 ^ s : ℕ) : ℝ)) * 2 ^ s := by
      push_cast; field_simp
    rw [h', abs_mul, abs_of_pos hP]
    calc |(R : ℝ) - (N : ℝ) / ((D * 2 ^ s : ℕ) : ℝ)| * 2 ^ s ≤ 1 / 2 * 2 ^ s :=
          mul_le_mul_of_nonneg_right h hP.le
      _ = 2 ^ s / 2 := by ring
  have hR53 : R ≤ 2 ^ 53 := by
    have h1 : (R : ℝ) * 2 ^ s ≤ 2 ^ 53 * 2 ^ s + 2 ^ s / 2 := by
      have := (abs_le.mp hRe).2
      have h2 : (2 : ℝ) ^ (53 + s) = 2 ^ 53 * 2 ^ s := pow_add _ _ _
      linarith
    have h3 : (R : ℝ) < 2 ^ 53 + 1 := by
      have : (R : ℝ) * 2 ^ s < (2 ^ 53 + 1) * 2 ^ s := by nlinarith
      exact lt_of_mul_lt_mul_right this hP.le
    have : R < 2 ^ 53 + 1 := by exact_mod_cast h3
    omega
  refine ⟨R, s, hR53, by omega, ?_, hxlo, hxhi, hRe⟩
  have hN0 : (N == 0) = false := by
    have : 0 < N := lt_of_lt_of_le (by positivity) hl
    simpa using this.ne'
  have hD0 : (D == 0) = false := by simpa using hD.ne'
  unfold Wasm.IEEE64.roundRationalMagnitude
  simp only [hN0, hD0, Bool.false_eq_true, ite_false]
  congr 1
  rw [← hI, ← hL, ← hs]
  by_cases h0 : s = 0
  · have hb : (s == 0) = true := by simp [h0]
    simp only [hR, h0, pow_zero, Nat.mul_one, ite_self]
  · have hb : (s == 0) = false := by simpa using h0
    simp only [hb, Bool.false_eq_true, ite_false, hR]

/-- The quotient of two positive words with a normal quotient below `2 ^ 1022` rounds to the
nearest nonnegative word. -/
theorem div_nearest (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hsa : Wasm.IEEE64.sign a = false) (hsb : Wasm.IEEE64.sign b = false)
    (hlo : 1 / (2 : ℝ) ^ 1022 ≤ value a / value b) (hhi : value a / value b < (2 : ℝ) ^ 1022) :
    F64NearestNonnegative.Nearest (value a / value b) (Wasm.IEEE64.div a b) := by
  set Ma := Wasm.IEEE64.scaledMagnitude a
  set Mb := Wasm.IEEE64.scaledMagnitude b
  have hva : value a = (Ma : ℝ) / 2 ^ 1074 := by
    simp [value, Wasm.IEEE64.scaledValue, hsa, Ma]
  have hvb : value b = (Mb : ℝ) / 2 ^ 1074 := by
    simp [value, Wasm.IEEE64.scaledValue, hsb, Mb]
  have h74 : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hq : value a / value b = (Ma : ℝ) / Mb := by
    rw [hva, hvb]; field_simp
  rw [hq] at hlo hhi ⊢
  have hpos : (0 : ℝ) < 1 / 2 ^ 1022 := by positivity
  have hMb : 0 < Mb := by
    rcases Nat.eq_zero_or_pos Mb with h | h
    · rw [h, Nat.cast_zero, div_zero] at hlo; linarith
    · exact h
  have hMa : 0 < Ma := by
    rcases Nat.eq_zero_or_pos Ma with h | h
    · rw [h, Nat.cast_zero, zero_div] at hlo; linarith
    · exact h
  have hMbR : (0 : ℝ) < Mb := by exact_mod_cast hMb
  set N := Ma * 2 ^ 1074 with hN
  have hxq : (N : ℝ) / Mb = (Ma : ℝ) / Mb * 2 ^ 1074 := by
    rw [hN]; push_cast; ring
  have hl : 2 ^ 52 * Mb ≤ N := by
    have h1 : (1 : ℝ) / 2 ^ 1022 * 2 ^ 1074 ≤ (Ma : ℝ) / Mb * 2 ^ 1074 :=
      mul_le_mul_of_nonneg_right hlo h74.le
    rw [← hxq, le_div_iff₀ hMbR] at h1
    have h2 : (1 : ℝ) / 2 ^ 1022 * 2 ^ 1074 = 2 ^ 52 := by norm_num
    rw [h2] at h1
    exact_mod_cast h1
  have hu : N < 2 ^ 2096 * Mb := by
    have h1 : (Ma : ℝ) / Mb * 2 ^ 1074 < 2 ^ 1022 * 2 ^ 1074 :=
      mul_lt_mul_of_pos_right hhi h74
    rw [← hxq, div_lt_iff₀ hMbR] at h1
    have h2 : (2 : ℝ) ^ 1022 * 2 ^ 1074 = 2 ^ 2096 := by norm_num
    rw [h2] at h1
    exact_mod_cast h1
  obtain ⟨R, s, hR53, hs, heq, hxlo, hxhi, hRe⟩ := round_rational N Mb hMb hl hu
  have hdiv : Wasm.IEEE64.div a b = Wasm.IEEE64.roundRationalMagnitude false N Mb := by
    have hMa0 : (Ma == 0) = false := by simpa using hMa.ne'
    have hMb0 : (Mb == 0) = false := by simpa using hMb.ne'
    simp [Wasm.IEEE64.div, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, hsa, hsb, Ma, Mb, N] at hMa0 hMb0 ⊢
    simp [hMa0, hMb0]
  rw [hdiv, heq]
  have hn : R * 2 ^ s < 2 ^ 2097 := by
    calc R * 2 ^ s ≤ 2 ^ 53 * 2 ^ 2043 :=
          Nat.mul_le_mul hR53 (Nat.pow_le_pow_right (by norm_num) hs)
      _ < 2 ^ 2097 := by norm_num
  obtain ⟨hf, hm, hsg⟩ := F64PackRelative.pack_spec false (R * 2 ^ s) hn
  rw [F64GridExact.roundedMagnitude_shifted_small R s hR53] at hm
  set w := Wasm.IEEE64.roundScaledMagnitude false (R * 2 ^ s)
  have hw := F64Magnitude.lt_limit_of_finite w hf hsg
  refine ⟨hw, fun v hv => ?_⟩
  rw [F64NearestSum.value_of_lt_limit w hw, F64NearestSum.value_of_lt_limit v hv, hm]
  have hx : (Ma : ℝ) / Mb = ((N : ℝ) / Mb) / 2 ^ 1074 := by rw [hxq]; field_simp
  rw [hx, ← sub_div, ← sub_div, abs_div, abs_div, abs_of_pos h74]
  apply div_le_div_of_nonneg_right _ h74.le
  push_cast
  exact grid_nearest _ s R hxlo hxhi hRe _ (fun g hg => F64NearestSum.magnitude_dvd v g hg)

#print axioms roundQuotient_error
#print axioms grid_nearest
#print axioms round_rational
#print axioms div_nearest

end LeanExe.ProofKit.F64NearestDiv
