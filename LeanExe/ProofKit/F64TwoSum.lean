import LeanExe.ProofKit.F64GridExact
import LeanExe.ProofKit.F64RoundNearest
import LeanExe.ProofKit.F64Exact

/-!
Dekker's error-free sum.  For finite `a` and `b` with `|b| ≤ |a|`, the words
`s = a + b`, `z = s - a`, and `t = b - z` satisfy `s + t = a + b` exactly, `s` is a nearest
rounding of `a + b`, and `|t| ≤ |b|` (`fast_two_sum`).  The proof works in scaled units, where every
value is an integer.  With `g` the exponent of `b` less one, `a` and `b` are multiples of `2 ^ g`.
When `a + b` has at most 53 bits on that grid it is exact, `z = b`, and `t = 0`.  Otherwise `|s|`
reaches `2 ^ (53 + g)`, so `s` is a multiple of `2 ^ (g + 1)`, and `s - a` and `(a + b) - s` fit
the grid of `2 ^ (g + 1)` or of `2 ^ g` with at most 53 bits, which `F64GridExact` makes exact.
-/

namespace LeanExe.ProofKit.F64TwoSum
open CodeLib.IEEE64 F64RoundNearest

set_option exponentiation.threshold 4096

theorem sv_grid (w : UInt64) :
    ∃ M : ℤ, M.natAbs < 2 ^ 53 ∧
      Wasm.IEEE64.scaledValue w = M * 2 ^ (Wasm.IEEE64.exponent w - 1) := by
  obtain ⟨M, hM, hm⟩ := F64Exact.magnitude_grid w
  refine ⟨if Wasm.IEEE64.sign w then -(M : ℤ) else M, ?_, ?_⟩
  · split <;> simpa using hM
  · simp only [Wasm.IEEE64.scaledValue, hm]
    split <;> push_cast <;> ring

/-- A word with a smaller magnitude has an exponent at most as large. -/
theorem exponent_le_of_magnitude (a b : UInt64)
    (h : Wasm.IEEE64.scaledMagnitude b ≤ Wasm.IEEE64.scaledMagnitude a) :
    Wasm.IEEE64.exponent b ≤ Wasm.IEEE64.exponent a := by
  by_contra hlt
  push Not at hlt
  have hfa : Wasm.IEEE64.fraction a < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have heb : Wasm.IEEE64.exponent b ≠ 0 := by omega
  have hmb : 2 ^ 52 * 2 ^ (Wasm.IEEE64.exponent b - 1) ≤ Wasm.IEEE64.scaledMagnitude b := by
    simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, heb, ite_false]
    exact Nat.mul_le_mul_right _ (by omega)
  by_cases hea : Wasm.IEEE64.exponent a = 0
  · have hma : Wasm.IEEE64.scaledMagnitude a < 2 ^ 52 := by
      simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, hea, ite_true]
      exact hfa
    have : 2 ^ 52 ≤ 2 ^ 52 * 2 ^ (Wasm.IEEE64.exponent b - 1) :=
      Nat.le_mul_of_pos_right _ (by positivity)
    omega
  · have hma : Wasm.IEEE64.scaledMagnitude a < 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent a - 1) := by
      simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, hea, ite_false]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    have hp : 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent a - 1) ≤
        2 ^ 52 * 2 ^ (Wasm.IEEE64.exponent b - 1) := by
      rw [← pow_add, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem value_nonpos_of_sign (x : UInt64) (hs : Wasm.IEEE64.sign x = true) : value x ≤ 0 := by
  simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  push_cast
  linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (Wasm.IEEE64.scaledMagnitude x : ℝ))]

theorem value_nonneg_of_sign (x : UInt64) (hs : Wasm.IEEE64.sign x = false) : 0 ≤ value x := by
  rw [F64Exact.value_of_sign x hs]
  positivity

/-- A nearest rounding is at least as close to `S` as any word. -/
theorem rounded_le {c : UInt64} {S : ℝ} (hc : Rounded c S) (v : UInt64) :
    |value c - S| ≤ |value v - S| := by
  have h := hc.2.2.2 v
  have hv : abs (|value v| - |S|) ≤ |value v - S| := abs_abs_sub_abs_le_abs_sub _ _
  have hcS : |value c - S| = abs (|value c| - |S|) := by
    rcases lt_trichotomy S 0 with hS | hS | hS
    · have := value_nonpos_of_sign c (hc.2.1 hS)
      rw [abs_of_nonpos this, abs_of_neg hS]
      rw [show -value c - -S = -(value c - S) by ring, abs_neg]
    · rw [hS, abs_zero, sub_zero, sub_zero, abs_abs]
    · have := value_nonneg_of_sign c (hc.2.2.1 hS)
      rw [abs_of_nonneg this, abs_of_pos hS]
  linarith

/-- An exact word is a nearest rounding of its value. -/
theorem rounded_self (c : UInt64) (hc : Finite c) : Rounded c (value c) := by
  refine ⟨hc, fun h => ?_, fun h => ?_, fun v => by simp⟩
  · cases hs : Wasm.IEEE64.sign c
    · have := value_nonneg_of_sign c hs
      linarith
    · rfl
  · cases hs : Wasm.IEEE64.sign c
    · rfl
    · have := value_nonpos_of_sign c hs
      linarith

/-- A nearest rounding of `S` with `|S| ≥ 2 ^ (53 + g)` in scaled units is a multiple of
`2 ^ (g + 1)`. -/
theorem rounded_dvd (c : UInt64) (S : ℝ) (hc : Rounded c S) (g : ℕ) (hg : g ≤ 2042)
    (hS : (2 : ℝ) ^ (53 + g) / 2 ^ 1074 ≤ |S|) :
    (2 : ℤ) ^ (g + 1) ∣ Wasm.IEEE64.scaledValue c := by
  obtain ⟨v, -, hvv⟩ : ∃ v : UInt64, Finite v ∧ Wasm.IEEE64.scaledValue v = 2 ^ 52 * 2 ^ (g + 1) :=
    ⟨_, F64GridExact.signed_grid_packing_exact (2 ^ 52) (g + 1) (by norm_num) (by omega)⟩
  have hvv' : Wasm.IEEE64.scaledValue v = 2 ^ (53 + g) := by
    rw [hvv, ← pow_add]
    congr 1
    omega
  have hvabs : |value v| = 2 ^ (53 + g) / 2 ^ 1074 := by
    rw [value, hvv', abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
    push_cast
    rw [abs_of_pos (by positivity)]
  have h := hc.2.2.2 v
  rw [hvabs, abs_of_nonpos (by linarith : (2 : ℝ) ^ (53 + g) / 2 ^ 1074 - |S| ≤ 0)] at h
  have hcabs : (2 : ℝ) ^ (53 + g) / 2 ^ 1074 ≤ |value c| := by
    have := neg_abs_le (|value c| - |S|)
    linarith
  have hmag : 2 ^ (53 + g) ≤ Wasm.IEEE64.scaledMagnitude c := by
    rw [abs_value] at hcabs
    have h := (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 1074)).mp hcabs
    exact_mod_cast h
  have hfc : Wasm.IEEE64.fraction c < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hec : g + 2 ≤ Wasm.IEEE64.exponent c := by
    by_contra hlt
    push Not at hlt
    by_cases he0 : Wasm.IEEE64.exponent c = 0
    · have : Wasm.IEEE64.scaledMagnitude c < 2 ^ 52 := by
        simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, he0, ite_true]
        exact hfc
      have : 2 ^ 52 ≤ 2 ^ (53 + g) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have hm : Wasm.IEEE64.scaledMagnitude c < 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent c - 1) := by
        simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, he0, ite_false]
        exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
      have : 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent c - 1) ≤ 2 ^ (53 + g) := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  obtain ⟨M, -, hM⟩ := sv_grid c
  rw [hM]
  exact Dvd.dvd.mul_left (pow_dvd_pow 2 (by omega)) M

/-- A grid multiple `M 2 ^ g` with `|M| ≤ 2 ^ 53` bounds `|M|`. -/
theorem mb_bound (Mb : ℤ) (hMb : Mb.natAbs < 2 ^ 53) (k g : ℕ) :
    (k : ℤ) * |Mb| * 2 ^ g ≤ ((2 ^ 53 : ℕ) : ℤ) * (k * 2 ^ g) := by
  have h1 : |Mb| ≤ ((2 ^ 53 : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hMb.le
  have h2 : (0 : ℤ) ≤ (k : ℤ) * 2 ^ g := by positivity
  calc (k : ℤ) * |Mb| * 2 ^ g = |Mb| * (k * 2 ^ g) := by ring
    _ ≤ ((2 ^ 53 : ℕ) : ℤ) * (k * 2 ^ g) := mul_le_mul_of_nonneg_right h1 h2

theorem natAbs_le_of_abs {z : ℤ} {n : ℕ} (g : ℕ) (h : |z * 2 ^ g| ≤ (n : ℤ) * 2 ^ g) :
    z.natAbs ≤ n := by
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ g)] at h
  have h2 := le_of_mul_le_mul_right h (by positivity : (0 : ℤ) < 2 ^ g)
  have : (z.natAbs : ℤ) ≤ n := by rw [Int.natCast_natAbs]; exact h2
  exact_mod_cast this

/-- **Dekker's error-free sum** for `|b| ≤ |a| < 2 ^ 900`. -/
theorem fast_two_sum (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (hab : |value b| ≤ |value a|) (hlim : |value a| < 2 ^ 900) :
    Finite (Wasm.IEEE64.add a b) ∧
      Finite (Wasm.IEEE64.sub b (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a)) ∧
      value (Wasm.IEEE64.add a b) +
          value (Wasm.IEEE64.sub b (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a)) =
        value a + value b ∧
      Rounded (Wasm.IEEE64.add a b) (value a + value b) ∧
      |value (Wasm.IEEE64.sub b (Wasm.IEEE64.sub (Wasm.IEEE64.add a b) a))| ≤ |value b| := by
  set X := Wasm.IEEE64.scaledValue a with hX
  set Y := Wasm.IEEE64.scaledValue b with hY
  have h1074 : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hva : value a = (X : ℝ) / 2 ^ 1074 := rfl
  have hvb : value b = (Y : ℝ) / 2 ^ 1074 := rfl
  -- exponents and grids
  have hmag : Wasm.IEEE64.scaledMagnitude b ≤ Wasm.IEEE64.scaledMagnitude a := by
    rw [abs_value, abs_value] at hab
    have := (div_le_div_iff_of_pos_right h1074).mp hab
    exact_mod_cast this
  have heab := exponent_le_of_magnitude a b hmag
  have hea := F64Exact.exponent_le_of_value a hlim
  set g := Wasm.IEEE64.exponent b - 1 with hg
  obtain ⟨Mb, hMb, hYM⟩ := sv_grid b
  obtain ⟨Ma, hMa, hXM⟩ := sv_grid a
  have hXg : X = (Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - g)) * 2 ^ g := by
    rw [hX, hXM, mul_assoc, ← pow_add]
    congr 2
    omega
  set A := Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - g) with hA
  have hYg : Y = Mb * 2 ^ g := hYM
  have hpg : (0 : ℤ) < 2 ^ g := by positivity
  set N := A + Mb with hN
  have hsum : X + Y = N * 2 ^ g := by rw [hXg, hYg, hN]; ring
  have hgle : g ≤ 2039 := by omega
  by_cases hsmall : N.natAbs ≤ 2 ^ 53
  · -- the sum is exact
    obtain ⟨hsf, hsv⟩ := F64GridExact.grid_add_exact a b ha hb N g hsum hsmall (by omega)
    set s := Wasm.IEEE64.add a b
    obtain ⟨hzf, hzv⟩ := F64GridExact.sub_grid_exact s a hsf ha Mb g
      (by rw [hsv, ← hX, ← hY, hYg]; ring) (by omega) (by omega)
    set z := Wasm.IEEE64.sub s a
    obtain ⟨htf, htv⟩ := F64GridExact.sub_grid_exact b z hb hzf 0 0
      (by rw [hzv, hsv, ← hX, ← hY]; ring) (by norm_num) (by norm_num)
    have hvs : value s = value a + value b := by
      rw [value, hsv, hva, hvb]
      push_cast
      ring
    have hvt : value (Wasm.IEEE64.sub b z) = 0 := by
      rw [value, htv, hzv, hsv, ← hX, ← hY]
      simp
    refine ⟨hsf, htf, by rw [hvs, hvt, add_zero], ?_, by rw [hvt, abs_zero]; exact abs_nonneg _⟩
    rw [← hvs]
    exact rounded_self s hsf
  · -- the sum has more than 53 bits on the grid of `2 ^ g`
    push Not at hsmall
    have hS : (2 : ℝ) ^ (53 + g) / 2 ^ 1074 ≤ |value a + value b| := by
      rw [hva, hvb, ← add_div, abs_div, abs_of_pos h1074]
      apply div_le_div_of_nonneg_right _ h1074.le
      have : ((2 : ℤ) ^ (53 + g) : ℝ) ≤ |((X + Y : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]
        have h2 : (2 : ℤ) ^ (53 + g) ≤ |X + Y| := by
          rw [hsum, abs_mul, abs_of_pos hpg, pow_add]
          apply mul_le_mul_of_nonneg_right _ hpg.le
          have : ((2 ^ 53 : ℕ) : ℤ) < (N.natAbs : ℤ) := by exact_mod_cast hsmall
          rw [Int.natCast_natAbs] at this
          push_cast at this
          linarith
        exact_mod_cast h2
      push_cast at this
      linarith
    have hS0 : value a + value b ≠ 0 := by
      intro h
      rw [h, abs_zero] at hS
      have : (0 : ℝ) < 2 ^ (53 + g) / 2 ^ 1074 := by positivity
      linarith
    have hmax : |value a + value b| < 2 ^ 1023 := by
      calc |value a + value b| ≤ |value a| + |value b| := abs_add_le _ _
        _ < 2 ^ 900 + 2 ^ 900 := by linarith
        _ ≤ 2 ^ 1023 := by norm_num
    have hsr := add_rounded a b ha hb hS0 hmax
    set s := Wasm.IEEE64.add a b with hsdef
    have hsf : Finite s := hsr.1
    have hdvd := rounded_dvd s _ hsr g (by omega) hS
    obtain ⟨K, hK⟩ := hdvd
    set Sv := Wasm.IEEE64.scaledValue s with hSv
    have hvsS : value s = (Sv : ℝ) / 2 ^ 1074 := rfl
    have hscale : ∀ T : ℤ, value s - (value a + value b) = ((Sv - (X + Y) : ℤ) : ℝ) / 2 ^ 1074 ∧
        (T : ℝ) / 2 ^ 1074 - (value a + value b) = ((T - (X + Y) : ℤ) : ℝ) / 2 ^ 1074 := by
      intro T
      constructor <;> (rw [hva, hvb]; try rw [hvsS]) <;> push_cast <;> ring
    have hcmp : ∀ v : UInt64, |Sv - (X + Y)| ≤ |Wasm.IEEE64.scaledValue v - (X + Y)| := by
      intro v
      have h := rounded_le hsr v
      rw [(hscale (Wasm.IEEE64.scaledValue v)).1, show value v =
        (Wasm.IEEE64.scaledValue v : ℝ) / 2 ^ 1074 from rfl,
        (hscale (Wasm.IEEE64.scaledValue v)).2, abs_div, abs_div, abs_of_pos h1074] at h
      have h2 := (div_le_div_iff_of_pos_right h1074).mp h
      rw [← Int.cast_abs, ← Int.cast_abs] at h2
      exact_mod_cast h2
    -- the error of `s` is at most `|b|`
    have herr : |Sv - (X + Y)| ≤ |Y| := by
      have := hcmp a
      rwa [← hX, show X - (X + Y) = -Y by ring, abs_neg] at this
    -- `z = s - a` is exact
    have hzex : ∃ (w : ℤ) (sh : ℕ), Sv - X = w * 2 ^ sh ∧ w.natAbs ≤ 2 ^ 53 ∧ sh ≤ 2043 := by
      by_cases hlt : g + 1 ≤ Wasm.IEEE64.exponent a - 1
      · have hXg1 : X = (Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - (g + 1))) * 2 ^ (g + 1) := by
          rw [hX, hXM, mul_assoc, ← pow_add]
          congr 2
          omega
        refine ⟨K - Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - (g + 1)), g + 1, ?_, ?_, by omega⟩
        · rw [hK, hXg1]
          ring
        · have hb2 : |Sv - X| ≤ 2 * |Y| := by
            have := abs_sub_le Sv (X + Y) X
            rw [show X + Y - X = Y by ring] at this
            linarith
          apply natAbs_le_of_abs (g + 1)
          have heq : (K - Ma * 2 ^ (Wasm.IEEE64.exponent a - 1 - (g + 1))) * 2 ^ (g + 1) =
              Sv - X := by rw [hK, hXg1]; ring
          rw [heq]
          calc |Sv - X| ≤ 2 * |Y| := hb2
            _ = ((2 : ℕ) : ℤ) * |Mb| * 2 ^ g := by rw [hYg, abs_mul, abs_of_pos hpg]; push_cast; ring
            _ ≤ ((2 ^ 53 : ℕ) : ℤ) * ((2 : ℕ) * 2 ^ g) := mb_bound Mb hMb 2 g
            _ = ((2 ^ 53 : ℕ) : ℤ) * 2 ^ (g + 1) := by rw [pow_succ]; push_cast; ring
      · -- equal exponents: the error is at most `2 ^ g`
        have heq : Wasm.IEEE64.exponent a - 1 = g := by omega
        have hAeq : A = Ma := by rw [hA, show Wasm.IEEE64.exponent a - 1 - g = 0 by omega]; ring
        have hNlt : N.natAbs < 2 ^ 54 := by
          rw [hN, hAeq]
          have := Int.natAbs_add_le Ma Mb
          omega
        -- the even neighbour of `N` on the grid of `2 ^ (g + 1)`
        set R : ℤ := (N + N % 2) / 2 with hR
        have hRN : 2 * R = N + N % 2 := by
          rw [hR]
          omega
        have hRabs : R.natAbs ≤ 2 ^ 53 := by omega
        obtain ⟨hvf, hvv⟩ := F64GridExact.signed_grid_packing_exact R (g + 1) hRabs (by omega)
        set v := Wasm.IEEE64.roundScaledMagnitude (R < 0) (R.natAbs * 2 ^ (g + 1))
        have hdist : |Wasm.IEEE64.scaledValue v - (X + Y)| ≤ 2 ^ g := by
          rw [hvv, hsum, pow_succ, show R * (2 ^ g * 2) - N * 2 ^ g = (2 * R - N) * 2 ^ g by ring,
            hRN, show N + N % 2 - N = N % 2 by ring, abs_mul, abs_of_pos hpg]
          have : |N % 2| ≤ 1 := by
            have h0 := Int.emod_nonneg N (by norm_num : (2 : ℤ) ≠ 0)
            have h1 := Int.emod_lt_of_pos N (by norm_num : (0 : ℤ) < 2)
            rw [abs_of_nonneg h0]
            omega
          nlinarith
        have herr2 : |Sv - (X + Y)| ≤ 2 ^ g := (hcmp v).trans hdist
        refine ⟨(Sv - X) / 2 ^ g, g, ?_, ?_, by omega⟩
        · have hd : (2 : ℤ) ^ g ∣ Sv - X := by
            rw [hK, hXg, hAeq, pow_succ]
            exact ⟨K * 2 - Ma, by ring⟩
          rw [Int.ediv_mul_cancel hd]
        · have hd : (2 : ℤ) ^ g ∣ Sv - X := by
            rw [hK, hXg, hAeq, pow_succ]
            exact ⟨K * 2 - Ma, by ring⟩
          apply natAbs_le_of_abs g
          rw [Int.ediv_mul_cancel hd]
          have hYa : |Y| = |Mb| * 2 ^ g := by rw [hYg, abs_mul, abs_of_pos hpg]
          have hM1 : |Mb| + 1 ≤ ((2 ^ 53 : ℕ) : ℤ) := by
            rw [Int.abs_eq_natAbs]
            exact_mod_cast hMb
          calc |Sv - X| ≤ |Sv - (X + Y)| + |Y| := by
                have := abs_sub_le Sv (X + Y) X
                rw [show X + Y - X = Y by ring] at this
                exact this
            _ ≤ (|Mb| + 1) * 2 ^ g := by rw [hYa]; linarith
            _ ≤ ((2 ^ 53 : ℕ) : ℤ) * 2 ^ g := mul_le_mul_of_nonneg_right hM1 hpg.le
    obtain ⟨w, sh, hw, hwabs, hsh⟩ := hzex
    obtain ⟨hzf, hzv⟩ := F64GridExact.sub_grid_exact s a hsf ha w sh
      hw hwabs hsh
    set z := Wasm.IEEE64.sub s a
    -- `t = b - z` is the rounding error of `s`
    have hd : (2 : ℤ) ^ g ∣ X + Y - Sv := by
      rw [hsum, hK, pow_succ]
      exact ⟨N - K * 2, by ring⟩
    obtain ⟨htf, htv⟩ := F64GridExact.sub_grid_exact b z hb hzf ((X + Y - Sv) / 2 ^ g) g
      (by rw [Int.ediv_mul_cancel hd, hzv, ← hSv, ← hX, ← hY]; ring)
      (by
        apply natAbs_le_of_abs g
        rw [Int.ediv_mul_cancel hd, show X + Y - Sv = -(Sv - (X + Y)) by ring, abs_neg]
        calc |Sv - (X + Y)| ≤ |Y| := herr
          _ = ((1 : ℕ) : ℤ) * |Mb| * 2 ^ g := by rw [hYg, abs_mul, abs_of_pos hpg]; push_cast; ring
          _ ≤ ((2 ^ 53 : ℕ) : ℤ) * ((1 : ℕ) * 2 ^ g) := mb_bound Mb hMb 1 g
          _ = ((2 ^ 53 : ℕ) : ℤ) * 2 ^ g := by push_cast; ring)
      (by omega)
    have hvt : value (Wasm.IEEE64.sub b z) = (((X + Y - Sv) : ℤ) : ℝ) / 2 ^ 1074 := by
      rw [value, htv, hzv, ← hSv, ← hX, ← hY]
      congr 1
      push_cast
      ring
    refine ⟨hsf, htf, ?_, hsr, ?_⟩
    · rw [hvt, hva, hvb, value, ← hSv]
      push_cast
      ring
    · rw [hvt, hvb, abs_div, abs_div, abs_of_pos h1074]
      apply div_le_div_of_nonneg_right _ h1074.le
      rw [show X + Y - Sv = -(Sv - (X + Y)) by ring, Int.cast_neg, abs_neg, ← Int.cast_abs,
        ← Int.cast_abs]
      exact_mod_cast herr

#print axioms rounded_le
#print axioms rounded_dvd
#print axioms fast_two_sum

end LeanExe.ProofKit.F64TwoSum
