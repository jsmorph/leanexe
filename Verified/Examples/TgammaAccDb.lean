import Verified.Examples.TgammaAccPath
import Verified.Examples.TgammaAccDbCheck

/-!
**The database of hard cases** of `Tgamma.accurate` within one step of `Γ` (`db_within`).  Each of
the 57 rows holds an argument `x`, a double `f`, and a correction `δ`, and the code returns the
rounded sum `f + δ`.  For each row a kernel check (`TgammaAccDbCheck.db_ok`) takes the range of
`⌊x⌋`, the reduced argument `d = 2 (x - ⌊x⌋) - 1`, the shift `m = j - ⌊x⌋` to the range, and the
exact rational `E = 2 ^ eoff accPoly d K`, where `K` is `1 / (x (x + 1) ⋯ (x + m - 1))` for
`m ≥ 0` and `(x + m) ⋯ (x - 1)` for `m < 0`, and finds `|δ| + |f + δ - E| ≤ (5/4) 2 ^ -53 |E|`.
The correction `δ` is about a quarter of a unit in the last place of `f`, a direction for
CORE-MATH's directed roundings, so `f + δ` itself lies up to `2 ^ -54` from `Γ x`.  The rounded
sum is a nearest double to `f + δ` (`F64RoundNearest.add_rounded`), and `f` is a double, so the
rounded sum lies within `|δ|` of `f + δ`.  `AccRangeFact` puts `E` within `2 ^ -62` of `Γ x`
(`gamma_kfac`), so the rounded sum lies within `(11/8) 2 ^ -53 |Γ x|` of `Γ x` (`db_entry`).
-/

namespace Verified.Examples.TgammaAccDb
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaAccPath PolyBound TgammaAccDbCheck

set_option exponentiation.threshold 4096

theorem eval_cast (p : List ℚ) (x : ℚ) : eval p (x : ℝ) = (evalQ p x : ℝ) := by
  induction p with
  | nil => simp [evalQ]
  | cons a p ih => simp [eval_cons, ih, evalQ]

theorem accPoly_cast (oh imax ol jmax : ℕ) (d : ℚ) :
    TgammaApprox.accPoly oh imax ol jmax (d : ℝ) = (accPolyQ oh imax ol jmax d : ℝ) := by
  unfold TgammaApprox.accPoly accPolyQ
  rw [eval_cast, eval_cast, Rat.cast_add]

theorem poch_cast (q : ℚ) (n : ℕ) :
    ((poch q n : ℚ) : ℝ) = ∏ j ∈ Finset.range n, ((q : ℝ) + j) := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
    rw [poch, Finset.prod_range_succ, ← ih, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast]

theorem gamma_kfac (q : ℚ) (hq : ∀ n : ℤ, (q : ℝ) ≠ n) (m : ℤ) :
    Real.Gamma q = Real.Gamma ((q : ℝ) + m) * (kfac q m : ℝ) := by
  unfold kfac
  split_ifs with hm
  · have hNP := GammaBasic.notPole_of_not_int hq
    have h := GammaBasic.gamma_add_nat hNP m.toNat
    have hmc : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
      have : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
      exact_mod_cast this
    have hne := GammaBasic.shift_prod_ne_zero hNP m.toNat
    rw [hmc] at h
    rw [h, Rat.cast_div, Rat.cast_one, poch_cast]
    field_simp
  · have hNP : GammaBasic.NotPole ((q : ℝ) + m) := GammaBasic.notPole_of_not_int
      (fun n hn => hq (n - m) (by push_cast; linarith))
    have h := GammaBasic.gamma_add_nat hNP (-m).toNat
    have hmc : (((-m).toNat : ℕ) : ℝ) = -(m : ℝ) := by
      have : (((-m).toNat : ℕ) : ℤ) = -m := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [hmc, show (q : ℝ) + m + -m = q by ring] at h
    rw [h, poch_cast]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp

theorem abs_abs_sub_of_lt (a b : ℝ) (h : |b| < |a|) : |(|a| - |a + b|)| = |b| := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [abs_of_neg ha] at h ⊢
    have hab : a + b < 0 := by linarith [neg_abs_le b, le_abs_self b]
    rw [abs_of_neg hab, show -a - -(a + b) = b by ring]
  · rw [ha, abs_zero] at h
    exact absurd h (not_lt.mpr (abs_nonneg b))
  · rw [abs_of_pos ha] at h ⊢
    have hab : 0 < a + b := by linarith [neg_abs_le b, le_abs_self b]
    rw [abs_of_pos hab, show a - (a + b) = -b by ring, abs_neg]

theorem abs_sub_eq_of_close (c s : ℝ) (h : |c - s| ≤ |s| / 2) :
    |c - s| = |(|c| - |s|)| := by
  have h1 := abs_le.mp h
  rcases lt_trichotomy s 0 with hs | hs | hs
  · rw [abs_of_neg hs] at h1
    have hc : c < 0 := by linarith
    rw [abs_of_neg hc, abs_of_neg hs, show -c - -s = -(c - s) by ring, abs_neg]
  · rw [hs, abs_zero] at h1
    have hc : c = 0 := by linarith
    rw [hc, hs]
    simp
  · rw [abs_of_pos hs] at h1
    have hc : 0 < c := by linarith
    rw [abs_of_pos hc, abs_of_pos hs]

/-- **A row of the database** within one step of `Γ`. -/
theorem db_entry (hA : TgammaApprox.AccRangeFact) (wx wf wd : UInt64)
    (hfx : Wasm.IEEE64.isFinite wx = true) (hff : Wasm.IEEE64.isFinite wf = true)
    (hfd : Wasm.IEEE64.isFinite wd = true) (r : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)
    (hr : r ∈ TgammaApprox.accRanges) (n : ℤ) (hn1 : (n : ℚ) < ratOfWord wx)
    (hn2 : ratOfWord wx < n + 1)
    (hδ : |ratOfWord wd| < |ratOfWord wf|)
    (hS : |ratOfWord wd| + |ratOfWord wf + ratOfWord wd - approxE (ratOfWord wx) n r| ≤
      5 / 4 * |approxE (ratOfWord wx) n r| / 2 ^ 53)
    (hE1 : 1 / 2 ^ 990 ≤ |approxE (ratOfWord wx) n r|)
    (hE2 : |approxE (ratOfWord wx) n r| ≤ 2 ^ 990) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value wx))
      (Float.ofBits wf + Float.ofBits wd).toBits := by
  obtain ⟨oh, imax, ol, jmax, j, eoff⟩ := r
  set qx := ratOfWord wx with hqx
  have hv : value wx = (qx : ℝ) := (ratOfWord_cast wx).symm
  rw [hv]
  have hn1r : (n : ℝ) < qx := by exact_mod_cast hn1
  have hn2r : (qx : ℝ) < n + 1 := by exact_mod_cast hn2
  have hq : ∀ k : ℤ, (qx : ℝ) ≠ k := by
    intro k hk
    rw [hk] at hn1r hn2r
    have h1 : n < k := by exact_mod_cast hn1r
    have h2 : k < n + 1 := by exact_mod_cast hn2r
    omega
  -- the range
  set d : ℚ := 2 * (qx - n) - 1 with hd
  have hd1 : |(d : ℝ)| ≤ 1 := by
    rw [hd]; push_cast; rw [abs_le]; constructor <;> linarith
  have hj4 : 4 ≤ j := (TgammaAccGamma.fact_ok _ hr).2
  have hj4r : (4 : ℝ) ≤ j := by exact_mod_cast hj4
  have hRF := hA oh imax ol jmax j eoff hr (d : ℝ) hd1
  rw [accPoly_cast] at hRF
  have hy : (j : ℝ) + (1 + (d : ℝ)) / 2 = (qx : ℝ) + ((j : ℤ) - n : ℤ) := by
    rw [hd]; push_cast; ring
  rw [hy] at hRF
  set Γy := Real.Gamma ((qx : ℝ) + ((j : ℤ) - n : ℤ)) with hΓydef
  have hΓy : 0 < Γy := by
    rw [hΓydef]
    apply Real.Gamma_pos_of_pos
    push_cast
    linarith
  have hk := gamma_kfac qx hq ((j : ℤ) - n)
  rw [← hΓydef] at hk
  set K : ℚ := kfac qx ((j : ℤ) - n) with hK
  set A : ℚ := accPolyQ oh imax ol jmax d with hAdef
  have hEdef : approxE qx n (oh, imax, ol, jmax, j, eoff) = 2 ^ eoff * A * K := rfl
  rw [hEdef] at hS hE1 hE2
  -- `E` against `Γ x`
  have hEG : |Real.Gamma qx - ((2 ^ eoff * A * K : ℚ) : ℝ)| ≤
      1 / 2 ^ 62 * |Real.Gamma qx| := by
    rw [hk]
    push_cast
    rw [show Γy * (K : ℝ) - 2 ^ eoff * (A : ℝ) * K = (Γy - 2 ^ eoff * A) * K by ring, abs_mul,
      abs_mul, abs_of_pos hΓy]
    have := mul_le_mul_of_nonneg_right hRF (abs_nonneg (K : ℝ))
    linarith
  -- the sum `f + δ` against `Γ x`
  set E : ℚ := 2 ^ eoff * A * K with hEq
  set S : ℚ := ratOfWord wf + ratOfWord wd with hSq
  have hSr : |((ratOfWord wd : ℚ) : ℝ)| + |(S : ℝ) - E| ≤ 5 / 4 * |(E : ℝ)| / 2 ^ 53 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hS
    push_cast at h
    exact h
  have hE1r : 1 / 2 ^ 990 ≤ |(E : ℝ)| := by
    have h := (Rat.cast_le (K := ℝ)).mpr hE1
    push_cast at h
    exact h
  have hE2r : |(E : ℝ)| ≤ 2 ^ 990 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hE2
    push_cast at h
    exact h
  have hδr : |((ratOfWord wd : ℚ) : ℝ)| < |((ratOfWord wf : ℚ) : ℝ)| := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hδ
    push_cast at h
    exact h
  set G := Real.Gamma qx with hGdef
  have hEG2 : |(E : ℝ)| ≤ |G| * (1 + 1 / 2 ^ 62) := by
    have := abs_sub_abs_le_abs_sub (E : ℝ) G
    rw [abs_sub_comm] at this
    linarith
  -- the rounded sum
  have hwf : Finite (Float.ofBits wf).toBits := TgammaWords.ofBits_finite wf hff
  have hwd : Finite (Float.ofBits wd).toBits := TgammaWords.ofBits_finite wd hfd
  have hbf : (Float.ofBits wf).toBits = wf := TgammaWords.ofBits_bits wf hff
  have hbd : (Float.ofBits wd).toBits = wd := TgammaWords.ofBits_bits wd hfd
  have hvf : value wf = (ratOfWord wf : ℝ) := (ratOfWord_cast wf).symm
  have hvd : value wd = (ratOfWord wd : ℝ) := (ratOfWord_cast wd).symm
  have hSv : value wf + value wd = (S : ℝ) := by rw [hvf, hvd, hSq, Rat.cast_add]
  have hSE : |(S : ℝ)| ≤ 2 * |(E : ℝ)| := by
    have := abs_sub_abs_le_abs_sub (S : ℝ) E
    have h2 : 5 / 4 * |(E : ℝ)| / 2 ^ 53 ≤ |(E : ℝ)| := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg (E : ℝ)]
    linarith [abs_nonneg ((ratOfWord wd : ℚ) : ℝ)]
  have hSE2 : |(E : ℝ)| / 2 ≤ |(S : ℝ)| := by
    have := abs_sub_abs_le_abs_sub (E : ℝ) S
    rw [abs_sub_comm] at this
    have h2 : 5 / 4 * |(E : ℝ)| / 2 ^ 53 ≤ |(E : ℝ)| / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [abs_nonneg (E : ℝ)]
    linarith [abs_nonneg ((ratOfWord wd : ℚ) : ℝ)]
  have hS0 : value wf + value wd ≠ 0 := by
    rw [hSv]
    intro h0
    rw [h0, abs_zero] at hSE2
    linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 990)]
  have hSmax : |value wf + value wd| < 2 ^ 1023 := by
    rw [hSv]
    linarith [(by norm_num : (2 : ℝ) * 2 ^ 990 < 2 ^ 1023)]
  obtain ⟨hcf, -, -, hnear⟩ := F64RoundNearest.add_rounded wf wd hff hfd hS0 hSmax
  have hres := fapprox_add (TgammaDD.fapprox_self _ hwf) (TgammaDD.fapprox_self _ hwd) |(S : ℝ)|
    (by simp only [add_zero]; rw [hbf, hbd, hSv]) (by rw [← hSv]; exact hSmax)
  simp only [zero_add] at hres
  rw [hbf, hbd, hSv] at hres
  obtain ⟨-, hres2⟩ := hres
  rw [F64Bits.toBits_add, hbf, hbd] at hres2
  rw [F64Bits.toBits_add, hbf, hbd]
  set c := Wasm.IEEE64.add wf wd with hcdef
  have hcS : |value c - S| ≤ |((ratOfWord wd : ℚ) : ℝ)| := by
    have hclose : |value c - S| ≤ |(S : ℝ)| / 2 := by
      have : |(S : ℝ)| / 2 ^ 53 ≤ |(S : ℝ)| / 2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) (by norm_num)
      linarith [hres2]
    rw [abs_sub_eq_of_close _ _ hclose]
    have hn := hnear wf
    rw [hSv, hvf, hSq, Rat.cast_add] at hn
    rw [hSq, Rat.cast_add]
    rw [abs_abs_sub_of_lt _ _ hδr] at hn
    exact hn
  apply F64RelativeStep.within_one_relative G c hcf
  · have := hE1r.trans hEG2
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 * (1 + 1 / 2 ^ 62) ≤ 1 / 2 ^ 990)]
  · have h1 := abs_sub_le (value c) (S : ℝ) G
    have h2 := abs_sub_le (S : ℝ) E G
    rw [abs_sub_comm (E : ℝ) G] at h2
    have h3 : 5 / 4 * |(E : ℝ)| / 2 ^ 53 ≤ 5 / 4 * (|G| * (1 + 1 / 2 ^ 62)) / 2 ^ 53 := by
      have := mul_le_mul_of_nonneg_left hEG2 (by norm_num : (0 : ℝ) ≤ 5 / 4)
      exact div_le_div_of_nonneg_right this (by positivity)
    simp only [unitRoundoff64]
    linarith [abs_nonneg G]

/-- **The database of hard cases** within one step of `Γ`. -/
theorem db_within (hA : TgammaApprox.AccRangeFact) : DbWithin := by
  intro k hk
  obtain ⟨i0, i1, i2⟩ := db_index k hk
  have h := db_ok k hk
  simp only [dbOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hfx, hff⟩, hfd⟩, hr⟩, hn1⟩, hδ⟩, hS⟩, hE1⟩, hE2⟩ := h
  unfold entry
  rw [i0, i1, i2, TgammaWords.ofBits_bits _ hfx]
  exact db_entry hA _ _ _ hfx hff hfd _ hr _ hn1 (Int.lt_floor_add_one _) hδ hS hE1 hE2

#print axioms gamma_kfac
#print axioms db_entry
#print axioms db_within

end Verified.Examples.TgammaAccDb
