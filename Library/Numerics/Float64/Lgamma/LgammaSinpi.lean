import Library.Numerics.Float64.Tgamma.TgammaSinpid
import Library.Numerics.Float64.Lgamma.LgammaSinpiNear
import Library.Numerics.Float64.Lgamma.LgammaApprox

/-!
**`Lgamma.asSinpipid` within `2^-63` of `sin (π x)/π`, relative,** for every double `x = n/2^53`
with `0 < n < 2^53`, with the low part at most `2^-50` of the high part (`asSinpipid_spec`), from
`LgammaApprox.SinpiFact` and `Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest`.  Within `3/256` of an integer, the rows
`ky ≥ 63`, the code evaluates the polynomial `z + z³ nearPoly (z²)` at `z = 1/2 - |x - 1/2|`
(`LgammaSinpiNear.near_spec`), within `2^-73` of the result.  Elsewhere it calls `Tgamma.asSinpid`
with `Lgamma.sinpiTable`, which passes the word check `Library.Numerics.Float64.Tgamma.TgammaSinpidTab.sinTabOK`
(`sinTabOK_lgamma`), and `Library.Numerics.Float64.Tgamma.TgammaSinpid.asSinpid_gen` with `κ = 1/π` gives a relative error below
`2^-63.7` on the rows `ky ≤ 62`, where `y = 64 - 128 |x - 1/2| ≥ 3/2`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaSinpi
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Tgamma.TgammaFloor Library.Numerics.Float64.Tgamma.TgammaLogdTab Library.Numerics.Float64.Tgamma.TgammaSinpidTab Library.Numerics.Float64.Tgamma.TgammaSinpidRed Library.Numerics.Float64.Tgamma.TgammaSinpid
  LgammaSinpiNear
open Library.Numerics.Float64.Tgamma (entry roundEven)

set_option exponentiation.threshold 4096

theorem sinTabOK_lgamma : sinTabOK Lgamma.sinpiTable = true := by decide +kernel

theorem sinKernel_eq (u : ℝ) : LgammaApprox.sinKernel u = Ks u := by
  obtain ⟨-, -, -, -, h4, h5, h6, h7⟩ := coef_words _ sinTabOK_lgamma
  have hc : LgammaApprox.coeffs Lgamma.sinpiTable 135 1 3 = [LgammaApprox.q Lgamma.sinpiTable 135,
      LgammaApprox.q Lgamma.sinpiTable 136, LgammaApprox.q Lgamma.sinpiTable 137] := rfl
  rw [LgammaApprox.sinKernel, hc, Ks]
  simp only [PolyBound.eval_cons, PolyBound.eval_nil, mul_zero, add_zero, LgammaApprox.q,
    Rat.cast_add, PolyBound.ratOfWord_cast, h4, h5, h6, h7]

theorem cosKernel_eq (u : ℝ) : LgammaApprox.cosKernel u = Kc u := by
  obtain ⟨h0, h1, h2, h3, -, -, -, -⟩ := coef_words _ sinTabOK_lgamma
  have hc : LgammaApprox.coeffs Lgamma.sinpiTable 131 1 3 = [LgammaApprox.q Lgamma.sinpiTable 131,
      LgammaApprox.q Lgamma.sinpiTable 132, LgammaApprox.q Lgamma.sinpiTable 133] := rfl
  rw [LgammaApprox.cosKernel, hc, Kc]
  simp only [PolyBound.eval_cons, PolyBound.eval_nil, mul_zero, add_zero, LgammaApprox.q,
    Rat.cast_add, PolyBound.ratOfWord_cast, h0, h1, h2, h3]

theorem nearPoly_eq (u : ℝ) : LgammaApprox.nearPoly u =
    (value Lgamma.sinpiTable[138]! + value Lgamma.sinpiTable[139]!) +
      u * (value Lgamma.sinpiTable[140]! + u * (value Lgamma.sinpiTable[141]! +
        u * value Lgamma.sinpiTable[142]!)) := by
  have hc : LgammaApprox.coeffs Lgamma.sinpiTable 140 1 3 = [LgammaApprox.q Lgamma.sinpiTable 140,
      LgammaApprox.q Lgamma.sinpiTable 141, LgammaApprox.q Lgamma.sinpiTable 142] := rfl
  rw [LgammaApprox.nearPoly, hc]
  simp only [PolyBound.eval_cons, PolyBound.eval_nil, mul_zero, add_zero, LgammaApprox.q,
    Rat.cast_add, PolyBound.ratOfWord_cast]

/-- The words of the near-integer polynomial are finite. -/
def nearOK (tab : Array UInt64) : Bool :=
  finW tab[138]! && finW tab[139]! && finW tab[140]! && finW tab[141]! && finW tab[142]!

theorem nearOK_lgamma : nearOK Lgamma.sinpiTable = true := by decide +kernel

theorem asSinpipid_eq (tab : Array UInt64) (x : Float) :
    Lgamma.asSinpipid tab x =
      let ax := (x - 0.5).abs
      let ky := (roundEven (ax * 128.0)).toUInt64
      if 64 - ky < 2 then
        nearTail (0.5 - ax) (entry tab 138) (entry tab 139) (entry tab 140) (entry tab 141)
          (entry tab 142)
      else Tgamma.asSinpid tab x := rfl

#print axioms asSinpipid_eq

/-- `|x - 1/2|` and `1/2 - |x - 1/2|` are exact for `x = n/2^53`. -/
theorem half_parts (x : Float) (n : ℕ) (hn0 : 0 < n) (hn : n < 2 ^ 53) (hx : Finite x.toBits)
    (hv : value x.toBits = n / 2 ^ 53) :
    Finite (x - 0.5).abs.toBits ∧ value (x - 0.5).abs.toBits = |(n : ℝ) / 2 ^ 53 - 1 / 2| ∧
      Finite (0.5 - (x - 0.5).abs).toBits ∧
      value (0.5 - (x - 0.5).abs).toBits = 1 / 2 - |(n : ℝ) / 2 ^ 53 - 1 / 2| := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = (n : ℤ) - 2 ^ 52 := ⟨_, rfl⟩
  have hzb : |z| < 2 ^ 52 := by rw [hz, abs_lt]; constructor <;> omega
  have hzr : (z : ℝ) / 2 ^ 53 = (n : ℝ) / 2 ^ 53 - 1 / 2 := by
    have : (z : ℝ) = (n : ℝ) - 2 ^ 52 := by rw [hz]; push_cast; ring
    rw [this]; ring
  have hzn : z.natAbs ≤ 2 ^ 53 := by
    have : (z.natAbs : ℤ) = |z| := Int.natCast_natAbs z
    omega
  obtain ⟨w1, hw1f, hw1v⟩ := grid_float z 53 hzn (by norm_num)
  have hX : |(n : ℝ) / 2 ^ 53 - 1 / 2| < 1 / 2 := by
    rw [← hzr, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53), div_lt_iff₀ (by positivity),
      ← Int.cast_abs]
    have : ((|z| : ℤ) : ℝ) < 2 ^ 52 := by exact_mod_cast hzb
    linarith [(by norm_num : (1 / 2 : ℝ) * 2 ^ 53 = 2 ^ 52)]
  obtain ⟨haf, hav⟩ := fsub_exact x 0.5 w1 hx half_finite hw1f
    (by rw [hw1v, hv, half_value, hzr]) (by
      rw [hv, half_value]; linarith [abs_nonneg ((n : ℝ) / 2 ^ 53 - 1 / 2),
        (by norm_num : (1 / 2 : ℝ) < 2 ^ 1023)])
  rw [hv, half_value] at hav
  obtain ⟨hbf, hbv⟩ := abs_float (x - 0.5) haf
  rw [hav] at hbv
  refine ⟨hbf, hbv, ?_⟩
  obtain ⟨w2, hw2f, hw2v⟩ := grid_float (2 ^ 52 - (|z|)) 53 (by
    have : ((2 ^ 52 - (|z|)).natAbs : ℤ) = |2 ^ 52 - (|z|)| := Int.natCast_natAbs _
    have h0 := abs_nonneg z
    have h1 : 0 ≤ 2 ^ 52 - |z| := by linarith
    rw [abs_of_nonneg h1] at this
    omega) (by norm_num)
  have hw2 : value w2.toBits = 1 / 2 - |(n : ℝ) / 2 ^ 53 - 1 / 2| := by
    rw [hw2v, ← hzr, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 53), Int.cast_sub,
      Int.cast_pow, Int.cast_ofNat, Int.cast_abs]
    field_simp
  obtain ⟨hcf, hcv⟩ := fsub_exact 0.5 (x - 0.5).abs w2 half_finite hbf hw2f
    (by rw [hw2, half_value, hbv]) (by
      rw [half_value, hbv]
      have h0 := abs_nonneg ((n : ℝ) / 2 ^ 53 - 1 / 2)
      have h1 : |(1 / 2 : ℝ) - (|(n : ℝ) / 2 ^ 53 - 1 / 2|)| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      linarith [(by norm_num : (1 : ℝ) < 2 ^ 1023)])
  rw [half_value, hbv] at hcv
  exact ⟨hcf, hcv⟩

#print axioms half_parts

theorem sin_eq_near (X : ℝ) :
    Real.sin (Real.pi * X) = Real.sin (Real.pi * (1 / 2 - |X - 1 / 2|)) := by
  rw [show Real.pi * (1 / 2 - |X - 1 / 2|) = Real.pi / 2 - Real.pi * |X - 1 / 2| by ring,
    Real.sin_pi_div_two_sub, ← abs_of_pos Real.pi_pos, ← abs_mul, Real.cos_abs,
    abs_of_pos Real.pi_pos, show Real.pi * (X - 1 / 2) = Real.pi * X - Real.pi / 2 by ring,
    Real.cos_sub_pi_div_two]

set_option maxHeartbeats 1000000 in
/-- **`asSinpipid` within `2^-63` of `sin (π x)/π`, relative,** for `x = n/2^53` with
`0 < n < 2^53`, with the low part at most `2^-50` of the high part. -/
theorem asSinpipid_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hS : LgammaApprox.SinpiFact) (x : Float) (n : ℕ)
    (hn0 : 0 < n) (hn : n < 2 ^ 53) (hx : Finite x.toBits) (hv : value x.toBits = n / 2 ^ 53) :
    Finite (Lgamma.asSinpipid Lgamma.sinpiTable x).1.toBits ∧
      Finite (Lgamma.asSinpipid Lgamma.sinpiTable x).2.toBits ∧
      |value (Lgamma.asSinpipid Lgamma.sinpiTable x).1.toBits +
          value (Lgamma.asSinpipid Lgamma.sinpiTable x).2.toBits -
          Real.sin (Real.pi * value x.toBits) / Real.pi| ≤
        Real.sin (Real.pi * value x.toBits) / Real.pi / 2 ^ 63 ∧
      |value (Lgamma.asSinpipid Lgamma.sinpiTable x).2.toBits| ≤
        |value (Lgamma.asSinpipid Lgamma.sinpiTable x).1.toBits| / 2 ^ 50 := by
  obtain ⟨hT1, hT2, hT3, hT4⟩ := hS
  obtain ⟨k, hk64, hky, -, -, hdb⟩ := red_spec x n hn0 hn hx hv
  obtain ⟨hbf, hbv, hzf, hzv⟩ := half_parts x n hn0 hn hx hv
  obtain ⟨R, hRd⟩ : ∃ R, R = Lgamma.asSinpipid Lgamma.sinpiTable x := ⟨_, rfl⟩
  rw [← hRd]
  have hR : R = if 64 - UInt64.ofNat k < 2 then
      nearTail (0.5 - (x - 0.5).abs) (entry Lgamma.sinpiTable 138) (entry Lgamma.sinpiTable 139)
        (entry Lgamma.sinpiTable 140) (entry Lgamma.sinpiTable 141) (entry Lgamma.sinpiTable 142)
      else Tgamma.asSinpid Lgamma.sinpiTable x := by
    rw [hRd, asSinpipid_eq]; dsimp only; rw [hky]
  have hX : |(n : ℝ) / 2 ^ 53 - 1 / 2| ≤ 1 / 2 - 1 / 2 ^ 53 := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have h2 : (n : ℝ) ≤ 2 ^ 53 - 1 := by
      have h3 : n + 1 ≤ 2 ^ 53 := by omega
      have h4 : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ 53 : ℕ) : ℝ) := by exact_mod_cast h3
      push_cast at h4
      linarith
    rw [abs_le]; constructor
    · have : (1 : ℝ) / 2 ^ 53 ≤ n / 2 ^ 53 := by gcongr
      linarith
    · have : (n : ℝ) / 2 ^ 53 ≤ (2 ^ 53 - 1) / 2 ^ 53 := by gcongr
      have e : ((2 : ℝ) ^ 53 - 1) / 2 ^ 53 = 1 - 1 / 2 ^ 53 := by field_simp
      linarith
  rw [hv]
  rcases (show 63 ≤ k ∨ k ≤ 62 by omega) with hk | hk
  · -- within `3/256` of an integer
    have hc : 64 - UInt64.ofNat k < 2 := by
      rw [ix_sub k hk64, UInt64.lt_iff_toNat_lt, ofNat_toNat _ (by omega)]
      simp only [UInt64.reduceToNat]; omega
    rw [hR, ite_eq_left hc]
    have hnear := nearOK_lgamma
    unfold nearOK at hnear
    simp only [Bool.and_eq_true] at hnear
    obtain ⟨⟨⟨⟨f138, f139⟩, f140⟩, f141⟩, f142⟩ := hnear
    have ek : ∀ (k : UInt64) (i : ℕ), k.toNat = i → finW Lgamma.sinpiTable[i]! = true →
        (entry Lgamma.sinpiTable k).toBits = Lgamma.sinpiTable[i]! := by
      intro k i hki hf
      rw [entry_bits _ _ (by rw [hki]; exact finW_spec _ hf), hki]
    have e138 := ek 138 138 rfl f138
    have e139 := ek 139 139 rfl f139
    have e140 := ek 140 140 rfl f140
    have e141 := ek 141 141 rfl f141
    have e142 := ek 142 142 rfl f142
    have hZ1 : 1 / 2 - |(n : ℝ) / 2 ^ 53 - 1 / 2| ≤ 3 / 256 := by
      have := (abs_le.mp hdb).2
      have hk' : (63 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    obtain ⟨Z, hZd⟩ : ∃ v, v = 1 / 2 - |(n : ℝ) / 2 ^ 53 - 1 / 2| := ⟨_, rfl⟩
    rw [← hZd] at hzv hZ1
    have hZ0 : 1 / 2 ^ 53 ≤ Z := by rw [hZd]; linarith
    have hN := near_spec hF (0.5 - (x - 0.5).abs) (entry Lgamma.sinpiTable 138)
      (entry Lgamma.sinpiTable 139) (entry Lgamma.sinpiTable 140) (entry Lgamma.sinpiTable 141)
      (entry Lgamma.sinpiTable 142) hzf (by rw [hzv]; exact hZ0) (by rw [hzv]; exact hZ1)
      (by rw [e138]; exact finW_spec _ f138) (by rw [e139]; exact finW_spec _ f139)
      (by rw [e140]; exact finW_spec _ f140) (by rw [e141]; exact finW_spec _ f141)
      (by rw [e142]; exact finW_spec _ f142)
      (by
        have h := word_bounds Lgamma.sinpiTable[138]! (-1645 / 1000) (-1644 / 1000) (by decide +kernel)
        rw [e138]; push_cast at h; constructor <;> linarith [h.1, h.2])
      (by
        have h := word_bounds Lgamma.sinpiTable[139]! (-1 / 2 ^ 54) (1 / 2 ^ 54) (by decide +kernel)
        rw [e139, abs_le]; push_cast at h; constructor <;> linarith [h.1, h.2])
      (by
        have h := word_bounds Lgamma.sinpiTable[140]! (-82 / 100) (82 / 100) (by decide +kernel)
        rw [e140, abs_le]; push_cast at h; constructor <;> linarith [h.1, h.2])
      (by
        have h := word_bounds Lgamma.sinpiTable[141]! (-20 / 100) (20 / 100) (by decide +kernel)
        rw [e141, abs_le]; push_cast at h; constructor <;> linarith [h.1, h.2])
      (by
        have h := word_bounds Lgamma.sinpiTable[142]! (-3 / 100) (3 / 100) (by decide +kernel)
        rw [e142, abs_le]; push_cast at h; constructor <;> linarith [h.1, h.2])
    obtain ⟨hN1, hN2, hNe, hNl⟩ := hN
    refine ⟨hN1, hN2, ?_, hNl⟩
    rw [hzv, e138, e139, e140, e141, e142] at hNe
    have hK := hT4 Z (by rw [abs_le]; constructor <;> linarith)
    rw [nearPoly_eq, abs_of_pos (by linarith : (0 : ℝ) < Z)] at hK
    rw [sin_eq_near, ← hZd]
    have hs : 2 * Z / (315 / 100) ≤ Real.sin (Real.pi * Z) / Real.pi := by
      have hZn : 0 ≤ Z := by linarith
      have h1 := Real.mul_le_sin (x := Real.pi * Z) (mul_nonneg Real.pi_pos.le hZn) (by
        have := mul_le_mul_of_nonneg_left (show Z ≤ 1 / 2 by linarith) Real.pi_pos.le
        linarith)
      rw [← mul_assoc, div_mul_cancel₀ 2 Real.pi_ne_zero] at h1
      rw [le_div_iff₀ Real.pi_pos]
      have h2 := mul_le_mul_of_nonneg_left Real.pi_lt_d2.le
        (show (0 : ℝ) ≤ 2 * Z / (315 / 100) by positivity)
      have h3 : 2 * Z / (315 / 100) * 3.15 = 2 * Z := by norm_num
      linarith
    have h2 := abs_add_le (value (nearTail (0.5 - (x - 0.5).abs) (entry Lgamma.sinpiTable 138)
        (entry Lgamma.sinpiTable 139) (entry Lgamma.sinpiTable 140) (entry Lgamma.sinpiTable 141)
        (entry Lgamma.sinpiTable 142)).1.toBits + value (nearTail (0.5 - (x - 0.5).abs)
        (entry Lgamma.sinpiTable 138) (entry Lgamma.sinpiTable 139) (entry Lgamma.sinpiTable 140)
        (entry Lgamma.sinpiTable 141) (entry Lgamma.sinpiTable 142)).2.toBits -
        (Z + Z ^ 3 * ((value Lgamma.sinpiTable[138]! + value Lgamma.sinpiTable[139]!) +
          Z ^ 2 * (value Lgamma.sinpiTable[140]! + Z ^ 2 * (value Lgamma.sinpiTable[141]! +
            Z ^ 2 * value Lgamma.sinpiTable[142]!)))))
      ((Z + Z ^ 3 * ((value Lgamma.sinpiTable[138]! + value Lgamma.sinpiTable[139]!) +
          Z ^ 2 * (value Lgamma.sinpiTable[140]! + Z ^ 2 * (value Lgamma.sinpiTable[141]! +
            Z ^ 2 * value Lgamma.sinpiTable[142]!)))) - Real.sin (Real.pi * Z) / Real.pi)
    rw [show ∀ a b c : ℝ, a - b + (b - c) = a - c from fun a b c => by ring, abs_sub_comm
      ((Z + Z ^ 3 * ((value Lgamma.sinpiTable[138]! + value Lgamma.sinpiTable[139]!) +
          Z ^ 2 * (value Lgamma.sinpiTable[140]! + Z ^ 2 * (value Lgamma.sinpiTable[141]! +
            Z ^ 2 * value Lgamma.sinpiTable[142]!)))))] at h2
    linarith
  · -- the table
    have hc : ¬ (64 - UInt64.ofNat k < 2) := by
      rw [ix_sub k hk64, UInt64.lt_iff_toNat_lt, ofNat_toNat _ (by omega)]
      simp only [UInt64.reduceToNat]; omega
    rw [hR, ite_eq_right hc]
    have hst : ∀ k ≤ 64, |value Lgamma.sinpiTable[2 * k]! + value Lgamma.sinpiTable[2 * k + 1]! -
        1 / Real.pi * Real.sin (k * Real.pi / 128)| ≤ 1 / 2 ^ 100 := by
      intro k hk
      have h := hT1 k hk
      simp only [LgammaApprox.stpi, LgammaApprox.q, Rat.cast_add, PolyBound.ratOfWord_cast] at h
      rw [one_div_mul_eq_div]; exact h
    have hs : ∀ d : ℝ, |d| ≤ 1 / 2 →
        |Real.sin (Real.pi * d / 128) - d * Ks (d ^ 2)| ≤ 1 / 2 ^ 73 * |d| := by
      intro d hd; have h := hT2 d hd; rw [sinKernel_eq] at h; exact h
    have hcc : ∀ d : ℝ, |d| ≤ 1 / 2 →
        |Real.cos (Real.pi * d / 128) - (1 + d ^ 2 * Kc (d ^ 2))| ≤ 1 / 2 ^ 76 * d ^ 2 := by
      intro d hd; have h := hT3 d hd; rw [cosKernel_eq] at h; exact h
    obtain ⟨h1, h2, h3, h4, h5, -⟩ := asSinpid_gen hF Lgamma.sinpiTable sinTabOK_lgamma (1 / Real.pi)
      (1 / 2 ^ 100) (1 / 2 ^ 73) (1 / 2 ^ 76) hst hs hcc x n hn0 hn hx hv
    refine ⟨h1, h2, ?_, h4⟩
    rw [hv] at h3 h5
    have hy : 3 / 2 ≤ 64 - 128 * |(n : ℝ) / 2 ^ 53 - 1 / 2| := by
      have := (abs_le.mp hdb).1
      have hk' : (k : ℝ) ≤ 62 := by exact_mod_cast hk
      linarith
    rw [min_eq_left (by linarith), one_mul, one_div_mul_eq_div] at h3
    have hs0 : 3 / 2 / 64 / (315 / 100) ≤ Real.sin (Real.pi * (n / 2 ^ 53)) / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      have h2 := mul_le_mul_of_nonneg_left Real.pi_lt_d2.le
        (show (0 : ℝ) ≤ 3 / 2 / 64 / (315 / 100) by norm_num)
      have h3 : (3 / 2 / 64 / (315 / 100) : ℝ) * 3.15 = 3 / 2 / 64 := by norm_num
      linarith
    linarith [(by norm_num : (81 / 80 * (1 / 2 ^ 100) + (1 + 1 / 2 ^ 50) * (1 / 2 ^ 73 / 2 +
      1 / 2 ^ 76 / 4) + 1 / 2 ^ 71 : ℝ) + 1 / 2 ^ 1060 ≤ 3 / 2 / 64 / (315 / 100) / 2 ^ 63),
      div_le_div_of_nonneg_right hs0 (by positivity : (0 : ℝ) ≤ 2 ^ 63)]

#print axioms asSinpipid_spec

#print axioms sinTabOK_lgamma
#print axioms nearOK_lgamma

end Library.Numerics.Float64.Lgamma.LgammaSinpi
