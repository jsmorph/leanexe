import Library.Numerics.Float64.Lgamma.LgammaRootEval

/-!
The code of `Lgamma.accurate` for one range of the polynomials about the negative zeros, before
the polynomial: the shifted argument `z = sx + x0` from the triple `e0 + e1 + e2` of `-x0`
(`z_spec`).  `e0 + sx` is exact by Sterbenz's lemma, since `sx` lies within `1/2` of `-e0`.
Both lie in the binade `[2^p, 2^(p+1))` and are multiples of `2^(p - 52)`, so `e0 + sx` is zero or
at least `2^(p - 52)`, and `fastTwoSum` with `|e1| ≤ 2^(p - 53)` is exact.  The low part then
takes `e2` with one rounding, and `zh + zl` is within `|z|/2^62` of `z` for `|z| ≥ 2^-90`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaRootPath
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD LgammaAccLow LgammaAccAdd

set_option exponentiation.threshold 4096

/-- `add a b` is `sub a (negate b)`. -/
theorem add_eq_sub (a b : UInt64) :
    Wasm.IEEE64.add a b = Wasm.IEEE64.sub a (Wasm.IEEE64.negate b) := by
  rw [show Wasm.IEEE64.sub a (Wasm.IEEE64.negate b) =
    Wasm.IEEE64.add a (Wasm.IEEE64.negate (Wasm.IEEE64.negate b)) from rfl,
    F64RelativeStep.negate_negate]

/-- **Sterbenz's lemma for a sum** of operands of opposite signs. -/
theorem add_sterbenz (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits)
    (h1 : |value a.toBits + value b.toBits| ≤ |value a.toBits|)
    (h2 : |value a.toBits + value b.toBits| ≤ |value b.toBits|)
    (h3 : |value b.toBits| < 2 ^ 1021) :
    Finite (a + b).toBits ∧ value (a + b).toBits = value a.toBits + value b.toBits := by
  obtain ⟨hnb, hnbv⟩ := F64Magnitude.negate_value b.toBits hb
  rw [F64Bits.toBits_add, add_eq_sub]
  obtain ⟨hf, hv⟩ := F64Sterbenz.sub_exact a.toBits (Wasm.IEEE64.negate b.toBits) ha hnb
    (by rw [hnbv, sub_neg_eq_add]; exact h1)
    (by rw [hnbv, sub_neg_eq_add, abs_neg]; exact h2)
    (by rw [hnbv, abs_neg]; exact h3)
  rw [hnbv, sub_neg_eq_add] at hv
  exact ⟨hf, hv⟩

/-- A double of magnitude at least `2^p` is a multiple of `2^(p - 52)`. -/
theorem grid_p (w : UInt64) (hw : Finite w) (p : ℕ) (hp : p ≤ 1000)
    (h : (2 : ℝ) ^ p ≤ |value w|) : ∃ K : ℤ, value w = K * 2 ^ p / 2 ^ 52 := by
  obtain ⟨K, hK⟩ := Library.Numerics.Float64.Tgamma.TgammaMainRed.grid w hw (p + 1021) (by omega)
    (by rw [show (2 : ℝ) ^ (53 + (p + 1021)) / 2 ^ 1074 = 2 ^ p by
          rw [show 53 + (p + 1021) = p + 1074 by omega, pow_add]; field_simp]
        exact h)
  refine ⟨K, ?_⟩
  have e : (2 : ℝ) ^ (p + 1021 + 1) = 2 ^ p * 2 ^ 1022 := by rw [← pow_add]
  rw [e] at hK
  have h1074 : (2 : ℝ) ^ 1074 = 2 ^ 52 * 2 ^ 1022 := by norm_num
  field_simp
  rw [h1074] at hK
  nlinarith [hK]

set_option maxHeartbeats 4000000 in
/-- **The shifted argument** `zh + zl ≈ sx + e0 + e1 + e2`. -/
theorem z_spec (e0 e1 e2 sx : Float) (h0 : Finite e0.toBits) (h1 : Finite e1.toBits)
    (h2 : Finite e2.toBits) (hsx : Finite sx.toBits) (p : ℕ) (hp : p ≤ 10)
    (he0 : (2 : ℝ) ^ p ≤ value e0.toBits) (hsx1 : (2 : ℝ) ^ p ≤ -value sx.toBits)
    (hsx2 : -value sx.toBits < 2 ^ (p + 1))
    (hnear : |value e0.toBits + value sx.toBits| ≤ 1 / 2)
    (he1 : |value e1.toBits| ≤ 2 ^ p / 2 ^ 53) (he2 : |value e2.toBits| ≤ 1 / 2 ^ 102)
    (hz : 1 / 2 ^ 90 ≤ |value sx.toBits + (value e0.toBits + value e1.toBits + value e2.toBits)|)
    (zh zl : Float) (hT : fastTwoSum (e0 + sx) e1 = (zh, zl)) :
    Finite zh.toBits ∧ Finite (zl + e2).toBits ∧
      |value zh.toBits + value (zl + e2).toBits -
          (value sx.toBits + (value e0.toBits + value e1.toBits + value e2.toBits))| ≤
        |value sx.toBits + (value e0.toBits + value e1.toBits + value e2.toBits)| / 2 ^ 62 ∧
      |value (zl + e2).toBits| ≤ |value zh.toBits| / 2 ^ 51 + 1 / 2 ^ 101 ∧
      |value zh.toBits| ≤ 1 := by
  have hpp : (1 : ℝ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)
  have hp11 : (2 : ℝ) ^ (p + 1) ≤ 2 ^ 11 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hp10 : (2 : ℝ) ^ p ≤ 2 ^ 10 := pow_le_pow_right₀ (by norm_num) hp
  have hsxn : value sx.toBits < 0 := by linarith
  -- `e0 + sx` is exact
  obtain ⟨af, av⟩ := add_sterbenz e0 sx h0 hsx
    (by rw [abs_of_pos (show (0 : ℝ) < value e0.toBits by linarith)]; linarith [abs_le.mp hnear])
    (by rw [abs_of_neg hsxn]; linarith [abs_le.mp hnear])
    (by rw [abs_of_neg hsxn]; linarith [(by norm_num : (2 : ℝ) ^ 11 < 2 ^ 1021)])
  -- the grid of the binade
  obtain ⟨K0, hK0⟩ := grid_p e0.toBits h0 p (by omega)
    (by rw [abs_of_pos (show (0 : ℝ) < value e0.toBits by linarith)]; exact he0)
  obtain ⟨K1, hK1⟩ := grid_p sx.toBits hsx p (by omega) (by rw [abs_of_neg hsxn]; exact hsx1)
  have hsum : value e0.toBits + value sx.toBits = ((K0 + K1 : ℤ) : ℝ) * 2 ^ p / 2 ^ 52 := by
    rw [hK0, hK1]; push_cast; ring
  -- the exact two-sum of `e0 + sx` and `e1`
  obtain ⟨zf, lf, hzs, hzl⟩ : Finite zh.toBits ∧ Finite zl.toBits ∧
      value zh.toBits + value zl.toBits = value e0.toBits + value sx.toBits + value e1.toBits ∧
      |value zl.toBits| ≤ |value zh.toBits| / 2 ^ 52 + 1 / 2 ^ 1074 := by
    by_cases hK : K0 + K1 = 0
    · have ha0 : value (e0 + sx).toBits = 0 := by rw [av, hsum, hK]; simp
      obtain ⟨f1, f2, v1, v2⟩ := LgammaLogdAcc.fts_zero (e0 + sx) e1 af h1 ha0
        (by linarith [abs_nonneg (value e1.toBits), (by norm_num : (2 : ℝ) ^ 10 / 2 ^ 53 < 2 ^ 1000),
          div_le_div_of_nonneg_right hp10 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)])
      rw [hT] at f1 f2 v1 v2
      dsimp only at f1 f2 v1 v2
      refine ⟨f1, f2, by rw [v1, v2, ← av, ha0]; ring, by rw [v2, abs_zero]; positivity⟩
    · have hK1' : (1 : ℝ) ≤ |((K0 + K1 : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hK
      have hge : 2 ^ p / 2 ^ 52 ≤ |value e0.toBits + value sx.toBits| := by
        rw [hsum, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ p),
          abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 52)]
        rw [div_le_div_iff_of_pos_right (by positivity)]
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) p]
      have hle : |value e1.toBits| ≤ 2 ^ p / 2 ^ 52 := by
        have : (2 : ℝ) ^ p / 2 ^ 53 ≤ 2 ^ p / 2 ^ 52 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) (by norm_num)
        linarith
      obtain ⟨f1, f2, v1, -, v2⟩ := fastTwoSum_spec (e0 + sx) e1 af h1
        (by rw [av]; linarith)
        (by rw [av]; linarith [(by norm_num : (1 : ℝ) / 2 < 2 ^ 900), abs_le.mp hnear])
      rw [hT] at f1 f2 v1 v2
      dsimp only at f1 f2 v1 v2
      exact ⟨f1, f2, by rw [v1, av], v2⟩
  set z := value sx.toBits + (value e0.toBits + value e1.toBits + value e2.toBits) with hzdef
  -- the high part
  have hzh : |value zh.toBits| ≤ |z| * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 101 := by
    have h3 := abs_sub_abs_le_abs_sub (value zh.toBits) (z - value e2.toBits)
    rw [show value zh.toBits - (z - value e2.toBits) = -value zl.toBits by rw [hzdef]; linarith,
      abs_neg] at h3
    have := abs_sub z (value e2.toBits)
    have := abs_nonneg z
    nlinarith
  have hzh1 : |value zh.toBits| ≤ 1 := by
    have : |z| ≤ 1 / 2 + 2 ^ p / 2 ^ 53 + 1 / 2 ^ 102 := by
      rw [hzdef, show value sx.toBits + (value e0.toBits + value e1.toBits + value e2.toBits) =
        (value e0.toBits + value sx.toBits) + value e1.toBits + value e2.toBits by ring]
      have := abs_add_le (value e0.toBits + value sx.toBits + value e1.toBits) (value e2.toBits)
      have := abs_add_le (value e0.toBits + value sx.toBits) (value e1.toBits)
      linarith
    have := div_le_div_of_nonneg_right hp10 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)
    nlinarith [(by norm_num : ((1 : ℝ) / 2 + 2 ^ 10 / 2 ^ 53 + 1 / 2 ^ 102) * (1 + 1 / 2 ^ 51) +
      1 / 2 ^ 101 ≤ 1), abs_nonneg z]
  have hzl1 : |value zl.toBits| ≤ 1 / 2 ^ 51 := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 51),
      div_le_div_of_nonneg_right hzh1 (by norm_num : (0 : ℝ) ≤ 2 ^ 52)]
  have hr := fapprox_add (fapprox_self zl lf) (fapprox_self e2 h2)
    (|value zl.toBits| + |value e2.toBits|) (by simp only [add_zero]; exact abs_add_le _ _)
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 51 + 1 / 2 ^ 102 < 2 ^ 1023)])
  obtain ⟨rf, re⟩ := hr
  simp only [zero_add] at re
  refine ⟨zf, rf, ?_, ?_, hzh1⟩
  · have k : value zh.toBits + value (zl + e2).toBits - z =
        value (zl + e2).toBits - (value zl.toBits + value e2.toBits) := by
      rw [hzdef]; linarith
    rw [k]
    have h80 : (1 : ℝ) / 2 ^ 154 ≤ |z| / 2 ^ 64 := by
      have := div_le_div_of_nonneg_right hz (by norm_num : (0 : ℝ) ≤ 2 ^ 64)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 154 ≤ 1 / 2 ^ 90 / 2 ^ 64)]
    have hzl' : |value zl.toBits| ≤ |z| / 2 ^ 51 + 1 / 2 ^ 152 := by
      have := div_le_div_of_nonneg_right hzh (by norm_num : (0 : ℝ) ≤ 2 ^ 52)
      have := abs_nonneg z
      nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 101 / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 152)]
    have : (|value zl.toBits| + |value e2.toBits|) / 2 ^ 53 ≤ |z| / 2 ^ 104 + 1 / 2 ^ 154 := by
      have h3 : |value zl.toBits| + |value e2.toBits| ≤ |z| / 2 ^ 51 + 1 / 2 ^ 101 := by
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 152 + 1 / 2 ^ 102 ≤ 1 / 2 ^ 101)]
      have := div_le_div_of_nonneg_right h3 (by norm_num : (0 : ℝ) ≤ 2 ^ 53)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 101 / 2 ^ 53 = 1 / 2 ^ 154)]
    have : |z| / 2 ^ 104 + |z| / 2 ^ 64 ≤ |z| / 2 ^ 62 := by
      have := abs_nonneg z
      linarith
    linarith
  · have h3 := abs_sub_abs_le_abs_sub (value (zl + e2).toBits) (value zl.toBits + value e2.toBits)
    have h4 := abs_add_le (value zl.toBits) (value e2.toBits)
    have h5 : (|value zl.toBits| + |value e2.toBits|) / 2 ^ 53 ≤ (1 / 2 ^ 51 + 1 / 2 ^ 102) / 2 ^ 53 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    linarith [(by norm_num : ((1 : ℝ) / 2 ^ 51 + 1 / 2 ^ 102) / 2 ^ 53 + 1 / 2 ^ 1074 + 1 / 2 ^ 102 ≤
      1 / 2 ^ 101), abs_nonneg (value zh.toBits)]

/-- The scaled magnitude of a finite word: a 53-bit integer times `2^(exponent - 1)`. -/
theorem mag_form (w : UInt64) :
    ∃ m : ℕ, Wasm.IEEE64.scaledMagnitude w = m * 2 ^ (Wasm.IEEE64.exponent w - 1) ∧
      m < 2 ^ 53 := by
  have hf : Wasm.IEEE64.fraction w < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  unfold Wasm.IEEE64.scaledMagnitude
  by_cases he : Wasm.IEEE64.exponent w = 0
  · exact ⟨Wasm.IEEE64.fraction w, by simp [he], by omega⟩
  · exact ⟨2 ^ 52 + Wasm.IEEE64.fraction w, by simp [he], by omega⟩

/-- **A product by the scale `2^E`** of a double of magnitude below 2 is exact. -/
theorem scale_exact (x sc : Float) (hx : Finite x.toBits) (hsc : Finite sc.toBits) (E : ℕ)
    (hE : E ≤ 30) (hscm : Wasm.IEEE64.scaledMagnitude sc.toBits = 2 ^ (1074 + E))
    (hx2 : |value x.toBits| < 2) :
    Finite (x * sc).toBits ∧ value (x * sc).toBits = value x.toBits * value sc.toBits := by
  have hxe : Wasm.IEEE64.exponent x.toBits < 1024 := by
    apply F64ExponentBounds.exponent_lt_of_magnitude_lt x.toBits 1024 (by norm_num)
    show |value x.toBits| < |value (UInt64.ofNat (1024 * 2 ^ 52))|
    rw [F64NearestBinade.boundary_power 1024 1 (by norm_num) (by norm_num) (by norm_num),
      abs_of_pos (by norm_num : (0 : ℝ) < 2 ^ (1 : Int))]
    exact lt_of_lt_of_le hx2 (le_of_eq (by norm_num))
  obtain ⟨m, hm, hm53⟩ := mag_form x.toBits
  have h := F64ExactProduct.mul_exact_scaled x.toBits sc.toBits hx hsc m 1
    (Wasm.IEEE64.exponent x.toBits - 1) (1074 + E) hm (by rw [hscm]; ring) (by omega)
    (by omega) (by omega)
  rw [F64Bits.toBits_mul]
  exact ⟨h.1, h.2.1⟩

/-- The doubles of a tail as a list. -/
def tailList (tab : Array UInt64) (o k : ℕ) : List ℚ :=
  (List.range k).map fun i => PolyBound.ratOfWord tab[o + 2 * i]!

theorem eval_tailList (tab : Array UInt64) (O N K : ℕ) (hK : 1 ≤ K) (t : ℝ) :
    PolyBound.eval (tailList tab (O + 2 * N) K) t = LgammaRootEval.tailQ tab O N K t := by
  rw [tailList, Library.Numerics.Float64.Tgamma.TgammaWords.eval_map_range, LgammaRootEval.tailQ, Library.Numerics.Float64.Tgamma.TgammaPoly.horner_eval _ K hK,
    zero_mul, add_zero]

set_option maxHeartbeats 4000000 in
/-- **The tail of a root polynomial**: `sh · polyD (...)` within `X e + X (M + e)/2^53 +
Lp |sl|` of `s Q (s)` for `s = sh + sl`, from the bound `(M, e)` of its Horner expression. -/
theorem tail_spec (tab : Array UInt64) (o2 kU : UInt64) (O N K : ℕ) (ho2 : o2.toNat = O + 2 * N)
    (hk : kU.toNat = K) (hK1 : 1 ≤ K) (hon : O + 2 * N + 2 * K < 2 ^ 63) (X R Lp : ℚ)
    (hok : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) X = true)
    (sh sl : Float) (hsh : Finite sh.toBits) (hX : |value sh.toBits| ≤ X)
    (hR1 : |value sh.toBits| ≤ R) (hR2 : |value sh.toBits + value sl.toBits| ≤ R)
    (hLp : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ R (0 :: tailList tab (O + 2 * N) K) ≤ Lp)
    (hXb : X * ((Library.Numerics.Float64.Tgamma.TgammaExpr.bnd (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) X).1 +
      (Library.Numerics.Float64.Tgamma.TgammaExpr.bnd (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) X).2) ≤ 1) :
    Finite (sh * Lgamma.polyD tab o2 kU sh).toBits ∧
      |value (sh * Lgamma.polyD tab o2 kU sh).toBits -
          (value sh.toBits + value sl.toBits) *
            LgammaRootEval.tailQ tab O N K (value sh.toBits + value sl.toBits)| ≤
        X * (Library.Numerics.Float64.Tgamma.TgammaExpr.bnd (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) X).2 +
          X * ((Library.Numerics.Float64.Tgamma.TgammaExpr.bnd (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) X).1 +
            (Library.Numerics.Float64.Tgamma.TgammaExpr.bnd (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) X).2) / 2 ^ 53 +
          1 / 2 ^ 1075 + Lp * |value sl.toBits| ∧
      |value (sh * Lgamma.polyD tab o2 kU sh).toBits| ≤
        X * ((Library.Numerics.Float64.Tgamma.TgammaExpr.bnd (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) X).1 +
          (Library.Numerics.Float64.Tgamma.TgammaExpr.bnd (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) X).2) *
            (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 := by
  set M := (Library.Numerics.Float64.Tgamma.TgammaExpr.bnd (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) X).1 with hM
  set e := (Library.Numerics.Float64.Tgamma.TgammaExpr.bnd (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) X).2 with he
  have hX0 : (0 : ℝ) ≤ X := (abs_nonneg _).trans hX
  have hX0q : (0 : ℚ) ≤ X := by exact_mod_cast hX0
  have hR0q : (0 : ℚ) ≤ R := by exact_mod_cast (abs_nonneg _).trans hR1
  obtain ⟨hMe0, hMe1⟩ := Library.Numerics.Float64.Tgamma.TgammaExpr.bnd_nonneg (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) X
    hX0q
  have hM0 : (0 : ℝ) ≤ M := by exact_mod_cast hMe0
  have he0 : (0 : ℝ) ≤ e := by exact_mod_cast hMe1
  rw [LgammaRootEval.polyD_eq tab o2 kU (by rw [hk]; exact hK1) (by rw [ho2, hk]; omega), ho2, hk]
  obtain ⟨hD, hDb⟩ := Library.Numerics.Float64.Tgamma.TgammaExpr.evalF_approx _ X sh hsh hX hok
  rw [← he] at hD
  rw [← hM] at hDb
  rw [LgammaRootEval.evalR_hornerE] at hD hDb
  set Q := Library.Numerics.Float64.Tgamma.TgammaPoly.horner (fun i => (PolyBound.ratOfWord tab[O + 2 * N + 2 * i]! : ℝ)) K 0
    (value sh.toBits) (K - 1) with hQ
  have hp := fapprox_mul (fapprox_self sh hsh) hD (X : ℝ) (M : ℝ) hX hDb
    ((X : ℝ) * ((M : ℝ) + e)) (by simp only [add_zero]; exact le_rfl)
    (by have : ((X * (M + e) : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hXb
        push_cast at this
        linarith [(by norm_num : (1 : ℝ) < 2 ^ 1022)])
  obtain ⟨pf, pe⟩ := hp
  simp only [zero_mul, zero_add, mul_zero, add_zero] at pe
  -- the Lipschitz part
  have hlip := Library.Numerics.Float64.Tgamma.TgammaPolyLip.eval_lip R hR0q (value sh.toBits) (value sh.toBits + value sl.toBits)
    hR1 hR2 (0 :: tailList tab (O + 2 * N) K)
  simp only [PolyBound.eval, eval_tailList tab O N K hK1] at hlip
  push_cast at hlip
  simp only [zero_add] at hlip
  have hLp' : (Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ R (0 :: tailList tab (O + 2 * N) K) : ℝ) ≤ Lp := by
    exact_mod_cast hLp
  rw [show value sh.toBits - (value sh.toBits + value sl.toBits) = -value sl.toBits by ring,
    abs_neg] at hlip
  have hQe : LgammaRootEval.tailQ tab O N K (value sh.toBits) = Q := rfl
  rw [hQe] at hlip
  have hlip' := hlip.trans (mul_le_mul_of_nonneg_right hLp' (abs_nonneg _))
  refine ⟨pf, ?_, ?_⟩
  · have k : value (sh * Library.Numerics.Float64.Tgamma.TgammaExpr.evalF (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) sh).toBits -
        (value sh.toBits + value sl.toBits) *
          LgammaRootEval.tailQ tab O N K (value sh.toBits + value sl.toBits) =
        (value (sh * Library.Numerics.Float64.Tgamma.TgammaExpr.evalF (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) sh).toBits -
          value sh.toBits * Q) +
        (value sh.toBits * Q - (value sh.toBits + value sl.toBits) *
          LgammaRootEval.tailQ tab O N K (value sh.toBits + value sl.toBits)) := by ring
    rw [k]
    have := abs_add_le (value (sh * Library.Numerics.Float64.Tgamma.TgammaExpr.evalF (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) sh).toBits -
          value sh.toBits * Q)
      (value sh.toBits * Q - (value sh.toBits + value sl.toBits) *
          LgammaRootEval.tailQ tab O N K (value sh.toBits + value sl.toBits))
    push_cast at pe ⊢
    linarith
  · have h1 := abs_sub_abs_le_abs_sub
      (value (sh * Library.Numerics.Float64.Tgamma.TgammaExpr.evalF (LgammaRootEval.hornerE tab (O + 2 * N) K (K - 1)) sh).toBits)
      (value sh.toBits * Q)
    have h2 : |value sh.toBits * Q| ≤ (X : ℝ) * M := by
      rw [abs_mul]; exact mul_le_mul hX hDb (abs_nonneg _) hX0
    push_cast at pe ⊢
    have h3 : (X : ℝ) * e + (X : ℝ) * ((M : ℝ) + e) / 2 ^ 53 ≤ (X : ℝ) * ((M : ℝ) + e) / 2 ^ 53 +
        (X : ℝ) * e := by linarith
    nlinarith

#print axioms tail_spec

/-- The magnitude bound of a tail's Horner expression on `[-X, X]`. -/
def tM (tab : Array UInt64) (o k : ℕ) (X : ℚ) : ℚ :=
  (Library.Numerics.Float64.Tgamma.TgammaExpr.bnd (LgammaRootEval.hornerE tab o k (k - 1)) X).1

/-- The error bound of a tail's Horner expression on `[-X, X]`. -/
def tE (tab : Array UInt64) (o k : ℕ) (X : ℚ) : ℚ :=
  (Library.Numerics.Float64.Tgamma.TgammaExpr.bnd (LgammaRootEval.hornerE tab o k (k - 1)) X).2

set_option maxHeartbeats 8000000 in
/-- **The polynomial of a range** at a double-double argument `sh + sl` in `[-Xn, Xp]`: the tail
by `tail_spec` and the double-double part by `LgammaRootEval.root_dd`. -/
theorem poly_part (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (tab : Array UInt64) (O N k P : ℕ) (hN1 : 1 ≤ N)
    (hk1 : 1 ≤ k) (hon : O + 2 * N + 2 * k < 2 ^ 63)
    (oD nD o2 kU : UInt64) (hoD : oD.toNat = O) (hnD : nD.toNat = N) (ho2 : o2.toNat = O + 2 * N)
    (hkU : kU.toNat = k)
    (Xp Xn Xh Xl : ℚ) (C Cl Es Λ K : List ℚ)
    (hok : LgammaRootEval.rootIvOk tab O N k P Xp Xn Xh Xl C Cl Es Λ K = true)
    (hE0 : ∀ m, 0 ≤ Es.getD m 0) (hΛ0 : ∀ m, 0 ≤ Λ.getD m 0)
    (Xt Rt Lt : ℚ) (htok : Library.Numerics.Float64.Tgamma.TgammaExpr.ok (LgammaRootEval.hornerE tab (O + 2 * N) k (k - 1)) Xt = true)
    (hLt : Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ Rt (0 :: tailList tab (O + 2 * N) k) ≤ Lt)
    (hXb : Xt * (tM tab (O + 2 * N) k Xt + tE tab (O + 2 * N) k Xt) ≤ 1)
    (htop : Xt * (tM tab (O + 2 * N) k Xt + tE tab (O + 2 * N) k Xt) * (1 + 1 / 2 ^ 53) +
      1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[O + 2 * (N - 1)]!))
    (hEi : (Xt * tE tab (O + 2 * N) k Xt + Xt * (tM tab (O + 2 * N) k Xt + tE tab (O + 2 * N) k Xt) /
        2 ^ 53 + 1 / 2 ^ 1075 + Lt * Xl) + (Xt * (tM tab (O + 2 * N) k Xt + tE tab (O + 2 * N) k Xt) *
        (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 + Cl.getD (N - 1) 0) / 2 ^ 53 ≤ Es.getD 0 0)
    (hΛi : (Xt * (tM tab (O + 2 * N) k Xt + tE tab (O + 2 * N) k Xt) * (1 + 1 / 2 ^ 53) +
        1 / 2 ^ 1075 + Cl.getD (N - 1) 0) * (1 + 1 / 2 ^ 53) ≤ Λ.getD 0 0)
    (sh sl : Float) (hshf : Finite sh.toBits) (hslf : Finite sl.toBits)
    (hXh : |value sh.toBits| ≤ (Xh : ℝ)) (hXl : |value sl.toBits| ≤ (Xl : ℝ))
    (hXt : |value sh.toBits| ≤ (Xt : ℝ)) (hRt1 : |value sh.toBits| ≤ (Rt : ℝ))
    (hRt2 : |value sh.toBits + value sl.toBits| ≤ (Rt : ℝ))
    (hs1 : -(Xn : ℝ) ≤ value sh.toBits + value sl.toBits)
    (hs2 : value sh.toBits + value sl.toBits ≤ Xp)
    (fh fl : Float)
    (hD : Lgamma.polyDD tab oD nD sh sl (sh * Lgamma.polyD tab o2 kU sh) = (fh, fl)) :
    Finite fh.toBits ∧ Finite fl.toBits ∧
      |value fh.toBits + value fl.toBits -
          Library.Numerics.Float64.Tgamma.TgammaPoly.horner (fun j => (LgammaRootEval.cf tab O N j : ℝ)) (N + k) 0
            (value sh.toBits + value sl.toBits) (N - 1 + k)| ≤ (Es.getD (N - 1) 0 : ℝ) ∧
      |value fl.toBits| ≤ (Λ.getD (N - 1) 0 : ℝ) := by
  have hXt0 : (0 : ℝ) ≤ Xt := (abs_nonneg _).trans hXt
  have hXl0 : (0 : ℝ) ≤ Xl := (abs_nonneg _).trans hXl
  obtain ⟨tf, te, tb⟩ := tail_spec tab o2 kU O N k ho2 hkU hk1 hon Xt Rt Lt htok sh sl hshf hXt hRt1
    hRt2 hLt hXb
  have hLt0 : (0 : ℝ) ≤ Lt := by
    have := Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ_nonneg Rt (by exact_mod_cast (abs_nonneg _).trans hRt1)
      (0 :: tailList tab (O + 2 * N) k)
    have h2 : ((Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ Rt (0 :: tailList tab (O + 2 * N) k) : ℚ) : ℝ) ≤ Lt := by
      exact_mod_cast hLt
    have h3 : (0 : ℝ) ≤ ((Library.Numerics.Float64.Tgamma.TgammaPolyLip.lipQ Rt (0 :: tailList tab (O + 2 * N) k) : ℚ) : ℝ) := by
      exact_mod_cast this
    linarith
  have hel : |value (sh * Lgamma.polyD tab o2 kU sh).toBits -
      (value sh.toBits + value sl.toBits) *
        LgammaRootEval.tailQ tab O N k (value sh.toBits + value sl.toBits)| ≤
      ((Xt * tE tab (O + 2 * N) k Xt + Xt * (tM tab (O + 2 * N) k Xt + tE tab (O + 2 * N) k Xt) /
        2 ^ 53 + 1 / 2 ^ 1075 + Lt * Xl : ℚ) : ℝ) := by
    push_cast
    have := mul_le_mul_of_nonneg_left hXl hLt0
    simp only [tE, tM] at te ⊢
    linarith
  have hlb : |value (sh * Lgamma.polyD tab o2 kU sh).toBits| ≤
      ((Xt * (tM tab (O + 2 * N) k Xt + tE tab (O + 2 * N) k Xt) * (1 + 1 / 2 ^ 53) +
        1 / 2 ^ 1075 : ℚ) : ℝ) := by
    push_cast
    simp only [tE, tM] at tb ⊢
    exact tb
  have htop' : ((Xt * (tM tab (O + 2 * N) k Xt + tE tab (O + 2 * N) k Xt) * (1 + 1 / 2 ^ 53) +
      1 / 2 ^ 1075 : ℚ) : ℝ) ≤ |((PolyBound.ratOfWord tab[O + 2 * (N - 1)]! : ℚ) : ℝ)| := by
    rw [← Library.Numerics.Float64.Tgamma.TgammaExpr.qabs_cast]; exact_mod_cast htop
  obtain ⟨f1, f2, e1, l1⟩ := LgammaRootEval.root_dd hF tab O N k P Xp Xn Xh Xl C Cl Es Λ K hok hE0
    hΛ0 oD nD hoD hnD hN1 hk1 (by omega) sh sl _ hshf hslf hXh hXl hs1 hs2 _ _ _ tf hel hlb htop'
    le_rfl (by
      have : ((Xt * (tM tab (O + 2 * N) k Xt + tE tab (O + 2 * N) k Xt) * (1 + 1 / 2 ^ 53) +
          1 / 2 ^ 1075 : ℚ) : ℝ) ≤ 1 * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 := by
        have h := (Rat.cast_le (K := ℝ)).mpr hXb
        push_cast at h ⊢
        nlinarith
      linarith [(by norm_num : (1 : ℝ) * (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤ 2 ^ 797)])
    (by have h := (Rat.cast_le (K := ℝ)).mpr hEi; push_cast at h ⊢; linarith)
    (by have h := (Rat.cast_le (K := ℝ)).mpr hΛi; push_cast at h ⊢; linarith)
  rw [hD] at f1 f2 e1 l1
  exact ⟨f1, f2, e1, l1⟩

#print axioms poly_part
#print axioms scale_exact
#print axioms add_sterbenz
#print axioms grid_p
#print axioms z_spec

end Library.Numerics.Float64.Lgamma.LgammaRootPath
