import Verified.Examples.LgammaFastPiece
import LeanExe.ProofKit.F64PositiveOrder
import LeanExe.ProofKit.F64PositiveSpacing
import LeanExe.ProofKit.F64ExponentBounds
import Verified.Examples.TgammaMainRed
import LeanExe.ProofKit.F64Grid
import LeanExe.ProofKit.F64Exact

/-!
The fast path of `Lgamma.lgammaWith` from `2 ^ -5` to `1/2` in magnitude: the piece of
`t + xl = 1 + x` (`fastTwoSum`) at `z = (t - offs k) + xl`, times `-x` on piece 4, plus `-log |x|`
from `asLogd` (`sumDD`).  `t` lies in `[1/2, 3/2]`, so its top bits select a piece `k < 8`
(`mid_t`).  `t - offs k` is exact by Sterbenz's lemma, and the sum with `xl` is exact because
`1 + x - offs k` is a multiple of the spacing `2 ^ (e - 1075)` of `x`, for the biased exponent `e`
of `x`, and the kernel checks `|1 + x - offs k| ≤ 2 ^ (e - 1022)` on each piece and binade that
the range reaches (`z_ok`, `mid_z`).  `PieceFact` puts the result within `1.4 · 10^-19` of
`ln Γ (1 + x)`, and `|ln |Γ x|| ≥ ln 2 - 0.58 > 1/10`, so the relative form of `FastSpec` holds
(`mid_spec`).
-/

namespace Verified.Examples.LgammaFastMid
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPolyDDD TgammaExpr TgammaWords
  LgammaPiecePoly LgammaFastSmall LgammaFastPiece LgammaPieceIdx LgammaWalk

set_option exponentiation.threshold 4096

/-! ### Words and grids -/

theorem word_value (w : UInt64) (q : ℚ) (h : PolyBound.ratOfWord w = q) : value w = (q : ℝ) := by
  rw [← PolyBound.ratOfWord_cast, h]

/-- A normal double is an integer multiple of `2 ^ (e - 1075)` for its biased exponent `e`. -/
theorem value_grid (w : UInt64) :
    ∃ m : ℤ, value w * 2 ^ 1074 = m * 2 ^ (Wasm.IEEE64.exponent w - 1) := by
  obtain ⟨M, -, hM⟩ := F64Exact.magnitude_grid w
  rcases F64Grid.value_cases w with hv | hv
  · refine ⟨M, ?_⟩
    rw [hv, hM, div_mul_cancel₀ _ (by positivity)]
    push_cast
    ring
  · refine ⟨-M, ?_⟩
    rw [hv, hM, neg_mul, div_mul_cancel₀ _ (by positivity)]
    push_cast
    ring

/-- The sum `d + xl` is exact when it equals `1 + v - o` for doubles `v` and `o` whose exponents
satisfy `1 ≤ e ≤ eo ≤ 1075` and `|1 + v - o| ≤ 2 ^ (e + 52)/2 ^ 1074`. -/
theorem sum_exact (d xl : Float) (hd : Finite d.toBits) (hxl : Finite xl.toBits) (x o : UInt64)
    (e eo : ℕ) (he : Wasm.IEEE64.exponent x = e) (heo : Wasm.IEEE64.exponent o = eo)
    (he1 : 1 ≤ e) (heeo : e ≤ eo) (heo1 : eo ≤ 1075)
    (hs : value d.toBits + value xl.toBits = 1 + value x - value o)
    (hz : |1 + value x - value o| ≤ (2 : ℝ) ^ (e + 52) / 2 ^ 1074) :
    Finite (d + xl).toBits ∧ value (d + xl).toBits = 1 + value x - value o := by
  obtain ⟨mx, hmx⟩ := value_grid x
  obtain ⟨mo, hmo⟩ := value_grid o
  rw [he] at hmx
  rw [heo] at hmo
  set z : ℤ := 2 ^ (1075 - e) + mx - mo * 2 ^ (eo - e) with hzdef
  have hp1 : (2 : ℝ) ^ 1074 = 2 ^ (e - 1) * 2 ^ (1075 - e) := by
    rw [← pow_add]; congr 1; omega
  have hp2 : (2 : ℝ) ^ (eo - 1) = 2 ^ (e - 1) * 2 ^ (eo - e) := by
    rw [← pow_add]; congr 1; omega
  have hsum : (value d.toBits + value xl.toBits) * 2 ^ 1074 = (z : ℝ) * 2 ^ (e - 1) := by
    rw [hs, hzdef]
    push_cast
    have : (1 + value x - value o) * 2 ^ 1074 =
        2 ^ 1074 + value x * 2 ^ 1074 - value o * 2 ^ 1074 := by ring
    rw [this, hmx, hmo, hp2, hp1]
    ring
  have hzb : |(z : ℝ)| ≤ 2 ^ 53 := by
    have hpos : (0 : ℝ) < 2 ^ (e - 1) := by positivity
    have h1 : |(z : ℝ)| * 2 ^ (e - 1) = |1 + value x - value o| * 2 ^ 1074 := by
      rw [← abs_of_pos hpos, ← abs_mul, ← hsum, hs, abs_mul,
        abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
    have h2 : |1 + value x - value o| * 2 ^ 1074 ≤ 2 ^ (e + 52) := by
      rw [le_div_iff₀ (by positivity)] at hz; exact hz
    have h3 : (2 : ℝ) ^ (e + 52) = 2 ^ 53 * 2 ^ (e - 1) := by
      rw [← pow_add]; congr 1; omega
    rw [h3, ← h1] at h2
    exact le_of_mul_le_mul_right h2 hpos
  have hs' : value d.toBits + value xl.toBits = 1 + value x - value o := hs
  obtain ⟨hf, hv⟩ := TgammaMainRed.add_exact d xl hd hxl z (e - 1) (by omega) hsum hzb
  exact ⟨hf, by rw [hv, hs']⟩

/-! ### Kernel checks -/

/-- The range of `1 + x` on piece `k` for positive `x` of biased exponent `e`, with the piece
widened by `2 ^ -50`. -/
def zloP (k e : ℕ) : ℚ := max (LgammaApprox.border k - 1 / 2 ^ 50) (1 + 2 ^ (e + 51) / 2 ^ 1074)
def zhiP (k e : ℕ) : ℚ :=
  min (LgammaApprox.border (k + 1) + 1 / 2 ^ 50) (1 + 2 ^ (e + 52) / 2 ^ 1074)

/-- The same range for negative `x`. -/
def zloN (k e : ℕ) : ℚ := max (LgammaApprox.border k - 1 / 2 ^ 50) (1 - 2 ^ (e + 52) / 2 ^ 1074)
def zhiN (k e : ℕ) : ℚ :=
  min (LgammaApprox.border (k + 1) + 1 / 2 ^ 50) (1 - 2 ^ (e + 51) / 2 ^ 1074)

/-- A nonempty range `[lo, hi]` lies within `B` of `off`. -/
def zOK (lo hi off B : ℚ) : Prop :=
  lo ≤ hi → PolyBound.qabs (lo - off) ≤ B ∧ PolyBound.qabs (hi - off) ≤ B

instance (lo hi off B : ℚ) : Decidable (zOK lo hi off B) := by unfold zOK; infer_instance

/-- `|1 + x - offs k| ≤ 2 ^ (e - 1022)` on each piece and binade that the range reaches. -/
theorem z_ok : ∀ k < 8, ∀ i < 4,
    zOK (zloP k (1018 + i)) (zhiP k (1018 + i)) (LgammaApprox.offs k)
        (2 ^ (1018 + i + 52) / 2 ^ 1074) ∧
      zOK (zloN k (1018 + i)) (zhiN k (1018 + i)) (LgammaApprox.offs k)
        (2 ^ (1018 + i + 52) / 2 ^ 1074) := by
  decide +kernel

/-- `|y - off| ≤ B` for `y` in a range `[lo, hi]` that `zOK` bounds. -/
theorem zOK_apply (lo hi off B : ℚ) (h : zOK lo hi off B) (y : ℝ) (hlo : (lo : ℝ) ≤ y)
    (hhi : y ≤ (hi : ℝ)) : |y - (off : ℝ)| ≤ (B : ℝ) := by
  obtain ⟨h1, h2⟩ := h (by exact_mod_cast hlo.trans hhi)
  have h1' := qcast_le h1
  have h2' := qcast_le h2
  rw [qabs_cast] at h1' h2'
  push_cast at h1' h2'
  rw [abs_le] at h1' h2' ⊢
  constructor <;> linarith [h1'.1, h2'.2]

/-- The offsets of the pieces `0` to `7` lie in the binades 1022 and 1023, and their polynomials
stay below `0.58`, except piece 4, below `0.7`, which carries the factor `-x`. -/
theorem mid_ok : ∀ k < 8, 1022 ≤ Wasm.IEEE64.exponent (wq (20 + k)) ∧
    Wasm.IEEE64.exponent (wq (20 + k)) ≤ 1023 := by
  decide +kernel

theorem hb_mid : (∀ k < 8, k ≠ 4 → hbQ k 4 ≤ 58 / 100) ∧ hbQ 4 4 ≤ 7 / 10 := by decide +kernel

/-- The borders as words: `tab[k] <<< 37` is `tw k · 2 ^ 37`, a positive finite double. -/
theorem border_words : ∀ k < 20, ((Lgamma.mainTable[k]! <<< 37 : UInt64)).toNat = tw k * 137438953472 ∧
    tw k * 137438953472 < 0x7FF0000000000000 := by
  decide +kernel

theorem tw8 : ∀ k < 19, 8 ≤ k → tw 8 ≤ tw k := by decide +kernel

theorem tw8_val : tw 8 = 0x1ffc05e := by decide +kernel

/-! ### `t = fl(1 + x)` and its piece -/

theorem border_le (k : ℕ) (hk : k < 20) (t : UInt64) (ht : t.toNat < 0x7FF0000000000000)
    (h : tw k ≤ t.toNat / 137438953472) : (LgammaApprox.border k : ℝ) ≤ value t := by
  obtain ⟨hw, hwl⟩ := border_words k hk
  have hb : (LgammaApprox.border k : ℝ) = value (Lgamma.mainTable[k]! <<< 37 : UInt64) :=
    PolyBound.ratOfWord_cast _
  rw [hb, F64PositiveOrder.value_le_iff (by rw [hw]; omega) (lt_of_lt_of_le ht (by norm_num)), hw]
  omega

theorem le_border (k : ℕ) (hk : k < 20) (t : UInt64) (ht : t.toNat < 0x7FF0000000000000)
    (h : t.toNat / 137438953472 < tw k) : value t ≤ (LgammaApprox.border k : ℝ) := by
  obtain ⟨hw, hwl⟩ := border_words k hk
  have hb : (LgammaApprox.border k : ℝ) = value (Lgamma.mainTable[k]! <<< 37 : UInt64) :=
    PolyBound.ratOfWord_cast _
  rw [hb, F64PositiveOrder.value_le_iff (lt_of_lt_of_le ht (by norm_num)) (by rw [hw]; omega), hw]
  omega

/-- **`t = fl(1 + x)`** lies in `[1/2, 3/2]`, its top bits select a piece `k < 8`, and `1 + x`
lies in that piece widened by `2 ^ -50`. -/
theorem mid_t (x : Float) (hx : Finite x.toBits)
    (hv1 : 1 / 2 ^ 5 ≤ |value x.toBits|) (hv2 : |value x.toBits| ≤ 1 / 2 - 1 / 2 ^ 54) :
    Finite (fastTwoSum 1.0 x).1.toBits ∧ Finite (fastTwoSum 1.0 x).2.toBits ∧
      value (fastTwoSum 1.0 x).1.toBits + value (fastTwoSum 1.0 x).2.toBits =
        1 + value x.toBits ∧
      |value (fastTwoSum 1.0 x).2.toBits| ≤ 1 / 2 ^ 51 ∧
      0 < value (fastTwoSum 1.0 x).1.toBits ∧
      ∃ k < 8, (Lgamma.piece Lgamma.mainTable ((fastTwoSum 1.0 x).1.toBits >>> 37)).toNat = k ∧
        (LgammaApprox.border k : ℝ) ≤ value (fastTwoSum 1.0 x).1.toBits ∧
        value (fastTwoSum 1.0 x).1.toBits ≤ (LgammaApprox.border (k + 1) : ℝ) := by
  set v := value x.toBits with hvdef
  obtain ⟨htf, hlf, hsum, hlx, hlt⟩ := fastTwoSum_spec 1.0 x LgammaSpecial.one_finite hx
    (by rw [LgammaSpecial.one_value, abs_one]; linarith)
    (by rw [LgammaSpecial.one_value, abs_one]; norm_num)
  rw [LgammaSpecial.one_value] at hsum
  have h1t : (fastTwoSum 1.0 x).1 = 1.0 + x := rfl
  -- `t` within `|1 + x|/2^53` of `1 + x`
  have ha := fapprox_add (fapprox_self 1.0 LgammaSpecial.one_finite) (fapprox_self x hx)
    (|1 + v|) (by rw [LgammaSpecial.one_value]; simp only [add_zero]; exact le_rfl)
    (lt_of_le_of_lt (abs_add_le 1 v) (by rw [abs_one]; linarith))
  rw [LgammaSpecial.one_value, ← h1t] at ha
  have hpos1 : (1 / 2 + 1 / 2 ^ 54 : ℝ) ≤ 1 + v := by
    have := abs_le.mp hv2; linarith
  have hlt1 : 1 + v ≤ 3 / 2 := by have := abs_le.mp hv2; linarith
  have habs1 : |1 + v| = 1 + v := abs_of_pos (by linarith)
  have hte := ha.2
  simp only [zero_add, habs1] at hte
  set t := (fastTwoSum 1.0 x).1 with htdef
  have htlo : 1 / 2 - 1 / 2 ^ 60 ≤ value t.toBits := by
    have := (abs_le.mp hte).1
    linarith
  have hthi : value t.toBits ≤ 3 / 2 + 1 / 2 ^ 52 := by
    have := (abs_le.mp hte).2
    have h2 : (1 + v) / 2 ^ 53 ≤ (3 / 2) / 2 ^ 53 := div_le_div_of_nonneg_right hlt1 (by norm_num)
    linarith
  have htpos : 0 < value t.toBits := by linarith
  have henc := F64PositiveOrder.positive_finite_encoding _ htf htpos
  have hlim : F64NearestNonnegative.limit = 0x7FF0000000000000 := rfl
  rw [hlim] at henc
  -- the bits of `t`
  have hb1 : 0x3FE0000000000000 ≤ t.toBits.toNat := by
    by_contra hn
    have h := (F64PositiveOrder.value_le_iff (left := t.toBits)
      (right := (0x3FDFFFFFFFFFFFFF : UInt64)) (lt_of_lt_of_le henc (by norm_num))
      (by decide)).mpr (by
        rw [show (0x3FDFFFFFFFFFFFFF : UInt64).toNat = 0x3FDFFFFFFFFFFFFF from rfl]; omega)
    rw [word_value (0x3FDFFFFFFFFFFFFF : UInt64) (1 / 2 - 1 / 2 ^ 54) (by decide +kernel)] at h
    push_cast at h
    linarith
  have hb2 : t.toBits.toNat ≤ 0x3FF8000000000001 := by
    by_contra hn
    have h := (F64PositiveOrder.value_le_iff (left := (0x3FF8000000000002 : UInt64))
      (right := t.toBits) (by decide) (lt_of_lt_of_le henc (by norm_num))).mpr (by
        rw [show (0x3FF8000000000002 : UInt64).toNat = 0x3FF8000000000002 from rfl]; omega)
    rw [word_value (0x3FF8000000000002 : UInt64) (3 / 2 + 1 / 2 ^ 51) (by decide +kernel)] at h
    push_cast at h
    linarith
  have hau : (t.toBits >>> 37).toNat = t.toBits.toNat / 137438953472 := by
    rw [UInt64.toNat_shiftRight, show (37 : UInt64).toNat % 64 = 37 from rfl,
      Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 37 = 137438953472 by norm_num]
  obtain ⟨k, hk, hkj, hk0, hk1⟩ := piece_spec (t.toBits >>> 37) (by rw [hau]; omega)
    (by rw [hau]; omega)
  rw [hau] at hk0 hk1
  have hk8 : k < 8 := by
    by_contra hn
    have := tw8 k hk (by omega)
    rw [tw8_val] at this
    omega
  refine ⟨htf, hlf, hsum, ?_, htpos, k, hk8, hkj, border_le k (by omega) _ henc hk0,
    le_border (k + 1) (by omega) _ henc hk1⟩
  have h2 : |value t.toBits| / 2 ^ 52 ≤ (3 / 2 + 1 / 2 ^ 52) / 2 ^ 52 :=
    div_le_div_of_nonneg_right (by rw [abs_of_pos htpos]; linarith) (by norm_num)
  linarith [(by norm_num : ((3 : ℝ) / 2 + 1 / 2 ^ 52) / 2 ^ 52 + 1 / 2 ^ 1074 ≤ 1 / 2 ^ 51)]

/-! ### The reduced argument -/

/-- **The reduced argument `z = (t - offs k) + xl`** equals `1 + x - offs k` and lies within
`pX k`, for `x` of biased exponent `1018 + i`. -/
theorem mid_z (x : Float) (hx : Finite x.toBits) (i : ℕ) (hi : i < 4)
    (he : Wasm.IEEE64.exponent x.toBits = 1018 + i)
    (hve : (2 : ℝ) ^ (1018 + i + 51) / 2 ^ 1074 ≤ |value x.toBits|)
    (hve' : |value x.toBits| ≤ (2 : ℝ) ^ (1018 + i + 52) / 2 ^ 1074)
    (t xl : Float) (htf : Finite t.toBits) (hlf : Finite xl.toBits)
    (hsum : value t.toBits + value xl.toBits = 1 + value x.toBits)
    (hxl : |value xl.toBits| ≤ 1 / 2 ^ 51) (k : ℕ) (hk : k < 8)
    (hb0 : (LgammaApprox.border k : ℝ) ≤ value t.toBits)
    (hb1 : value t.toBits ≤ (LgammaApprox.border (k + 1) : ℝ)) :
    Finite ((t - Float.ofBits (wq (20 + k))) + xl).toBits ∧
      value ((t - Float.ofBits (wq (20 + k))) + xl).toBits =
        1 + value x.toBits - (LgammaApprox.offs k : ℝ) ∧
      |value ((t - Float.ofBits (wq (20 + k))) + xl).toBits| ≤ (pX k : ℝ) ∧
      (LgammaApprox.border k : ℝ) - 1 / 2 ^ 50 ≤ 1 + value x.toBits ∧
      1 + value x.toBits ≤ (LgammaApprox.border (k + 1) : ℝ) + 1 / 2 ^ 50 := by
  obtain ⟨hw, hhalf, hbo, hob, hb2, hb9, hpx1, hpx2⟩ := offs_ok k (by omega)
  have hhalf' := qcast_le hhalf
  have hbo' := qcast_le hbo
  have hob' := qcast_le hob
  have hb2' := qcast_le hb2
  have hpx1' := qcast_le hpx1
  have hpx2' := qcast_le hpx2
  have hb9' := qcast_le hb9
  push_cast at hhalf' hbo' hob' hb2' hpx1' hpx2' hb9'
  obtain ⟨heo1, heo2⟩ := mid_ok k hk
  set v := value x.toBits with hvdef
  have hof := ofBits_finite _ hw
  have hov : value (Float.ofBits (wq (20 + k))).toBits = (LgammaApprox.offs k : ℝ) :=
    ofBits_value _ hw
  have hov' : value (wq (20 + k)) = (LgammaApprox.offs k : ℝ) := (PolyBound.ratOfWord_cast _).symm
  have htpos : 0 < value t.toBits := by linarith
  have hd : |value t.toBits - (LgammaApprox.offs k : ℝ)| ≤
      (LgammaApprox.border (k + 1) : ℝ) - (LgammaApprox.border k : ℝ) := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hdf, hdv⟩ := sub_float t (Float.ofBits (wq (20 + k))) htf hof
    (by rw [hov, abs_of_pos htpos]; linarith)
    (by rw [hov, abs_of_pos (by linarith : (0 : ℝ) < (LgammaApprox.offs k : ℝ))]; linarith)
    (by rw [hov, abs_of_pos (by linarith : (0 : ℝ) < (LgammaApprox.offs k : ℝ))]; linarith)
  rw [hov] at hdv
  have hy0 : (LgammaApprox.border k : ℝ) - 1 / 2 ^ 50 ≤ 1 + v := by
    have := (abs_le.mp hxl).1; linarith
  have hy1 : 1 + v ≤ (LgammaApprox.border (k + 1) : ℝ) + 1 / 2 ^ 50 := by
    have := (abs_le.mp hxl).2; linarith
  -- `|1 + x - offs k| ≤ 2 ^ (e - 1022)`
  have hB : (((2 ^ (1018 + i + 52) / 2 ^ 1074 : ℚ)) : ℝ) = (2 : ℝ) ^ (1018 + i + 52) / 2 ^ 1074 := by
    simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  have hz : |1 + v - (LgammaApprox.offs k : ℝ)| ≤ (2 : ℝ) ^ (1018 + i + 52) / 2 ^ 1074 := by
    have hv0 : v ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hve
      have : (0 : ℝ) < 2 ^ (1018 + i + 51) / 2 ^ 1074 := by positivity
      linarith
    rcases lt_or_gt_of_ne hv0 with hneg | hpos
    · rw [abs_of_neg hneg] at hve hve'
      rw [← hB]
      refine zOK_apply _ _ _ _ (z_ok k hk i hi).2 (1 + v) ?_ ?_
      · simp only [zloN]; push_cast; exact max_le hy0 (by linarith)
      · simp only [zhiN]; push_cast; exact le_min hy1 (by linarith)
    · rw [abs_of_pos hpos] at hve hve'
      rw [← hB]
      refine zOK_apply _ _ _ _ (z_ok k hk i hi).1 (1 + v) ?_ ?_
      · simp only [zloP]; push_cast; exact max_le hy0 (by linarith)
      · simp only [zhiP]; push_cast; exact le_min hy1 (by linarith)
  obtain ⟨hzf, hzv⟩ := sum_exact (t - Float.ofBits (wq (20 + k))) xl hdf hlf x.toBits (wq (20 + k))
    (1018 + i) (Wasm.IEEE64.exponent (wq (20 + k))) he rfl (by omega) (by omega) (by omega)
    (by rw [hdv, hov']; linarith) (by rw [hov']; exact hz)
  rw [hov'] at hzv
  refine ⟨hzf, hzv, ?_, hy0, hy1⟩
  rw [hzv, abs_le]
  constructor <;> linarith

/-! ### The piece at `1 + x` -/

/-- **The piece of `1 + x`**, times `-x` on piece 4, within `2 ^ -60` of `ln Γ (1 + x)`. -/
theorem mid_piece (hF : FmaSpec.FmaNearest) (hPF : LgammaApprox.PieceFact) (x : Float)
    (hx : Finite x.toBits) (hv2 : |value x.toBits| ≤ 1 / 2) (k : ℕ) (hk : k < 8) (jj : UInt64)
    (hjj : jj.toNat = k) (z : Float) (hzf : Finite z.toBits)
    (hzv : value z.toBits = 1 + value x.toBits - (LgammaApprox.offs k : ℝ))
    (hzX : |value z.toBits| ≤ (pX k : ℝ))
    (hy0 : (LgammaApprox.border k : ℝ) - 1 / 2 ^ 50 ≤ 1 + value x.toBits)
    (hy1 : 1 + value x.toBits ≤ (LgammaApprox.border (k + 1) : ℝ) + 1 / 2 ^ 50)
    (P Q : Float × Float) (hP : P = Lgamma.piecePoly Lgamma.mainTable jj z)
    (hQ : Q = if jj == 4 then mulDDD (-x) P.1 P.2 else (P.1, P.2)) :
    Finite Q.1.toBits ∧ Finite Q.2.toBits ∧ |value Q.2.toBits| ≤ 1 / 2 ^ 38 ∧
      |value Q.1.toBits| ≤ 1 ∧
      |GammaBasic.lgamma (1 + value x.toBits) - (value Q.1.toBits + value Q.2.toBits)| ≤
        1 / 2 ^ 60 ∧
      |GammaBasic.lgamma (1 + value x.toBits)| ≤ 59 / 100 := by
  have hk19 : k < 19 := by omega
  have ho := (idx jj k hjj hk19).2.1
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := piece_poly hF k hk19 (191 + 10 * jj) ho z hzf hzX P
    (by rw [hP, piecePoly_eq jj k hjj hk19])
  have hLm := (evalF_approx (tE k) (pX k) z hzf hzX (ok_all k hk19)).2
  have hpb : |LgammaApprox.piecePoly k (value z.toBits)| ≤ (hbQ k 4 : ℝ) := by
    have h := horner_le k hk19 (191 + 10 * jj) ho _ _ hzX hLm 4 le_rfl
    rwa [horner_piece k hk19 (191 + 10 * jj) ho] at h
  have hpf := hPF k hk19 (1 + value x.toBits) hy0 hy1
  have hpaeq : LgammaApprox.pieceApprox k (1 + value x.toBits) =
      (if k = 4 then 1 - (1 + value x.toBits) else if k = 10 then 1 + value x.toBits - 2 else 1) *
        LgammaApprox.piecePoly k (value z.toBits) := by
    rw [hzv]; rfl
  set v := value x.toBits with hvdef
  set pp := LgammaApprox.piecePoly k (value z.toBits) with hppdef
  set lg := GammaBasic.lgamma (1 + v) with hlgdef
  set pA := LgammaApprox.pieceApprox k (1 + v) with hpAdef
  have hpE : (pE k : ℝ) ≤ 10 / 2 ^ 66 := by
    have h1 := qcast_le (low_ok k hk19).2
    push_cast at h1
    have h2 : (pLow k : ℝ) / 2 ^ 66 ≤ 10 / 2 ^ 66 :=
      div_le_div_of_nonneg_right (hp5.trans hp6) (by norm_num)
    linarith
  have hP1b : |value P.1.toBits| ≤ 11 := by
    have h1 := LgammaFastSmall.abs_le_three (value P.1.toBits) (value P.2.toBits) pp
    linarith [(by norm_num : (10 : ℝ) / 2 ^ 66 + 10 + 1 / 2 ^ 40 ≤ 11)]
  have hhb := qcast_le hb_mid.2
  push_cast at hhb
  -- `|Q - pA| ≤ 2 ^ -62` and `|pA| ≤ 0.58`
  have key : Finite Q.1.toBits ∧ Finite Q.2.toBits ∧ |value Q.2.toBits| ≤ 1 / 2 ^ 38 ∧
      |value Q.1.toBits + value Q.2.toBits - pA| ≤ 1 / 2 ^ 62 ∧ |pA| ≤ 58 / 100 := by
    by_cases hk4 : k = 4
    · have hb4 : (jj == 4) = true :=
        beq_iff_eq.mpr (UInt64.toNat_inj.mp (hjj.trans (hk4.trans (by decide))))
      rw [ite_eq_left hb4] at hQ
      subst hk4
      obtain ⟨hnf, hnv⟩ := LgammaFastTiny.neg_float x hx
      obtain ⟨hm1, hm2, hm3, hm4, -⟩ := mulDDD_spec hF (-x) P.1 P.2 hnf hp1 hp2
        (11 * |v|) (1 / 2 ^ 40 * |v|)
        (by rw [hnv, abs_neg]; exact mul_le_mul_of_nonneg_right hP1b (abs_nonneg _))
        (by rw [hnv, abs_neg]; exact mul_le_mul_of_nonneg_right hp4 (abs_nonneg _))
        (by linarith [abs_nonneg v]) (by linarith [abs_nonneg v])
      rw [hnv] at hm3
      rw [hQ]
      have hpa' : pA = -v * pp := by rw [hpaeq, ite_eq_left rfl]; ring
      have hA : |-v * (value P.1.toBits + value P.2.toBits) - -v * pp| ≤ 1 / 2 * (10 / 2 ^ 66) := by
        rw [← mul_sub, abs_mul, abs_neg]
        exact mul_le_mul hv2 (hp3.trans hpE) (abs_nonneg _) (by norm_num)
      refine ⟨hm1, hm2, ?_, ?_, ?_⟩
      · have : 1 / 2 ^ 40 * |v| * (1 + 1 / 2 ^ 51) + 11 * |v| / 2 ^ 52 + 1 / 2 ^ 1071 ≤ 1 / 2 ^ 38 := by
          linarith [abs_nonneg v]
        linarith
      · have h1 := abs_sub_le (value (mulDDD (-x) P.1 P.2).1.toBits +
          value (mulDDD (-x) P.1 P.2).2.toBits) (-v * (value P.1.toBits + value P.2.toBits)) (-v * pp)
        rw [hpa']
        have : (3 * (1 / 2 ^ 40 * |v|) + 11 * |v| / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1072 ≤ 1 / 2 ^ 90 := by
          linarith [abs_nonneg v]
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 90 + 1 / 2 * (10 / 2 ^ 66) ≤ 1 / 2 ^ 62)]
      · rw [hpa', abs_mul, abs_neg]
        have := mul_le_mul hv2 hpb (abs_nonneg _) (by norm_num)
        linarith
    · have hb4 : ¬ (jj == 4) = true := fun h =>
        hk4 (hjj.symm.trans ((congrArg UInt64.toNat (beq_iff_eq.mp h)).trans (by decide)))
      rw [ite_eq_right hb4] at hQ
      rw [hQ]
      have hpa' : pA = pp := by rw [hpaeq]; simp [hk4, show k ≠ 10 by omega]
      have hhk := qcast_le (hb_mid.1 k hk hk4)
      push_cast at hhk
      refine ⟨hp1, hp2, by linarith, ?_, ?_⟩
      · rw [hpa']; linarith [(by norm_num : (10 : ℝ) / 2 ^ 66 ≤ 1 / 2 ^ 62)]
      · rw [hpa']; linarith
  obtain ⟨hq1, hq2, hq2b, herr, hpab⟩ := key
  have hl1 : |lg| ≤ |pA| + 12 / 10 ^ 20 * |lg| := by
    have := abs_sub_abs_le_abs_sub lg pA
    linarith
  have hlg : |lg| ≤ 59 / 100 := by linarith
  refine ⟨hq1, hq2, hq2b, ?_, ?_, hlg⟩
  · have h1 := abs_sub_abs_le_abs_sub (value Q.1.toBits) (-(value Q.2.toBits))
    rw [sub_neg_eq_add, abs_neg] at h1
    have h2 := abs_sub_abs_le_abs_sub (value Q.1.toBits + value Q.2.toBits) pA
    linarith [(by norm_num : (58 : ℝ) / 100 + 1 / 2 ^ 62 + 1 / 2 ^ 38 ≤ 1)]
  · have h1 := abs_sub_le lg pA (value Q.1.toBits + value Q.2.toBits)
    rw [abs_sub_comm pA] at h1
    linarith [(by norm_num : (12 : ℝ) / 10 ^ 20 * (59 / 100) + 1 / 2 ^ 62 ≤ 1 / 2 ^ 60),
      mul_le_mul_of_nonneg_left hlg (by norm_num : (0 : ℝ) ≤ 12 / 10 ^ 20)]

/-! ### The leaf -/

/-- The binade of `x` from its sign-cleared bits. -/
theorem mid_x (x : Float) (hlo : 0x3FA0000000000000 ≤ (F64Order.absBits x.toBits).toNat)
    (hhi : (F64Order.absBits x.toBits).toNat < 0x3FE0000000000000) :
    ∃ i < 4, Wasm.IEEE64.exponent x.toBits = 1018 + i ∧
      (2 : ℝ) ^ (1018 + i + 51) / 2 ^ 1074 ≤ |value x.toBits| ∧
      |value x.toBits| ≤ (2 : ℝ) ^ (1018 + i + 52) / 2 ^ 1074 ∧
      1 / 2 ^ 5 ≤ |value x.toBits| ∧ |value x.toBits| ≤ 1 / 2 - 1 / 2 ^ 54 := by
  have hexp := F64Order.exponent_abs x.toBits
  rw [show (2 : ℕ) ^ 52 = 4503599627370496 by norm_num] at hexp
  have he1 : 1018 ≤ Wasm.IEEE64.exponent x.toBits := by omega
  have he2 : Wasm.IEEE64.exponent x.toBits ≤ 1021 := by omega
  obtain ⟨i, hi, hei⟩ : ∃ i, i < 4 ∧ Wasm.IEEE64.exponent x.toBits = 1018 + i :=
    ⟨Wasm.IEEE64.exponent x.toBits - 1018, by omega, by omega⟩
  rw [hei] at hexp
  obtain ⟨hb1, hb1a⟩ := F64ExponentBounds.boundary_fields (1018 + i) (by omega)
  obtain ⟨hb2, hb2a⟩ := F64ExponentBounds.boundary_fields (1018 + i + 1) (by omega)
  have hw1 := F64PositiveSpacing.boundary_value (1018 + i) (by omega) (by omega)
  have hw2 := F64PositiveSpacing.boundary_value (1018 + i + 1) (by omega) (by omega)
  have hl := F64Order.abs_value_mono (F64ExponentBounds.boundary (1018 + i)) x.toBits (by
    rw [hb1a, UInt64.le_iff_toNat_le, hb1, show (2 : ℕ) ^ 52 = 4503599627370496 by norm_num]
    omega)
  have hu := F64Order.abs_value_mono x.toBits (F64ExponentBounds.boundary (1018 + i + 1)) (by
    rw [hb2a, UInt64.le_iff_toNat_le, hb2, show (2 : ℕ) ^ 52 = 4503599627370496 by norm_num]
    omega)
  rw [F64ExponentBounds.boundary, hw1,
    abs_of_pos (show (0 : ℝ) < 2 ^ (1018 + i + 51) / 2 ^ 1074 by positivity)] at hl
  rw [F64ExponentBounds.boundary, hw2,
    abs_of_pos (show (0 : ℝ) < 2 ^ (1018 + i + 1 + 51) / 2 ^ 1074 by positivity),
    show 1018 + i + 1 + 51 = 1018 + i + 52 by omega] at hu
  have hm := F64Order.abs_value_mono x.toBits (0x3FDFFFFFFFFFFFFF : UInt64) (by
    rw [show F64Order.absBits (0x3FDFFFFFFFFFFFFF : UInt64) = 0x3FDFFFFFFFFFFFFF by decide,
      UInt64.le_iff_toNat_le, show (0x3FDFFFFFFFFFFFFF : UInt64).toNat = 0x3FDFFFFFFFFFFFFF from rfl]
    omega)
  rw [word_value (0x3FDFFFFFFFFFFFFF : UInt64) (1 / 2 - 1 / 2 ^ 54) (by decide +kernel)] at hm
  push_cast at hm
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2 - 1 / 2 ^ 54)] at hm
  have h5 : (1 : ℝ) / 2 ^ 5 ≤ 2 ^ (1018 + i + 51) / 2 ^ 1074 :=
    calc (1 : ℝ) / 2 ^ 5 = 2 ^ 1069 / 2 ^ 1074 := by norm_num
      _ ≤ 2 ^ (1018 + i + 51) / 2 ^ 1074 :=
        div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
  exact ⟨i, hi, hei, hl, hu, h5.trans hl, hm⟩

/-- **The fast path from `2 ^ -5` to `1/2`.** -/
theorem mid_spec (hF : FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hPF : LgammaApprox.PieceFact) (x : Float) (hx : Finite x.toBits)
    (hlo : 0x3FA0000000000000 ≤ (F64Order.absBits x.toBits).toNat)
    (hhi : (F64Order.absBits x.toBits).toNat < 0x3FE0000000000000)
    (lh ll : Float) (h : Lgamma.asLogd Tgamma.logdTable x.abs = (lh, ll)) (sign : Float)
    (jj : UInt64) (hjj : jj = Lgamma.piece Lgamma.mainTable ((fastTwoSum 1.0 x).1.toBits >>> 37))
    (P Q S : Float × Float)
    (hP : P = Lgamma.piecePoly Lgamma.mainTable jj
      (((fastTwoSum 1.0 x).1 - entry Lgamma.mainTable (20 + jj)) + (fastTwoSum 1.0 x).2))
    (hQ : Q = if jj == 4 then mulDDD (-x) P.1 P.2 else (P.1, P.2))
    (hS : S = sumDD (-lh) (-ll) Q.1 Q.2) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (S.1, S.2, Q.1.abs * Float.ofBits 0x3BF87F4D7D0AF16B +
        lh.abs * Float.ofBits 0x3B82E3B40A0E9B4F, sign) := by
  obtain ⟨i, hi, he, hve, hve', hv1, hv2⟩ := mid_x x hlo hhi
  obtain ⟨htf, hlf, hsum, hxl, htpos, k, hk8, hkj, hb0, hb1⟩ := mid_t x hx hv1 hv2
  rw [← hjj] at hkj
  have hent : entry Lgamma.mainTable (20 + jj) = Float.ofBits (wq (20 + k)) :=
    entry_eq _ _ _ (idx jj k hkj (by omega)).1
  obtain ⟨hzf, hzv, hzX, hy0, hy1⟩ :=
    mid_z x hx i hi he hve hve' _ _ htf hlf hsum hxl k hk8 hb0 hb1
  rw [← hent] at hzf hzv hzX
  obtain ⟨hq1, hq2, hq2b, hq1b, hqe, hlg⟩ :=
    mid_piece hF hPF x hx (by linarith) k hk8 jj hkj _ hzf hzv hzX hy0 hy1 P Q hP hQ
  set v := value x.toBits with hvdef
  -- `log |x|`
  obtain ⟨haf, hav⟩ := SinhWords.abs_float x hx
  have hv0 : 0 < |v| := by linarith
  have hpos : 0 < value x.abs.toBits := by rw [hav]; exact hv0
  obtain ⟨hlf', hllf, herr, hllb⟩ := LgammaLogd.asLogd_spec hF hL x.abs haf hpos
  rw [h] at hlf' hllf herr hllb
  dsimp only at hlf' hllf herr hllb
  rw [hav] at herr
  obtain ⟨hnlf, hnlv⟩ := LgammaFastTiny.neg_float lh hlf'
  obtain ⟨hnllf, hnllv⟩ := LgammaFastTiny.neg_float ll hllf
  have hl2a : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2b : Real.log 2 < 0.6932 := by have := Real.log_two_lt_d9; linarith
  have hg1 : Real.log (|v|) ≤ -0.6931 := by
    have h1 := Real.log_le_log hv0 (show |v| ≤ 1 / 2 by linarith)
    rw [one_div, Real.log_inv] at h1
    linarith
  have hg2 : -3.4660 ≤ Real.log (|v|) := by
    have h1 := Real.log_le_log (by positivity) hv1
    rw [one_div, Real.log_inv, Real.log_pow] at h1
    push_cast at h1
    linarith
  have hgabs : |Real.log (|v|)| ≤ 7 / 2 := by rw [abs_le]; constructor <;> linarith
  have hab : |value lh.toBits| ≤ 4 := by
    have h1 := abs_le_three (value lh.toBits) (value ll.toBits) (Real.log (|v|))
    have h2 : |Real.log (|v|)| / 2 ^ 78 ≤ 7 / 2 / 2 ^ 78 :=
      div_le_div_of_nonneg_right hgabs (by positivity)
    linarith
  have hbb : |value ll.toBits| ≤ 1 / 2 ^ 21 := by
    have h2 : |value lh.toBits| / 2 ^ 52 ≤ 4 / 2 ^ 52 :=
      div_le_div_of_nonneg_right hab (by positivity)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 22 + 4 / 2 ^ 52 ≤ 1 / 2 ^ 21)]
  have hlh0 : 69 / 100 ≤ |value lh.toBits| := by
    have h1 := abs_le_three (Real.log (|v|)) (-value ll.toBits) (value lh.toBits)
    rw [show Real.log (|v|) + -value ll.toBits - value lh.toBits =
      -(value lh.toBits + value ll.toBits - Real.log (|v|)) by ring, abs_neg, abs_neg] at h1
    have h2 : |Real.log (|v|)| / 2 ^ 78 ≤ 7 / 2 / 2 ^ 78 :=
      div_le_div_of_nonneg_right hgabs (by positivity)
    have h3 : |Real.log (|v|)| = -Real.log (|v|) := abs_of_neg (by linarith)
    linarith
  -- `-log |x| + ln Γ (1 + x)`
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := TgammaDD.sumDD_spec (-lh) (-ll) Q.1 Q.2 hnlf hnllf hq1 hq2
    (by rw [hnlv, abs_neg]; linarith) (by linarith) (1 / 2 ^ 21 + 1 / 2 ^ 38)
    (by rw [hnllv, abs_neg]; linarith) (by norm_num)
  rw [← hS] at hs1 hs2 hs3 hs4 hs5
  rw [hnlv, hnllv] at hs3
  rw [hnlv] at hs5
  have hs1b : |value S.1.toBits| ≤ 6 := by
    have h1 := abs_add_le (-value lh.toBits) (value Q.1.toBits)
    rw [abs_neg] at h1
    linarith
  -- `ln |Γ x| = ln Γ (1 + x) - ln |x|`
  have hnp := GammaBasic.notPole_of_neg_one_lt (x := v) (by linarith [neg_abs_le v])
    (abs_pos.mp hv0)
  have hadd := GammaBasic.lgamma_add_one hnp
  rw [add_comm v 1, ← Real.log_abs v] at hadd
  have hLeq : Real.log (Real.Gamma v) = GammaBasic.lgamma (1 + v) - Real.log (|v|) := by
    rw [hadd, GammaBasic.lgamma]
    ring
  set L := Real.log (Real.Gamma v) with hLdef
  have hL1 : 1 / 10 ≤ |L| := by
    rw [hLeq]
    have := abs_sub_abs_le_abs_sub (Real.log (|v|)) (GammaBasic.lgamma (1 + v))
    rw [abs_sub_comm] at this
    have h3 : |Real.log (|v|)| = -Real.log (|v|) := abs_of_neg (by linarith)
    linarith
  have hL2 : |L| ≤ 5 := by
    rw [hLeq]
    have := abs_sub (GammaBasic.lgamma (1 + v)) (Real.log (|v|))
    linarith
  have hE : |L - (value S.1.toBits + value S.2.toBits)| ≤ 1 / 2 ^ 59 := by
    rw [hLeq, abs_le]
    have h1 := abs_le.mp hqe
    have h2 := abs_le.mp herr
    have h3 := abs_le.mp hs3
    have h4 : |Real.log (|v|)| / 2 ^ 78 ≤ 7 / 2 / 2 ^ 78 :=
      div_le_div_of_nonneg_right hgabs (by positivity)
    have h5 : |value S.1.toBits| / 2 ^ 52 ≤ 6 / 2 ^ 52 :=
      div_le_div_of_nonneg_right hs1b (by positivity)
    constructor <;> linarith
  -- the error bound
  have hw3 : Wasm.IEEE64.isFinite 0x3BF87F4D7D0AF16B = true := by decide
  have hw4 : Wasm.IEEE64.isFinite 0x3B82E3B40A0E9B4F = true := by decide
  have hc3 : (0 : ℚ) ≤ PolyBound.ratOfWord 0x3BF87F4D7D0AF16B ∧
      PolyBound.ratOfWord 0x3BF87F4D7D0AF16B ≤ 1 / 2 ^ 63 := by decide +kernel
  have hc4 : (49 / 10 ^ 23 : ℚ) ≤ PolyBound.ratOfWord 0x3B82E3B40A0E9B4F ∧
      PolyBound.ratOfWord 0x3B82E3B40A0E9B4F ≤ 1 / 2 ^ 70 := by decide +kernel
  have hc3a := qcast_le hc3.1
  have hc3b := qcast_le hc3.2
  have hc4a := qcast_le hc4.1
  have hc4b := qcast_le hc4.2
  push_cast at hc3a hc3b hc4a hc4b
  obtain ⟨hqaf, hqav⟩ := SinhWords.abs_float Q.1 hq1
  obtain ⟨hlaf, hlav⟩ := SinhWords.abs_float lh hlf'
  have ha := fapprox_self Q.1.abs hqaf
  have hb := fapprox_self (Float.ofBits 0x3BF87F4D7D0AF16B) (ofBits_finite _ hw3)
  have hc := fapprox_self lh.abs hlaf
  have hd := fapprox_self (Float.ofBits 0x3B82E3B40A0E9B4F) (ofBits_finite _ hw4)
  rw [hqav] at ha
  rw [ofBits_value _ hw3] at hb
  rw [hlav] at hc
  rw [ofBits_value _ hw4] at hd
  have hm1 := fapprox_mul ha hb 1 (1 / 2 ^ 63) (by rw [abs_abs]; exact hq1b)
    (by rw [abs_of_nonneg hc3a]; exact hc3b) (1 * (1 / 2 ^ 63)) (by norm_num) (by norm_num)
  have hm2 := fapprox_mul hc hd 4 (1 / 2 ^ 70) (by rw [abs_abs]; exact hab)
    (by rw [abs_of_nonneg (by linarith)]; exact hc4b) (4 * (1 / 2 ^ 70)) (by norm_num) (by norm_num)
  have hp1 : 0 ≤ |value Q.1.toBits| * ((PolyBound.ratOfWord 0x3BF87F4D7D0AF16B : ℚ) : ℝ) :=
    mul_nonneg (abs_nonneg _) hc3a
  have hp1' : |value Q.1.toBits| * ((PolyBound.ratOfWord 0x3BF87F4D7D0AF16B : ℚ) : ℝ) ≤
      1 * (1 / 2 ^ 63) := mul_le_mul hq1b hc3b hc3a (by norm_num)
  have hp2 : 69 / 100 * (49 / 10 ^ 23) ≤
      |value lh.toBits| * ((PolyBound.ratOfWord 0x3B82E3B40A0E9B4F : ℚ) : ℝ) :=
    mul_le_mul hlh0 hc4a (by norm_num) (abs_nonneg _)
  have hp2' : |value lh.toBits| * ((PolyBound.ratOfWord 0x3B82E3B40A0E9B4F : ℚ) : ℝ) ≤
      4 * (1 / 2 ^ 70) := mul_le_mul hab hc4b (by linarith) (by norm_num)
  have hs := fapprox_add hm1 hm2 (1 / 2 ^ 61) (by
      rw [abs_of_nonneg (by linarith)]
      norm_num
      linarith) (by norm_num)
  have hev := abs_le.mp hs.2
  set E := Q.1.abs * Float.ofBits 0x3BF87F4D7D0AF16B + lh.abs * Float.ofBits 0x3B82E3B40A0E9B4F
    with hEdef
  have hE1 : 1 / 2 ^ 73 ≤ value E.toBits := by
    norm_num at hev
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 73 + 1 / 2 ^ 100 ≤ 69 / 100 * (49 / 10 ^ 23))]
  have hE2 : value E.toBits ≤ 1 / 2 ^ 62 := by
    norm_num at hev
    linarith [(by norm_num : (1 : ℝ) * (1 / 2 ^ 63) + 4 * (1 / 2 ^ 70) + 1 / 2 ^ 100 ≤ 1 / 2 ^ 62)]
  unfold FastSpec
  dsimp only
  refine ⟨hs1, hs2, hs.1, le_trans (by norm_num) hE1, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 21 + 1 / 2 ^ 38 ≤ 1)]
  · linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 10)]
  · linarith [(by norm_num : (5 : ℝ) ≤ 2 ^ 1020)]
  · have h4 : (|value S.2.toBits| + value E.toBits) / 2 ^ 52 ≤ (1 / 2 ^ 19 + 1 / 2 ^ 62) / 2 ^ 52 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : (1 / 2 ^ 21 + 1 / 2 ^ 38) * (1 + 1 / 2 ^ 51) + 6 / 2 ^ 51 + 1 / 2 ^ 1073 ≤
          (1 : ℝ) / 2 ^ 19 := by norm_num
      have h5 : |value S.1.toBits| / 2 ^ 51 ≤ 6 / 2 ^ 51 :=
        div_le_div_of_nonneg_right hs1b (by positivity)
      linarith
    have h5 : (1 : ℝ) / 10 / 2 ^ 54 ≤ |L| / 2 ^ 54 := div_le_div_of_nonneg_right hL1 (by positivity)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 59 + 2 * (1 / 2 ^ 62) +
      (1 / 2 ^ 19 + 1 / 2 ^ 62) / 2 ^ 52 ≤ 1 / 10 / 2 ^ 54)]

#print axioms sum_exact
#print axioms mid_t
#print axioms mid_z
#print axioms mid_piece
#print axioms mid_spec

end Verified.Examples.LgammaFastMid
