import Library.Numerics.Decimal.Shared.StrconvGrid
import Library.Numerics.Decimal.Shared.StrconvRound

/-!
The references of `StrconvRound` in terms of the grid of `StrconvGrid`.  The encoding `n` of a
finite nonnegative binary64 word is its `toNat`, and Talos's `scaledMagnitude` of the word is
`mag b64 n`, in units of `2 ^ -1074`; for binary32 the same holds with `b32` and units of
`2 ^ -149`.  So the nearest-even word of a real `y` is the word of the grid's nearest-even encoding
of `y · 2 ^ 1074` (`nearestEven64_iff`), and `ref64` writes ProofKit's
`F64PositiveRounding.roundNearestEven y` as the word of `refPos b64 (y · 2 ^ 1074)`.  For binary32,
`ref32` does the same for `StrconvBinary32.roundNearestEven`, and `nearestEven32_unique` gives the
uniqueness of its nearest-even word.  `round64_dec` and `round32_dec` restate the references of a
decimal in these terms.
-/

namespace Library.Numerics.Decimal.Shared.StrconvWords
open StrconvGrid StrconvGrammar StrconvRound LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem half_b64 : half b64 = 2 ^ 52 := rfl
theorem half_b32 : half b32 = 2 ^ 23 := rfl
theorem limit_b64 : limit b64 = 0x7FF0000000000000 := by unfold limit; rw [half_b64]; rfl
theorem limit_b32 : limit b32 = 0x7F800000 := by unfold limit; rw [half_b32]; rfl

theorem threshold_b64 :
    threshold b64 = F64PositiveRounding.overflowThreshold * 2 ^ 1074 := by
  unfold threshold F64PositiveRounding.overflowThreshold
  simp only [b64]
  norm_num

theorem threshold_b32 :
    threshold b32 = StrconvBinary32.overflowThreshold * 2 ^ 149 := by
  unfold threshold StrconvBinary32.overflowThreshold
  simp only [b32]
  norm_num

/-! ### Binary64 -/

theorem toNat64 (n : ℕ) (hn : n < limit b64) : (UInt64.ofNat n).toNat = n := by
  rw [limit_b64] at hn
  exact UInt64.toNat_ofNat_of_lt' (hn.trans (by decide))

theorem scaledMagnitude64 (n : ℕ) (hn : n < limit b64) :
    Wasm.IEEE64.scaledMagnitude (UInt64.ofNat n) = mag b64 n := by
  have h1 := toNat64 n hn
  rw [limit_b64] at hn
  unfold Wasm.IEEE64.scaledMagnitude Wasm.IEEE64.exponent Wasm.IEEE64.fraction mag
  rw [h1, half_b64]
  have h2 : n / 2 ^ 52 % 2 ^ 11 = n / 2 ^ 52 := Nat.mod_eq_of_lt (by omega)
  rw [h2]
  by_cases h : n < 2 ^ 52
  · have h3 : n / 2 ^ 52 = 0 := Nat.div_eq_of_lt h
    rw [if_pos h, h3, Nat.mod_eq_of_lt h]
    rfl
  · have h3 : (n / 2 ^ 52 == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, Nat.div_eq_zero_iff_lt (by norm_num : 0 < 2 ^ 52)]
      exact h
    rw [if_neg h]
    dsimp only
    simp only [h3, Bool.false_eq_true, ite_false]

theorem value64 (n : ℕ) (hn : n < limit b64) :
    CodeLib.IEEE64.value (UInt64.ofNat n) = (mag b64 n : ℝ) / 2 ^ 1074 := by
  have h1 := toNat64 n hn
  have hs : Wasm.IEEE64.sign (UInt64.ofNat n) = false := by
    rw [limit_b64] at hn
    simp only [Wasm.IEEE64.sign, h1, decide_eq_false_iff_not, not_le]
    omega
  simp [CodeLib.IEEE64.value, Wasm.IEEE64.scaledValue, hs, scaledMagnitude64 n hn]

theorem dist_scale (a y : ℝ) (k : ℕ) :
    |a / 2 ^ k - y| = |a - y * 2 ^ k| / 2 ^ k := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  rw [show a / 2 ^ k - y = (a - y * 2 ^ k) / 2 ^ k by field_simp, abs_div, abs_of_pos hp]

theorem nearest64_iff (y : ℝ) (n : ℕ) (hn : n < limit b64) :
    F64NearestNonnegative.Nearest y (UInt64.ofNat n) ↔ Nearest b64 (y * 2 ^ 1074) n := by
  have hp : (0 : ℝ) < 2 ^ 1074 := by positivity
  have hlim : F64NearestNonnegative.limit = limit b64 := by rw [limit_b64]; rfl
  constructor
  · intro h
    refine ⟨hn, fun m hm => ?_⟩
    have h2 := h.2 (UInt64.ofNat m) (by rw [hlim, toNat64 m hm]; exact hm)
    rw [value64 n hn, value64 m hm, dist_scale, dist_scale] at h2
    exact (div_le_div_iff_of_pos_right hp).mp h2
  · intro h
    refine ⟨by rw [hlim, toNat64 n hn]; exact hn, fun v hv => ?_⟩
    have hv' : v.toNat < limit b64 := by rw [← hlim]; exact hv
    have h2 := h.2 v.toNat hv'
    have hv2 : v = UInt64.ofNat v.toNat := by simp
    rw [hv2, value64 n hn, value64 v.toNat hv', dist_scale, dist_scale]
    exact div_le_div_of_nonneg_right h2 hp.le

theorem nearestEven64_iff (y : ℝ) (n : ℕ) (hn : n < limit b64) :
    F64NearestNonnegative.NearestEven y (UInt64.ofNat n) ↔ NearestEven b64 (y * 2 ^ 1074) n := by
  have hlim : F64NearestNonnegative.limit = limit b64 := by rw [limit_b64]; rfl
  constructor
  · intro h
    refine ⟨(nearest64_iff y n hn).mp h.1, fun m hm => ?_⟩
    have h2 := h.2 (UInt64.ofNat m) ((nearest64_iff y m hm.1).mpr hm)
    rwa [toNat64 n hn, toNat64 m hm.1] at h2
  · intro h
    refine ⟨(nearest64_iff y n hn).mpr h.1, fun v hv => ?_⟩
    have hv' : v.toNat < limit b64 := by rw [← hlim]; exact hv.1
    have hv2 : v = UInt64.ofNat v.toNat := by simp
    rw [hv2] at hv
    have h2 := h.2 v.toNat ((nearest64_iff y v.toNat hv').mp hv)
    rwa [toNat64 n hn]

/-- ProofKit's binary64 reference is the word of the grid's reference. -/
theorem ref64 (y : ℝ) :
    F64PositiveRounding.roundNearestEven y = UInt64.ofNat (refPos b64 (y * 2 ^ 1074)) := by
  have hp : (0 : ℝ) < 2 ^ 1074 := by positivity
  unfold F64PositiveRounding.roundNearestEven refPos
  by_cases ht : F64PositiveRounding.overflowThreshold ≤ y
  · have ht' : threshold b64 ≤ y * 2 ^ 1074 := by
      rw [threshold_b64]; exact mul_le_mul_of_nonneg_right ht hp.le
    rw [if_pos ht, if_pos ht', limit_b64]; rfl
  · have ht' : ¬ threshold b64 ≤ y * 2 ^ 1074 := by
      rw [threshold_b64]; intro h; exact ht (le_of_mul_le_mul_right h hp)
    rw [if_neg ht, if_neg ht']
    have hc := Classical.choose_spec (exists_nearest_even b64 (y * 2 ^ 1074))
    exact F64NearestEven.roundNearestEven_eq y _ ((nearestEven64_iff y _ hc.1.1).mpr hc)

/-! ### Binary32 -/

theorem toNat32 (n : ℕ) (hn : n < limit b32) : (UInt32.ofNat n).toNat = n := by
  rw [limit_b32] at hn
  exact UInt32.toNat_ofNat_of_lt' (hn.trans (by decide))

theorem scaledMagnitude32 (n : ℕ) (hn : n < limit b32) :
    Wasm.IEEE32.scaledMagnitude (UInt32.ofNat n) = mag b32 n := by
  have h1 := toNat32 n hn
  rw [limit_b32] at hn
  unfold Wasm.IEEE32.scaledMagnitude Wasm.IEEE32.exponent Wasm.IEEE32.fraction mag
  rw [h1, half_b32]
  have h2 : n / 2 ^ 23 % 2 ^ 8 = n / 2 ^ 23 := Nat.mod_eq_of_lt (by omega)
  rw [h2]
  by_cases h : n < 2 ^ 23
  · have h3 : n / 2 ^ 23 = 0 := Nat.div_eq_of_lt h
    rw [if_pos h, h3, Nat.mod_eq_of_lt h]
    rfl
  · have h3 : (n / 2 ^ 23 == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, Nat.div_eq_zero_iff_lt (by norm_num : 0 < 2 ^ 23)]
      exact h
    rw [if_neg h]
    dsimp only
    simp only [h3, Bool.false_eq_true, ite_false]

theorem value32 (n : ℕ) (hn : n < limit b32) :
    CodeLib.IEEE32.value (UInt32.ofNat n) = (mag b32 n : ℝ) / 2 ^ 149 := by
  have h1 := toNat32 n hn
  have hs : Wasm.IEEE32.sign (UInt32.ofNat n) = false := by
    rw [limit_b32] at hn
    simp only [Wasm.IEEE32.sign, h1, decide_eq_false_iff_not, not_le]
    omega
  simp [CodeLib.IEEE32.value, Wasm.IEEE32.scaledValue, hs, scaledMagnitude32 n hn]

theorem nearest32_iff (y : ℝ) (n : ℕ) (hn : n < limit b32) :
    StrconvBinary32.Nearest y (UInt32.ofNat n) ↔ Nearest b32 (y * 2 ^ 149) n := by
  have hp : (0 : ℝ) < 2 ^ 149 := by positivity
  have hlim : StrconvBinary32.limit = limit b32 := by rw [limit_b32]; rfl
  constructor
  · intro h
    refine ⟨hn, fun m hm => ?_⟩
    have h2 := h.2 (UInt32.ofNat m) (by rw [hlim, toNat32 m hm]; exact hm)
    rw [value32 n hn, value32 m hm, dist_scale, dist_scale] at h2
    exact (div_le_div_iff_of_pos_right hp).mp h2
  · intro h
    refine ⟨by rw [hlim, toNat32 n hn]; exact hn, fun v hv => ?_⟩
    have hv' : v.toNat < limit b32 := by rw [← hlim]; exact hv
    have h2 := h.2 v.toNat hv'
    have hv2 : v = UInt32.ofNat v.toNat := by simp
    rw [hv2, value32 n hn, value32 v.toNat hv', dist_scale, dist_scale]
    exact div_le_div_of_nonneg_right h2 hp.le

theorem nearestEven32_iff (y : ℝ) (n : ℕ) (hn : n < limit b32) :
    StrconvBinary32.NearestEven y (UInt32.ofNat n) ↔ NearestEven b32 (y * 2 ^ 149) n := by
  have hlim : StrconvBinary32.limit = limit b32 := by rw [limit_b32]; rfl
  constructor
  · intro h
    refine ⟨(nearest32_iff y n hn).mp h.1, fun m hm => ?_⟩
    have h2 := h.2 (UInt32.ofNat m) ((nearest32_iff y m hm.1).mpr hm)
    rwa [toNat32 n hn, toNat32 m hm.1] at h2
  · intro h
    refine ⟨(nearest32_iff y n hn).mpr h.1, fun v hv => ?_⟩
    have hv' : v.toNat < limit b32 := by rw [← hlim]; exact hv.1
    have hv2 : v = UInt32.ofNat v.toNat := by simp
    rw [hv2] at hv
    have h2 := h.2 v.toNat ((nearest32_iff y v.toNat hv').mp hv)
    rwa [toNat32 n hn]

/-- The nearest-even binary32 word is unique. -/
theorem nearestEven32_unique (y : ℝ) (a b : UInt32) (ha : StrconvBinary32.NearestEven y a)
    (hb : StrconvBinary32.NearestEven y b) : a = b := by
  have hlim : StrconvBinary32.limit = limit b32 := by rw [limit_b32]; rfl
  have ha' : a.toNat < limit b32 := by rw [← hlim]; exact ha.1.1
  have hb' : b.toNat < limit b32 := by rw [← hlim]; exact hb.1.1
  have e1 : a = UInt32.ofNat a.toNat := by simp
  have e2 : b = UInt32.ofNat b.toNat := by simp
  rw [e1] at ha; rw [e2] at hb
  have := nearest_even_unique b32 _ _ _ ((nearestEven32_iff y _ ha').mp ha)
    ((nearestEven32_iff y _ hb').mp hb)
  exact UInt32.toNat_inj.mp this

/-- The binary32 reference is the word of the grid's reference. -/
theorem ref32 (y : ℝ) :
    StrconvBinary32.roundNearestEven y = UInt32.ofNat (refPos b32 (y * 2 ^ 149)) := by
  have hp : (0 : ℝ) < 2 ^ 149 := by positivity
  unfold StrconvBinary32.roundNearestEven refPos
  by_cases ht : StrconvBinary32.overflowThreshold ≤ y
  · have ht' : threshold b32 ≤ y * 2 ^ 149 := by
      rw [threshold_b32]; exact mul_le_mul_of_nonneg_right ht hp.le
    rw [if_pos ht, if_pos ht', limit_b32]; rfl
  · have ht' : ¬ threshold b32 ≤ y * 2 ^ 149 := by
      rw [threshold_b32]; intro h; exact ht (le_of_mul_le_mul_right h hp)
    rw [if_neg ht, if_neg ht']
    have hc := Classical.choose_spec (exists_nearest_even b32 (y * 2 ^ 149))
    exact nearestEven32_unique y _ _ (StrconvBinary32.nearestEven_spec y)
      ((nearestEven32_iff y _ hc.1.1).mpr hc)

/-! ### Decimals -/

theorem round64_dec (neg : Bool) (d : ℕ) (e : ℤ) :
    round64 (.dec neg d e) =
      withSign64 neg (UInt64.ofNat (refPos b64 (d * (10 : ℝ) ^ e * 2 ^ 1074))) := by
  rw [round64, ref64]

theorem round32_dec (neg : Bool) (d : ℕ) (e : ℤ) :
    round32 (.dec neg d e) =
      withSign32 neg (UInt32.ofNat (refPos b32 (d * (10 : ℝ) ^ e * 2 ^ 149))) := by
  rw [round32, ref32]

#print axioms value64
#print axioms ref64
#print axioms value32
#print axioms nearestEven32_unique
#print axioms ref32
#print axioms round64_dec
#print axioms round32_dec

end Library.Numerics.Decimal.Shared.StrconvWords
