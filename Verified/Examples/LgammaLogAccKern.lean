import Verified.Examples.LgammaPolyDD
import Verified.Examples.LgammaApprox
import Verified.Examples.TgammaWords

/-!
The kernel of `Lgamma.asLogdAccurate`: for the reduced argument `X = dxh + dxl`, `|X| ≤ 1/2400`, the
tail `dxh (c₆ + dxh (c₇ + dxh c₈))` in doubles, the double-double polynomial `polyDD` of degree 5
with that tail added to its last coefficient (`LgammaPolyDD.polyDD_damped_core`), and the product
`mulDD` by `X` give `X · logAccPoly X` within `|X|/2^94 + |dxl| 2^-40` (`kern_spec`).  The bound is
relative to `X` when `dxl = 0`, which the reduction gives next to 1.
-/

namespace Verified.Examples.LgammaLogAccKern
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPoly TgammaPolyDDD TgammaMul
  LgammaPolyDD TgammaWords

set_option exponentiation.threshold 4096

/-- The table of `asLogdAccurate`. -/
abbrev H := Lgamma.logAccurateTable

/-- The real value of word `i` of the table. -/
noncomputable def hv (i : ℕ) : ℝ := (PolyBound.ratOfWord H[i]! : ℝ)

theorem kw_fin : ∀ i < 18, Wasm.IEEE64.isFinite H[198 + i]! = true := by decide +kernel

theorem kw_hi : (PolyBound.ratOfWord H[198]! = 1 ∧ PolyBound.ratOfWord H[200]! = -1 / 2 ∧
    PolyBound.ratOfWord H[204]! = -1 / 4) ∧
    (1 / 3 - 1 / 2 ^ 50 ≤ PolyBound.ratOfWord H[202]! ∧ PolyBound.ratOfWord H[202]! ≤ 1 / 3) ∧
    (1 / 5 ≤ PolyBound.ratOfWord H[206]! ∧ PolyBound.ratOfWord H[206]! ≤ 1 / 5 + 1 / 2 ^ 50) ∧
    (-1 / 6 ≤ PolyBound.ratOfWord H[208]! ∧ PolyBound.ratOfWord H[208]! ≤ -1 / 6 + 1 / 2 ^ 40) := by
  decide +kernel

theorem kw_lo : ∀ i < 6, |PolyBound.ratOfWord H[199 + 2 * i]!| ≤ 1 / 2 ^ 55 := by decide +kernel

theorem kw_tail : |PolyBound.ratOfWord H[210]!| ≤ 1 / 7 ∧ |PolyBound.ratOfWord H[212]!| ≤ 1 / 7 ∧
    |PolyBound.ratOfWord H[214]!| ≤ 1 / 8 := by decide +kernel

theorem fin_word (i : ℕ) (hi : i < 18) : Finite (Float.ofBits H[198 + i]!).toBits :=
  ofBits_finite _ (kw_fin i hi)

theorem val_word (i : ℕ) (hi : i < 18) :
    value (Float.ofBits H[198 + i]!).toBits = hv (198 + i) :=
  ofBits_value _ (kw_fin i hi)

/-- The high coefficients lie between 1/7 and 1 in magnitude. -/
theorem kw_hib (k : ℕ) (hk : k < 6) :
    1 / 7 ≤ |hv (198 + 2 * k)| ∧ |hv (198 + 2 * k)| ≤ 1 := by
  obtain ⟨⟨h0, h2, h6⟩, ⟨h4a, h4b⟩, ⟨h8a, h8b⟩, ⟨h10a, h10b⟩⟩ := kw_hi
  interval_cases k <;> simp only [hv, Nat.reduceMul, Nat.reduceAdd]
  · rw [h0]; norm_num
  · rw [h2]; norm_num
  · have a := (Rat.cast_le (K := ℝ)).mpr h4a
    have b := (Rat.cast_le (K := ℝ)).mpr h4b
    push_cast at a b
    rw [abs_of_pos (by linarith)]
    constructor <;> linarith [(by norm_num : (1 : ℝ) / 7 ≤ 1 / 3 - 1 / 2 ^ 50)]
  · rw [h6]; norm_num
  · have a := (Rat.cast_le (K := ℝ)).mpr h8a
    have b := (Rat.cast_le (K := ℝ)).mpr h8b
    push_cast at a b
    rw [abs_of_pos (by linarith)]
    constructor <;> linarith [(by norm_num : (1 : ℝ) / 5 + 1 / 2 ^ 50 ≤ 1)]
  · have a := (Rat.cast_le (K := ℝ)).mpr h10a
    have b := (Rat.cast_le (K := ℝ)).mpr h10b
    push_cast at a b
    rw [abs_of_neg (by linarith [(by norm_num : (-1 : ℝ) / 6 + 1 / 2 ^ 40 < 0)])]
    constructor <;> linarith [(by norm_num : (1 : ℝ) / 7 ≤ 1 / 6 - 1 / 2 ^ 40)]

theorem kw_lob (k : ℕ) (hk : k < 6) : |hv (199 + 2 * k)| ≤ 1 / 2 ^ 55 := by
  have := (Rat.cast_le (K := ℝ)).mpr (kw_lo k hk)
  push_cast at this
  rw [hv]
  exact this

theorem val_at (i : ℕ) (h1 : 198 ≤ i) (h2 : i < 216) :
    value (Float.ofBits H[i]!).toBits = hv i := by
  have := val_word (i - 198) (by omega)
  rwa [show 198 + (i - 198) = i by omega] at this

/-- The exact Horner value of `polyDD` is `logAccPoly`. -/
theorem horner_eq_poly (X : ℝ) :
    horner (cDD H 198) 6 (X * (hv 210 + X * (hv 212 + X * hv 214))) X 5 =
      LgammaApprox.logAccPoly X := by
  simp only [horner, cDD, LgammaApprox.logAccPoly, LgammaApprox.ddCoeffs, LgammaApprox.q,
    PolyBound.eval, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, List.singleton_append,
    UInt64.reduceToNat, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub]
  rw [val_at 198 (by norm_num) (by norm_num), val_at 199 (by norm_num) (by norm_num),
    val_at 200 (by norm_num) (by norm_num), val_at 201 (by norm_num) (by norm_num),
    val_at 202 (by norm_num) (by norm_num), val_at 203 (by norm_num) (by norm_num),
    val_at 204 (by norm_num) (by norm_num), val_at 205 (by norm_num) (by norm_num),
    val_at 206 (by norm_num) (by norm_num), val_at 207 (by norm_num) (by norm_num),
    val_at 208 (by norm_num) (by norm_num), val_at 209 (by norm_num) (by norm_num)]
  simp only [hv]
  push_cast
  ring

theorem hv_tail : |hv 210| ≤ 1 / 7 ∧ |hv 212| ≤ 1 / 7 ∧ |hv 214| ≤ 1 / 8 := by
  obtain ⟨a, b, c⟩ := kw_tail
  refine ⟨?_, ?_, ?_⟩ <;> simp only [hv]
  · have := (Rat.cast_le (K := ℝ)).mpr a; push_cast at this; exact this
  · have := (Rat.cast_le (K := ℝ)).mpr b; push_cast at this; exact this
  · have := (Rat.cast_le (K := ℝ)).mpr c; push_cast at this; exact this

theorem entry_at (i : ℕ) (h1 : 198 ≤ i) (h2 : i < 216) (hi : (UInt64.ofNat i).toNat = i) :
    Tgamma.entry H (UInt64.ofNat i) = Float.ofBits H[i]! := by
  unfold Tgamma.entry; rw [hi]

/-- **The tail** `dxh (c₆ + dxh (c₇ + dxh c₈))` in doubles, within `2^-65` of its exact value. -/
theorem tail_spec (dxh : Float) (hh : Finite dxh.toBits)
    (hXh : |value dxh.toBits| ≤ 1 / 2400 + 1 / 2 ^ 51) :
    Finite (dxh * (Tgamma.entry H 210 + dxh * (Tgamma.entry H 212 + dxh * Tgamma.entry H 214))).toBits ∧
      |value (dxh * (Tgamma.entry H 210 + dxh * (Tgamma.entry H 212 +
          dxh * Tgamma.entry H 214))).toBits -
        value dxh.toBits * (hv 210 + value dxh.toBits * (hv 212 + value dxh.toBits * hv 214))| ≤
        1 / 2 ^ 65 ∧
      |value (dxh * (Tgamma.entry H 210 + dxh * (Tgamma.entry H 212 +
          dxh * Tgamma.entry H 214))).toBits| ≤ 1 / 2 ^ 13 := by
  obtain ⟨h6, h7, h8⟩ := hv_tail
  have e6 : Tgamma.entry H 210 = Float.ofBits H[210]! := rfl
  have e7 : Tgamma.entry H 212 = Float.ofBits H[212]! := rfl
  have e8 : Tgamma.entry H 214 = Float.ofBits H[214]! := rfl
  rw [e6, e7, e8]
  set a := value dxh.toBits with hadef
  set A : ℝ := 1 / 2400 + 1 / 2 ^ 51 with hAdef
  have f6 : FApprox (Float.ofBits H[210]!) (hv 210) 0 := by
    have := fapprox_self _ (fin_word 12 (by norm_num))
    rwa [val_word 12 (by norm_num)] at this
  have f7 : FApprox (Float.ofBits H[212]!) (hv 212) 0 := by
    have := fapprox_self _ (fin_word 14 (by norm_num))
    rwa [val_word 14 (by norm_num)] at this
  have f8 : FApprox (Float.ofBits H[214]!) (hv 214) 0 := by
    have := fapprox_self _ (fin_word 16 (by norm_num))
    rwa [val_word 16 (by norm_num)] at this
  have fa : FApprox dxh a 0 := fapprox_self _ hh
  have hA0 : (0 : ℝ) ≤ A := by norm_num
  -- `u1 = dxh c₈`
  have s1 := fapprox_mul fa f8 A (1 / 8) hXh h8 (A / 8) (by rw [hAdef]; norm_num) (by norm_num)
  have s1' : FApprox (dxh * Float.ofBits H[214]!) (a * hv 214) (1 / 2 ^ 66) :=
    Approx.mono s1 (by rw [hAdef]; norm_num)
  have hu1 : |a * hv 214| ≤ A / 8 := by
    rw [abs_mul]; have := mul_le_mul hXh h8 (abs_nonneg _) hA0; linarith
  -- `u2 = c₇ + u1`
  have s2 := fapprox_add f7 s1' (1 / 7 + A / 8 + 1 / 2 ^ 66)
    (by have := abs_add_le (hv 212) (a * hv 214); linarith) (by norm_num)
  have s2' : FApprox (Float.ofBits H[212]! + dxh * Float.ofBits H[214]!) (hv 212 + a * hv 214)
      (1 / 2 ^ 55) := Approx.mono s2 (by rw [hAdef]; norm_num)
  have hu2 : |hv 212 + a * hv 214| ≤ 1 / 7 + A / 8 := by
    have := abs_add_le (hv 212) (a * hv 214); linarith
  -- `u3 = dxh u2`
  have s3 := fapprox_mul fa s2' A (1 / 7 + A / 8) hXh hu2 (A * (1 / 7 + A / 8 + 1 / 2 ^ 55))
    (by rw [add_zero]) (by rw [hAdef]; norm_num)
  have s3' : FApprox (dxh * (Float.ofBits H[212]! + dxh * Float.ofBits H[214]!))
      (a * (hv 212 + a * hv 214)) (1 / 2 ^ 65) := Approx.mono s3 (by rw [hAdef]; norm_num)
  have hu3 : |a * (hv 212 + a * hv 214)| ≤ A * (1 / 7 + A / 8) := by
    rw [abs_mul]; exact mul_le_mul hXh hu2 (abs_nonneg _) hA0
  -- `u4 = c₆ + u3`
  have s4 := fapprox_add f6 s3' (1 / 7 + A * (1 / 7 + A / 8) + 1 / 2 ^ 65)
    (by have := abs_add_le (hv 210) (a * (hv 212 + a * hv 214)); linarith) (by rw [hAdef]; norm_num)
  have s4' : FApprox (Float.ofBits H[210]! + dxh * (Float.ofBits H[212]! + dxh * Float.ofBits H[214]!))
      (hv 210 + a * (hv 212 + a * hv 214)) (1 / 2 ^ 55) := Approx.mono s4 (by rw [hAdef]; norm_num)
  have hu4 : |hv 210 + a * (hv 212 + a * hv 214)| ≤ 1 / 7 + A * (1 / 7 + A / 8) := by
    have := abs_add_le (hv 210) (a * (hv 212 + a * hv 214)); linarith
  -- `fl = dxh u4`
  have s5 := fapprox_mul fa s4' A (1 / 7 + A * (1 / 7 + A / 8)) hXh hu4
    (A * (1 / 7 + A * (1 / 7 + A / 8) + 1 / 2 ^ 55))
    (by rw [add_zero]) (by rw [hAdef]; norm_num)
  have hu5 : |a * (hv 210 + a * (hv 212 + a * hv 214))| ≤ A * (1 / 7 + A * (1 / 7 + A / 8)) := by
    rw [abs_mul]; exact mul_le_mul hXh hu4 (abs_nonneg _) hA0
  refine ⟨s5.1, s5.2.trans (by rw [hAdef]; norm_num), ?_⟩
  have h1 := abs_sub_abs_le_abs_sub (value (dxh * (Float.ofBits H[210]! + dxh *
    (Float.ofBits H[212]! + dxh * Float.ofBits H[214]!))).toBits)
    (a * (hv 210 + a * (hv 212 + a * hv 214)))
  have h2 := s5.2
  have h3 : A * (1 / 7 + A * (1 / 7 + A / 8)) + (0 * (1 / 7 + A * (1 / 7 + A / 8)) + A * (1 / 2 ^ 55) +
      0 * (1 / 2 ^ 55) + A * (1 / 7 + A * (1 / 7 + A / 8) + 1 / 2 ^ 55) / 2 ^ 53 + 1 / 2 ^ 1075) ≤
      1 / 2 ^ 13 := by rw [hAdef]; norm_num
  linarith


/-- `cDD` of the kernel's table: the coefficient `k` is at most `1 + 2^-55`. -/
theorem cdd_le (k : ℕ) (hk : k < 6) : |cDD H 198 k| ≤ 1 + 1 / 2 ^ 55 := by
  have h1 := (kw_hib k hk).2
  have h2 := kw_lob k hk
  simp only [cDD, UInt64.reduceToNat]
  rw [val_word (2 * k) (by omega), show 198 + 2 * k + 1 = 198 + (2 * k + 1) by omega,
    val_word (2 * k + 1) (by omega), show 198 + (2 * k + 1) = 199 + 2 * k by omega]
  have := abs_add_le (hv (198 + 2 * k)) (hv (199 + 2 * k))
  linarith

/-- The Horner values of the kernel stay below `1.001` for `|X| ≤ 1/2399`. -/
theorem horner_le (X L : ℝ) (hX : |X| ≤ 1 / 2399) (hL : |L| ≤ 1 / 2 ^ 12) (m : ℕ) (hm : m + 1 ≤ 6) :
    |horner (cDD H 198) 6 L X m| ≤ 1001 / 1000 := by
  induction m with
  | zero =>
    simp only [horner]
    have := cdd_le 5 (by norm_num)
    have := abs_add_le (cDD H 198 5) L
    linarith [(by norm_num : (1 : ℝ) + 1 / 2 ^ 55 + 1 / 2 ^ 12 ≤ 1001 / 1000)]
  | succ m ih =>
    simp only [horner]
    have h1 := cdd_le (6 - 2 - m) (by omega)
    have h2 := ih (by omega)
    have h3 : |X * horner (cDD H 198) 6 L X m| ≤ 1 / 2399 * (1001 / 1000) := by
      rw [abs_mul]; exact mul_le_mul hX h2 (abs_nonneg _) (by norm_num)
    have := abs_add_le (cDD H 198 (6 - 2 - m)) (X * horner (cDD H 198) 6 L X m)
    linarith [(by norm_num : (1 : ℝ) + 1 / 2 ^ 55 + 1 / 2399 * (1001 / 1000) ≤ 1001 / 1000)]

/-- The change of the tail `t (c₆ + t (c₇ + t c₈))` from `t = a` to `t = a + b`. -/
theorem tail_change (a b : ℝ) (ha : |a| ≤ 1 / 2400 + 1 / 2 ^ 51) (hb : |b| ≤ 1 / 2 ^ 52) :
    |a * (hv 210 + a * (hv 212 + a * hv 214)) -
        (a + b) * (hv 210 + (a + b) * (hv 212 + (a + b) * hv 214))| ≤ |b| / 6 := by
  obtain ⟨h6, h7, h8⟩ := hv_tail
  have key : a * (hv 210 + a * (hv 212 + a * hv 214)) -
      (a + b) * (hv 210 + (a + b) * (hv 212 + (a + b) * hv 214)) =
      -b * (hv 210 + (2 * a + b) * hv 212 + (3 * a ^ 2 + 3 * a * b + b ^ 2) * hv 214) := by ring
  rw [key, abs_mul, abs_neg, div_eq_mul_one_div]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hs1 : |2 * a + b| ≤ 2 * (1 / 2400 + 1 / 2 ^ 51) + 1 / 2 ^ 52 := by
    have := abs_add_le (2 * a) b
    rw [abs_mul, abs_two] at this
    linarith
  have ha2 : a ^ 2 ≤ (1 / 2400 + 1 / 2 ^ 51) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  have hb2 : b ^ 2 ≤ (1 / 2 ^ 52) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hab : |a * b| ≤ (1 / 2400 + 1 / 2 ^ 51) * (1 / 2 ^ 52) := by
    rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) (by norm_num)
  have hs2 : |3 * a ^ 2 + 3 * a * b + b ^ 2| ≤
      3 * (1 / 2400 + 1 / 2 ^ 51) ^ 2 + 3 * ((1 / 2400 + 1 / 2 ^ 51) * (1 / 2 ^ 52)) +
        (1 / 2 ^ 52) ^ 2 := by
    have h1 := abs_add_le (3 * a ^ 2 + 3 * a * b) (b ^ 2)
    have h2 := abs_add_le (3 * a ^ 2) (3 * a * b)
    have h3 : |3 * a * b| = 3 * |a * b| := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have h4 : |3 * a ^ 2| = 3 * a ^ 2 := abs_of_nonneg (by positivity)
    have h5 : |b ^ 2| = b ^ 2 := abs_of_nonneg (by positivity)
    linarith
  have t2 : |(2 * a + b) * hv 212| ≤ (2 * (1 / 2400 + 1 / 2 ^ 51) + 1 / 2 ^ 52) * (1 / 7) := by
    rw [abs_mul]; exact mul_le_mul hs1 h7 (abs_nonneg _) (by norm_num)
  have t3 : |(3 * a ^ 2 + 3 * a * b + b ^ 2) * hv 214| ≤
      (3 * (1 / 2400 + 1 / 2 ^ 51) ^ 2 + 3 * ((1 / 2400 + 1 / 2 ^ 51) * (1 / 2 ^ 52)) +
        (1 / 2 ^ 52) ^ 2) * (1 / 8) := by
    rw [abs_mul]; exact mul_le_mul hs2 h8 (abs_nonneg _) (by positivity)
  have := abs_add_le (hv 210 + (2 * a + b) * hv 212) ((3 * a ^ 2 + 3 * a * b + b ^ 2) * hv 214)
  have := abs_add_le (hv 210) ((2 * a + b) * hv 212)
  linarith [(by norm_num : (1 : ℝ) / 7 + (2 * (1 / 2400 + 1 / 2 ^ 51) + 1 / 2 ^ 52) * (1 / 7) +
    (3 * (1 / 2400 + 1 / 2 ^ 51) ^ 2 + 3 * ((1 / 2400 + 1 / 2 ^ 51) * (1 / 2 ^ 52)) +
      (1 / 2 ^ 52) ^ 2) * (1 / 8) ≤ 1 / 6)]

set_option maxHeartbeats 4000000 in
/-- **The kernel** `X · logAccPoly X` at `X = dxh + dxl`, for `|dxh| ≤ 1/2400 + 2^-51` and
`|dxl| ≤ Xl ≤ 2^-52`: the error is relative to `X` up to the terms in `Xl`. -/
theorem kern_spec (hF : FmaSpec.FmaNearest) (dxh dxl : Float) (hh : Finite dxh.toBits)
    (hl : Finite dxl.toBits) (Xl : ℝ) (hXh : |value dxh.toBits| ≤ 1 / 2400 + 1 / 2 ^ 51)
    (hXl : |value dxl.toBits| ≤ Xl) (hXl1 : Xl ≤ 1 / 2 ^ 52) :
    let fl := dxh * (Tgamma.entry H 210 + dxh * (Tgamma.entry H 212 + dxh * Tgamma.entry H 214))
    let P := Lgamma.polyDD H 198 6 dxh dxl fl
    let Q := mulDD dxh dxl P.1 P.2
    Finite Q.1.toBits ∧ Finite Q.2.toBits ∧
      |value Q.1.toBits + value Q.2.toBits - (value dxh.toBits + value dxl.toBits) *
          LgammaApprox.logAccPoly (value dxh.toBits + value dxl.toBits)| ≤
        |value dxh.toBits + value dxl.toBits| / 2 ^ 93 + Xl / 2 ^ 40 + 1 / 2 ^ 1060 ∧
      |value Q.2.toBits| ≤ |value dxh.toBits + value dxl.toBits| / 2 ^ 44 + 2 * Xl +
        1 / 2 ^ 1060 ∧
      |value Q.1.toBits| ≤ (|value dxh.toBits + value dxl.toBits| + Xl) * (1 + 1 / 2 ^ 8) +
        1 / 2 ^ 1060 := by
  intro fl P Q
  obtain ⟨hflf, hfle, hflb⟩ := tail_spec dxh hh hXh
  have hXl0 : 0 ≤ Xl := (abs_nonneg _).trans hXl
  have hb52 : |value dxl.toBits| ≤ 1 / 2 ^ 52 := hXl.trans hXl1
  have hXb : |value dxh.toBits + value dxl.toBits| ≤ 1 / 2399 := (abs_add_le (value dxh.toBits) (value dxl.toBits)).trans
    (by linarith [(by norm_num : (1 : ℝ) / 2400 + 1 / 2 ^ 51 + 1 / 2 ^ 52 ≤ 1 / 2399)])
  set L := (value dxh.toBits + value dxl.toBits) * (hv 210 + (value dxh.toBits + value dxl.toBits) * (hv 212 + (value dxh.toBits + value dxl.toBits) * hv 214)) with hLdef
  have hel : |value fl.toBits - L| ≤ 1 / 2 ^ 65 + 1 / (6 * 2 ^ 52) := by
    have h1 := tail_change (value dxh.toBits) (value dxl.toBits) hXh hb52
    have h2 := abs_sub_le (value fl.toBits) (value dxh.toBits * (hv 210 + value dxh.toBits * (hv 212 + value dxh.toBits * hv 214))) L
    have h3 : |value dxl.toBits| / 6 ≤ 1 / 2 ^ 52 / 6 := div_le_div_of_nonneg_right hb52 (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 52 / 6 = 1 / (6 * 2 ^ 52))]
  have hL12 : |L| ≤ 1 / 2 ^ 12 := by
    have := abs_sub_abs_le_abs_sub L (value fl.toBits)
    rw [abs_sub_comm] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 13 + (1 / 2 ^ 65 + 1 / (6 * 2 ^ 52)) ≤ 1 / 2 ^ 12)]
  -- the polynomial
  have hfh : ∀ k < (6 : UInt64).toNat,
      Finite (Float.ofBits H[(198 : UInt64).toNat + 2 * k]!).toBits := by
    intro k hk
    simp only [UInt64.reduceToNat] at hk ⊢
    exact fin_word (2 * k) (by omega)
  have hfl : ∀ k < (6 : UInt64).toNat,
      Finite (Float.ofBits H[(198 : UInt64).toNat + 2 * k + 1]!).toBits := by
    intro k hk
    simp only [UInt64.reduceToNat] at hk ⊢
    rw [show 198 + 2 * k + 1 = 198 + (2 * k + 1) by omega]
    exact fin_word (2 * k + 1) (by omega)
  have hCh : ∀ k < (6 : UInt64).toNat,
      |value (Float.ofBits H[(198 : UInt64).toNat + 2 * k]!).toBits| ≤ 1 := by
    intro k hk
    simp only [UInt64.reduceToNat] at hk ⊢
    rw [val_word (2 * k) (by omega)]
    exact (kw_hib k hk).2
  have hCl : ∀ k < (6 : UInt64).toNat,
      |value (Float.ofBits H[(198 : UInt64).toNat + 2 * k + 1]!).toBits| ≤ 1 / 2 ^ 55 := by
    intro k hk
    simp only [UInt64.reduceToNat] at hk ⊢
    rw [show 198 + 2 * k + 1 = 198 + (2 * k + 1) by omega, val_word (2 * k + 1) (by omega),
      show 198 + (2 * k + 1) = 199 + 2 * k by omega]
    exact kw_lob k hk
  have htop : |value fl.toBits| ≤
      |value (Float.ofBits H[(198 : UInt64).toNat + 2 * ((6 : UInt64).toNat - 1)]!).toBits| := by
    simp only [UInt64.reduceToNat, Nat.reduceSub, Nat.reduceMul]
    rw [show (198 + 10 : ℕ) = 198 + 2 * 5 by norm_num, val_word (2 * 5) (by norm_num)]
    have := (kw_hib 5 (by norm_num)).1
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 13 ≤ 1 / 7)]
  have hM : ∀ m, m + 1 ≤ (6 : UInt64).toNat →
      |horner (cDD H 198) (6 : UInt64).toNat L (value dxh.toBits + value dxl.toBits) m| ≤ 1001 / 1000 := by
    intro m hm
    simp only [UInt64.reduceToNat] at hm ⊢
    exact horner_le (value dxh.toBits + value dxl.toBits) L hXb hL12 m hm
  have hdom : ∀ m, m + 2 ≤ (6 : UInt64).toNat →
      (|horner (cDD H 198) (6 : UInt64).toNat L (value dxh.toBits + value dxl.toBits) m| + 1 / 2) * (1 / 2400 + 1 / 2 ^ 51) *
          (1 + 1 / 2 ^ 53) + 1 / 2 ^ 1075 ≤
        |value (Float.ofBits H[(198 : UInt64).toNat + 2 * ((6 : UInt64).toNat - 2 - m)]!).toBits| := by
    intro m hm
    have h1 := hM m (by omega)
    simp only [UInt64.reduceToNat] at hm h1 ⊢
    rw [val_word (2 * (6 - 2 - m)) (by omega)]
    have h2 := (kw_hib (6 - 2 - m) (by omega)).1
    have h3 : (|horner (cDD H 198) 6 L (value dxh.toBits + value dxl.toBits) m| + 1 / 2) * (1 / 2400 + 1 / 2 ^ 51) *
        (1 + 1 / 2 ^ 53) ≤ (1001 / 1000 + 1 / 2) * (1 / 2400 + 1 / 2 ^ 51) * (1 + 1 / 2 ^ 53) := by
      gcongr
    linarith [(by norm_num : (1001 / 1000 + 1 / 2 : ℝ) * (1 / 2400 + 1 / 2 ^ 51) * (1 + 1 / 2 ^ 53) +
      1 / 2 ^ 1075 ≤ 1 / 7)]
  obtain ⟨hP1, hP2, hPe, hPl⟩ := polyDD_damped_core hF H 198 6 dxh dxl fl (by decide)
    (by decide) hfh hfl (1 / 2400 + 1 / 2 ^ 51) (1 / 2 ^ 52) (1001 / 1000) 1 (1 / 2 ^ 55)
    (1 / 2 ^ 45) L (1 / 2 ^ 65 + 1 / (6 * 2 ^ 52)) (1 / 2 ^ 13) (polyT 1 (1 / 2 ^ 13)) hh hl hXh
    hb52 (by norm_num) hCh hCl hflf hel hflb htop hM (Or.inr le_rfl) (by unfold polyT; positivity)
    (by unfold polyT; norm_num)
    (by simp only [UInt64.reduceToNat]; unfold polyT polyGrowD; norm_num)
    (by simp only [UInt64.reduceToNat]; unfold polyT polyEpsD polyLowD; norm_num)
    (by norm_num) (by norm_num) (by norm_num) (1 / 2)
    (by simp only [UInt64.reduceToNat]; unfold polyT polyEpsD polyLowD; norm_num) (by norm_num) hdom
  simp only [UInt64.reduceToNat, Nat.reduceSub] at hPe hPl
  rw [hLdef, horner_eq_poly (value dxh.toBits + value dxl.toBits)] at hPe
  have hEP : (1 / 2400 + 1 / 2 ^ 51 + 1 / 2 ^ 52) ^ 5 * (1 / 2 ^ 65 + 1 / (6 * 2 ^ 52) +
      (polyT 1 (1 / 2 ^ 13) + 1 / 2 ^ 55) / 2 ^ 53) +
      ((5 : ℕ) : ℝ) * polyEpsD (1 / 2400 + 1 / 2 ^ 51) (1 / 2 ^ 52) (1001 / 1000) 1 (1 / 2 ^ 55)
        (1 / 2 ^ 45) ≤ 1 / 2 ^ 94 := by
    unfold polyT polyEpsD polyLowD; norm_num
  have hPe' := hPe.trans hEP
  -- the bound on the polynomial
  have hpoly : |LgammaApprox.logAccPoly (value dxh.toBits + value dxl.toBits)| ≤ 1001 / 1000 := by
    have := hM 5 (by decide)
    simp only [UInt64.reduceToNat] at this
    rw [hLdef, horner_eq_poly (value dxh.toBits + value dxl.toBits)] at this
    exact this
  have hph : |value P.1.toBits| ≤ 1002 / 1000 := by
    have h1 := abs_sub_abs_le_abs_sub (value P.1.toBits + value P.2.toBits) (LgammaApprox.logAccPoly (value dxh.toBits + value dxl.toBits))
    have h2 := abs_add_le (value P.1.toBits) (value P.2.toBits)
    have h3 := abs_sub_abs_le_abs_sub (value P.1.toBits) (-value P.2.toBits)
    rw [sub_neg_eq_add, abs_neg] at h3
    linarith [(by norm_num : (1001 : ℝ) / 1000 + 1 / 2 ^ 94 + 2 * (1 / 2 ^ 45) ≤ 1002 / 1000)]
  -- the product by `X`
  have hH : |value P.1.toBits| * |value dxh.toBits| ≤ 1002 / 1000 * |value dxh.toBits| := mul_le_mul_of_nonneg_right hph (abs_nonneg _)
  have hP1' : |value P.1.toBits| * |value dxl.toBits| ≤ 1002 / 1000 * Xl := mul_le_mul hph hXl (abs_nonneg _) (by norm_num)
  have hP2' : |value P.2.toBits| * |value dxh.toBits| ≤ 1 / 2 ^ 45 * |value dxh.toBits| := mul_le_mul_of_nonneg_right hPl (abs_nonneg _)
  have hL2' : |value P.2.toBits| * |value dxl.toBits| ≤ 1 / 2 ^ 45 * Xl := mul_le_mul hPl hXl (abs_nonneg _) (by norm_num)
  have ha1 : |value dxh.toBits| ≤ 1 / 2399 := le_trans hXh (by norm_num)
  obtain ⟨hQ1, hQ2, hQe, hQ2b, hQ1b⟩ := mulDD_spec hF dxh dxl P.1 P.2 hh hl hP1 hP2
    (1002 / 1000 * |value dxh.toBits|) (1002 / 1000 * Xl) (1 / 2 ^ 45 * |value dxh.toBits|) (1 / 2 ^ 45 * Xl) hH hP1' hP2' hL2'
    (by linarith [(by norm_num : (1002 / 1000 : ℝ) * (1 / 2399) ≤ 2 ^ 900)])
    (by linarith [(by norm_num : (1002 / 1000 : ℝ) * (1 / 2 ^ 52) + 1 / 2 ^ 45 * (1 / 2399) ≤
      2 ^ 900)])
  have haX : |value dxh.toBits| ≤ |value dxh.toBits + value dxl.toBits| + Xl := by
    have := abs_sub_abs_le_abs_sub (value dxh.toBits) (-value dxl.toBits)
    rw [sub_neg_eq_add, abs_neg] at this
    linarith
  refine ⟨hQ1, hQ2, ?_, ?_, ?_⟩
  · have hsplit : value Q.1.toBits + value Q.2.toBits - (value dxh.toBits + value dxl.toBits) * LgammaApprox.logAccPoly (value dxh.toBits + value dxl.toBits) =
        (value Q.1.toBits + value Q.2.toBits - (value dxh.toBits + value dxl.toBits) * (value P.1.toBits + value P.2.toBits)) +
          (value dxh.toBits + value dxl.toBits) * (value P.1.toBits + value P.2.toBits - LgammaApprox.logAccPoly (value dxh.toBits + value dxl.toBits)) := by ring
    rw [hsplit]
    have h1 := abs_add_le (value Q.1.toBits + value Q.2.toBits - (value dxh.toBits + value dxl.toBits) * (value P.1.toBits + value P.2.toBits))
      ((value dxh.toBits + value dxl.toBits) * (value P.1.toBits + value P.2.toBits - LgammaApprox.logAccPoly (value dxh.toBits + value dxl.toBits)))
    have h2 : |(value dxh.toBits + value dxl.toBits) * (value P.1.toBits + value P.2.toBits - LgammaApprox.logAccPoly (value dxh.toBits + value dxl.toBits))| ≤ |value dxh.toBits + value dxl.toBits| * (1 / 2 ^ 94) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hPe' (abs_nonneg _)
    have hQe' : |value Q.1.toBits + value Q.2.toBits -
        (value dxh.toBits + value dxl.toBits) * (value P.1.toBits + value P.2.toBits)| ≤
        1 / 2 ^ 45 * Xl + (4 * (1002 / 1000 * Xl + 1 / 2 ^ 45 * |value dxh.toBits|) +
          1002 / 1000 * |value dxh.toBits| / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1070 := hQe
    have := abs_nonneg (value dxh.toBits + value dxl.toBits)
    linarith
  · have h1 : 1 / 2 ^ 45 * |value dxh.toBits| ≤ 1 / 2 ^ 45 * (|value dxh.toBits + value dxl.toBits| + Xl) :=
      mul_le_mul_of_nonneg_left haX (by norm_num)
    have h2 : 1002 / 1000 * |value dxh.toBits| / 2 ^ 52 ≤
        1002 / 1000 * (|value dxh.toBits + value dxl.toBits| + Xl) / 2 ^ 52 := by
      gcongr
    have h0 : 0 ≤ |value dxh.toBits + value dxl.toBits| := abs_nonneg _
    linarith
  · have h1 : 1002 / 1000 * |value dxh.toBits| * (1 + 1 / 2 ^ 53) ≤
        1002 / 1000 * (|value dxh.toBits + value dxl.toBits| + Xl) * (1 + 1 / 2 ^ 53) := by
      gcongr
    have hnn : 0 ≤ |value dxh.toBits + value dxl.toBits| + Xl := by positivity
    have h2 := mul_le_mul_of_nonneg_left
      (show (1002 / 1000 : ℝ) * (1 + 1 / 2 ^ 53) ≤ 1 + 1 / 2 ^ 8 by norm_num) hnn
    linarith

#print axioms kern_spec

end Verified.Examples.LgammaLogAccKern
