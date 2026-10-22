import Library.Numerics.Float64.Tgamma.TgammaAccFin
import Library.Numerics.Float64.Tgamma.TgammaAccSel
import Library.Numerics.Float64.Tgamma.TgammaAccRanges
import Library.Numerics.Float64.Tgamma.TgammaAccGamma
import Library.Numerics.Float64.Tgamma.TgammaAccComb
import Library.Numerics.Float64.Tgamma.TgammaAccCrr
import Library.Numerics.Float64.Tgamma.TgammaRefl9
import Library.Numerics.Float64.Tgamma.TgammaFloor

/-!
The branch of `Tgamma.accurate` from `1/4` as `accRangeVal`, with its pairs as projections and its
loops as `TgammaAccUp.upStep` and `TgammaAccDown.downStep` (`accurate_range_eq`), and the facts
about its integer values: the difference `jm = j - ⌊x⌋` and the loop counts are exact, and `x` lies
on the grids that the loops need.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAccPre
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaAccUp TgammaAccDown
  TgammaAccFin TgammaAccCrr

set_option exponentiation.threshold 4096

/-- The body of the loop of `Tgamma.accurate` for `x < j`, as the code writes it. -/
def upBody :
    UInt64 → Float × Float × Float × Float × UInt64 → Float × Float × Float × Float × UInt64 :=
  fun _ s =>
    let (xph, xpl, wh, wl, eoff) := s
    let (xph, l) := if xph.abs > 1.0 then fastTwoSum xph 1.0 else fastTwoSum 1.0 xph
    let (xph, xpl) := fastTwoSum xph (xpl + l)
    let (wh, wl) := mulDD3 xph xpl wh wl
    if wh.abs > Float.ofBits 0x6050000000000000 then
      (xph, xpl, wh * Float.ofBits 0x20B0000000000000, wl * Float.ofBits 0x20B0000000000000,
        eoff - 500)
    else (xph, xpl, wh, wl, eoff)

/-- The body of the loop of `Tgamma.accurate` for `x ≥ j + 1`, as the code writes it. -/
def downBody : UInt64 → Float × Float × Float × Float → Float × Float × Float × Float :=
  fun _ s =>
    let (xph, xpl, wh, wl) := s
    let (xph, l) := fastTwoSum xph (-1.0)
    let (xph, xpl) := fastTwoSum xph (xpl + l)
    let (wh, wl) := mulDD3 xph xpl wh wl
    (xph, xpl, wh, wl)

theorem upBody_eq : upBody = fun _ s => upStep s := by
  funext i s
  obtain ⟨a, b, c, d, e⟩ := s
  rfl

theorem downBody_eq : downBody = fun _ s => downStep s := by
  funext i s
  obtain ⟨a, b, c, d⟩ := s
  rfl

/-- The product `(wh, wl)` of `Tgamma.accurate` and its scale word. -/
def stW (x jm : Float) (eoff : UInt64) : Float × Float × UInt64 :=
  if jm > 0.0 then
    let (_, _, wh, wl, eoff) := LeanExe.loop (jm - 1.0).toUInt64
      (x, (0.0 : Float), x, (0.0 : Float), eoff) upBody
    (wh, wl, eoff)
  else if jm < 0.0 then
    let (_, _, wh, wl) := LeanExe.loop (-1.0 - jm).toUInt64
      (x - 1.0, (0.0 : Float), x - 1.0, (0.0 : Float)) downBody
    (wh, wl, eoff)
  else ((1.0 : Float), (0.0 : Float), eoff)

/-- The quotient or product of the polynomial `fh + fl` and the product `wh + wl`. -/
def stF (fh fl jm wh wl : Float) : Float × Float :=
  if jm > 0.0 then
    let rh := 1.0 / wh
    mulDD3 fh fl rh ((Library.Numerics.Arithmetic.Fma.Fma.fma rh (-wh) 1.0 - wl * rh) * rh)
  else if jm < 0.0 then mulDD3 fh fl wh wl
  else (fh, fl)

/-- The adjustment of the low part, the rounding test, and the final rounding. -/
def stEnd (dbTab : Array UInt64) (x jm : Float) (eoff : UInt64) (f : Float × Float) : Float :=
  let (fh, fl) := f
  let fl := adjLow fh fl jm
  let eps := Float.ofBits 0x398E000000000000 * fh
  let ub := fh + (fl + eps)
  let lb := fh + (fl - eps)
  if ub != lb then database dbTab x (Float.ofBits (finRes fh fl eoff))
  else Float.ofBits (finRes fh fl eoff)

/-- The branch of `Tgamma.accurate` from `1/4` in three stages. -/
def accRangeVal (dbTab : Array UInt64) (x : Float) : Float :=
  let ix := floorF x
  let d := 2.0 * (x - (ix + 0.5))
  let (oh, imax, ol, jmax, j, eoff) := accurateRange ix
  let jm := j - ix
  let (fh, fl) := poly3 accurateTable d oh imax ol jmax
  let (wh, wl, eoff) := stW x jm eoff
  stEnd dbTab x jm eoff (stF fh fl jm wh wl)

theorem accurate_range_eq (dbTab : Array UInt64) (x : Float) (h : ¬ x.abs < 0.25) :
    accurate accurateTable dbTab x = accRangeVal dbTab x := by
  unfold accurate
  rw [ite_eq_right h]
  rfl

theorem gt_zero_iff (f : Float) (hf : Finite f.toBits) : f > 0.0 ↔ 0 < value f.toBits := by
  rw [GT.gt, F64UpperWord.float_lt_iff _ _ TgammaMainRed.zero_finite hf,
    TgammaMainRed.zero_value]

theorem lt_zero_iff (f : Float) (hf : Finite f.toBits) : f < 0.0 ↔ value f.toBits < 0 := by
  rw [F64UpperWord.float_lt_iff _ _ hf TgammaMainRed.zero_finite, TgammaMainRed.zero_value]

/-- The difference of two doubles with integer values is exact. -/
theorem int_sub (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (A B : ℤ)
    (hA : value a.toBits = A) (hB : value b.toBits = B) (hAB : |A - B| ≤ 2 ^ 53) :
    Finite (a - b).toBits ∧ value (a - b).toBits = A - B := by
  obtain ⟨h1, h2⟩ := TgammaAcc1.grid_sub a b ha hb (A - B) 0
    (by rw [hA, hB]; push_cast; ring) hAB (by norm_num)
  exact ⟨h1, by rw [h2, hA, hB]⟩

/-- The count `jm - 1` of the loop for `x < j`. -/
theorem count_up (jm : Float) (hjm : Finite jm.toBits) (M : ℕ) (hv : value jm.toBits = M + 1)
    (hM : M ≤ 300) : (jm - 1.0).toUInt64 = UInt64.ofNat M := by
  have hM' : ((M : ℤ) + 1 - 1) = M := by ring
  obtain ⟨hf, hval⟩ := int_sub jm 1.0 hjm TgammaRecip.one_finite ((M : ℤ) + 1) 1
    (by rw [hv]; push_cast; ring) (by rw [TgammaRecip.one_value]; norm_num)
    (by rw [hM', abs_of_nonneg (by positivity)]
        calc (M : ℤ) ≤ 300 := by exact_mod_cast hM
          _ ≤ 2 ^ 53 := by norm_num)
  exact TgammaMainRed.toUInt64_nat _ M hf (by rw [hval]; push_cast; ring) (by omega)

/-- The count `-1 - jm` of the loop for `x ≥ j + 1`. -/
theorem count_down (jm : Float) (hjm : Finite jm.toBits) (M : ℕ)
    (hv : value jm.toBits = -((M : ℝ) + 1)) (hM : M ≤ 300) :
    (-1.0 - jm).toUInt64 = UInt64.ofNat M := by
  have hM' : ((-1 : ℤ) - (-((M : ℤ) + 1))) = M := by ring
  obtain ⟨hf, hval⟩ := int_sub (-1.0) jm neg_one_finite hjm (-1) (-((M : ℤ) + 1))
    (by rw [neg_one_value]; norm_num) (by rw [hv]; push_cast; ring)
    (by rw [hM', abs_of_nonneg (by positivity)]
        calc (M : ℤ) ≤ 300 := by exact_mod_cast hM
          _ ≤ 2 ^ 53 := by norm_num)
  exact TgammaMainRed.toUInt64_nat _ M hf (by rw [hval]; push_cast; ring) (by omega)

/-- A double from `1/4` on lies on the grid `2 ^ -54`. -/
theorem grid54 (x : Float) (hx : Finite x.toBits) (hq : 1 / 4 ≤ |value x.toBits|) :
    ∃ z : ℤ, value x.toBits = z / 2 ^ 54 := by
  obtain ⟨K, hK⟩ := TgammaMainRed.grid x.toBits hx 1019 (by norm_num)
    (by rw [show (2 : ℝ) ^ (53 + 1019) / 2 ^ 1074 = 1 / 4 by norm_num]; exact hq)
  refine ⟨K, ?_⟩
  have h : value x.toBits = K * 2 ^ (1019 + 1) / 2 ^ 1074 := by
    rw [← hK]; field_simp
  rw [h, show (2 : ℝ) ^ 1074 = 2 ^ (1019 + 1) * 2 ^ 54 by norm_num, ← div_div,
    mul_div_cancel_right₀ _ (by positivity)]

/-- A number on the grid `2 ^ -54` other than an integer lies `2 ^ -54` from every integer. -/
theorem dist_int (v : ℝ) (z : ℤ) (hz : v = z / 2 ^ 54) (hnint : ∀ n : ℤ, v ≠ n) (n : ℤ) :
    1 / 2 ^ 54 ≤ |v + n| := by
  have he : v + n = ((z + n * 2 ^ 54 : ℤ) : ℝ) / 2 ^ 54 := by
    rw [hz]; push_cast; field_simp; ring
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 54)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hne : z + n * 2 ^ 54 ≠ 0 := by
    intro h0
    apply hnint (-n)
    have hz' : (z : ℝ) = ((-n : ℤ) : ℝ) * 2 ^ 54 := by
      exact_mod_cast (by linarith : z = (-n) * 2 ^ 54)
    rw [hz, hz']
    field_simp
  have h1 := Int.one_le_abs hne
  rw [← Int.cast_abs]
  exact_mod_cast h1

/-- A double in `[1, 2 ^ 52)` is `k / 2 ^ g` with `|k| ≤ 2 ^ 53`. -/
theorem grid53 (w : UInt64) (h1 : 1 ≤ value w) (h2 : value w < 2 ^ 52) :
    ∃ (k : ℤ) (g : ℕ), g ≤ 52 ∧ value w = k / 2 ^ g ∧ |k| ≤ 2 ^ 53 := by
  obtain ⟨N, hN⟩ : ∃ N, N = ⌊value w⌋₊ := ⟨_, rfl⟩
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.one_le_floor_iff _ |>.mpr h1
  obtain ⟨a, ha⟩ : ∃ a, a = Nat.log 2 N := ⟨_, rfl⟩
  have ha1 : 2 ^ a ≤ N := by rw [ha]; exact Nat.pow_log_le_self 2 (by omega)
  have ha2 : N < 2 ^ (a + 1) := by rw [ha]; exact Nat.lt_pow_succ_log_self (by norm_num) N
  have hA1 : (2 : ℝ) ^ a ≤ value w := by
    have : ((2 ^ a : ℕ) : ℝ) ≤ N := by exact_mod_cast ha1
    push_cast at this
    exact this.trans (by rw [hN]; exact Nat.floor_le (by linarith))
  have hA2 : value w < 2 ^ (a + 1) := by
    have h3 : value w < N + 1 := by rw [hN]; exact Nat.lt_floor_add_one _
    have h4 : ((N + 1 : ℕ) : ℝ) ≤ ((2 ^ (a + 1) : ℕ) : ℝ) := by exact_mod_cast ha2
    push_cast at h4
    linarith
  have ha52 : a ≤ 52 := by
    by_contra hc
    have : (2 : ℝ) ^ 53 ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [(by norm_num : (2 : ℝ) ^ 52 ≤ 2 ^ 53)]
  obtain ⟨k, hk⟩ := TgammaRefl4.grid w a ha52 (by rw [abs_of_pos (by linarith)]; exact hA1)
  refine ⟨k, 52 - a, by omega, hk, ?_⟩
  have hkv : (k : ℝ) = value w * 2 ^ (52 - a) := by rw [hk]; field_simp
  have hp : (2 : ℝ) ^ (a + 1) * 2 ^ (52 - a) = 2 ^ 53 := by
    rw [← pow_add]; congr 1; omega
  have hkr : |(k : ℝ)| ≤ 2 ^ 53 := by
    rw [hkv, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < value w),
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (52 - a)), ← hp]
    exact mul_le_mul_of_nonneg_right hA2.le (by positivity)
  rw [← Int.cast_abs] at hkr
  exact_mod_cast hkr

#print axioms upBody_eq
#print axioms downBody_eq
#print axioms accurate_range_eq
#print axioms count_up
#print axioms count_down
#print axioms grid54
#print axioms dist_int
#print axioms grid53

end Library.Numerics.Float64.Tgamma.TgammaAccPre
