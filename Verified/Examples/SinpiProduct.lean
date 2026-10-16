import Verified.Examples.SinpiSingle
import Verified.Examples.TanBigWords

/-!
`Sinpi.piProduct` on words: `π x` as `w + t` from the 24-bit head `hi` of `x`, the exact tail
`lo = x - hi`, `π` as `pi_hi + pi_lo` with `pi_hi` of 26 bits, and a final exact two-sum.  For
`x` from `2 ^ -54` to `1/2`, `w + t` lies within `π x / 2 ^ 60` of `π x` and `|t| ≤ |w| / 2 ^ 52`.
-/

namespace Verified.Examples.SinpiProduct

open CodeLib.IEEE64 LeanExe.ProofKit TanWords TanTrunc TanOdd TanBigWords SinpiSingle TrigApprox

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

set_option exponentiation.threshold 1200

def piHi : UInt64 := 0x400921FB58000000
def piLo : UInt64 := 0xBE5DDE973DCB3B3A
def piC : UInt64 := 0x400921FB54442D18

/-- `Sinpi.piProduct` on words. -/
def productW (b : UInt64) : UInt64 × UInt64 :=
  let hi := canon (singleW b)
  let lo := Wasm.IEEE64.sub b hi
  let lo := Wasm.IEEE64.add (Wasm.IEEE64.mul lo (Wasm.IEEE64.add piLo piHi))
    (Wasm.IEEE64.mul hi piLo)
  let hi := Wasm.IEEE64.mul hi piHi
  let w := Wasm.IEEE64.add hi lo
  (w, Wasm.IEEE64.add (Wasm.IEEE64.sub hi w) lo)

theorem product_bits (x : Float) :
    (Sinpi.piProduct x).1.toBits = (productW x.toBits).1 ∧
      (Sinpi.piProduct x).2.toBits = (productW x.toBits).2 := by
  have h1 : (Float.ofBits 0x400921FB58000000).toBits = piHi := by
    rw [F64Bits.toBits_ofBits]; decide
  have h2 : (Float.ofBits 0xBE5DDE973DCB3B3A).toBits = piLo := by
    rw [F64Bits.toBits_ofBits]; decide
  unfold Sinpi.piProduct productW
  simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_add, h1, h2, toSingle_bits]
  refine ⟨?_, ?_⟩ <;> first | trivial | rfl

theorem const_facts : Finite piHi ∧ Finite piLo ∧ Wasm.IEEE64.add piLo piHi = piC ∧ Finite piC ∧
    value piHi = 52707179 / 2 ^ 24 ∧ value piLo = -(8407515482766138 / 2 ^ 78) ∧
    value piC = 7074237752028440 / 2 ^ 51 ∧
    Wasm.IEEE64.scaledMagnitude piHi = 52707179 * 2 ^ 1050 := by
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide, by unfold CodeLib.IEEE64.Finite; decide,
    by decide +kernel, by unfold CodeLib.IEEE64.Finite; decide, ?_, ?_, ?_, by decide +kernel⟩
  · rw [TrigReduce.value_word _ 52707179 24 (by norm_num) (by decide +kernel)]
    norm_num
  · rw [TrigSmall.value_of_scaled]
    have : Wasm.IEEE64.scaledValue piLo = -(8407515482766138 * 2 ^ 996) := by decide +kernel
    rw [this]
    norm_num
  · rw [TrigReduce.value_word _ 7074237752028440 51 (by norm_num) (by decide +kernel)]
    norm_num

/-- `pi_hi + pi_lo` and the rounded `pi_lo + pi_hi` against `π`. -/
theorem pi_parts : |52707179 / 2 ^ 24 - 8407515482766138 / 2 ^ 78 - Real.pi| ≤ 1 / 2 ^ 66 ∧
    |7074237752028440 / 2 ^ 51 - Real.pi| ≤ 1 / 2 ^ 50 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  norm_num at h1 h2
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- The error of `w + t` against `π V` in real numbers. -/
theorem product_real (V h lo p1 p2 lo2 : ℝ) (hV0 : 1 / 2 ^ 54 ≤ V) (hV1 : V ≤ 1 / 2)
    (hh : h = V - lo) (hlo : |lo| ≤ V / 2 ^ 24)
    (hp1 : |p1 - lo * (7074237752028440 / 2 ^ 51)| ≤
      𝐮 * |lo * (7074237752028440 / 2 ^ 51)| + η)
    (hp2 : |p2 - h * -(8407515482766138 / 2 ^ 78)| ≤
      𝐮 * |h * -(8407515482766138 / 2 ^ 78)| + η)
    (hlo2 : |lo2 - (p1 + p2)| ≤ 𝐮 * |p1 + p2|) :
    |h * (52707179 / 2 ^ 24) + lo2 - Real.pi * V| ≤ V / 2 ^ 62 ∧ |lo2| ≤ V / 2 ^ 20 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  obtain ⟨hpi1, hpi2⟩ := pi_parts
  have hV0' : 0 ≤ V := le_trans (by positivity) hV0
  have hlo' := abs_le.mp hlo
  have hhb : |h| ≤ V * (1 + 1 / 2 ^ 24) := by
    rw [hh]
    have := sub_abs V lo
    rw [abs_of_nonneg hV0'] at this
    linarith
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 7074237752028440 / 2 ^ 51)] at hp1
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 8407515482766138 / 2 ^ 78)] at hp2
  have hid : h * (52707179 / 2 ^ 24) + lo2 - Real.pi * V =
      h * (52707179 / 2 ^ 24 - 8407515482766138 / 2 ^ 78 - Real.pi) +
        lo * (7074237752028440 / 2 ^ 51 - Real.pi) +
        (p1 - lo * (7074237752028440 / 2 ^ 51)) + (p2 - h * -(8407515482766138 / 2 ^ 78)) +
        (lo2 - (p1 + p2)) := by
    rw [hh]; ring
  have e1 : |h * (52707179 / 2 ^ 24 - 8407515482766138 / 2 ^ 78 - Real.pi)| ≤
      V * (1 + 1 / 2 ^ 24) * (1 / 2 ^ 66) := by
    rw [abs_mul]; exact mul_le_mul hhb hpi1 (abs_nonneg _) (by positivity)
  have e2 : |lo * (7074237752028440 / 2 ^ 51 - Real.pi)| ≤ V / 2 ^ 24 * (1 / 2 ^ 50) := by
    rw [abs_mul]; exact mul_le_mul hlo hpi2 (abs_nonneg _) (by positivity)
  have hp1b := abs_sub_abs_le_abs_sub p1 (lo * (7074237752028440 / 2 ^ 51))
  have hp2b := abs_sub_abs_le_abs_sub p2 (h * -(8407515482766138 / 2 ^ 78))
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 7074237752028440 / 2 ^ 51)] at hp1b
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 8407515482766138 / 2 ^ 78)]
    at hp2b
  have hsum := abs_add_le p1 p2
  have hl2 := abs_sub_abs_le_abs_sub lo2 (p1 + p2)
  have t1 := abs_add_le (h * (52707179 / 2 ^ 24 - 8407515482766138 / 2 ^ 78 - Real.pi) +
      lo * (7074237752028440 / 2 ^ 51 - Real.pi) + (p1 - lo * (7074237752028440 / 2 ^ 51)) +
      (p2 - h * -(8407515482766138 / 2 ^ 78))) (lo2 - (p1 + p2))
  have t2 := abs_add_le (h * (52707179 / 2 ^ 24 - 8407515482766138 / 2 ^ 78 - Real.pi) +
      lo * (7074237752028440 / 2 ^ 51 - Real.pi) + (p1 - lo * (7074237752028440 / 2 ^ 51)))
      (p2 - h * -(8407515482766138 / 2 ^ 78))
  have t3 := abs_add_le (h * (52707179 / 2 ^ 24 - 8407515482766138 / 2 ^ 78 - Real.pi) +
      lo * (7074237752028440 / 2 ^ 51 - Real.pi)) (p1 - lo * (7074237752028440 / 2 ^ 51))
  have t4 := abs_add_le (h * (52707179 / 2 ^ 24 - 8407515482766138 / 2 ^ 78 - Real.pi))
      (lo * (7074237752028440 / 2 ^ 51 - Real.pi))
  have hηV : (1 : ℝ) / 2 ^ 1075 ≤ V / 2 ^ 1000 := by
    have : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 54 / 2 ^ 1000 := by norm_num
    have : 1 / 2 ^ 54 / 2 ^ 1000 ≤ V / 2 ^ 1000 := div_le_div_of_nonneg_right hV0 (by positivity)
    linarith
  simp only [hu, hη] at hp1 hp2 hlo2
  constructor
  · rw [hid]
    linarith
  · linarith

/-- `add a b` is `sub a (negate b)`. -/
theorem add_eq_sub (a b : UInt64) :
    Wasm.IEEE64.add a b = Wasm.IEEE64.sub a (Wasm.IEEE64.negate b) := by
  rw [show Wasm.IEEE64.sub a (Wasm.IEEE64.negate b) =
    Wasm.IEEE64.add a (Wasm.IEEE64.negate (Wasm.IEEE64.negate b)) from rfl,
    F64RelativeStep.negate_negate]

/-- The two-sum of `a` and a small `b`: `w = a + b` rounded and `t = (a - w) + b` with
`w + t = a + b` exactly. -/
theorem two_sum (a b : UInt64) (ha : Finite a) (hb : Finite b) (hsmall : 4 * |value b| ≤ |value a|)
    (hbig : |value a| < 2 ^ 1020) :
    Finite (Wasm.IEEE64.add a b) ∧
      |value (Wasm.IEEE64.add a b) - (value a + value b)| ≤ |value a + value b| / 2 ^ 53 ∧
      Finite (Wasm.IEEE64.add (Wasm.IEEE64.sub a (Wasm.IEEE64.add a b)) b) ∧
      value (Wasm.IEEE64.add (Wasm.IEEE64.sub a (Wasm.IEEE64.add a b)) b) =
        value a + value b - value (Wasm.IEEE64.add a b) := by
  obtain ⟨hnf, hnv⟩ := F64Magnitude.negate_value b hb
  have h := F64SignedNearestSum.small_two_diff a (Wasm.IEEE64.negate b) ha hnf
    (by rw [hnv, abs_neg]; exact hsmall) hbig
  rw [← add_eq_sub, hnv, sub_neg_eq_add] at h
  obtain ⟨h1, h2, -, -, h5, h6⟩ := h
  rw [← add_eq_sub] at h5 h6
  exact ⟨h1, h2, h5, h6⟩

/-- `Sinpi.piProduct` on a positive word `b` from `2 ^ -54` to `1/2`: `w + t` within
`V / 2 ^ 62` of `π V`, and `|t| ≤ |w| / 2 ^ 52`. -/
theorem product_spec (b : UInt64) (V : ℝ) (hs : b.toNat < 2 ^ 63) (hfb : Finite b)
    (hV : value b = V) (hV0 : 1 / 2 ^ 54 ≤ V) (hV1 : V ≤ 1 / 2) :
    Finite (productW b).1 ∧ Finite (productW b).2 ∧
      |value (productW b).1 + value (productW b).2 - Real.pi * V| ≤ V / 2 ^ 62 ∧
      |value (productW b).2| ≤ |value (productW b).1| / 2 ^ 52 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hη : η = 1 / 2 ^ 1075 := rfl
  obtain ⟨fh, fl, hc, fc, vh, vl, vc, mh⟩ := const_facts
  have hV0' : 0 < V := lt_of_lt_of_le (by positivity) hV0
  have hab : |value b| = V := by rw [hV]; exact abs_of_pos hV0'
  have he1 : 2 ≤ Wasm.IEEE64.exponent b := exp_two b (by
    rw [hab]
    have : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 54 := by norm_num
    linarith)
  have he2 : Wasm.IEEE64.exponent b ≤ 0 + 1023 :=
    exp_upper b 0 (by rw [hab, pow_zero]; linarith)
  obtain ⟨hif, hi63, hid, m, hm, hm24⟩ := single_spec b hs (by omega) (by omega)
  have hcanon : canon (singleW b) = singleW b := by
    unfold canon
    rw [not_nan_of_finite hif]
    rfl
  have hP : productW b = (Wasm.IEEE64.add (Wasm.IEEE64.mul (singleW b) piHi)
      (Wasm.IEEE64.add (Wasm.IEEE64.mul (Wasm.IEEE64.sub b (singleW b)) piC)
        (Wasm.IEEE64.mul (singleW b) piLo)),
      Wasm.IEEE64.add (Wasm.IEEE64.sub (Wasm.IEEE64.mul (singleW b) piHi)
        (Wasm.IEEE64.add (Wasm.IEEE64.mul (singleW b) piHi)
          (Wasm.IEEE64.add (Wasm.IEEE64.mul (Wasm.IEEE64.sub b (singleW b)) piC)
            (Wasm.IEEE64.mul (singleW b) piLo))))
        (Wasm.IEEE64.add (Wasm.IEEE64.mul (Wasm.IEEE64.sub b (singleW b)) piC)
          (Wasm.IEEE64.mul (singleW b) piLo))) := by
    simp only [productW, hcanon, hc]
  rw [hP]
  generalize hhi : singleW b = hi at hif hi63 hid hm ⊢
  have hd' := abs_le.mp hid
  rw [hV] at hd'
  have hV24 : V / 2 ^ 24 ≤ V / 2 := div_le_div_of_nonneg_left hV0'.le (by norm_num) (by norm_num)
  have hpos : 0 < value hi := by linarith
  -- `lo = x - hi` is exact.
  obtain ⟨hlf, hlv⟩ := sterbenz b hi hfb hif (by rw [hV]; positivity)
    (by rw [abs_of_pos hpos, hab]; linarith) (by rw [abs_of_pos hpos, hab]; linarith) (by omega)
  generalize hlo : Wasm.IEEE64.sub b hi = lo at hlf hlv ⊢
  have hlob : |value lo| ≤ V / 2 ^ 24 := by
    rw [hlv, hV, abs_sub_comm]; rw [hV] at hid; exact hid
  -- `hi pi_hi` is exact.
  obtain ⟨hpf, hpv, -, -⟩ := F64ExactProduct.mul_exact_scaled hi piHi hif fh m 52707179
    (Wasm.IEEE64.exponent b - 1 + 29) 1050 hm mh
    (calc m * 52707179 ≤ 2 ^ 24 * 52707179 := Nat.mul_le_mul_right _ hm24
      _ < 2 ^ 53 := by norm_num) (by omega) (by omega)
  rw [vh] at hpv
  generalize hh2 : Wasm.IEEE64.mul hi piHi = hi2 at hpf hpv ⊢
  -- The roundings of `lo c`, `hi pi_lo`, and their sum.
  have h4 : (4 : ℝ) < 2 ^ 1022 := four_lt 1022 (by norm_num)
  have h4' : (4 : ℝ) < 2 ^ 1023 := four_lt 1023 (by norm_num)
  have hhb : value hi ≤ 1 := by linarith
  obtain ⟨hp1f, hp1e⟩ := F64MulBounds.mul_real_mixed lo piC hlf fc (by
    rw [vc, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 7074237752028440 / 2 ^ 51)]
    have : |value lo| * (7074237752028440 / 2 ^ 51) ≤ 1 * 4 :=
      mul_le_mul (by linarith) (by norm_num) (by positivity) (by norm_num)
    linarith)
  obtain ⟨hp2f, hp2e⟩ := F64MulBounds.mul_real_mixed hi piLo hif fl (by
    rw [vl, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 8407515482766138 / 2 ^ 78),
      abs_of_pos hpos]
    have : value hi * (8407515482766138 / 2 ^ 78) ≤ 1 * 1 :=
      mul_le_mul hhb (by norm_num) (by positivity) (by norm_num)
    linarith)
  rw [vc] at hp1e
  rw [vl] at hp2e
  generalize hq1 : Wasm.IEEE64.mul lo piC = p1 at hp1f hp1e ⊢
  generalize hq2 : Wasm.IEEE64.mul hi piLo = p2 at hp2f hp2e ⊢
  have hp1b : |value p1| ≤ 1 := by
    have := abs_sub_abs_le_abs_sub (value p1) (value lo * (7074237752028440 / 2 ^ 51))
    have h1 : |value lo * (7074237752028440 / 2 ^ 51)| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 7074237752028440 / 2 ^ 51)]
      have : |value lo| * (7074237752028440 / 2 ^ 51) ≤ (1 / 2 ^ 25) * 4 :=
        mul_le_mul (by linarith) (by norm_num) (by positivity) (by norm_num)
      linarith
    rw [hu, hη] at hp1e
    have := abs_nonneg (value lo * (7074237752028440 / 2 ^ 51))
    linarith
  have hp2b : |value p2| ≤ 1 := by
    have := abs_sub_abs_le_abs_sub (value p2) (value hi * -(8407515482766138 / 2 ^ 78))
    have h1 : |value hi * -(8407515482766138 / 2 ^ 78)| ≤ 1 / 2 := by
      rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 8407515482766138 / 2 ^ 78),
        abs_of_pos hpos]
      have : value hi * (8407515482766138 / 2 ^ 78) ≤ 1 * (1 / 4) :=
        mul_le_mul hhb (by norm_num) (by positivity) (by norm_num)
      linarith
    rw [hu, hη] at hp2e
    have := abs_nonneg (value hi * -(8407515482766138 / 2 ^ 78))
    linarith
  obtain ⟨hl2f, hl2e⟩ := F64AddBounds.add_real_relative p1 p2 hp1f hp2f (by
    have := abs_add_le (value p1) (value p2)
    linarith)
  generalize hq3 : Wasm.IEEE64.add p1 p2 = lo2 at hl2f hl2e ⊢
  obtain ⟨herr, hl2b⟩ := product_real V (value hi) (value lo) (value p1) (value p2) (value lo2)
    hV0 hV1 (by rw [hlv, hV]; ring) hlob hp1e hp2e hl2e
  rw [← hpv] at herr
  -- The two-sum.
  have hhi2 : 3 * V ≤ |value hi2| := by
    rw [hpv, abs_mul, abs_of_pos hpos, abs_of_pos (by positivity : (0 : ℝ) < 52707179 / 2 ^ 24)]
    have : V * (1 - 1 / 2 ^ 24) ≤ value hi := by linarith
    have : V * (1 - 1 / 2 ^ 24) * (52707179 / 2 ^ 24) ≤ value hi * (52707179 / 2 ^ 24) :=
      mul_le_mul_of_nonneg_right this (by positivity)
    have h3 : (3 : ℝ) ≤ (1 - 1 / 2 ^ 24) * (52707179 / 2 ^ 24) := by norm_num
    have := mul_le_mul_of_nonneg_left h3 hV0'.le
    linarith
  have hhi2u : |value hi2| < 2 ^ 1020 := by
    rw [hpv, abs_mul, abs_of_pos hpos, abs_of_pos (by positivity : (0 : ℝ) < 52707179 / 2 ^ 24)]
    have : value hi * (52707179 / 2 ^ 24) ≤ 1 * 4 :=
      mul_le_mul hhb (by norm_num) (by positivity) (by norm_num)
    have : (4 : ℝ) < 2 ^ 1020 := four_lt 1020 (by norm_num)
    linarith
  have hsm : 4 * |value lo2| ≤ |value hi2| := by
    have : V / 2 ^ 20 * 4 ≤ 3 * V := by linarith
    linarith
  obtain ⟨hwf, hwe, htf, htv⟩ := two_sum hi2 lo2 hpf hl2f hsm hhi2u
  refine ⟨hwf, htf, ?_, ?_⟩
  · rw [htv, show value (Wasm.IEEE64.add hi2 lo2) + (value hi2 + value lo2 -
      value (Wasm.IEEE64.add hi2 lo2)) = value hi2 + value lo2 by ring]
    exact herr
  · rw [htv]
    have h1 := abs_sub_abs_le_abs_sub (value hi2 + value lo2) (value (Wasm.IEEE64.add hi2 lo2))
    rw [abs_sub_comm (value hi2 + value lo2)] at h1
    rw [abs_sub_comm]
    have h2 := abs_nonneg (value (Wasm.IEEE64.add hi2 lo2))
    have h3 : |value (Wasm.IEEE64.add hi2 lo2) - (value hi2 + value lo2)| =
        |value hi2 + value lo2 - value (Wasm.IEEE64.add hi2 lo2)| := abs_sub_comm _ _
    linarith

#print axioms product_spec

end Verified.Examples.SinpiProduct
