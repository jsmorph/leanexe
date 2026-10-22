import Library.Numerics.Float64.Bessel.BesselSmallY0

/-!
The main path of `Bessel.y1` below 2, `x (U(z)/V(z)) + tpi (ĵ L̂ - 1/x)` with `z = x x`, for
doubles `ĵ` and `L̂` within given errors of `J₁(x)` and `ln x`.  Each lemma `piece_k` follows it
through `F64Approx` on one range of `x` from 1 to 2, with the Horner bounds that the kernel checks
on that range (`facts_k`), `|J₁| ≤ Jm`, and `|ln x| ≤ Lm`; `small_piece` covers `2^-54 ≤ x ≤ 1`
with the error as `α u/x + β u ℓ + γ u` for `ℓ = |ln x|`, from `|J₁(x)| ≤ 0.51 x` and
`x ℓ ≤ 0.3679`.  `code_eq` reads the coefficients from `Bessel.j1Table`.  This file is generated
by `tools/bessel/gensmall.py`.
-/

namespace Library.Numerics.Float64.Bessel.BesselSmallY1
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyCalculus F64Approx F64HalfUlp F64Horner
  BesselPQEval BesselPQRange BesselCS BesselSmallEval BesselSmallApprox BesselJ0Large BesselSmallJ0
  BesselCombine BesselSmallY0 Real
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

def u1w : List UInt64 := [0xBFC91866143CBC8A, 0x3FA9D3C776292CD1, 0xBF5F55E54844F50F, 0x3EF8AB038FA6B88E, 0xBE78AC00569105B8]
def v1w : List UInt64 := [0x3F94650D3F4DA9F0, 0x3F2A8C896C257764, 0x3EB6C05A894E8CA6, 0x3E3ABF1D5BA69A86, 0x3DB25039DACA772A]

theorem words : (∀ w ∈ u1w, Finite w) ∧ (∀ w ∈ v1w, Finite w) := by
  unfold CodeLib.IEEE64.Finite
  decide

theorem lists : u1w.map ratOfWord = U1 ∧ 1 :: v1w.map ratOfWord = V1 := ⟨rfl, rfl⟩

/-- The table entries 92 to 101 of `j1Table` as the Horner forms of `U` and `V`. -/
theorem code_eq (z : Float) :
    Bessel.entry Bessel.j1Table 92 + z * (Bessel.entry Bessel.j1Table 93 +
        z * (Bessel.entry Bessel.j1Table 94 + z * (Bessel.entry Bessel.j1Table 95 +
        z * Bessel.entry Bessel.j1Table 96))) = hornerF (u1w.map Float.ofBits) z ∧
      1.0 + z * (Bessel.entry Bessel.j1Table 97 + z * (Bessel.entry Bessel.j1Table 98 +
        z * (Bessel.entry Bessel.j1Table 99 + z * (Bessel.entry Bessel.j1Table 100 +
        z * Bessel.entry Bessel.j1Table 101)))) = hornerF (1.0 :: v1w.map Float.ofBits) z :=
  ⟨rfl, rfl⟩

theorem uv_at (zf : Float) (hzf : Finite zf.toBits) (z δ : ℝ) (lo hi : ℚ)
    (hR : hornerOK U1 lo hi = true) (hS : hornerOK V1 lo hi = true)
    (h1 : (lo : ℝ) ≤ value zf.toBits) (h2 : value zf.toBits ≤ hi) (h3 : (lo : ℝ) ≤ z)
    (h4 : z ≤ hi) (hδ : |value zf.toBits - z| ≤ δ) :
    FApprox (hornerF (u1w.map Float.ofBits) zf) (eval U1 z)
        (hornerErr U1 lo hi + magBound (derivP U1) lo hi * δ) ∧
      FApprox (hornerF (1.0 :: v1w.map Float.ofBits) zf) (eval V1 z)
        (hornerErr V1 lo hi + magBound (derivP V1) lo hi * δ) := by
  obtain ⟨wr, ws⟩ := words
  obtain ⟨b1, b2⟩ := words_rel u1w wr
  obtain ⟨c1, c2⟩ := words_rel_one v1w ws
  exact ⟨horner_at _ _ U1 b1 b2 (by decide) lo hi hR zf hzf z δ h1 h2 h3 h4 hδ,
    horner_at _ _ V1 c1 c2 (by decide) lo hi hS zf hzf z δ h1 h2 h3 h4 hδ⟩

theorem facts_0 : hornerOK U1 (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) = true ∧ hornerOK V1 (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) = true ∧
    hornerErr U1 (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) ≤ (138277 / 4503599627370496000000 : ℚ) ∧ magBound (derivP U1) (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) ≤ (46689 / 1000000 : ℚ) ∧
    magBound U1 (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) ≤ (147503 / 1000000 : ℚ) ∧ hornerErr V1 (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) ≤ (1077263 / 9007199254740992000000 : ℚ) ∧
    magBound (derivP V1) (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) ≤ (20437 / 1000000 : ℚ) ∧ (1020113 / 1000000 : ℚ) ≤ lowBound V1 (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) := by
  decide +kernel

theorem facts_1 : hornerOK U1 (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) = true ∧ hornerOK V1 (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) = true ∧
    hornerErr U1 (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) ≤ (147397 / 4503599627370496000000 : ℚ) ∧ magBound (derivP U1) (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) ≤ (9143 / 200000 : ℚ) ∧
    magBound U1 (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) ≤ (135231 / 1000000 : ℚ) ∧ hornerErr V1 (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) ≤ (1095869 / 9007199254740992000000 : ℚ) ∧
    magBound (derivP V1) (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) ≤ (257 / 12500 : ℚ) ∧ (41021 / 40000 : ℚ) ≤ lowBound V1 (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) := by
  decide +kernel

theorem facts_2 : hornerOK U1 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) = true ∧ hornerOK V1 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) = true ∧
    hornerErr U1 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) ≤ (88789 / 2251799813685248000000 : ℚ) ∧ magBound (derivP U1) (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) ≤ (22319 / 500000 : ℚ) ∧
    magBound U1 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) ≤ (121819 / 1000000 : ℚ) ∧ hornerErr V1 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) ≤ (45587 / 360287970189639680000 : ℚ) ∧
    magBound (derivP V1) (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) ≤ (417 / 20000 : ℚ) ∧ (1031569 / 1000000 : ℚ) ≤ lowBound V1 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) := by
  decide +kernel

theorem facts_3 : hornerOK U1 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) = true ∧ hornerOK V1 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) = true ∧
    hornerErr U1 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) ≤ (411549 / 9007199254740992000000 : ℚ) ∧ magBound (derivP U1) (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) ≤ (42191 / 1000000 : ℚ) ∧
    magBound U1 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) ≤ (11497 / 125000 : ℚ) ∧ hornerErr V1 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) ≤ (596381 / 4503599627370496000000 : ℚ) ∧
    magBound (derivP V1) (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) ≤ (21197 / 1000000 : ℚ) ∧ (1045783 / 1000000 : ℚ) ≤ lowBound V1 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) := by
  decide +kernel

theorem facts_4 : hornerOK U1 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) = true ∧ hornerOK V1 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) = true ∧
    hornerErr U1 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) ≤ (105357 / 2251799813685248000000 : ℚ) ∧ magBound (derivP U1) (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) ≤ (39381 / 1000000 : ℚ) ∧
    magBound U1 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) ≤ (58843 / 1000000 : ℚ) ∧ hornerErr V1 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) ≤ (611499 / 4503599627370496000000 : ℚ) ∧
    magBound (derivP V1) (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) ≤ (21393 / 1000000 : ℚ) ∧ (16608 / 15625 : ℚ) ≤ lowBound V1 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) := by
  decide +kernel

theorem facts_5 : hornerOK U1 (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) = true ∧ hornerOK V1 (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) = true ∧
    hornerErr U1 (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) ≤ (212909 / 4503599627370496000000 : ℚ) ∧ magBound (derivP U1) (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) ≤ (37853 / 1000000 : ℚ) ∧
    magBound U1 (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) ≤ (20673 / 500000 : ℚ) ∧ hornerErr V1 (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) ≤ (619541 / 4503599627370496000000 : ℚ) ∧
    magBound (derivP V1) (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) ≤ (21497 / 1000000 : ℚ) ∧ (16759 / 15625 : ℚ) ≤ lowBound V1 (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) := by
  decide +kernel

theorem facts_6 : hornerOK U1 (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) = true ∧ hornerOK V1 (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) = true ∧
    hornerErr U1 (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) ≤ (442557 / 9007199254740992000000 : ℚ) ∧ magBound (derivP U1) (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) ≤ (1853 / 50000 : ℚ) ∧
    magBound U1 (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) ≤ (32421 / 1000000 : ℚ) ∧ hornerErr V1 (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) ≤ (313957 / 2251799813685248000000 : ℚ) ∧
    magBound (derivP V1) (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) ≤ (5401 / 250000 : ℚ) ∧ (538843 / 500000 : ℚ) ≤ lowBound V1 (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) := by
  decide +kernel

theorem facts_small : hornerOK U1 (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) = true ∧ hornerOK V1 (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) = true ∧
    hornerErr U1 (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) ≤ (150409 / 4503599627370496000000 : ℚ) ∧ magBound (derivP U1) (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) ≤ (12611 / 250000 : ℚ) ∧
    magBound U1 (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) ≤ (98029 / 500000 : ℚ) ∧ hornerErr V1 (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) ≤ (1060773 / 9007199254740992000000 : ℚ) ∧
    magBound (derivP V1) (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) ≤ (10163 / 500000 : ℚ) ∧ (999897 / 1000000 : ℚ) ≤ lowBound V1 (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) := by
  decide +kernel

/-- The main path of `y1` for `1 ≤ x ≤ 9/8`. -/
theorem piece_0 (x J L : Float) (hf : Finite x.toBits) (v : ℝ) (hv : value x.toBits = v)
    (ha : (1 : ℝ) ≤ v) (hb : v ≤ (9 / 8 : ℝ)) (hJ : FApprox J (J1 v) ((87 / 50 : ℝ) * 𝐮)) (hJm : |J1 v| ≤ (619 / 1250 : ℝ))
    (hL : FApprox L (Real.log v) ((3 / 20 : ℝ) * 𝐮 + 1 / 2 ^ 59)) (hLm : |Real.log v| ≤ (1 / 8 : ℝ))
    (hp0 : 0 ≤ J1 v * Real.log v) :
    FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
        hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) + Bessel.tpi * (J * L - 1.0 / x))
      (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v))
      ((167 / 40 : ℝ) * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts_0
  have hx0 : FApprox x (value x.toBits) 0 := fapprox_exact x hf
  subst hv
  set v := value x.toBits
  have hx : FApprox x v 0 := hx0
  have hz := sq_near x hf (9 / 8 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (1 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (9 / 8 : ℝ) ^ 2 := by nlinarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := uv_at (x * x) hz.1 z _ (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP U1) (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP V1) (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (u1w.map Float.ofBits) (x * x)) (eval U1 z) ((42 / 125 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval V1 z) ((138 / 125 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval U1 z| ≤ (147503 / 1000000 : ℝ) := (magBound_sound U1 (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (1020113 / 1000000 : ℝ) ≤ |eval V1 z| := by
    have := (lowBound_sound V1 (1125899906842623 / 1125899906842624 : ℚ) (91197892454252625 / 72057594037927936 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hq := fapprox_div hH hS' (147503 / 1000000 : ℝ) (1020113 / 1000000 : ℝ) hHm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval U1 z / eval V1 z) ((631 / 1000 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |eval U1 z / eval V1 z| ≤ (28919 / 200000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hHm (by norm_num) hSm).trans (by norm_num)
  have hvb : |v| ≤ (9 / 8 : ℝ) := by rw [abs_of_nonneg (by linarith)]; exact hb
  have hxq := fapprox_mul hx hq' (9 / 8 : ℝ) (28919 / 200000 : ℝ) hvb hqm _ le_rfl (by rw [hu]; norm_num)
  have hxq' : FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x))) (v * (eval U1 z / eval V1 z)) ((873 / 1000 : ℝ) * 𝐮) :=
    fmono hxq (by rw [hu]; norm_num)
  have hxqm : |v * (eval U1 z / eval V1 z)| ≤ (16267 / 100000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hvb hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hp := fapprox_mul hJ hL (619 / 1250 : ℝ) (1 / 8 : ℝ) hJm hLm _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox (J * L) (J1 v * Real.log v) ((181 / 500 : ℝ) * 𝐮) := fmono hp (by rw [hu]; norm_num)
  have hpm : |J1 v * Real.log v| ≤ (619 / 10000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hJm hLm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hinv := fapprox_div fapprox_one hx 1 (1 : ℝ) (by norm_num)
    (by rw [abs_of_pos (by linarith)]; exact ha) (by norm_num) _ le_rfl (by norm_num)
  have hinv' : FApprox (1.0 / x) (1 / v) ((1001 / 1000 : ℝ) * 𝐮) := fmono hinv (by rw [hu]; norm_num)
  have hiv1 : 1 / v ≤ (1 : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num) ha
    norm_num at this ⊢; linarith
  have hiv2 : (8 / 9 : ℝ) ≤ 1 / v := by
    have := one_div_le_one_div_of_le (by linarith) hb
    norm_num at this ⊢; linarith
  have hdm : |J1 v * Real.log v - 1 / v| ≤ (1 : ℝ) := by
    have h1 := (abs_le.mp hpm).2
    have h2 : (619 / 10000 : ℝ) - (8 / 9 : ℝ) ≤ (1 : ℝ) := by norm_num
    rw [abs_le]; constructor <;> linarith
  have hd := fapprox_sub hp' hinv' ((1 : ℝ) + ((181 / 500 : ℝ) * 𝐮 + (1001 / 1000 : ℝ) * 𝐮)) (by linarith)
    (by rw [hu]; norm_num)
  have hd' : FApprox (J * L - 1.0 / x) (J1 v * Real.log v - 1 / v) ((591 / 250 : ℝ) * 𝐮) :=
    fmono hd (by rw [hu]; norm_num)
  have ht := fapprox_mul tpi_near hd' (6367 / 10000) (1 : ℝ) tpi_le hdm _ le_rfl
    (by rw [hu]; norm_num)
  have ht' : FApprox (Bessel.tpi * (J * L - 1.0 / x)) (2 / π * (J1 v * Real.log v - 1 / v))
      ((1251 / 500 : ℝ) * 𝐮) := fmono ht (by rw [hu]; norm_num)
  have htm : |2 / π * (J1 v * Real.log v - 1 / v)| ≤ (6367 / 10000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul tpi_le hdm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hres := fapprox_add hxq' ht' (799371 / 1000000 : ℝ) (by
    have h1 := abs_add_le (v * (eval U1 z / eval V1 z)) (2 / π * (J1 v * Real.log v - 1 / v))
    have h2 : (873 / 1000 : ℝ) * 𝐮 + (1251 / 500 : ℝ) * 𝐮 ≤ (799371 / 1000000 : ℝ) - ((16267 / 100000 : ℝ) + (6367 / 10000 : ℝ)) := by rw [hu]; norm_num
    linarith) (by norm_num)
  exact fmono hres (by rw [hu]; norm_num)

/-- The main path of `y1` for `9/8 ≤ x ≤ 5/4`. -/
theorem piece_1 (x J L : Float) (hf : Finite x.toBits) (v : ℝ) (hv : value x.toBits = v)
    (ha : (9 / 8 : ℝ) ≤ v) (hb : v ≤ (5 / 4 : ℝ)) (hJ : FApprox J (J1 v) ((87 / 50 : ℝ) * 𝐮)) (hJm : |J1 v| ≤ (5313 / 10000 : ℝ))
    (hL : FApprox L (Real.log v) ((3 / 10 : ℝ) * 𝐮 + 1 / 2 ^ 59)) (hLm : |Real.log v| ≤ (1 / 4 : ℝ))
    (hp0 : 0 ≤ J1 v * Real.log v) :
    FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
        hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) + Bessel.tpi * (J * L - 1.0 / x))
      (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v))
      ((4177 / 1000 : ℝ) * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts_1
  have hx0 : FApprox x (value x.toBits) 0 := fapprox_exact x hf
  subst hv
  set v := value x.toBits
  have hx : FApprox x v 0 := hx0
  have hz := sq_near x hf (5 / 4 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (9 / 8 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (5 / 4 : ℝ) ^ 2 := by nlinarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := uv_at (x * x) hz.1 z _ (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP U1) (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP V1) (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (u1w.map Float.ofBits) (x * x)) (eval U1 z) ((367 / 1000 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval V1 z) ((141 / 125 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval U1 z| ≤ (135231 / 1000000 : ℝ) := (magBound_sound U1 (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (41021 / 40000 : ℝ) ≤ |eval V1 z| := by
    have := (lowBound_sound V1 (91197892454252463 / 72057594037927936 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hq := fapprox_div hH hS' (135231 / 1000000 : ℝ) (41021 / 40000 : ℝ) hHm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval U1 z / eval V1 z) ((127 / 200 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |eval U1 z / eval V1 z| ≤ (65933 / 500000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hHm (by norm_num) hSm).trans (by norm_num)
  have hvb : |v| ≤ (5 / 4 : ℝ) := by rw [abs_of_nonneg (by linarith)]; exact hb
  have hxq := fapprox_mul hx hq' (5 / 4 : ℝ) (65933 / 500000 : ℝ) hvb hqm _ le_rfl (by rw [hu]; norm_num)
  have hxq' : FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x))) (v * (eval U1 z / eval V1 z)) ((959 / 1000 : ℝ) * 𝐮) :=
    fmono hxq (by rw [hu]; norm_num)
  have hxqm : |v * (eval U1 z / eval V1 z)| ≤ (164833 / 1000000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hvb hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hp := fapprox_mul hJ hL (5313 / 10000 : ℝ) (1 / 4 : ℝ) hJm hLm _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox (J * L) (J1 v * Real.log v) ((92 / 125 : ℝ) * 𝐮) := fmono hp (by rw [hu]; norm_num)
  have hpm : |J1 v * Real.log v| ≤ (5313 / 40000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hJm hLm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hinv := fapprox_div fapprox_one hx 1 (9 / 8 : ℝ) (by norm_num)
    (by rw [abs_of_pos (by linarith)]; exact ha) (by norm_num) _ le_rfl (by norm_num)
  have hinv' : FApprox (1.0 / x) (1 / v) ((889 / 1000 : ℝ) * 𝐮) := fmono hinv (by rw [hu]; norm_num)
  have hiv1 : 1 / v ≤ (8 / 9 : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num) ha
    norm_num at this ⊢; linarith
  have hiv2 : (4 / 5 : ℝ) ≤ 1 / v := by
    have := one_div_le_one_div_of_le (by linarith) hb
    norm_num at this ⊢; linarith
  have hdm : |J1 v * Real.log v - 1 / v| ≤ (8 / 9 : ℝ) := by
    have h1 := (abs_le.mp hpm).2
    have h2 : (5313 / 40000 : ℝ) - (4 / 5 : ℝ) ≤ (8 / 9 : ℝ) := by norm_num
    rw [abs_le]; constructor <;> linarith
  have hd := fapprox_sub hp' hinv' ((8 / 9 : ℝ) + ((92 / 125 : ℝ) * 𝐮 + (889 / 1000 : ℝ) * 𝐮)) (by linarith)
    (by rw [hu]; norm_num)
  have hd' : FApprox (J * L - 1.0 / x) (J1 v * Real.log v - 1 / v) ((1257 / 500 : ℝ) * 𝐮) :=
    fmono hd (by rw [hu]; norm_num)
  have ht := fapprox_mul tpi_near hd' (6367 / 10000) (8 / 9 : ℝ) tpi_le hdm _ le_rfl
    (by rw [hu]; norm_num)
  have ht' : FApprox (Bessel.tpi * (J * L - 1.0 / x)) (2 / π * (J1 v * Real.log v - 1 / v))
      ((2487 / 1000 : ℝ) * 𝐮) := fmono ht (by rw [hu]; norm_num)
  have htm : |2 / π * (J1 v * Real.log v - 1 / v)| ≤ (141489 / 250000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul tpi_le hdm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hres := fapprox_add hxq' ht' (73079 / 100000 : ℝ) (by
    have h1 := abs_add_le (v * (eval U1 z / eval V1 z)) (2 / π * (J1 v * Real.log v - 1 / v))
    have h2 : (959 / 1000 : ℝ) * 𝐮 + (2487 / 1000 : ℝ) * 𝐮 ≤ (73079 / 100000 : ℝ) - ((164833 / 1000000 : ℝ) + (141489 / 250000 : ℝ)) := by rw [hu]; norm_num
    linarith) (by norm_num)
  exact fmono hres (by rw [hu]; norm_num)

/-- The main path of `y1` for `5/4 ≤ x ≤ 3/2`. -/
theorem piece_2 (x J L : Float) (hf : Finite x.toBits) (v : ℝ) (hv : value x.toBits = v)
    (ha : (5 / 4 : ℝ) ≤ v) (hb : v ≤ (3 / 2 : ℝ)) (hJ : FApprox J (J1 v) ((113 / 50 : ℝ) * 𝐮)) (hJm : |J1 v| ≤ (6129 / 10000 : ℝ))
    (hL : FApprox L (Real.log v) ((1662 / 3125 : ℝ) * 𝐮 + 1 / 2 ^ 59)) (hLm : |Real.log v| ≤ (277 / 625 : ℝ))
    (hp0 : 0 ≤ J1 v * Real.log v) :
    FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
        hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) + Bessel.tpi * (J * L - 1.0 / x))
      (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v))
      ((594 / 125 : ℝ) * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts_2
  have hx0 : FApprox x (value x.toBits) 0 := fapprox_exact x hf
  subst hv
  set v := value x.toBits
  have hx : FApprox x v 0 := hx0
  have hz := sq_near x hf (3 / 2 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (5 / 4 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (3 / 2 : ℝ) ^ 2 := by nlinarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := uv_at (x * x) hz.1 z _ (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP U1) (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP V1) (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (u1w.map Float.ofBits) (x * x)) (eval U1 z) ((57 / 125 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval V1 z) ((1187 / 1000 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval U1 z| ≤ (121819 / 1000000 : ℝ) := (magBound_sound U1 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (1031569 / 1000000 : ℝ) ≤ |eval V1 z| := by
    have := (lowBound_sound V1 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hq := fapprox_div hH hS' (121819 / 1000000 : ℝ) (1031569 / 1000000 : ℝ) hHm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval U1 z / eval V1 z) ((697 / 1000 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |eval U1 z / eval V1 z| ≤ (118091 / 1000000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hHm (by norm_num) hSm).trans (by norm_num)
  have hvb : |v| ≤ (3 / 2 : ℝ) := by rw [abs_of_nonneg (by linarith)]; exact hb
  have hxq := fapprox_mul hx hq' (3 / 2 : ℝ) (118091 / 1000000 : ℝ) hvb hqm _ le_rfl (by rw [hu]; norm_num)
  have hxq' : FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x))) (v * (eval U1 z / eval V1 z)) ((1223 / 1000 : ℝ) * 𝐮) :=
    fmono hxq (by rw [hu]; norm_num)
  have hxqm : |v * (eval U1 z / eval V1 z)| ≤ (177137 / 1000000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hvb hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hp := fapprox_mul hJ hL (6129 / 10000 : ℝ) (277 / 625 : ℝ) hJm hLm _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox (J * L) (J1 v * Real.log v) ((1609 / 1000 : ℝ) * 𝐮) := fmono hp (by rw [hu]; norm_num)
  have hpm : |J1 v * Real.log v| ≤ (135819 / 500000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hJm hLm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hinv := fapprox_div fapprox_one hx 1 (5 / 4 : ℝ) (by norm_num)
    (by rw [abs_of_pos (by linarith)]; exact ha) (by norm_num) _ le_rfl (by norm_num)
  have hinv' : FApprox (1.0 / x) (1 / v) ((801 / 1000 : ℝ) * 𝐮) := fmono hinv (by rw [hu]; norm_num)
  have hiv1 : 1 / v ≤ (4 / 5 : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num) ha
    norm_num at this ⊢; linarith
  have hiv2 : (2 / 3 : ℝ) ≤ 1 / v := by
    have := one_div_le_one_div_of_le (by linarith) hb
    norm_num at this ⊢; linarith
  have hdm : |J1 v * Real.log v - 1 / v| ≤ (4 / 5 : ℝ) := by
    have h1 := (abs_le.mp hpm).2
    have h2 : (135819 / 500000 : ℝ) - (2 / 3 : ℝ) ≤ (4 / 5 : ℝ) := by norm_num
    rw [abs_le]; constructor <;> linarith
  have hd := fapprox_sub hp' hinv' ((4 / 5 : ℝ) + ((1609 / 1000 : ℝ) * 𝐮 + (801 / 1000 : ℝ) * 𝐮)) (by linarith)
    (by rw [hu]; norm_num)
  have hd' : FApprox (J * L - 1.0 / x) (J1 v * Real.log v - 1 / v) ((3211 / 1000 : ℝ) * 𝐮) :=
    fmono hd (by rw [hu]; norm_num)
  have ht := fapprox_mul tpi_near hd' (6367 / 10000) (4 / 5 : ℝ) tpi_le hdm _ le_rfl
    (by rw [hu]; norm_num)
  have ht' : FApprox (Bessel.tpi * (J * L - 1.0 / x)) (2 / π * (J1 v * Real.log v - 1 / v))
      ((1421 / 500 : ℝ) * 𝐮) := fmono ht (by rw [hu]; norm_num)
  have htm : |2 / π * (J1 v * Real.log v - 1 / v)| ≤ (6367 / 12500 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul tpi_le hdm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hres := fapprox_add hxq' ht' (343249 / 500000 : ℝ) (by
    have h1 := abs_add_le (v * (eval U1 z / eval V1 z)) (2 / π * (J1 v * Real.log v - 1 / v))
    have h2 : (1223 / 1000 : ℝ) * 𝐮 + (1421 / 500 : ℝ) * 𝐮 ≤ (343249 / 500000 : ℝ) - ((177137 / 1000000 : ℝ) + (6367 / 12500 : ℝ)) := by rw [hu]; norm_num
    linarith) (by norm_num)
  exact fmono hres (by rw [hu]; norm_num)

/-- The main path of `y1` for `3/2 ≤ x ≤ 7/4`. -/
theorem piece_3 (x J L : Float) (hf : Finite x.toBits) (v : ℝ) (hv : value x.toBits = v)
    (ha : (3 / 2 : ℝ) ≤ v) (hb : v ≤ (7 / 4 : ℝ)) (hJ : FApprox J (J1 v) ((149 / 50 : ℝ) * 𝐮)) (hJm : |J1 v| ≤ (6511 / 10000 : ℝ))
    (hL : FApprox L (Real.log v) ((8523 / 12500 : ℝ) * 𝐮 + 1 / 2 ^ 59)) (hLm : |Real.log v| ≤ (2841 / 5000 : ℝ))
    (hp0 : 0 ≤ J1 v * Real.log v) :
    FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
        hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) + Bessel.tpi * (J * L - 1.0 / x))
      (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v))
      ((5097 / 1000 : ℝ) * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts_3
  have hx0 : FApprox x (value x.toBits) 0 := fapprox_exact x hf
  subst hv
  set v := value x.toBits
  have hx : FApprox x v 0 := hx0
  have hz := sq_near x hf (7 / 4 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (3 / 2 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (7 / 4 : ℝ) ^ 2 := by nlinarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := uv_at (x * x) hz.1 z _ (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP U1) (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP V1) (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (u1w.map Float.ofBits) (x * x)) (eval U1 z) ((541 / 1000 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval V1 z) ((629 / 500 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval U1 z| ≤ (11497 / 125000 : ℝ) := (magBound_sound U1 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (1045783 / 1000000 : ℝ) ≤ |eval V1 z| := by
    have := (lowBound_sound V1 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hq := fapprox_div hH hS' (11497 / 125000 : ℝ) (1045783 / 1000000 : ℝ) hHm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval U1 z / eval V1 z) ((89 / 125 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |eval U1 z / eval V1 z| ≤ (1759 / 20000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hHm (by norm_num) hSm).trans (by norm_num)
  have hvb : |v| ≤ (7 / 4 : ℝ) := by rw [abs_of_nonneg (by linarith)]; exact hb
  have hxq := fapprox_mul hx hq' (7 / 4 : ℝ) (1759 / 20000 : ℝ) hvb hqm _ le_rfl (by rw [hu]; norm_num)
  have hxq' : FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x))) (v * (eval U1 z / eval V1 z)) ((7 / 5 : ℝ) * 𝐮) :=
    fmono hxq (by rw [hu]; norm_num)
  have hxqm : |v * (eval U1 z / eval V1 z)| ≤ (153913 / 1000000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hvb hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hp := fapprox_mul hJ hL (6511 / 10000 : ℝ) (2841 / 5000 : ℝ) hJm hLm _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox (J * L) (J1 v * Real.log v) ((1259 / 500 : ℝ) * 𝐮) := fmono hp (by rw [hu]; norm_num)
  have hpm : |J1 v * Real.log v| ≤ (92489 / 250000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hJm hLm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hinv := fapprox_div fapprox_one hx 1 (3 / 2 : ℝ) (by norm_num)
    (by rw [abs_of_pos (by linarith)]; exact ha) (by norm_num) _ le_rfl (by norm_num)
  have hinv' : FApprox (1.0 / x) (1 / v) ((667 / 1000 : ℝ) * 𝐮) := fmono hinv (by rw [hu]; norm_num)
  have hiv1 : 1 / v ≤ (2 / 3 : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num) ha
    norm_num at this ⊢; linarith
  have hiv2 : (4 / 7 : ℝ) ≤ 1 / v := by
    have := one_div_le_one_div_of_le (by linarith) hb
    norm_num at this ⊢; linarith
  have hdm : |J1 v * Real.log v - 1 / v| ≤ (2 / 3 : ℝ) := by
    have h1 := (abs_le.mp hpm).2
    have h2 : (92489 / 250000 : ℝ) - (4 / 7 : ℝ) ≤ (2 / 3 : ℝ) := by norm_num
    rw [abs_le]; constructor <;> linarith
  have hd := fapprox_sub hp' hinv' ((2 / 3 : ℝ) + ((1259 / 500 : ℝ) * 𝐮 + (667 / 1000 : ℝ) * 𝐮)) (by linarith)
    (by rw [hu]; norm_num)
  have hd' : FApprox (J * L - 1.0 / x) (J1 v * Real.log v - 1 / v) ((963 / 250 : ℝ) * 𝐮) :=
    fmono hd (by rw [hu]; norm_num)
  have ht := fapprox_mul tpi_near hd' (6367 / 10000) (2 / 3 : ℝ) tpi_le hdm _ le_rfl
    (by rw [hu]; norm_num)
  have ht' : FApprox (Bessel.tpi * (J * L - 1.0 / x)) (2 / π * (J1 v * Real.log v - 1 / v))
      ((1559 / 500 : ℝ) * 𝐮) := fmono ht (by rw [hu]; norm_num)
  have htm : |2 / π * (J1 v * Real.log v - 1 / v)| ≤ (424467 / 1000000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul tpi_le hdm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hres := fapprox_add hxq' ht' (578381 / 1000000 : ℝ) (by
    have h1 := abs_add_le (v * (eval U1 z / eval V1 z)) (2 / π * (J1 v * Real.log v - 1 / v))
    have h2 : (7 / 5 : ℝ) * 𝐮 + (1559 / 500 : ℝ) * 𝐮 ≤ (578381 / 1000000 : ℝ) - ((153913 / 1000000 : ℝ) + (424467 / 1000000 : ℝ)) := by rw [hu]; norm_num
    linarith) (by norm_num)
  exact fmono hres (by rw [hu]; norm_num)

/-- The main path of `y1` for `7/4 ≤ x ≤ 15/8`. -/
theorem piece_4 (x J L : Float) (hf : Finite x.toBits) (v : ℝ) (hv : value x.toBits = v)
    (ha : (7 / 4 : ℝ) ≤ v) (hb : v ≤ (15 / 8 : ℝ)) (hJ : FApprox J (J1 v) ((389 / 100 : ℝ) * 𝐮)) (hJm : |J1 v| ≤ (6217 / 10000 : ℝ))
    (hL : FApprox L (Real.log v) ((18921 / 25000 : ℝ) * 𝐮 + 1 / 2 ^ 59)) (hLm : |Real.log v| ≤ (6307 / 10000 : ℝ))
    (hp0 : 0 ≤ J1 v * Real.log v) :
    FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
        hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) + Bessel.tpi * (J * L - 1.0 / x))
      (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v))
      ((5207 / 1000 : ℝ) * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts_4
  have hx0 : FApprox x (value x.toBits) 0 := fapprox_exact x hf
  subst hv
  set v := value x.toBits
  have hx : FApprox x v 0 := hx0
  have hz := sq_near x hf (15 / 8 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (7 / 4 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (15 / 8 : ℝ) ^ 2 := by nlinarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := uv_at (x * x) hz.1 z _ (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP U1) (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP V1) (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (u1w.map Float.ofBits) (x * x)) (eval U1 z) ((14 / 25 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval V1 z) ((1299 / 1000 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval U1 z| ≤ (58843 / 1000000 : ℝ) := (magBound_sound U1 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (16608 / 15625 : ℝ) ≤ |eval V1 z| := by
    have := (lowBound_sound V1 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hq := fapprox_div hH hS' (58843 / 1000000 : ℝ) (16608 / 15625 : ℝ) hHm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval U1 z / eval V1 z) ((13 / 20 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |eval U1 z / eval V1 z| ≤ (55361 / 1000000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hHm (by norm_num) hSm).trans (by norm_num)
  have hvb : |v| ≤ (15 / 8 : ℝ) := by rw [abs_of_nonneg (by linarith)]; exact hb
  have hxq := fapprox_mul hx hq' (15 / 8 : ℝ) (55361 / 1000000 : ℝ) hvb hqm _ le_rfl (by rw [hu]; norm_num)
  have hxq' : FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x))) (v * (eval U1 z / eval V1 z)) ((1323 / 1000 : ℝ) * 𝐮) :=
    fmono hxq (by rw [hu]; norm_num)
  have hxqm : |v * (eval U1 z / eval V1 z)| ≤ (51901 / 500000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hvb hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hp := fapprox_mul hJ hL (6217 / 10000 : ℝ) (6307 / 10000 : ℝ) hJm hLm _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox (J * L) (J1 v * Real.log v) ((1663 / 500 : ℝ) * 𝐮) := fmono hp (by rw [hu]; norm_num)
  have hpm : |J1 v * Real.log v| ≤ (392107 / 1000000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hJm hLm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hinv := fapprox_div fapprox_one hx 1 (7 / 4 : ℝ) (by norm_num)
    (by rw [abs_of_pos (by linarith)]; exact ha) (by norm_num) _ le_rfl (by norm_num)
  have hinv' : FApprox (1.0 / x) (1 / v) ((143 / 250 : ℝ) * 𝐮) := fmono hinv (by rw [hu]; norm_num)
  have hiv1 : 1 / v ≤ (4 / 7 : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num) ha
    norm_num at this ⊢; linarith
  have hiv2 : (8 / 15 : ℝ) ≤ 1 / v := by
    have := one_div_le_one_div_of_le (by linarith) hb
    norm_num at this ⊢; linarith
  have hdm : |J1 v * Real.log v - 1 / v| ≤ (4 / 7 : ℝ) := by
    have h1 := (abs_le.mp hpm).2
    have h2 : (392107 / 1000000 : ℝ) - (8 / 15 : ℝ) ≤ (4 / 7 : ℝ) := by norm_num
    rw [abs_le]; constructor <;> linarith
  have hd := fapprox_sub hp' hinv' ((4 / 7 : ℝ) + ((1663 / 500 : ℝ) * 𝐮 + (143 / 250 : ℝ) * 𝐮)) (by linarith)
    (by rw [hu]; norm_num)
  have hd' : FApprox (J * L - 1.0 / x) (J1 v * Real.log v - 1 / v) ((447 / 100 : ℝ) * 𝐮) :=
    fmono hd (by rw [hu]; norm_num)
  have ht := fapprox_mul tpi_near hd' (6367 / 10000) (4 / 7 : ℝ) tpi_le hdm _ le_rfl
    (by rw [hu]; norm_num)
  have ht' : FApprox (Bessel.tpi * (J * L - 1.0 / x)) (2 / π * (J1 v * Real.log v - 1 / v))
      ((427 / 125 : ℝ) * 𝐮) := fmono ht (by rw [hu]; norm_num)
  have htm : |2 / π * (J1 v * Real.log v - 1 / v)| ≤ (363829 / 1000000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul tpi_le hdm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hres := fapprox_add hxq' ht' (29227 / 62500 : ℝ) (by
    have h1 := abs_add_le (v * (eval U1 z / eval V1 z)) (2 / π * (J1 v * Real.log v - 1 / v))
    have h2 : (1323 / 1000 : ℝ) * 𝐮 + (427 / 125 : ℝ) * 𝐮 ≤ (29227 / 62500 : ℝ) - ((51901 / 500000 : ℝ) + (363829 / 1000000 : ℝ)) := by rw [hu]; norm_num
    linarith) (by norm_num)
  exact fmono hres (by rw [hu]; norm_num)

/-- The main path of `y1` for `15/8 ≤ x ≤ 31/16`. -/
theorem piece_5 (x J L : Float) (hf : Finite x.toBits) (v : ℝ) (hv : value x.toBits = v)
    (ha : (15 / 8 : ℝ) ≤ v) (hb : v ≤ (31 / 16 : ℝ)) (hJ : FApprox J (J1 v) ((389 / 100 : ℝ) * 𝐮)) (hJm : |J1 v| ≤ (1503 / 2500 : ℝ))
    (hL : FApprox L (Real.log v) ((993 / 1250 : ℝ) * 𝐮 + 1 / 2 ^ 59)) (hLm : |Real.log v| ≤ (331 / 500 : ℝ))
    (hp0 : 0 ≤ J1 v * Real.log v) :
    FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
        hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) + Bessel.tpi * (J * L - 1.0 / x))
      (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v))
      ((51 / 10 : ℝ) * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts_5
  have hx0 : FApprox x (value x.toBits) 0 := fapprox_exact x hf
  subst hv
  set v := value x.toBits
  have hx : FApprox x v 0 := hx0
  have hz := sq_near x hf (31 / 16 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (15 / 8 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (31 / 16 : ℝ) ^ 2 := by nlinarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := uv_at (x * x) hz.1 z _ (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP U1) (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP V1) (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (u1w.map Float.ofBits) (x * x)) (eval U1 z) ((71 / 125 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval V1 z) ((33 / 25 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval U1 z| ≤ (20673 / 500000 : ℝ) := (magBound_sound U1 (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (16759 / 15625 : ℝ) ≤ |eval V1 z| := by
    have := (lowBound_sound V1 (253327479039590175 / 72057594037927936 : ℚ) (1081989810475762625 / 288230376151711744 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hq := fapprox_div hH hS' (20673 / 500000 : ℝ) (16759 / 15625 : ℝ) hHm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval U1 z / eval V1 z) ((77 / 125 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |eval U1 z / eval V1 z| ≤ (38549 / 1000000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hHm (by norm_num) hSm).trans (by norm_num)
  have hvb : |v| ≤ (31 / 16 : ℝ) := by rw [abs_of_nonneg (by linarith)]; exact hb
  have hxq := fapprox_mul hx hq' (31 / 16 : ℝ) (38549 / 1000000 : ℝ) hvb hqm _ le_rfl (by rw [hu]; norm_num)
  have hxq' : FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x))) (v * (eval U1 z / eval V1 z)) ((1269 / 1000 : ℝ) * 𝐮) :=
    fmono hxq (by rw [hu]; norm_num)
  have hxqm : |v * (eval U1 z / eval V1 z)| ≤ (74689 / 1000000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hvb hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hp := fapprox_mul hJ hL (1503 / 2500 : ℝ) (331 / 500 : ℝ) hJm hLm _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox (J * L) (J1 v * Real.log v) ((3461 / 1000 : ℝ) * 𝐮) := fmono hp (by rw [hu]; norm_num)
  have hpm : |J1 v * Real.log v| ≤ (79599 / 200000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hJm hLm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hinv := fapprox_div fapprox_one hx 1 (15 / 8 : ℝ) (by norm_num)
    (by rw [abs_of_pos (by linarith)]; exact ha) (by norm_num) _ le_rfl (by norm_num)
  have hinv' : FApprox (1.0 / x) (1 / v) ((267 / 500 : ℝ) * 𝐮) := fmono hinv (by rw [hu]; norm_num)
  have hiv1 : 1 / v ≤ (8 / 15 : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num) ha
    norm_num at this ⊢; linarith
  have hiv2 : (16 / 31 : ℝ) ≤ 1 / v := by
    have := one_div_le_one_div_of_le (by linarith) hb
    norm_num at this ⊢; linarith
  have hdm : |J1 v * Real.log v - 1 / v| ≤ (8 / 15 : ℝ) := by
    have h1 := (abs_le.mp hpm).2
    have h2 : (79599 / 200000 : ℝ) - (16 / 31 : ℝ) ≤ (8 / 15 : ℝ) := by norm_num
    rw [abs_le]; constructor <;> linarith
  have hd := fapprox_sub hp' hinv' ((8 / 15 : ℝ) + ((3461 / 1000 : ℝ) * 𝐮 + (267 / 500 : ℝ) * 𝐮)) (by linarith)
    (by rw [hu]; norm_num)
  have hd' : FApprox (J * L - 1.0 / x) (J1 v * Real.log v - 1 / v) ((4529 / 1000 : ℝ) * 𝐮) :=
    fmono hd (by rw [hu]; norm_num)
  have ht := fapprox_mul tpi_near hd' (6367 / 10000) (8 / 15 : ℝ) tpi_le hdm _ le_rfl
    (by rw [hu]; norm_num)
  have ht' : FApprox (Bessel.tpi * (J * L - 1.0 / x)) (2 / π * (J1 v * Real.log v - 1 / v))
      ((427 / 125 : ℝ) * 𝐮) := fmono ht (by rw [hu]; norm_num)
  have htm : |2 / π * (J1 v * Real.log v - 1 / v)| ≤ (169787 / 500000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul tpi_le hdm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hres := fapprox_add hxq' ht' (51783 / 125000 : ℝ) (by
    have h1 := abs_add_le (v * (eval U1 z / eval V1 z)) (2 / π * (J1 v * Real.log v - 1 / v))
    have h2 : (1269 / 1000 : ℝ) * 𝐮 + (427 / 125 : ℝ) * 𝐮 ≤ (51783 / 125000 : ℝ) - ((74689 / 1000000 : ℝ) + (169787 / 500000 : ℝ)) := by rw [hu]; norm_num
    linarith) (by norm_num)
  exact fmono hres (by rw [hu]; norm_num)

/-- The main path of `y1` for `31/16 ≤ x ≤ 2`. -/
theorem piece_6 (x J L : Float) (hf : Finite x.toBits) (v : ℝ) (hv : value x.toBits = v)
    (ha : (31 / 16 : ℝ) ≤ v) (hb : v ≤ (2 : ℝ)) (hJ : FApprox J (J1 v) ((389 / 100 : ℝ) * 𝐮)) (hJm : |J1 v| ≤ (1497 / 2500 : ℝ))
    (hL : FApprox L (Real.log v) ((5199 / 6250 : ℝ) * 𝐮 + 1 / 2 ^ 59)) (hLm : |Real.log v| ≤ (1733 / 2500 : ℝ))
    (hp0 : 0 ≤ J1 v * Real.log v) :
    FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
        hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) + Bessel.tpi * (J * L - 1.0 / x))
      (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v))
      ((129 / 25 : ℝ) * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts_6
  have hx0 : FApprox x (value x.toBits) 0 := fapprox_exact x hf
  subst hv
  set v := value x.toBits
  have hx : FApprox x v 0 := hx0
  have hz := sq_near x hf (2 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (31 / 16 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (2 : ℝ) ^ 2 := by nlinarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := uv_at (x * x) hz.1 z _ (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP U1) (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP V1) (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (u1w.map Float.ofBits) (x * x)) (eval U1 z) ((591 / 1000 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval V1 z) ((1343 / 1000 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval U1 z| ≤ (32421 / 1000000 : ℝ) := (magBound_sound U1 (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (538843 / 500000 : ℝ) ≤ |eval V1 z| := by
    have := (lowBound_sound V1 (1081989810475760703 / 288230376151711744 : ℚ) (1125899906842625 / 281474976710656 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hq := fapprox_div hH hS' (32421 / 1000000 : ℝ) (538843 / 500000 : ℝ) hHm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval U1 z / eval V1 z) ((77 / 125 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |eval U1 z / eval V1 z| ≤ (7521 / 250000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hHm (by norm_num) hSm).trans (by norm_num)
  have hvb : |v| ≤ (2 : ℝ) := by rw [abs_of_nonneg (by linarith)]; exact hb
  have hxq := fapprox_mul hx hq' (2 : ℝ) (7521 / 250000 : ℝ) hvb hqm _ le_rfl (by rw [hu]; norm_num)
  have hxq' : FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x))) (v * (eval U1 z / eval V1 z)) ((1293 / 1000 : ℝ) * 𝐮) :=
    fmono hxq (by rw [hu]; norm_num)
  have hxqm : |v * (eval U1 z / eval V1 z)| ≤ (7521 / 125000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hvb hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hp := fapprox_mul hJ hL (1497 / 2500 : ℝ) (1733 / 2500 : ℝ) hJm hLm _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox (J * L) (J1 v * Real.log v) ((181 / 50 : ℝ) * 𝐮) := fmono hp (by rw [hu]; norm_num)
  have hpm : |J1 v * Real.log v| ≤ (415089 / 1000000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hJm hLm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hinv := fapprox_div fapprox_one hx 1 (31 / 16 : ℝ) (by norm_num)
    (by rw [abs_of_pos (by linarith)]; exact ha) (by norm_num) _ le_rfl (by norm_num)
  have hinv' : FApprox (1.0 / x) (1 / v) ((517 / 1000 : ℝ) * 𝐮) := fmono hinv (by rw [hu]; norm_num)
  have hiv1 : 1 / v ≤ (16 / 31 : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num) ha
    norm_num at this ⊢; linarith
  have hiv2 : (1 / 2 : ℝ) ≤ 1 / v := by
    have := one_div_le_one_div_of_le (by linarith) hb
    norm_num at this ⊢; linarith
  have hdm : |J1 v * Real.log v - 1 / v| ≤ (16 / 31 : ℝ) := by
    have h1 := (abs_le.mp hpm).2
    have h2 : (415089 / 1000000 : ℝ) - (1 / 2 : ℝ) ≤ (16 / 31 : ℝ) := by norm_num
    rw [abs_le]; constructor <;> linarith
  have hd := fapprox_sub hp' hinv' ((16 / 31 : ℝ) + ((181 / 50 : ℝ) * 𝐮 + (517 / 1000 : ℝ) * 𝐮)) (by linarith)
    (by rw [hu]; norm_num)
  have hd' : FApprox (J * L - 1.0 / x) (J1 v * Real.log v - 1 / v) ((2327 / 500 : ℝ) * 𝐮) :=
    fmono hd (by rw [hu]; norm_num)
  have ht := fapprox_mul tpi_near hd' (6367 / 10000) (16 / 31 : ℝ) tpi_le hdm _ le_rfl
    (by rw [hu]; norm_num)
  have ht' : FApprox (Bessel.tpi * (J * L - 1.0 / x)) (2 / π * (J1 v * Real.log v - 1 / v))
      ((1739 / 500 : ℝ) * 𝐮) := fmono ht (by rw [hu]; norm_num)
  have htm : |2 / π * (J1 v * Real.log v - 1 / v)| ≤ (16431 / 50000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul tpi_le hdm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hres := fapprox_add hxq' ht' (388789 / 1000000 : ℝ) (by
    have h1 := abs_add_le (v * (eval U1 z / eval V1 z)) (2 / π * (J1 v * Real.log v - 1 / v))
    have h2 : (1293 / 1000 : ℝ) * 𝐮 + (1739 / 500 : ℝ) * 𝐮 ≤ (388789 / 1000000 : ℝ) - ((7521 / 125000 : ℝ) + (16431 / 50000 : ℝ)) := by rw [hu]; norm_num
    linarith) (by norm_num)
  exact fmono hres (by rw [hu]; norm_num)

/-- The main path of `y1` for `2^-54 ≤ x ≤ 1`, with `ℓ = |ln x|`. -/
theorem small_piece (x J L : Float) (hf : Finite x.toBits) (v : ℝ) (hv : value x.toBits = v)
    (ha : (1 / 18014398509481984 : ℝ) ≤ v) (hb : v ≤ (1 : ℝ)) (ℓ : ℝ) (hℓ : |Real.log v| = ℓ) (hℓ1 : ℓ ≤ 38)
    (hvl : v * ℓ ≤ 3679 / 10000) (hJ : FApprox J (J1 v) (14 / 10 * 𝐮)) (hJm : |J1 v| ≤ 51 / 100 * v)
    (hL : FApprox L (Real.log v) (6 / 5 * 𝐮 * ℓ + 1 / 2 ^ 59)) :
    FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
        hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) + Bessel.tpi * (J * L - 1.0 / x))
      (v * (eval U1 (v ^ 2) / eval V1 (v ^ 2)) + 2 / π * (J1 v * Real.log v - 1 / v))
      ((2909 / 1000 : ℝ) * 𝐮 * (1 / v) + (447 / 500 : ℝ) * 𝐮 * ℓ + (2581 / 1000 : ℝ) * 𝐮) := by
  have hℓ0 : 0 ≤ ℓ := by rw [← hℓ]; exact abs_nonneg _
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) ha
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts_small
  have hx0 : FApprox x (value x.toBits) 0 := fapprox_exact x hf
  subst hv
  set v := value x.toBits
  have hx : FApprox x v 0 := hx0
  have hz := sq_near x hf (1 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (1 / 18014398509481984 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (1 : ℝ) ^ 2 := by nlinarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := uv_at (x * x) hz.1 z _ (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP U1) (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP V1) (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (u1w.map Float.ofBits) (x * x)) (eval U1 z) ((44 / 125 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval V1 z) ((541 / 500 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval U1 z| ≤ (98029 / 500000 : ℝ) := (magBound_sound U1 (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (999897 / 1000000 : ℝ) ≤ |eval V1 z| := by
    have := (lowBound_sound V1 (-1 / 1125899906842624 : ℚ) (1125899906842625 / 1125899906842624 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hq := fapprox_div hH hS' (98029 / 500000 : ℝ) (999897 / 1000000 : ℝ) hHm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x)) (eval U1 z / eval V1 z) ((761 / 1000 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |eval U1 z / eval V1 z| ≤ (196079 / 1000000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hHm (by norm_num) hSm).trans (by norm_num)
  have hy1 : 1 ≤ 1 / v := by rw [le_div_iff₀ hv0]; linarith
  have hy54 : 1 / v ≤ 2 ^ 54 := by rw [div_le_iff₀ hv0]; norm_num at ha ⊢; linarith
  have hvb : |v| ≤ v := le_of_eq (abs_of_pos hv0)
  have hxq := fapprox_mul hx hq' v (196079 / 1000000 : ℝ) hvb hqm _ le_rfl (by rw [hu]; linarith)
  have hxq' : FApprox (x * (hornerF (u1w.map Float.ofBits) (x * x) /
      hornerF (1.0 :: v1w.map Float.ofBits) (x * x))) (v * (eval U1 z / eval V1 z)) ((479 / 500 : ℝ) * 𝐮) :=
    fmono hxq (by rw [hu]; linarith)
  have hxqm : |v * (eval U1 z / eval V1 z)| ≤ (196079 / 1000000 : ℝ) := by
    rw [abs_mul, abs_of_pos hv0]
    calc v * |eval U1 z / eval V1 z| ≤ 1 * (196079 / 1000000 : ℝ) :=
          mul_le_mul hb hqm (abs_nonneg _) zero_le_one
      _ = (196079 / 1000000 : ℝ) := one_mul _
  have hp := fapprox_mul hJ hL (51 / 100 * v) ℓ hJm (le_of_eq hℓ) _ le_rfl (by rw [hu]; linarith)
  have hp' : FApprox (J * L) (J1 v * Real.log v) ((1401 / 1000 : ℝ) * 𝐮 * ℓ + (421 / 1000 : ℝ) * 𝐮) :=
    fmono hp (by rw [hu]; linarith)
  have hpm : |J1 v * Real.log v| ≤ 51 / 100 := by
    rw [abs_mul, hℓ]
    have := mul_le_mul_of_nonneg_right hJm hℓ0
    linarith
  have hinv := fapprox_div fapprox_one hx 1 v (by norm_num) (le_abs_self v) hv0 _ le_rfl (by
      have : (1 + 0) / (v - 0) = 1 / v := by ring
      rw [this]
      linarith)
  have hinv' : FApprox (1.0 / x) (1 / v) ((1001 / 1000 : ℝ) * 𝐮 * (1 / v)) := by
    refine fmono hinv ?_
    calc _ = 1 / v / 2 ^ 53 + 1 / 2 ^ 1075 := by ring
      _ ≤ (1001 / 1000 : ℝ) * 𝐮 * (1 / v) := by rw [hu]; linarith
  have hdm : |J1 v * Real.log v - 1 / v| ≤ 51 / 100 + 1 / v := by
    have := abs_sub (J1 v * Real.log v) (1 / v)
    rw [abs_of_pos (one_div_pos.mpr hv0)] at this
    linarith
  have hd := fapprox_sub hp' hinv'
    (51 / 100 + 1 / v + ((1401 / 1000 : ℝ) * 𝐮 * ℓ + (421 / 1000 : ℝ) * 𝐮 + (1001 / 1000 : ℝ) * 𝐮 * (1 / v))) (by linarith)
    (by rw [hu]; linarith)
  have hd' : FApprox (J * L - 1.0 / x) (J1 v * Real.log v - 1 / v)
      ((1001 / 500 : ℝ) * 𝐮 * (1 / v) + (701 / 500 : ℝ) * 𝐮 * ℓ + (233 / 250 : ℝ) * 𝐮) := fmono hd (by rw [hu]; linarith)
  have ht := fapprox_mul tpi_near hd' (6367 / 10000) (51 / 100 + 1 / v) tpi_le hdm _ le_rfl
    (by rw [hu]; linarith)
  have ht' : FApprox (Bessel.tpi * (J * L - 1.0 / x)) (2 / π * (J1 v * Real.log v - 1 / v))
      ((284 / 125 : ℝ) * 𝐮 * (1 / v) + (893 / 1000 : ℝ) * 𝐮 * ℓ + (551 / 500 : ℝ) * 𝐮) := fmono ht (by rw [hu]; linarith)
  have htm : |2 / π * (J1 v * Real.log v - 1 / v)| ≤ 6367 / 10000 * (51 / 100 + 1 / v) := by
    rw [abs_mul]; exact mul_le_mul tpi_le hdm (abs_nonneg _) (by norm_num)
  have hres := fapprox_add hxq' ht'
    ((196079 / 1000000 : ℝ) + 6367 / 10000 * (51 / 100 + 1 / v) +
      ((479 / 500 : ℝ) * 𝐮 + ((284 / 125 : ℝ) * 𝐮 * (1 / v) + (893 / 1000 : ℝ) * 𝐮 * ℓ + (551 / 500 : ℝ) * 𝐮))) (by
      have := abs_add_le (v * (eval U1 z / eval V1 z)) (2 / π * (J1 v * Real.log v - 1 / v))
      linarith) (by rw [hu]; linarith)
  exact fmono hres (by rw [hu]; linarith)

#print axioms piece_0
#print axioms piece_1
#print axioms piece_2
#print axioms piece_3
#print axioms piece_4
#print axioms piece_5
#print axioms piece_6
#print axioms small_piece

end Library.Numerics.Float64.Bessel.BesselSmallY1
