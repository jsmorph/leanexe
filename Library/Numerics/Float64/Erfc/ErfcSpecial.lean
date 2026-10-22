import Library.Numerics.Float64.Erfc.ErfcHardRows
import Library.Numerics.Float64.Erfc.ErfcAsymAccFin
import Library.Numerics.Float64.Erf.ErfTailPieces0

/-!
The input `0x1.a8f7bfbd15495p+4` of `erfc_asympt_accurate`, whose value of `erfc` lies in the
subnormal range near `c₀ = 0x1.99ef5883f656cp-1024` (the word `0x000667BD620FD95B`).  The code
returns `fma (2^-1074, -0.25, c₀)`, whose exact value `c₀ - 2^-1076` the fma rounds to within
`2^-1076` (`Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest`).  An enclosure of `erfc` from the model of `erfcxN` on
`ErfTailPieces0`'s piece and ten squarings of `exp (-x²/1024)` (`ErfcHardRows.asym_encl`) puts
`erfc x` within `3 · 2^-1076` of `c₀ - 2^-1076`, so the result lies within `2^-1074` of `erfc x`
and within one step (`ErfcAsymAccFin.within_small`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcSpecial

open Real Set CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcRound ErfcHardRows ErfcAsymAccFin
  FmaSpec PolyBound RealErf

set_option exponentiation.threshold 4096

def los : List ℚ :=
    [(733842563613807902728604146241448289240797195915 / 2 ^ 160 : ℚ),
      (1473894778947433166817772391950504253485334863905 / 2 ^ 162 : ℚ),
      (743196505539271966647688603044775354274233858665 / 2 ^ 163 : ℚ),
      (1511708318998558695278530802497462265743228933047 / 2 ^ 168 : ℚ),
      (781819870521306553621886025711927285485920892207 / 2 ^ 175 : ℚ),
      (52278620010498777230269505204779491154582606665 / 2 ^ 187 : ℚ),
      (119682016485714517480233678959001757976596934385 / 2 ^ 220 : ℚ),
      (1254493626376964581806986042836275744120622505329 / 2 ^ 287 : ℚ),
      (2153612720536568019455838402080795990744466595665 / 2 ^ 415 : ℚ),
      (1586740524809553697337203864965979878781718968465 / 2 ^ 669 : ℚ),
      (861355686768501262981222861573352733817642585269 / 2 ^ 1177 : ℚ)]

def his : List ℚ :=
    [(1467685127227615805457208292482919352499708949501 / 2 ^ 161 : ℚ),
      (368473694736858291704443097987637498557863849411 / 2 ^ 160 : ℚ),
      (743196505539271966647688603044821482889604647089 / 2 ^ 163 : ℚ),
      (94481769937409918454908175156103120171162502943 / 2 ^ 164 : ℚ),
      (195454967630326638405471506428030347256394534251 / 2 ^ 173 : ℚ),
      (1672915840335960871368624166553774391372816199539 / 2 ^ 192 : ℚ),
      (1914912263771432279683738863345929799673273472689 / 2 ^ 224 : ℚ),
      (1254493626376964581806986042838767383563808910773 / 2 ^ 287 : ℚ),
      (2153612720536568019455838402089350879006966941281 / 2 ^ 415 : ℚ),
      (1586740524809553697337203864978586033789890409395 / 2 ^ 669 : ℚ),
      (1722711373537002525962445723174078269009667299859 / 2 ^ 1178 : ℚ)]

def yLo : ℚ := (8927592522258725272446305593116651776752041 / 2 ^ 1166 : ℚ)

def yHi : ℚ := (1142731842849116834877422901474726601835635035 / 2 ^ 1173 : ℚ)

instance (p : List ℚ) (a b c s eD : ℚ) (N : ℕ) (los his : List ℚ) (x Ylo Yhi : ℚ) :
    Decidable (AsymEncl p a b c s eD N los his x Ylo Yhi) := by
  unfold AsymEncl; infer_instance

theorem encl : AsymEncl Library.Numerics.Float64.Erf.ErfTailPieces0.p0 Library.Numerics.Float64.Erf.ErfTailPieces0.a0 Library.Numerics.Float64.Erf.ErfTailPieces0.b0 Library.Numerics.Float64.Erf.ErfTailPieces0.c0 Library.Numerics.Float64.Erf.ErfTailPieces0.s0
    Library.Numerics.Float64.Erf.ErfTailPieces0.eD0 30 los his (ratOfWord 0x403A8F7BFBD15495) yLo yHi := by
  decide +kernel

theorem erfc_encl : (yLo : ℝ) ≤ erfc (ratOfWord 0x403A8F7BFBD15495 : ℚ) ∧
    erfc (ratOfWord 0x403A8F7BFBD15495 : ℚ) ≤ yHi :=
  asym_encl _ _ _ _ _ _ _ _ _ _ _ _ Library.Numerics.Float64.Erf.ErfTailPieces0.model0 encl

theorem conds : Finite (0x0000000000000001 : UInt64) ∧ Finite (0x000667BD620FD95B : UInt64) ∧
    Finite (0xBFD0000000000000 : UInt64) ∧ Finite (0x403A8F7BFBD15495 : UInt64) ∧
    ratOfWord 0x0000000000000001 = 1 / 2 ^ 1074 ∧ ratOfWord 0xBFD0000000000000 = -1 / 4 ∧
    yHi - (ratOfWord 0x000667BD620FD95B - 1 / 2 ^ 1076) < 3 / 2 ^ 1076 ∧
    (ratOfWord 0x000667BD620FD95B - 1 / 2 ^ 1076) - yLo < 3 / 2 ^ 1076 ∧
    0 < ratOfWord 0x000667BD620FD95B - 2 / 2 ^ 1076 ∧ yHi ≤ 1 ∧
    ratOfWord 0x000667BD620FD95B ≤ 1 := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

/-- One step for `erfc_asympt_accurate`'s result at `0x1.a8f7bfbd15495p+4`. -/
theorem special_within (hF : FmaNearest) (x : Float) (hx : ff x)
    (heq : (x == Float.ofBits 0x403A8F7BFBD15495) = true) :
    F64SignedRounding.WithinSteps 1 (erfc (fv x))
      (Library.Numerics.Arithmetic.Fma.fma (Float.ofBits 0x0000000000000001) (-0.25)
        (Float.ofBits 0x000667BD620FD95B)).toBits := by
  obtain ⟨f1, fc, fq, fx, v1, vq, d1, d2, d3, d4, d5⟩ := conds
  obtain ⟨af, av⟩ := ofBits_ff _ f1
  obtain ⟨bf, bv⟩ := lit (-0.25 : Float) 0xBFD0000000000000 rfl fq
  obtain ⟨cf, cv⟩ := ofBits_ff _ fc
  obtain ⟨xf, xv⟩ := ofBits_ff _ fx
  have hxv : fv x = ratOfWord 0x403A8F7BFBD15495 := by
    rw [(fbeq_iff _ _ hx xf).mp heq, xv]
  obtain ⟨e1, e2⟩ := erfc_encl
  rw [← hxv] at e1 e2
  set c0 : ℚ := ratOfWord 0x000667BD620FD95B with hc0
  have hA : value (Float.ofBits 0x0000000000000001).toBits = 1 / 2 ^ 1074 := by
    have := av; unfold fv at this; rw [this, v1]; push_cast; ring
  have hB : value (-0.25 : Float).toBits = -1 / 4 := by
    have := bv; unfold fv at this; rw [this, vq]; push_cast; ring
  have hC : value (Float.ofBits 0x000667BD620FD95B).toBits = (c0 : ℝ) := by
    have := cv; unfold fv at this; exact this
  have hW : value (0x000667BD620FD95B : UInt64) = (c0 : ℝ) := (ratOfWord_cast _).symm
  have k1 : ((yHi - (c0 - 1 / 2 ^ 1076) : ℚ) : ℝ) < ((3 / 2 ^ 1076 : ℚ) : ℝ) := by qc d1
  have k2 : (((c0 - 1 / 2 ^ 1076) - yLo : ℚ) : ℝ) < ((3 / 2 ^ 1076 : ℚ) : ℝ) := by qc d2
  have k3 : ((0 : ℚ) : ℝ) < ((c0 - 2 / 2 ^ 1076 : ℚ) : ℝ) := by qc d3
  have k4 : ((yHi : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by qc d4
  have k5 : ((c0 : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by qc d5
  push_cast at k1 k2 k3 k4 k5
  have hSb : |value (Float.ofBits 0x0000000000000001).toBits * value (-0.25 : Float).toBits +
      value (Float.ofBits 0x000667BD620FD95B).toBits| ≤ 2 ^ 1023 := by
    rw [hA, hB, hC, abs_le]
    constructor <;> nlinarith
  obtain ⟨rf, rn⟩ := hF _ _ _ af bf cf hSb
  have hr := rn _ fc
  rw [hA, hB, hC, hW, show (c0 : ℝ) - (1 / 2 ^ 1074 * (-1 / 4) + c0) = 1 / 2 ^ 1076 by ring,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2 ^ 1076)] at hr
  have hr2 := abs_le.mp hr
  refine within_small _ rf ?_ _ (erfc_pos _).le (by linarith) ?_
  · nlinarith [hr2.1]
  · rw [abs_lt]
    constructor <;> nlinarith [hr2.1, hr2.2]

#print axioms special_within

end Library.Numerics.Float64.Erfc.ErfcSpecial
