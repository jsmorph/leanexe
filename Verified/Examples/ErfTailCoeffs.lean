import Verified.Examples.ErfTailBase

/-!
The coefficients of the two tail rational functions of `s_erf.c`, as `Erf.erfTail` holds them,
the ends of the ranges where the code uses each, and the positivity of their denominators.  `R_a/S_a`
serves `1.25 ≤ x` below the high word `0x4006DB6E` in `erf` and `0x4006DB6D` in `erfc`, and `R_b/S_b`
serves `x` from the high word `0x4006DB6D` to 28, so each kernel's bound covers both functions' uses.
-/

namespace Verified.Examples.ErfTailCoeffs
open Real Set LeanExe.ProofKit PolyBound PolyChecks PolyCalculus RealErfScaled ErfTailBase

/-- `ra0 + ra1 s + ... + ra7 s⁷`. -/
def tailRA : List ℚ :=
  [ratOfWord 0xBF843412600D6435, ratOfWord 0xBFE63416E4BA7360, ratOfWord 0xC0251E0441B0E726,
    ratOfWord 0xC04F300AE4CBA38D, ratOfWord 0xC0644CB184282266, ratOfWord 0xC067135CEBCCABB2,
    ratOfWord 0xC054526557E4D2F2, ratOfWord 0xC023A0EFC69AC25C]

/-- `1 + sa1 s + ... + sa8 s⁸`. -/
def tailSA : List ℚ :=
  [1, ratOfWord 0x4033A6B9BD707687, ratOfWord 0x4061350C526AE721, ratOfWord 0x407B290DD58A1A71,
    ratOfWord 0x40842B1921EC2868, ratOfWord 0x407AD02157700314, ratOfWord 0x405B28A3EE48AE2C,
    ratOfWord 0x401A47EF8E484A93, ratOfWord 0xBFAEEFF2EE749A62]

/-- `rb0 + rb1 s + ... + rb6 s⁶`. -/
def tailRB : List ℚ :=
  [ratOfWord 0xBF84341239E86F4A, ratOfWord 0xBFE993BA70C285DE, ratOfWord 0xC031C209555F995A,
    ratOfWord 0xC064145D43C5ED98, ratOfWord 0xC083EC881375F228, ratOfWord 0xC09004616A2E5992,
    ratOfWord 0xC07E384E9BDC383F]

/-- `1 + sb1 s + ... + sb7 s⁷`. -/
def tailSB : List ℚ :=
  [1, ratOfWord 0x403E568B261D5190, ratOfWord 0x40745CAE221B9F0A, ratOfWord 0x409802EB189D5118,
    ratOfWord 0x40A8FFB7688C246A, ratOfWord 0x40A3F219CEDF3BE6, ratOfWord 0x407DA874E79FE763,
    ratOfWord 0xC03670E242712D62]

/-- The bound on the tail kernels' error. -/
def epsT : ℚ := 1 / 2 ^ 56

/-- The double with high word `0x4006DB6D`, from which `erfc` uses `R_b/S_b`. -/
def tailB1 : ℚ := (1497965 / 2 ^ 19 : ℚ)

/-- The double with high word `0x4006DB6E`, below which `erf` uses `R_a/S_a`. -/
def tailB2 : ℚ := (748983 / 2 ^ 18 : ℚ)

theorem sa_check : check (subP (subP tailSA [1 / 2]) [(192 : ℚ)]) 0 (16 / 25) (192 : ℚ) 20 = true := by
  decide +kernel

theorem sb_check : check (subP (subP tailSB [1 / 2]) [(8 : ℚ)]) 0 (274877906944 / 2243899141225 : ℚ) (8 : ℚ) 20 = true := by
  decide +kernel

theorem spos_a (x : ℝ) (hx : ((5 / 4 : ℚ) : ℝ) ≤ x) : 0 < eval (hatP tailSA 8) x := by
  push_cast at hx
  have hx0 : 0 < x := by linarith
  refine hatP_pos tailSA 8 (by decide +kernel) (16 / 25) (1 / 2) (192 : ℚ) 20 sa_check (by norm_num) hx0 ?_
  push_cast
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  nlinarith

theorem spos_b (x : ℝ) (hx : (tailB1 : ℝ) ≤ x) : 0 < eval (hatP tailSB 7) x := by
  have hB : (0 : ℝ) < tailB1 := by exact_mod_cast (show (0 : ℚ) < tailB1 by decide +kernel)
  have hx0 : 0 < x := lt_of_lt_of_le hB hx
  refine hatP_pos tailSB 7 (by decide +kernel) (274877906944 / 2243899141225 : ℚ) (1 / 2) (8 : ℚ) 20 sb_check (by norm_num) hx0 ?_
  have hs : ((x ^ 2)⁻¹ : ℝ) ≤ ((tailB1 : ℝ) ^ 2)⁻¹ := by
    apply inv_anti₀ (by positivity)
    nlinarith
  have he : (((tailB1 : ℝ) ^ 2)⁻¹) = (((274877906944 / 2243899141225 : ℚ) : ℚ) : ℝ) := by
    rw [show ((274877906944 / 2243899141225 : ℚ) : ℚ) = (tailB1 ^ 2)⁻¹ by decide +kernel]
    push_cast
    rfl
  rw [he] at hs
  exact hs

#print axioms spos_a
#print axioms spos_b

end Verified.Examples.ErfTailCoeffs
