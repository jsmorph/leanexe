import Verified.Examples.BesselCombine

/-!
One case of the path from 2: given the rounded `P̂`, `Q̂`, `ĉc`, and `ŝs` with their errors and
magnitude bounds, and numeric conditions that `norm_num` checks for each range and branch, the
result of the code lies within `K u M` of the large-argument form, for every `M` at least
`0.7978 Pl / √x`.  `case_sub` covers `j0` and `j1`, `case_add` covers `y0` and `y1`, and `case_one`
covers the path above `2 ^ 129`, where the code multiplies `invsqrtpi` by one term alone.
`case_finish` absorbs the underflow term `2 ^ -1075` into `2 ^ -500 / √x` for `x ≤ 2 ^ 1024`.
-/

namespace Verified.Examples.BesselCase
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx BesselPQEval BesselPQRange BesselCombine Real

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- The last bound of every case. -/
theorem case_finish {r : Float} {F w E K M Pl : ℝ} (hr : FApprox r F (E / √w + 1 / 2 ^ 1075))
    (hw2 : 2 ≤ w) (hwb : w ≤ 2 ^ 1024)
    (hK : E + 1 / 2 ^ 500 ≤ K * 𝐮 * (7978 / 10000 * Pl))
    (hM : 7978 / 10000 * Pl / √w ≤ M) (hK0 : 0 ≤ K) :
    |value r.toBits - F| ≤ K * 𝐮 * M := by
  have hu0 : 0 ≤ 𝐮 := by norm_num [unitRoundoff64]
  have hsw : 0 < √w := Real.sqrt_pos.mpr (by linarith)
  have hs : √w ≤ 2 ^ 512 := by
    rw [show (2 : ℝ) ^ 512 = √((2 ^ 512) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by rw [← pow_mul]; exact hwb)
  have hη : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 500 / √w := by
    rw [le_div_iff₀ hsw]
    calc (1 : ℝ) / 2 ^ 1075 * √w ≤ 1 / 2 ^ 1075 * 2 ^ 512 := by gcongr
      _ ≤ 1 / 2 ^ 500 := by norm_num
  have h1 : E / √w + 1 / 2 ^ 1075 ≤ K * 𝐮 * (7978 / 10000 * Pl / √w) := by
    have h2 : E / √w + 1 / 2 ^ 500 / √w ≤ K * 𝐮 * (7978 / 10000 * Pl) / √w := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right hK hsw.le
    rw [mul_div_assoc] at h2
    linarith
  have h3 : K * 𝐮 * (7978 / 10000 * Pl / √w) ≤ K * 𝐮 * M :=
    mul_le_mul_of_nonneg_left hM (mul_nonneg hK0 hu0)
  linarith [hr.2]

/-- The bracket `P A - Q B` of `j0` and `j1`. -/
theorem case_sub {p q c s xa : Float} {P Q A B eP eQ eA eB Pm Qm Am Bm Pl K M : ℝ}
    (hp : FApprox p P eP) (hq : FApprox q Q eQ) (hc : FApprox c A eA) (hs : FApprox s B eB)
    (hPm : |P| ≤ Pm) (hQm : |Q| ≤ Qm) (hAm : |A| ≤ Am) (hBm : |B| ≤ Bm)
    (h1 : (Pm + eP) * (Am + eA) < 2 ^ 1022) (h2 : (Qm + eQ) * (Bm + eB) < 2 ^ 1022)
    (hlt : Pm * Am + Qm * Bm + (mulErr eP eA Pm Am + mulErr eQ eB Qm Bm) < 2)
    (hK : finErr (mulErr eP eA Pm Am + mulErr eQ eB Qm Bm + 𝐮) (Pm * Am + Qm * Bm) +
      1 / 2 ^ 500 ≤ K * 𝐮 * (7978 / 10000 * Pl)) (hK0 : 0 ≤ K)
    (hxf : Finite xa.toBits) (hx2 : 2 ≤ value xa.toBits) (hxb : value xa.toBits ≤ 2 ^ 1024)
    (hM : 7978 / 10000 * Pl / √(value xa.toBits) ≤ M) :
    |value (Bessel.invsqrtpi * (p * c - q * s) / xa.sqrt).toBits -
      (P * A - Q * B) / √(π * value xa.toBits)| ≤ K * 𝐮 * M := by
  have hT := combine_sub hp hq hc hs hPm hQm hAm hBm h1 h2 hlt
  have hMT : |P * A - Q * B| ≤ Pm * Am + Qm * Bm := by
    have := abs_sub (P * A) (Q * B)
    rw [abs_mul, abs_mul] at this
    have e1 := mul_le_mul hPm hAm (abs_nonneg _) ((abs_nonneg _).trans hPm)
    have e2 := mul_le_mul hQm hBm (abs_nonneg _) ((abs_nonneg _).trans hQm)
    linarith
  have hr := final_step hT hMT (by
    have : 𝐮 ≤ 1 := by norm_num [unitRoundoff64]
    linarith) hxf hx2
  exact case_finish hr hx2 hxb hK hM hK0

/-- The bracket `P B + Q A` of `y0` and `y1`. -/
theorem case_add {p q c s xa : Float} {P Q A B eP eQ eA eB Pm Qm Am Bm Pl K M : ℝ}
    (hp : FApprox p P eP) (hq : FApprox q Q eQ) (hc : FApprox c A eA) (hs : FApprox s B eB)
    (hPm : |P| ≤ Pm) (hQm : |Q| ≤ Qm) (hAm : |A| ≤ Am) (hBm : |B| ≤ Bm)
    (h1 : (Pm + eP) * (Bm + eB) < 2 ^ 1022) (h2 : (Qm + eQ) * (Am + eA) < 2 ^ 1022)
    (hlt : Pm * Bm + Qm * Am + (mulErr eP eB Pm Bm + mulErr eQ eA Qm Am) < 2)
    (hK : finErr (mulErr eP eB Pm Bm + mulErr eQ eA Qm Am + 𝐮) (Pm * Bm + Qm * Am) +
      1 / 2 ^ 500 ≤ K * 𝐮 * (7978 / 10000 * Pl)) (hK0 : 0 ≤ K)
    (hxf : Finite xa.toBits) (hx2 : 2 ≤ value xa.toBits) (hxb : value xa.toBits ≤ 2 ^ 1024)
    (hM : 7978 / 10000 * Pl / √(value xa.toBits) ≤ M) :
    |value (Bessel.invsqrtpi * (p * s + q * c) / xa.sqrt).toBits -
      (P * B + Q * A) / √(π * value xa.toBits)| ≤ K * 𝐮 * M := by
  have hT := combine_add hp hq hc hs hPm hQm hAm hBm h1 h2 hlt
  have hMT : |P * B + Q * A| ≤ Pm * Bm + Qm * Am := by
    have := abs_add_le (P * B) (Q * A)
    rw [abs_mul, abs_mul] at this
    have e1 := mul_le_mul hPm hBm (abs_nonneg _) ((abs_nonneg _).trans hPm)
    have e2 := mul_le_mul hQm hAm (abs_nonneg _) ((abs_nonneg _).trans hQm)
    linarith
  have hr := final_step hT hMT (by
    have : 𝐮 ≤ 1 := by norm_num [unitRoundoff64]
    linarith) hxf hx2
  exact case_finish hr hx2 hxb hK hM hK0

/-- The path above `2 ^ 129`: one term `c` in place of the bracket `T`. -/
theorem case_one {c xa : Float} {T A eA d MT Pl K M : ℝ} (hc : FApprox c A eA) (hTA : |A - T| ≤ d)
    (hMT : |T| ≤ MT) (hsm : MT + (eA + d) ≤ 4)
    (hK : finErr (eA + d) MT + 1 / 2 ^ 500 ≤ K * 𝐮 * (7978 / 10000 * Pl)) (hK0 : 0 ≤ K)
    (hxf : Finite xa.toBits) (hx2 : 2 ≤ value xa.toBits) (hxb : value xa.toBits ≤ 2 ^ 1024)
    (hM : 7978 / 10000 * Pl / √(value xa.toBits) ≤ M) :
    |value (Bessel.invsqrtpi * c / xa.sqrt).toBits - T / √(π * value xa.toBits)| ≤ K * 𝐮 * M := by
  have hcT : FApprox c T (eA + d) := fshift hc hTA
  have hr := final_step hcT hMT hsm hxf hx2
  exact case_finish hr hx2 hxb hK hM hK0

#print axioms case_finish
#print axioms case_sub
#print axioms case_add
#print axioms case_one

end Verified.Examples.BesselCase
