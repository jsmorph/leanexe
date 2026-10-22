import Library.Numerics.Float64.Erfc.ErfcTrack4
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
`Erfc.dMul` with relative bounds.  The products of the asymptotic paths of `Erfc` multiply
double-doubles whose values scale with `1/x` and `exp (-x²)`, so their bounds are reals: with
`|A| ≤ MA`, the error at most `ra MA`, and the low part at most `la MA`, and likewise for `B`, the
product has the error at most `(ra + rb + ra rb + la lb + 3 u (la + lb) + 4 u² + 2^-92) MA MB`
when `MA MB ≥ 2^-980`, where the underflow terms become relative (`pr_dMul_rel`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcRel

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcTrack4 Library.Numerics.Arithmetic.Fma.FmaSpec

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)
local notation "K" => (1 + 1 / 2 ^ 19 : ℝ)

theorem pr_dMul_rel (hF : FmaNearest) {ah al bh bl : Float} {A B MA LA eA MB LB eB : ℝ}
    (ha : Pr ah al A MA LA eA) (hb : Pr bh bl B MB LB eB) (ra la rb lb : ℝ)
    (hra : eA ≤ ra * MA) (hla : LA ≤ la * MA) (hrb : eB ≤ rb * MB) (hlb : LB ≤ lb * MB)
    (hr1 : ra + la ≤ 1 / 2 ^ 20) (hr2 : rb + lb ≤ 1 / 2 ^ 20)
    (hP : 1 / 2 ^ 980 ≤ MA * MB) (hMA : MA ≤ 2 ^ 20) (hMB : MB ≤ 2 ^ 20) :
    Pr (Erfc.dMul ah al bh bl).1 (Erfc.dMul ah al bh bl).2 (A * B) (MA * MB)
      (((1 + 1 / 2 ^ 18) * (la + lb) + 2 * u) * (MA * MB))
      ((ra + rb + ra * rb + la * lb + 3 * u * (la + lb) + 4 * u * u + 1 / 2 ^ 92) * (MA * MB)) := by
  have hMA0 := ha.M_nonneg
  have hMB0 := hb.M_nonneg
  have heA0 := ha.e_nonneg
  have heB0 := hb.e_nonneg
  have hLA0 := ha.L_nonneg
  have hLB0 := hb.L_nonneg
  set P := MA * MB with hPdef
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have hMA1 : 0 < MA := by
    rcases hMA0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hPdef; linarith
  have hMB1 : 0 < MB := by
    rcases hMB0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hPdef; linarith
  have hra0 : 0 ≤ ra := le_of_mul_le_mul_right (by rw [zero_mul]; linarith) hMA1
  have hla0 : 0 ≤ la := le_of_mul_le_mul_right (by rw [zero_mul]; linarith) hMA1
  have hrb0 : 0 ≤ rb := le_of_mul_le_mul_right (by rw [zero_mul]; linarith) hMB1
  have hlb0 : 0 ≤ lb := le_of_mul_le_mul_right (by rw [zero_mul]; linarith) hMB1
  have hη : η ≤ 1 / 2 ^ 95 * P := by
    calc η = 1 / 2 ^ 95 * (1 / 2 ^ 980) := by norm_num
      _ ≤ 1 / 2 ^ 95 * P := by gcongr
  have hHA : MA + eA + LA ≤ K * MA := by
    have : (ra + la) * MA ≤ 1 / 2 ^ 20 * MA := mul_le_mul_of_nonneg_right hr1 hMA0
    linarith
  have hHB : MB + eB + LB ≤ K * MB := by
    have : (rb + lb) * MB ≤ 1 / 2 ^ 20 * MB := mul_le_mul_of_nonneg_right hr2 hMB0
    linarith
  have hKK : K * MA * (K * MB) = K * K * P := by rw [hPdef]; ring
  set Ttl := u * u * (K * MA * (K * MB)) + 2 * η + (u * (K * MA * (K * MB)) + η) with hTtl
  set T0 : ℝ := u * K * K * (1 + u) + 3 / 2 ^ 95 with hT0
  have hT : Ttl ≤ T0 * P := by
    have e : Ttl = u * K * K * (1 + u) * P + 3 * η := by rw [hTtl, hKK]; ring
    rw [e, hT0]
    linarith
  have hT0' : 0 ≤ Ttl := by rw [hTtl]; positivity
  set F1 := (K * MA * LB + Ttl) * (1 + u) + η with hF1
  have hHL : K * MA * LB ≤ K * lb * P := by
    calc K * MA * LB ≤ K * MA * (lb * MB) :=
          mul_le_mul_of_nonneg_left hlb (mul_nonneg (by norm_num) hMA0)
      _ = K * lb * P := by rw [hPdef]; ring
  have hLH : LA * (K * MB) ≤ K * la * P := by
    calc LA * (K * MB) ≤ la * MA * (K * MB) :=
          mul_le_mul_of_nonneg_right hla (mul_nonneg (by norm_num) hMB0)
      _ = K * la * P := by rw [hPdef]; ring
  have hu1 : (0 : ℝ) ≤ 1 + u := by norm_num
  have hF1b : F1 ≤ (K * lb * P + T0 * P) * (1 + u) + 1 / 2 ^ 95 * P := by
    rw [hF1]
    have := mul_le_mul_of_nonneg_right (add_le_add hHL hT) hu1
    linarith
  have hF10 : 0 ≤ F1 := by rw [hF1]; positivity
  have hlaP : 0 ≤ la * P := mul_nonneg hla0 hP0.le
  have hlbP : 0 ≤ lb * P := mul_nonneg hlb0 hP0.le
  have hraP : 0 ≤ ra * P := mul_nonneg hra0 hP0.le
  have hrbP : 0 ≤ rb * P := mul_nonneg hrb0 hP0.le
  have hrrP : 0 ≤ ra * rb * P := mul_nonneg (mul_nonneg hra0 hrb0) hP0.le
  have hllP : 0 ≤ la * lb * P := mul_nonneg (mul_nonneg hla0 hlb0) hP0.le
  have hla1 : la * P ≤ P := mul_le_of_le_one_left hP0.le (by linarith)
  have hlb1 : lb * P ≤ P := mul_le_of_le_one_left hP0.le (by linarith)
  have hT0P : T0 * P ≤ P := mul_le_of_le_one_left hP0.le (by rw [hT0]; norm_num)
  have hP1 : P ≤ 2 ^ 40 := by
    rw [hPdef]
    calc MA * MB ≤ 2 ^ 20 * 2 ^ 20 := mul_le_mul hMA hMB hMB0 (by norm_num)
      _ = 2 ^ 40 := by norm_num
  refine pr_dMul hF ha hb (K * MA) (K * MB) Ttl F1 P _ _ hHA hHB le_rfl le_rfl le_rfl ?_ ?_ ?_
  · -- the low part
    have k0 := mul_le_mul_of_nonneg_right (add_le_add hLH hF1b) hu1
    have c1 : K * (1 + u) ≤ 1 + 1 / 2 ^ 18 := by norm_num
    have c2 : K * (1 + u) * (1 + u) ≤ 1 + 1 / 2 ^ 18 := by norm_num
    have c3 : T0 * (1 + u) * (1 + u) + (1 + u) / 2 ^ 95 + 1 / 2 ^ 95 ≤ 2 * u := by
      rw [hT0]; norm_num
    have k1 := mul_le_mul_of_nonneg_right c1 hlaP
    have k2 := mul_le_mul_of_nonneg_right c2 hlbP
    have k3 := mul_le_mul_of_nonneg_right c3 hP0.le
    have hTP : 0 ≤ T0 * P := by rw [hT0]; positivity
    linarith
  · -- the error
    have t1 : (MA + eA) * eB ≤ (rb + ra * rb) * P := by
      calc (MA + eA) * eB ≤ (MA + ra * MA) * (rb * MB) :=
            mul_le_mul (by linarith) hrb heB0 (add_nonneg hMA0 (mul_nonneg hra0 hMA0))
        _ = (rb + ra * rb) * P := by rw [hPdef]; ring
    have t2 : MB * eA ≤ ra * P := by
      calc MB * eA ≤ MB * (ra * MA) := mul_le_mul_of_nonneg_left hra hMB0
        _ = ra * P := by rw [hPdef]; ring
    have t3 : LA * LB ≤ la * lb * P := by
      calc LA * LB ≤ (la * MA) * (lb * MB) := mul_le_mul hla hlb hLB0 (mul_nonneg hla0 hMA0)
        _ = la * lb * P := by rw [hPdef]; ring
    have t4 : u * u * (K * MA * (K * MB)) = u * u * K * K * P := by rw [hKK]; ring
    have t5 : u * (K * MA * LB + Ttl) ≤ u * (K * lb * P + T0 * P) :=
      mul_le_mul_of_nonneg_left (add_le_add hHL hT) (by norm_num)
    have t6 : u * (LA * (K * MB) + F1) ≤
        u * (K * la * P + ((K * lb * P + T0 * P) * (1 + u) + 1 / 2 ^ 95 * P)) :=
      mul_le_mul_of_nonneg_left (add_le_add hLH hF1b) (by norm_num)
    have c1 : u * K ≤ 3 * u := by norm_num
    have c2 : u * K + u * K * (1 + u) ≤ 3 * u := by norm_num
    have c3 : u * u * K * K + u * T0 + u * T0 * (1 + u) + u / 2 ^ 95 + 4 / 2 ^ 95 ≤
        4 * u * u + 1 / 2 ^ 92 := by
      rw [hT0]; norm_num
    have k1 := mul_le_mul_of_nonneg_right c1 hlaP
    have k2 := mul_le_mul_of_nonneg_right c2 hlbP
    have k3 := mul_le_mul_of_nonneg_right c3 hP0.le
    linarith
  · -- no overflow
    have hTP : 0 ≤ T0 * P := by rw [hT0]; positivity
    have k : K * MA * (K * MB) + K * MA * LB + LA * (K * MB) + Ttl + F1 ≤ 8 * P := by
      rw [hKK]
      linarith
    linarith

#print axioms pr_dMul_rel

end Library.Numerics.Float64.Erfc.ErfcRel
