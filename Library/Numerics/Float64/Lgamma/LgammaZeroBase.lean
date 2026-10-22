import LeanExe.ProofKit.GammaReflect
import LeanExe.ProofKit.GammaConvex
import LeanExe.ProofKit.F64Grid
import Library.Numerics.Float64.Tgamma.GammaPi

/-!
Lower bounds on `|lgamma|` at the doubles of an interval `(-n - 1, -n)`, from the values of
`lgamma` at the doubles next to its two zeros.  `lgamma` is convex on the interval
(`GammaConvex.convexOn_lgamma_neg`), positive next to both ends and negative between the zeros.
With `xa < xb` the consecutive doubles around the left zero and `xc < xd` those around the right
zero, every double of the interval lies left of `xa`, between `xb` and `xc`, or right of `xd`
(`F64Grid.grid_split`), so `|lgamma|` there is at least the smallest of the four values
(`interval_bound`).  `interval_bound_right` drops `xa` when the left zero lies between `-n - 1` and
the first double, and `interval_bound_cut` replaces `xc < xd` by a point `xe` where `lgamma` is
negative, for the part of the interval left of `xe`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaZeroBase

open Real Set LeanExe.ProofKit GammaBasic GammaConvex F64Grid CodeLib.IEEE64

/-- The Taylor-model parameters for values at a point: radius 0, 104 bits, at most 60 series terms
with factor below `2 ^ -110`, and `π` within `2 ^ -128`. -/
def cfgZ : TaylorModel.Cfg := ⟨0, 2, 104, 60, 1 / 2 ^ 110, Library.Numerics.Float64.Tgamma.GammaPi.piLo128, Library.Numerics.Float64.Tgamma.GammaPi.piHi128⟩

theorem cfgZ_pi : ((cfgZ.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfgZ.piHi : ℚ) : ℝ) := Library.Numerics.Float64.Tgamma.GammaPi.pi_bounds128

theorem abs_ge_of_neg_dist {n : ℕ} {k : ℕ} (hnk : (2 : ℝ) ^ k ≤ n) {v : ℝ} (hv : v < -n) :
    (2 : ℝ) ^ k ≤ |v| := by
  rw [abs_of_neg (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)]
  linarith

/-- The bound on `|lgamma|` at the doubles of `(-n - 1, -n)` from the four doubles next to its
zeros. -/
theorem interval_bound (n k : ℕ) (hk : k ≤ 52) (hnk : (2 : ℝ) ^ k ≤ n) (ma mc : ℤ)
    {ca cb cc cd : ℝ}
    (hxa : -(n : ℝ) - 1 < ma / 2 ^ (52 - k)) (hxd : ((mc : ℝ) + 1) / 2 ^ (52 - k) < -n)
    (hbc : ((ma : ℝ) + 1) / 2 ^ (52 - k) ≤ mc / 2 ^ (52 - k))
    (hfa : ca ≤ lgamma (ma / 2 ^ (52 - k))) (hfb : lgamma (((ma : ℝ) + 1) / 2 ^ (52 - k)) ≤ -cb)
    (hfc : lgamma (mc / 2 ^ (52 - k)) ≤ -cc) (hfd : cd ≤ lgamma (((mc : ℝ) + 1) / 2 ^ (52 - k)))
    (hca : 0 ≤ ca) (hcb : 0 ≤ cb) (hcc : 0 ≤ cc) (hcd : 0 ≤ cd)
    (w : UInt64) (hlo : -(n : ℝ) - 1 < value w) (hhi : value w < -n) :
    min (min ca cb) (min cc cd) ≤ |lgamma (value w)| := by
  have hcv := convexOn_lgamma_neg n
  have hpos : (0 : ℝ) < 2 ^ (52 - k) := by positivity
  have habs := abs_ge_of_neg_dist hnk hhi
  have hab : (ma : ℝ) / 2 ^ (52 - k) < ((ma : ℝ) + 1) / 2 ^ (52 - k) :=
    (div_lt_div_iff_of_pos_right hpos).mpr (by linarith)
  have hcdx : (mc : ℝ) / 2 ^ (52 - k) < ((mc : ℝ) + 1) / 2 ^ (52 - k) :=
    (div_lt_div_iff_of_pos_right hpos).mpr (by linarith)
  have mxa : (ma : ℝ) / 2 ^ (52 - k) ∈ Ioo (-(n : ℝ) - 1) (-n) := ⟨hxa, by linarith⟩
  have mxb : ((ma : ℝ) + 1) / 2 ^ (52 - k) ∈ Ioo (-(n : ℝ) - 1) (-n) := ⟨by linarith, by linarith⟩
  have mxc : (mc : ℝ) / 2 ^ (52 - k) ∈ Ioo (-(n : ℝ) - 1) (-n) := ⟨by linarith, by linarith⟩
  have mxd : ((mc : ℝ) + 1) / 2 ^ (52 - k) ∈ Ioo (-(n : ℝ) - 1) (-n) := ⟨by linarith, hxd⟩
  have mv : value w ∈ Ioo (-(n : ℝ) - 1) (-n) := ⟨hlo, hhi⟩
  have m1 : min (min ca cb) (min cc cd) ≤ ca := (min_le_left _ _).trans (min_le_left _ _)
  have m2 : min (min ca cb) (min cc cd) ≤ cb := (min_le_left _ _).trans (min_le_right _ _)
  have m3 : min (min ca cb) (min cc cd) ≤ cc := (min_le_right _ _).trans (min_le_left _ _)
  have m4 : min (min ca cb) (min cc cd) ≤ cd := (min_le_right _ _).trans (min_le_right _ _)
  rcases grid_split w hk habs ma with h1 | h1
  · have := convex_left hcv mv mxb h1 hab (hca.trans hfa) (hfb.trans (by linarith))
    rw [abs_of_nonneg (by linarith)]
    linarith
  rcases grid_split w hk habs mc with h2 | h2
  · have := convex_mid hcv mxb mxc h1 h2
    have hneg : lgamma (value w) ≤ -min cb cc := by
      refine this.trans (max_le ?_ ?_)
      · linarith [min_le_left cb cc]
      · linarith [min_le_right cb cc]
    rw [abs_of_nonpos (by linarith [le_min hcb hcc])]
    have : min (min ca cb) (min cc cd) ≤ min cb cc := le_min m2 m3
    linarith
  · have := convex_right hcv mv mxc h2 hcdx (hcd.trans hfd) (hfc.trans (by linarith))
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The bound when the left zero lies between `-n - 1` and the first double: `ma` is the left end
`-n - 1` on the grid. -/
theorem interval_bound_right (n k : ℕ) (hk : k ≤ 52) (hnk : (2 : ℝ) ^ k ≤ n) (ma mc : ℤ)
    {cb cc cd : ℝ}
    (hxa : (ma : ℝ) / 2 ^ (52 - k) = -(n : ℝ) - 1) (hxd : ((mc : ℝ) + 1) / 2 ^ (52 - k) < -n)
    (hbc : ((ma : ℝ) + 1) / 2 ^ (52 - k) ≤ mc / 2 ^ (52 - k))
    (hfb : lgamma (((ma : ℝ) + 1) / 2 ^ (52 - k)) ≤ -cb)
    (hfc : lgamma (mc / 2 ^ (52 - k)) ≤ -cc) (hfd : cd ≤ lgamma (((mc : ℝ) + 1) / 2 ^ (52 - k)))
    (hcb : 0 ≤ cb) (hcc : 0 ≤ cc) (hcd : 0 ≤ cd)
    (w : UInt64) (hlo : -(n : ℝ) - 1 < value w) (hhi : value w < -n) :
    min cb (min cc cd) ≤ |lgamma (value w)| := by
  have hcv := convexOn_lgamma_neg n
  have hpos : (0 : ℝ) < 2 ^ (52 - k) := by positivity
  have habs := abs_ge_of_neg_dist hnk hhi
  have hab : (ma : ℝ) / 2 ^ (52 - k) < ((ma : ℝ) + 1) / 2 ^ (52 - k) :=
    (div_lt_div_iff_of_pos_right hpos).mpr (by linarith)
  have hcdx : (mc : ℝ) / 2 ^ (52 - k) < ((mc : ℝ) + 1) / 2 ^ (52 - k) :=
    (div_lt_div_iff_of_pos_right hpos).mpr (by linarith)
  have mxb : ((ma : ℝ) + 1) / 2 ^ (52 - k) ∈ Ioo (-(n : ℝ) - 1) (-n) := ⟨by linarith, by linarith⟩
  have mxc : (mc : ℝ) / 2 ^ (52 - k) ∈ Ioo (-(n : ℝ) - 1) (-n) := ⟨by linarith, by linarith⟩
  have mv : value w ∈ Ioo (-(n : ℝ) - 1) (-n) := ⟨hlo, hhi⟩
  have m2 : min cb (min cc cd) ≤ cb := min_le_left _ _
  have m3 : min cb (min cc cd) ≤ cc := (min_le_right _ _).trans (min_le_left _ _)
  have m4 : min cb (min cc cd) ≤ cd := (min_le_right _ _).trans (min_le_right _ _)
  rcases grid_split w hk habs ma with h1 | h1
  · linarith
  rcases grid_split w hk habs mc with h2 | h2
  · have := convex_mid hcv mxb mxc h1 h2
    have hneg : lgamma (value w) ≤ -min cb cc := by
      refine this.trans (max_le ?_ ?_)
      · linarith [min_le_left cb cc]
      · linarith [min_le_right cb cc]
    rw [abs_of_nonpos (by linarith [le_min hcb hcc])]
    have : min cb (min cc cd) ≤ min cb cc := le_min m2 m3
    linarith
  · have := convex_right hcv mv mxc h2 hcdx (hcd.trans hfd) (hfc.trans (by linarith))
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- The bound left of a point `xe` of `(-n - 1, -n)` where `lgamma` is negative, from the doubles
next to the left zero. -/
theorem interval_bound_cut (n k : ℕ) (hk : k ≤ 52) (hnk : (2 : ℝ) ^ k ≤ n) (ma : ℤ) {xe : ℝ}
    {ca cb ce : ℝ}
    (hxa : -(n : ℝ) - 1 < ma / 2 ^ (52 - k)) (hxe : xe < -n)
    (hbe : ((ma : ℝ) + 1) / 2 ^ (52 - k) ≤ xe)
    (hfa : ca ≤ lgamma (ma / 2 ^ (52 - k))) (hfb : lgamma (((ma : ℝ) + 1) / 2 ^ (52 - k)) ≤ -cb)
    (hfe : lgamma xe ≤ -ce) (hca : 0 ≤ ca) (hcb : 0 ≤ cb) (hce : 0 ≤ ce)
    (w : UInt64) (hlo : -(n : ℝ) - 1 < value w) (hhi : value w ≤ xe) :
    min ca (min cb ce) ≤ |lgamma (value w)| := by
  have hcv := convexOn_lgamma_neg n
  have hpos : (0 : ℝ) < 2 ^ (52 - k) := by positivity
  have habs := abs_ge_of_neg_dist hnk (lt_of_le_of_lt hhi hxe)
  have hab : (ma : ℝ) / 2 ^ (52 - k) < ((ma : ℝ) + 1) / 2 ^ (52 - k) :=
    (div_lt_div_iff_of_pos_right hpos).mpr (by linarith)
  have mxb : ((ma : ℝ) + 1) / 2 ^ (52 - k) ∈ Ioo (-(n : ℝ) - 1) (-n) := ⟨by linarith, by linarith⟩
  have mxe : xe ∈ Ioo (-(n : ℝ) - 1) (-n) := ⟨by linarith, hxe⟩
  have mv : value w ∈ Ioo (-(n : ℝ) - 1) (-n) := ⟨hlo, by linarith⟩
  have m1 : min ca (min cb ce) ≤ ca := min_le_left _ _
  have m2 : min ca (min cb ce) ≤ cb := (min_le_right _ _).trans (min_le_left _ _)
  have m3 : min ca (min cb ce) ≤ ce := (min_le_right _ _).trans (min_le_right _ _)
  rcases grid_split w hk habs ma with h1 | h1
  · have := convex_left hcv mv mxb h1 hab (hca.trans hfa) (hfb.trans (by linarith))
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have := convex_mid hcv mxb mxe h1 hhi
    have hneg : lgamma (value w) ≤ -min cb ce := by
      refine this.trans (max_le ?_ ?_)
      · linarith [min_le_left cb ce]
      · linarith [min_le_right cb ce]
    rw [abs_of_nonpos (by linarith [le_min hcb hce])]
    have : min ca (min cb ce) ≤ min cb ce := le_min m2 m3
    linarith

#print axioms interval_bound
#print axioms interval_bound_right
#print axioms interval_bound_cut

end Library.Numerics.Float64.Lgamma.LgammaZeroBase
