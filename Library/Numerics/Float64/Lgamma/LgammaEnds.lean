import Library.Numerics.Float64.Lgamma.LgammaFastWalk
import Library.Numerics.Float64.Lgamma.LgammaEndCell
import Library.Numerics.Float64.Lgamma.LgammaEndEncl

/-!
The fast path of `Lgamma.lgammaR` at the 14 ends `x = ±(2k + 1)/4`, `k < 7`, of the windows of the
accurate path, where the accurate path is not within one step.  At each of them the rounding test
of the fast path passes and its result lies within one step of `ln |Γ x|` (`fast_ends`).  The walk
of `LgammaFastWalk.fast_within` reaches the leaf of each input: `LgammaFastMid.mid_bounds` at
`±1/4`, a piece at `3/4` to `13/4` (`pos_end`), and its reflection at `-3/4` to `-13/4`
(`neg_end`, from `LgammaReflCore.refl_core`).  Each leaf bounds the error of `fh + fl` by `R`,
`eps` by `E`, and `|fl|` by `F`, and `end_of_check` turns the bounds into `EndSpec` with
`LgammaEndCell.test_pass` when the kernel checks `CellOK`: the interval of radius
`M ≥ R + E + (F + E)/2^53` around the enclosure of `ln |Γ x|` from `LgammaEndEncl` lies in the
rounding cell of the word `W` of the input.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaEnds
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Lgamma LgammaBranches LgammaWalk LgammaLeaf
  LgammaFastWalk LgammaEndEncl
open Library.Numerics.Float64.Tgamma (floorF)

set_option exponentiation.threshold 4096
set_option linter.auxLemma false

/-- The fast path's `(fh, fl, eps, sign)` passes the rounding test with a finite word within one
step of `L`. -/
def EndSpec (L : ℝ) (r : Float × Float × Float × Float) : Prop :=
  ∃ W : UInt64, Finite W ∧ (r.1 + (r.2.1 + r.2.2.1)).toBits = W ∧
    (r.1 + (r.2.1 - r.2.2.1)).toBits = W ∧ F64SignedRounding.WithinSteps 1 L W

/-- **One step for the code's choice** under `EndSpec`, with no condition on the accurate path. -/
theorem select_ends (fh fl eps sign acc : Float) (L : ℝ) (h : EndSpec L (fh, fl, eps, sign)) :
    F64SignedRounding.WithinSteps 1 L
      (if (fh + (fl + eps) != fh + (fl - eps)) = true then (acc, sign)
        else (fh + (fl + eps), sign)).1.toBits := by
  obtain ⟨W, hW, hub, hlb, hin⟩ := h
  exact LgammaEndCell.select_end fh fl eps sign acc W L hW hub hlb hin

/-- The conditions, checked by the kernel, that put the interval of radius `M` around every number
from `lo` to `hi` in the rounding cell of the finite word `W`. -/
def CellOK (W : UInt64) (lo hi M : ℚ) : Prop :=
  Wasm.IEEE64.isFinite W = true ∧ 1 ≤ W.toNat % 2 ^ 63 ∧ W.toNat % 2 ^ 63 + 1 < 2 ^ 63 ∧
    M ≤ 1 / 2 ^ 54 ∧
    (Wasm.IEEE64.sign W = true → hi < 0 ∧ 1 / 2 ^ 1021 ≤ -hi ∧ -lo < 2 ^ 1021 ∧
      M ≤ -hi / 2 ^ 54 ∧
      PolyBound.ratOfWord (UInt64.ofNat (W.toNat % 2 ^ 63 - 1)) +
        PolyBound.ratOfWord (UInt64.ofNat (W.toNat % 2 ^ 63)) < 2 * (-hi - M) ∧
      2 * (-lo + M) < PolyBound.ratOfWord (UInt64.ofNat (W.toNat % 2 ^ 63)) +
        PolyBound.ratOfWord (UInt64.ofNat (W.toNat % 2 ^ 63 + 1))) ∧
    (Wasm.IEEE64.sign W = false → 0 < lo ∧ 1 / 2 ^ 1021 ≤ lo ∧ hi < 2 ^ 1021 ∧
      M ≤ lo / 2 ^ 54 ∧
      PolyBound.ratOfWord (UInt64.ofNat (W.toNat % 2 ^ 63 - 1)) +
        PolyBound.ratOfWord (UInt64.ofNat (W.toNat % 2 ^ 63)) < 2 * (lo - M) ∧
      2 * (hi + M) < PolyBound.ratOfWord (UInt64.ofNat (W.toNat % 2 ^ 63)) +
        PolyBound.ratOfWord (UInt64.ofNat (W.toNat % 2 ^ 63 + 1)))

instance (W : UInt64) (lo hi M : ℚ) : Decidable (CellOK W lo hi M) := by
  unfold CellOK
  infer_instance

/-- **The rounding test passes** when the bounds `R`, `E`, and `F` of a leaf fit in the radius `M`
of a checked cell. -/
theorem end_of_check (fh fl eps sign : Float) (L R E F : ℝ) (W : UInt64) (lo hi M : ℚ)
    (hfh : Finite fh.toBits) (hfl : Finite fl.toBits) (he : Finite eps.toBits)
    (he0 : 0 ≤ value eps.toBits) (heE : value eps.toBits ≤ E) (hflF : |value fl.toBits| ≤ F)
    (hR : |L - (value fh.toBits + value fl.toBits)| ≤ R) (hM : R + E + (F + E) / 2 ^ 53 ≤ M)
    (hlo : (lo : ℝ) ≤ L) (hhi : L ≤ hi) (hc : CellOK W lo hi M) :
    EndSpec L (fh, fl, eps, sign) := by
  obtain ⟨hfin, hm1, hm2, hM54, hneg, hpos⟩ := hc
  have hFE : F + E ≤ 1 := by
    have h0 := (Rat.cast_le (K := ℝ)).mpr hM54
    push_cast at h0
    have hR0 : 0 ≤ R := (abs_nonneg _).trans hR
    have hE0 : 0 ≤ E := he0.trans heE
    have : (F + E) / 2 ^ 53 ≤ 1 / 2 ^ 54 := by linarith
    have h2 : F + E ≤ 2 ^ 53 / 2 ^ 54 := by
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 ^ 53)
      rw [mul_div_cancel₀ _ (by positivity)] at this
      linarith
    linarith [(by norm_num : (2 : ℝ) ^ 53 / 2 ^ 54 ≤ 1)]
  have hW64 := W.toNat_lt
  have habs : value (UInt64.ofNat (W.toNat % 2 ^ 63)) = |value W| := by
    have : UInt64.ofNat (W.toNat % 2 ^ 63) = Wasm.IEEE64.abs W := by
      apply UInt64.toNat_inj.mp
      rw [F64UpperWord.abs_toNat]
      exact UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
    rw [this, F64UpperWord.value_abs]
  cases hs : Wasm.IEEE64.sign W with
  | false =>
    obtain ⟨p0, p1, p2, p3, p4, p5⟩ := hpos hs
    have q0 := (Rat.cast_lt (K := ℝ)).mpr p0
    have q1 := (Rat.cast_le (K := ℝ)).mpr p1
    have q2 := (Rat.cast_lt (K := ℝ)).mpr p2
    have q3 := (Rat.cast_le (K := ℝ)).mpr p3
    have q4 := (Rat.cast_lt (K := ℝ)).mpr p4
    have q5 := (Rat.cast_lt (K := ℝ)).mpr p5
    push_cast at q0 q1 q2 q3
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_ofNat,
      PolyBound.ratOfWord_cast] at q4 q5
    rw [habs] at q4 q5
    have hL0 : 0 < L := lt_of_lt_of_le q0 hlo
    have hLa : |L| = L := abs_of_pos hL0
    have hd : (lo : ℝ) / 2 ^ 54 ≤ L / 2 ^ 54 := div_le_div_of_nonneg_right hlo (by positivity)
    have hlo' : value (UInt64.ofNat (W.toNat % 2 ^ 63 - 1)) + |value W| <
        2 * (|L| - (R + E + (F + E) / 2 ^ 53)) := by
      rw [hLa]
      calc _ < 2 * ((lo : ℝ) - M) := q4
        _ ≤ _ := by linarith
    have hhi' : 2 * (|L| + (R + E + (F + E) / 2 ^ 53)) <
        |value W| + value (UInt64.ofNat (W.toNat % 2 ^ 63 + 1)) := by
      rw [hLa]
      calc _ ≤ 2 * ((hi : ℝ) + M) := by linarith
        _ < _ := q5
    obtain ⟨hub, hlb, hin⟩ := LgammaEndCell.test_pass fh fl eps W L R E F hfh hfl he he0 heE
      hflF hR hFE (by rw [hLa]; linarith) (by rw [hLa]; linarith) (by rw [hLa]; linarith)
      (by rw [decide_eq_false (not_lt.mpr hL0.le)]; exact hs) hm1 hm2 hlo' hhi'
    exact ⟨W, hfin, hub, hlb, hin⟩
  | true =>
    obtain ⟨p0, p1, p2, p3, p4, p5⟩ := hneg hs
    have q0 := (Rat.cast_lt (K := ℝ)).mpr p0
    have q1 := (Rat.cast_le (K := ℝ)).mpr p1
    have q2 := (Rat.cast_lt (K := ℝ)).mpr p2
    have q3 := (Rat.cast_le (K := ℝ)).mpr p3
    have q4 := (Rat.cast_lt (K := ℝ)).mpr p4
    have q5 := (Rat.cast_lt (K := ℝ)).mpr p5
    push_cast at q0 q1 q2 q3
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sub, Rat.cast_neg, Rat.cast_ofNat,
      PolyBound.ratOfWord_cast] at q4 q5
    rw [habs] at q4 q5
    have hL0 : L < 0 := lt_of_le_of_lt hhi q0
    have hLa : |L| = -L := abs_of_neg hL0
    have hd : -(hi : ℝ) / 2 ^ 54 ≤ -L / 2 ^ 54 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hlo' : value (UInt64.ofNat (W.toNat % 2 ^ 63 - 1)) + |value W| <
        2 * (|L| - (R + E + (F + E) / 2 ^ 53)) := by
      rw [hLa]
      calc _ < 2 * (-(hi : ℝ) - M) := by linarith [q4]
        _ ≤ _ := by linarith
    have hhi' : 2 * (|L| + (R + E + (F + E) / 2 ^ 53)) <
        |value W| + value (UInt64.ofNat (W.toNat % 2 ^ 63 + 1)) := by
      rw [hLa]
      calc _ ≤ 2 * (-(lo : ℝ) + M) := by linarith
        _ < _ := by linarith [q5]
    obtain ⟨hub, hlb, hin⟩ := LgammaEndCell.test_pass fh fl eps W L R E F hfh hfl he he0 heE
      hflF hR hFE (by rw [hLa]; linarith) (by rw [hLa]; linarith) (by rw [hLa]; linarith)
      (by rw [decide_eq_true hL0]; exact hs) hm1 hm2 hlo' hhi'
    exact ⟨W, hfin, hub, hlb, hin⟩

/-! ### The leaves -/

/-- The radius for the leaf at `±1/4`. -/
def midM : ℚ := 1 / 2 ^ 59 + 1 / 2 ^ 62 + (1 / 2 ^ 19 + 1 / 2 ^ 62) / 2 ^ 53

/-- **The leaf at `±1/4`**, from the bounds of `LgammaFastMid.mid_bounds`. -/
theorem mid_end (S1 S2 E sign : Float) (L : ℝ) (hs1 : Finite S1.toBits) (hs2 : Finite S2.toBits)
    (hsE : Finite E.toBits) (hE1 : 1 / 2 ^ 73 ≤ value E.toBits)
    (hE2 : value E.toBits ≤ 1 / 2 ^ 62) (hS2 : |value S2.toBits| ≤ 1 / 2 ^ 19)
    (hE : |L - (value S1.toBits + value S2.toBits)| ≤ 1 / 2 ^ 59) (W : UInt64) (lo hi : ℚ)
    (hlo : (lo : ℝ) ≤ L) (hhi : L ≤ hi) (hc : CellOK W lo hi midM) :
    EndSpec L (S1, S2, E, sign) :=
  end_of_check S1 S2 E sign L (1 / 2 ^ 59) (1 / 2 ^ 62) (1 / 2 ^ 19) W lo hi midM hs1 hs2 hsE
    (le_trans (by positivity) hE1) hE2 hS2 hE (by simp only [midM]; push_cast; rfl) hlo hhi hc

/-- The radius for a piece at a positive end. -/
def posM (lo hi : ℚ) : ℚ :=
  3 * ((max |lo| |hi| + 1 / 2 ^ 37) / 2 ^ 63 + 1 / 2 ^ 78) +
    (1 / 2 ^ 38 + ((max |lo| |hi| + 1 / 2 ^ 37) / 2 ^ 63 + 1 / 2 ^ 78)) / 2 ^ 53

/-- **The leaf at a positive end**: a piece. -/
theorem pos_end (x : Float) (t : Float × Float × Float) (h4 : value x.toBits ≤ 4)
    (hl : LeafSpec (value x.toBits) t) (sign : Float) (W : UInt64) (lo hi : ℚ)
    (hlo : (lo : ℝ) ≤ Real.log (Real.Gamma (value x.toBits)))
    (hhi : Real.log (Real.Gamma (value x.toBits)) ≤ hi) (hc : CellOK W lo hi (posM lo hi)) :
    EndSpec (Real.log (Real.Gamma (value x.toBits))) (t.1, t.2.1, t.2.2, sign) := by
  obtain ⟨h1, h2, h3, hcase⟩ := hl
  rcases hcase with ⟨-, hfb, hlb, helo, hehi, hpos⟩ | ⟨ha, -⟩
  swap
  · linarith
  set L := Real.log (Real.Gamma (value x.toBits)) with hLdef
  have hLg : GammaBasic.lgamma (value x.toBits) = L := rfl
  rw [hLg] at hpos
  have hLm : |L| ≤ max |(lo : ℝ)| |(hi : ℝ)| := abs_le_max_abs_abs hlo hhi
  set Φ := max |(lo : ℝ)| |(hi : ℝ)| + 1 / 2 ^ 37 with hΦ
  have hR : |L - (value t.1.toBits + value t.2.1.toBits)| ≤ 2 * value t.2.2.toBits := by
    have : 0 ≤ |value t.1.toBits| / 2 ^ 65 := by positivity
    linarith
  have hfh : |value t.1.toBits| ≤ Φ := by
    have a := abs_sub_abs_le_abs_sub (value t.1.toBits + value t.2.1.toBits) L
    rw [abs_sub_comm] at a
    have c : |value t.1.toBits| / 2 ^ 63 ≤ 16 / 2 ^ 63 :=
      div_le_div_of_nonneg_right hfb (by positivity)
    have d := abs_sub (value t.1.toBits + value t.2.1.toBits) (value t.2.1.toBits)
    rw [add_sub_cancel_right] at d
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 38 + 2 * (16 / 2 ^ 63 + 1 / 2 ^ 78) ≤ 1 / 2 ^ 37)]
  set E := Φ / 2 ^ 63 + 1 / 2 ^ 78 with hE
  have heE : value t.2.2.toBits ≤ E := by
    have : |value t.1.toBits| / 2 ^ 63 ≤ Φ / 2 ^ 63 :=
      div_le_div_of_nonneg_right hfh (by positivity)
    linarith
  have he0 : 0 ≤ value t.2.2.toBits := by
    have : 0 ≤ |value t.1.toBits| * (869 / 10 ^ 22) := by positivity
    linarith
  refine end_of_check t.1 t.2.1 t.2.2 sign L (2 * E) E (1 / 2 ^ 38) W lo hi (posM lo hi) h1 h2 h3
    he0 heE hlb (by linarith) ?_ hlo hhi hc
  simp only [posM]
  push_cast
  rw [hE, hΦ]
  apply le_of_eq
  ring

/-- Bounds of the leaf at a negative end in terms of enclosures `lo ≤ ln |Γ x| ≤ hi` and
`glo ≤ ln Γ (-x) ≤ ghi`: `gPhi` bounds `|fh|` of the piece at `-x`, `leafE` its `eps`, and
`lam` the logarithm `ln (-x sin (π x)/π)` that the reflection adds. -/
def gPhi (glo ghi : ℚ) : ℚ := max |glo| |ghi| + 1 / 2 ^ 37

def leafE (glo ghi : ℚ) : ℚ := gPhi glo ghi / 2 ^ 63 + 1 / 2 ^ 78

def lam (lo hi glo ghi : ℚ) : ℚ := max |lo| |hi| + max |glo| |ghi| + 1 / 2 ^ 19

/-- The factor `8 · 10^-22` of the reflection's `eps`. -/
def c8 : ℚ := PolyBound.ratOfWord 0x3B8E392010175EE6

/-- The rounding errors of the reflection's `eps`: of the product, with `|ln| ≤ 43`, and of the
sum. -/
def negEm : ℚ := 43 * c8 / 2 ^ 53 + 1 / 2 ^ 1075

def negBs : ℚ := 16 / 2 ^ 63 + 1 / 2 ^ 78 + 43 * c8 + negEm

def negE (lo hi glo ghi : ℚ) : ℚ :=
  leafE glo ghi + lam lo hi glo ghi * c8 + negEm + negBs / 2 ^ 53

def negR (glo ghi : ℚ) : ℚ :=
  2 * leafE glo ghi + 114 / 100 / 2 ^ 71 / (225 / 1000) + 2 / 10 ^ 21 +
    (3 * (1 / 2 ^ 38 + 1 / 2 ^ 20) + 60 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53

def negF : ℚ := (1 / 2 ^ 38 + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) + 60 / 2 ^ 51 + 1 / 2 ^ 1073

/-- The radius for the reflection of a piece at a negative end. -/
def negM (lo hi glo ghi : ℚ) : ℚ :=
  negR glo ghi + negE lo hi glo ghi + (negF + negE lo hi glo ghi) / 2 ^ 53

/-- `sin (π φ)/π` at the fractional parts 1/4 and 3/4 is at least `0.225`. -/
theorem s_ge : (225 / 1000 : ℝ) ≤ √2 / 2 / Real.pi := by
  have h1 : (1414 / 1000 : ℝ) ≤ √2 := by
    rw [show (1414 / 1000 : ℝ) = √((1414 / 1000) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2 := Real.pi_lt_d4
  rw [le_div_iff₀ Real.pi_pos]
  linarith

set_option maxHeartbeats 1000000 in
/-- **The leaf at a negative end**: the reflection of a piece. -/
theorem neg_end (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (x : Float) (hx : Finite x.toBits)
    (hneg : value x.toBits ≤ -1 / 2) (h4 : -4 < value x.toBits)
    (hint : ∀ n : ℤ, value x.toBits ≠ n)
    (hs : Real.sin (Real.pi * Int.fract (value x.toBits)) = √2 / 2)
    (t : Float × Float × Float) (hl : LeafSpec (-value x.toBits) t) (A B C D : Float × Float)
    (hA : A = Lgamma.asSinpipid Lgamma.sinpiTable (x - floorF x))
    (hB : B = Tgamma.mulDDD (-x) A.1 A.2) (hC : C = Lgamma.asLogd Tgamma.logdTable B.1)
    (hD : D = Tgamma.sumDD t.1 t.2.1 C.1 (C.2 + B.2 / B.1)) (sign : Float) (W : UInt64)
    (lo hi glo ghi : ℚ) (hlo : (lo : ℝ) ≤ Real.log (Real.Gamma (value x.toBits)))
    (hhi : Real.log (Real.Gamma (value x.toBits)) ≤ hi)
    (hglo : (glo : ℝ) ≤ GammaBasic.lgamma (-value x.toBits))
    (hghi : GammaBasic.lgamma (-value x.toBits) ≤ ghi)
    (hc : CellOK W lo hi (negM lo hi glo ghi)) :
    EndSpec (Real.log (Real.Gamma (value x.toBits)))
      (-D.1, -D.2, t.2.2 + C.1.abs * Float.ofBits 0x3B8E392010175EE6, sign) := by
  have h52 : -2 ^ 52 < value x.toBits := by linarith
  obtain ⟨hf1, hf2, hf3, he1000, -⟩ :=
    neg_leaf hF hL hS x hx hneg h52 hint t hl A B C D hA hB hC hD sign
  obtain ⟨h1, h2, h3, hcase⟩ := hl
  rcases hcase with ⟨-, hfb, hlb, helo, hehi, hpos⟩ | ⟨ha, -⟩
  swap
  · linarith
  obtain ⟨hC1, hD1, hD2, hC43, hD1b, hC1e, hD2b, ρ, hρ, hcore⟩ :=
    LgammaReflCore.refl_core hF hL hS x hx h52 hneg hint t.1 t.2.1 h1 h2
      (by linarith [(by norm_num : (16 : ℝ) ≤ 2 ^ 897)])
      (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 38 ≤ 2 ^ 700)]) A B C D hA hB hC hD
  set v := value x.toBits with hvdef
  set L := Real.log (Real.Gamma v) with hLdef
  have hrefl := LgammaReflCore.refl_L v (by linarith) hint
  rw [← hLdef] at hrefl
  rw [hs] at hrefl hcore hC1e hρ
  set T := Real.log (-v * (√2 / 2 / Real.pi)) with hT
  -- the bounds on `|L|`, `ln Γ (-x)`, and the leaf
  have hLm : |L| ≤ max |(lo : ℝ)| |(hi : ℝ)| := abs_le_max_abs_abs hlo hhi
  have hGm : |GammaBasic.lgamma (-v)| ≤ max |(glo : ℝ)| |(ghi : ℝ)| :=
    abs_le_max_abs_abs hglo hghi
  have hR0 : |GammaBasic.lgamma (-v) - (value t.1.toBits + value t.2.1.toBits)| ≤
      2 * value t.2.2.toBits := by
    have : 0 ≤ |value t.1.toBits| / 2 ^ 65 := by positivity
    linarith
  have hfh : |value t.1.toBits| ≤ (gPhi glo ghi : ℝ) := by
    simp only [gPhi]
    push_cast
    have a := abs_sub_abs_le_abs_sub (value t.1.toBits + value t.2.1.toBits)
      (GammaBasic.lgamma (-v))
    rw [abs_sub_comm] at a
    have c : |value t.1.toBits| / 2 ^ 63 ≤ 16 / 2 ^ 63 :=
      div_le_div_of_nonneg_right hfb (by positivity)
    have d := abs_sub (value t.1.toBits + value t.2.1.toBits) (value t.2.1.toBits)
    rw [add_sub_cancel_right] at d
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 38 + 2 * (16 / 2 ^ 63 + 1 / 2 ^ 78) ≤ 1 / 2 ^ 37)]
  have hel : value t.2.2.toBits ≤ (leafE glo ghi : ℝ) := by
    simp only [leafE]
    push_cast
    have : |value t.1.toBits| / 2 ^ 63 ≤ (gPhi glo ghi : ℝ) / 2 ^ 63 :=
      div_le_div_of_nonneg_right hfh (by positivity)
    linarith
  have he0 : 0 ≤ value t.2.2.toBits := by
    have : 0 ≤ |value t.1.toBits| * (869 / 10 ^ 22) := by positivity
    linarith
  -- the logarithm of the reflection
  have hlam : |value C.1.toBits| ≤ (lam lo hi glo ghi : ℝ) := by
    simp only [lam]
    push_cast
    have hTL : T = -L - GammaBasic.lgamma (-v) := by rw [hrefl]; ring
    have a := abs_sub_abs_le_abs_sub (value C.1.toBits) T
    have b : |T| ≤ |L| + |GammaBasic.lgamma (-v)| := by
      rw [hTL]
      have := abs_sub (-L) (GammaBasic.lgamma (-v))
      rwa [abs_neg] at this
    linarith
  -- `eps` of the reflection
  have hc8f : Wasm.IEEE64.isFinite 0x3B8E392010175EE6 = true := by decide
  have hc8v : value (Float.ofBits 0x3B8E392010175EE6).toBits = (c8 : ℝ) := by
    rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ hc8f]
    rfl
  have hc8 : (0 : ℚ) ≤ c8 ∧ c8 ≤ 1 / 10 ^ 21 := by decide +kernel
  have hc8a : (0 : ℝ) ≤ c8 := by exact_mod_cast hc8.1
  have hc8b := (Rat.cast_le (K := ℝ)).mpr hc8.2
  push_cast at hc8b
  obtain ⟨haf, hav⟩ := Library.Numerics.Float64.Sinh.SinhWords.abs_float C.1 hC1
  have ha := Library.Numerics.Float64.Tgamma.TgammaDD.fapprox_self C.1.abs haf
  rw [hav] at ha
  have hb := Library.Numerics.Float64.Tgamma.TgammaDD.fapprox_self _ (Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ hc8f)
  rw [hc8v] at hb
  have hm := fapprox_mul ha hb 43 c8 (by rw [abs_abs]; exact hC43) (by rw [abs_of_nonneg hc8a])
    (43 * c8) (by simp) (by linarith [(by norm_num : (43 : ℝ) * (1 / 10 ^ 21) < 2 ^ 1022)])
  simp only [zero_mul, mul_zero, zero_add, add_zero] at hm
  have hfe : value t.2.2.toBits ≤ 16 / 2 ^ 63 + 1 / 2 ^ 78 := by
    have : |value t.1.toBits| / 2 ^ 63 ≤ 16 / 2 ^ 63 :=
      div_le_div_of_nonneg_right hfb (by positivity)
    linarith
  have hpc : 0 ≤ |value C.1.toBits| * (c8 : ℝ) := mul_nonneg (abs_nonneg _) hc8a
  have hpc' : |value C.1.toBits| * (c8 : ℝ) ≤ 43 * c8 := mul_le_mul_of_nonneg_right hC43 hc8a
  have hpl : |value C.1.toBits| * (c8 : ℝ) ≤ lam lo hi glo ghi * c8 :=
    mul_le_mul_of_nonneg_right hlam hc8a
  have hsum := fapprox_add (Library.Numerics.Float64.Tgamma.TgammaDD.fapprox_self t.2.2 h3) hm (negBs : ℝ) (by
      simp only [negBs, negEm]
      push_cast
      rw [abs_of_nonneg (by linarith)]
      linarith) (by
      simp only [negBs, negEm]
      push_cast
      linarith [(by norm_num : (16 : ℝ) / 2 ^ 63 + 1 / 2 ^ 78 + 43 * (1 / 10 ^ 21) +
        (43 * (1 / 10 ^ 21) / 2 ^ 53 + 1 / 2 ^ 1075) < 2 ^ 1023)])
  have heps : value (t.2.2 + C.1.abs * Float.ofBits 0x3B8E392010175EE6).toBits ≤
      (negE lo hi glo ghi : ℝ) := by
    have h := (abs_le.mp hsum.2).2
    simp only [negE, negEm]
    push_cast
    linarith
  -- the error of the reflection
  obtain ⟨-, hn1⟩ := LgammaFastTiny.neg_float D.1 hD1
  obtain ⟨-, hn2⟩ := LgammaFastTiny.neg_float D.2 hD2
  have hD60 : |value D.1.toBits| ≤ 60 := by
    have : (|value t.1.toBits| + 43) * (1 + 1 / 2 ^ 51) ≤ 59 * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith [(by norm_num : (59 : ℝ) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ≤ 60)]
  have hρm : ρ ≤ 114 / 100 / 2 ^ 71 / (225 / 1000) := by
    rcases hρ with h | ⟨-, h⟩
    · rw [h]
      norm_num
    · rw [h]
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) s_ge
  have hR : |L - (value (-D.1).toBits + value (-D.2).toBits)| ≤ (negR glo ghi : ℝ) := by
    rw [hn1, hn2, hrefl]
    rw [show -(GammaBasic.lgamma (-v) + T) - (-value D.1.toBits + -value D.2.toBits) =
      -(GammaBasic.lgamma (-v) + T - (value D.1.toBits + value D.2.toBits)) by ring, abs_neg]
    have hin : (3 * (|value t.2.1.toBits| + 1 / 2 ^ 20) + |value D.1.toBits| / 2 ^ 52 +
        1 / 2 ^ 1074) / 2 ^ 53 ≤
        (3 * (1 / 2 ^ 38 + 1 / 2 ^ 20) + 60 / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 := by
      have : |value D.1.toBits| / 2 ^ 52 ≤ 60 / 2 ^ 52 :=
        div_le_div_of_nonneg_right hD60 (by positivity)
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    simp only [negR]
    push_cast
    linarith
  have hFb : |value (-D.2).toBits| ≤ (negF : ℝ) := by
    rw [hn2, abs_neg]
    have : (|value t.2.1.toBits| + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) ≤
        (1 / 2 ^ 38 + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have : |value D.1.toBits| / 2 ^ 51 ≤ 60 / 2 ^ 51 :=
      div_le_div_of_nonneg_right hD60 (by positivity)
    simp only [negF]
    push_cast
    linarith
  refine end_of_check (-D.1) (-D.2) _ sign L (negR glo ghi) (negE lo hi glo ghi) negF W lo hi
    (negM lo hi glo ghi) hf1 hf2 hf3 (le_trans (by positivity) he1000) heps hFb hR ?_ hlo hhi hc
  simp only [negM]
  push_cast
  exact le_rfl

/-- A quarter of an odd number is not a natural number. -/
theorem odd_quarter (k m : ℕ) (h : ((2 * k + 1) / 4 : ℝ) = m) : False := by
  have h' : ((2 * k + 1 : ℕ) : ℝ) = ((4 * m : ℕ) : ℝ) := by
    push_cast
    linarith
  have := Nat.cast_injective h'
  omega

set_option maxHeartbeats 4000000 in
/-- **The fast path at the 14 ends** `x = ±(2k + 1)/4`, `k < 7`: the rounding test passes, and the
result lies within one step of `ln |Γ x|`. -/
theorem fast_ends (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (hPF : LgammaApprox.PieceFact)
    (hAP : LgammaApprox.AccPolyFact) (x : Float) (hx : Finite x.toBits)
    (hk : ∃ k : ℕ, k < 7 ∧ |value x.toBits| = (2 * k + 1) / 4)
    (h1 : ¬ x.toBits <<< 1 ≥ 0xFEAEA9B24F16A34C)
    (h2 : ¬ (floorF x == x && x ≤ 0.0) = true)
    (h3 : ¬ (floorF x == x && (x == 1.0 || x == 2.0)) = true) :
    F64SignedRounding.WithinSteps 1 (Real.log (Real.Gamma (value x.toBits)))
      (lgammaR x).1.toBits := by
  obtain ⟨k, hk7, hkv⟩ := hk
  have hk6 : (k : ℝ) ≤ 6 := by exact_mod_cast (by omega : k ≤ 6)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hq1 : 1 / 4 ≤ |value x.toBits| := by rw [hkv]; linarith
  have hq2 : |value x.toBits| ≤ 13 / 4 := by rw [hkv]; linarith
  have hv0 : value x.toBits ≠ 0 := by
    intro h
    rw [h, abs_zero] at hq1
    linarith
  have hint : value x.toBits < 0 → ∀ n : ℤ, value x.toBits ≠ n := by
    intro _ n hn
    rw [hn] at hkv
    have h4 : ((4 * |n| : ℤ) : ℝ) = ((2 * k + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h4' : 4 * |n| = ((2 * k + 1 : ℕ) : ℤ) := by exact_mod_cast h4
    push_cast at h4'
    generalize |n| = m at h4'
    omega
  have hv1' : |value x.toBits| ≠ ((1 : ℕ) : ℝ) :=
    fun h => odd_quarter k 1 (by rw [← hkv, h])
  have hv2' : |value x.toBits| ≠ ((2 : ℕ) : ℝ) :=
    fun h => odd_quarter k 2 (by rw [← hkv, h])
  obtain ⟨haf, hav⟩ := Library.Numerics.Float64.Sinh.SinhWords.abs_float x hx
  have hfb := fin_bits _ hx
  have habsN : (x.abs.toBits).toNat = x.toBits.toNat % 9223372036854775808 := by
    rw [F64Bits.toBits_abs, F64UpperWord.abs_toNat]; rfl
  have hsign : (x.toBits >>> 63 == 1) = true ↔ value x.toBits < 0 := by
    constructor
    · intro hn
      rcases lt_or_gt_of_ne hv0 with h | h
      · exact h
      · have hs := F64Exact.sign_of_pos x.toBits h
        simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not] at hs
        exact absurd ((LgammaSpecial.sign_test _).mp hn) hs
    · intro hneg
      by_contra hn
      have hs : Wasm.IEEE64.sign x.toBits = false := by
        simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
        intro h; exact hn ((LgammaSpecial.sign_test _).mpr h)
      have := F64TwoSum.value_nonneg_of_sign _ hs
      linarith
  unfold lgammaR
  rewrite [lgammaWith.eq_1, ite_eq_right h1]
  extract_lets fx au sgn z z2 z4 q0 q2 q4 q6 ax zh zl z2h z4h q0s q2s fls j0 z0
  have h2' : ¬ (fx == x && x ≤ 0.0) = true := h2
  have h3' : ¬ (fx == x && (x == 1.0 || x == 2.0)) = true := h3
  rewrite [ite_eq_right h2', ite_eq_right h3']
  split
  next fh fl eps sign heq =>
  extract_lets ub lb
  refine select_ends fh fl eps sign _ _ ?_
  rw [← heq]
  clear heq
  have hauN : au.toNat = x.toBits.toNat % 9223372036854775808 / 137438953472 := au_nat x.toBits
  walk_step
  · -- below `1/2` in magnitude: `x = ±1/4`
    intro hc
    rw [LgammaPieceIdx.tab0, UInt64.lt_iff_toNat_lt] at hc
    simp only [UInt64.reduceToNat] at hc
    have hhalf : |value x.toBits| < 1 / 2 := abs_lt_word _ (0x3FE0000000000000 : UInt64) _
      LgammaSign.half_word (by decide) (by simp only [UInt64.reduceToNat]; omega)
    have hk0' : k = 0 := by
      by_contra hne
      have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      linarith
    subst hk0'
    norm_num at hkv
    walk_step; intro lh ll hlh
    walk_step
    · intro ht
      rw [UInt64.lt_iff_toNat_lt] at ht
      simp only [UInt64.reduceToNat] at ht
      have := abs_lt_word x.toBits _ _ w75 (by decide) (by simp only [UInt64.reduceToNat]; omega)
      exfalso
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 75 < 1 / 4)]
    · intro ht
      rw [UInt64.lt_iff_toNat_lt] at ht
      simp only [UInt64.reduceToNat] at ht
      walk_step
      · intro hs
        rw [UInt64.lt_iff_toNat_lt] at hs
        simp only [UInt64.reduceToNat] at hs
        have := abs_lt_word x.toBits _ _ w5 (by decide) (by simp only [UInt64.reduceToNat]; omega)
        exfalso
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 5 < 1 / 4)]
      · intro hs
        rw [UInt64.lt_iff_toNat_lt] at hs
        simp only [UInt64.reduceToNat] at hs
        walk_step; intro t xl htx
        walk_step; intro au2 hau2
        walk_step; intro j hj
        walk_step; intro zz hzz
        walk_step; intro p1 p2 hP
        walk_step; intro q1 q2 hQ
        walk_step; intro e he
        walk_step; intro s1 s2 hS'
        rw [hzz, hj, hau2] at hP
        rw [hj, hau2] at hQ
        rw [he]
        obtain ⟨hs1, hs2, hsE, hE1, hE2, hS2, -, -, hE⟩ :=
          LgammaFastMid.mid_bounds hF hL hPF x hx
          (by rw [F64Order.absBits_toNat]; simp only [Nat.reducePow]; omega)
          (by rw [F64Order.absBits_toNat]; simp only [Nat.reducePow]; omega)
          lh ll hlh (piece mainTable (t.toBits >>> 37)) (by rw [htx]) (p1, p2) (q1, q2)
          (s1, s2) (by rw [htx]; exact hP.symm) hQ.symm hS'.symm
        rcases lt_or_gt_of_ne hv0 with hneg | hpos
        · have hv : value x.toBits = -1 / 4 := by
            rw [abs_of_neg hneg] at hkv
            linarith
          have he := e_n1 hAP
          exact mid_end s1 s2 _ sgn _ hs1 hs2 hsE hE1 hE2 hS2 hE 0x3FF96EE685DEFB2D
            (15895753125511859903154736983051556857406 / 10 ^ 40 : ℚ)
            (15895753125511859903163207312524099860810 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by decide +kernel)
        · have hv : value x.toBits = 1 / 4 := by
            rw [abs_of_pos hpos] at hkv
            linarith
          have he := e_p1 hAP
          exact mid_end s1 s2 _ sgn _ hs1 hs2 hsE hE1 hE2 hS2 hE 0x3FF49BBD81C16EFB
            (12880225246980774573701869237460901457553 / 10 ^ 40 : ℚ)
            (12880225246980774573710339566933444460957 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by decide +kernel)
  · -- from `1/2` on
    intro hc
    rw [LgammaPieceIdx.tab0, UInt64.lt_iff_toNat_lt] at hc
    simp only [UInt64.reduceToNat] at hc
    have hhalf : 1 / 2 ≤ |value x.toBits| := word_le_abs _ (0x3FE0000000000000 : UInt64) _
      LgammaSign.half_word (by decide) (by simp only [UInt64.reduceToNat]; omega)
    have hax : value ax.toBits = |value x.toBits| := hav
    have haxN : ax.toBits.toNat / 137438953472 = au.toNat := by rw [hauN, ← habsN]
    have haxb : ax.toBits.toNat < 0x7FF0000000000000 := by
      have : ax.toBits.toNat = x.toBits.toNat % 9223372036854775808 := habsN
      omega
    have hk1 : 1 ≤ k := by
      by_contra hne
      have : k = 0 := by omega
      subst this
      norm_num at hkv
      linarith
    walk_bridge (LeafSpec (value ax.toBits))
    · walk_step
      · -- Stirling's series, which starts above `8`
        intro h19
        rw [tab19, ge_iff_le, UInt64.le_iff_toNat_le] at h19
        simp only [UInt64.reduceToNat] at h19
        have hb19 : (LgammaApprox.border 19 : ℝ) ≤ value ax.toBits :=
          LgammaFastMid.border_le 19 (by norm_num) ax.toBits haxb
            (by rw [haxN, LgammaPieceIdx.tw_ends.2]; exact h19)
        have hb19' := LgammaPiecePoly.qcast_le LgammaStir.border19
        push_cast at hb19'
        exfalso
        rw [hax] at hb19
        linarith
      · -- a piece
        intro h19
        rw [tab19, ge_iff_le, UInt64.le_iff_toNat_le, not_le] at h19
        simp only [UInt64.reduceToNat] at h19
        walk_step; intro p1 p2 hP
        walk_step; intro q1 q2 hQ
        walk_step; intro r1 r2 hR
        obtain ⟨k', hk', hkj, hk0, hk1⟩ := LgammaPieceIdx.piece_spec au (by omega) (by omega)
        have hb0 : (LgammaApprox.border k' : ℝ) ≤ value ax.toBits :=
          LgammaFastMid.border_le k' (by omega) ax.toBits haxb (by rw [haxN]; exact hk0)
        have hb1 : value ax.toBits ≤ (LgammaApprox.border (k' + 1) : ℝ) :=
          LgammaFastMid.le_border (k' + 1) (by omega) ax.toBits haxb (by rw [haxN]; exact hk1)
        exact leaf_piece hF hPF ax haf k' hk' j0 hkj hb0 hb1 (by rw [hax]; exact_mod_cast hv1')
          (by rw [hax]; exact_mod_cast hv2') (p1, p2) (q1, q2) (r1, r2) hP.symm hQ.symm hR.symm
    · intro fh fl eps hl
      walk_step
      · intro hn
        have hneg : value x.toBits < 0 := hsign.mp hn
        walk_step; intro sh sl hA
        walk_step; intro sh2 sl2 hB
        walk_step; intro lh ll hC
        walk_step; intro dh dl hD
        have hint' := hint hneg
        rw [hax, abs_of_neg hneg] at hl
        interval_cases k
        · -- `x = -3/4`
          have hv : value x.toBits = -3 / 4 := by
            rw [abs_of_neg hneg] at hkv
            norm_num at hkv
            linarith
          have hv' : -value x.toBits = 3 / 4 := by rw [hv]; norm_num
          have he := e_n3 hAP
          have hg := e_p3 hAP
          refine neg_end hF hL hS x hx (by linarith) (by linarith) hint' ?_ (fh, fl, eps) hl
            (sh, sl) (sh2, sl2) (lh, ll) (dh, dl) hA.symm hB.symm hC.symm hD.symm _
            0x3FF93616060EA5E0
            (15757045971498583848094059297399175772578 / 10 ^ 40 : ℚ)
            (15757045971498583848102529626871718775999 / 10 ^ 40 : ℚ)
            (2032809514312953714810094553888025495898 / 10 ^ 40 : ℚ)
            (2032809514312953714818564883360568499296 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by rw [hv']; push_cast; exact hg.1) (by rw [hv']; push_cast; exact hg.2)
            (by decide +kernel)
          rw [LgammaEndEncl.fract_eq _ (1 / 4) (-1) (by rw [hv]; norm_num) (by norm_num)
            (by norm_num), LgammaEndEncl.sin_q1]
        · -- `x = -5/4`
          have hv : value x.toBits = -5 / 4 := by
            rw [abs_of_neg hneg] at hkv
            norm_num at hkv
            linarith
          have hv' : -value x.toBits = 5 / 4 := by rw [hv]; norm_num
          have he := e_n5 hAP
          have hg := e_p5 hAP
          refine neg_end hF hL hS x hx (by linarith) (by linarith) hint' ?_ (fh, fl, eps) hl
            (sh, sl) (sh2, sl2) (lh, ll) (dh, dl) hA.symm hB.symm hC.symm hD.symm _
            0x3FF5DCE78CEBA7E9
            (13664317612369762345491786079953211823650 / 10 ^ 40 : ℚ)
            (13664317612369762345500256409425754827068 / 10 ^ 40 : ℚ)
            (-982718364218131614642773191702629903955 / 10 ^ 40 : ℚ)
            (-982718364218131614634302862230086900557 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by rw [hv']; push_cast; exact hg.1) (by rw [hv']; push_cast; exact hg.2)
            (by decide +kernel)
          rw [LgammaEndEncl.fract_eq _ (3 / 4) (-2) (by rw [hv]; norm_num) (by norm_num)
            (by norm_num), LgammaEndEncl.sin_q3]
        · -- `x = -7/4`
          have hv : value x.toBits = -7 / 4 := by
            rw [abs_of_neg hneg] at hkv
            norm_num at hkv
            linarith
          have hv' : -value x.toBits = 7 / 4 := by rw [hv]; norm_num
          have he := e_n7 hAP
          have hg := e_p7 hAP
          refine neg_end hF hL hS x hx (by linarith) (by linarith) hint' ?_ (fh, fl, eps) hl
            (sh, sl) (sh2, sl2) (lh, ll) (dh, dl) hA.symm hB.symm hC.symm hD.symm _
            0x3FF041E656D68578
            (10160888092144356985372468797922095332632 / 10 ^ 40 : ℚ)
            (10160888092144356985406350115812267346222 / 10 ^ 40 : ℚ)
            (-844011210204855559594801000259063324223 / 10 ^ 40 : ℚ)
            (-844011210204855559560919682368891310653 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by rw [hv']; push_cast; exact hg.1) (by rw [hv']; push_cast; exact hg.2)
            (by decide +kernel)
          rw [LgammaEndEncl.fract_eq _ (1 / 4) (-2) (by rw [hv]; norm_num) (by norm_num)
            (by norm_num), LgammaEndEncl.sin_q1]
        · -- `x = -9/4`
          have hv : value x.toBits = -9 / 4 := by
            rw [abs_of_neg hneg] at hkv
            norm_num at hkv
            linarith
          have hv' : -value x.toBits = 9 / 4 := by rw [hv]; norm_num
          have he := e_n9 hAP
          have hg := e_p9 hAP
          refine neg_end hF hL hS x hx (by linarith) (by linarith) hint' ?_ (fh, fl, eps) hl
            (sh, sl) (sh2, sl2) (lh, ll) (dh, dl) hA.symm hB.symm hC.symm hD.symm _
            0x3FE1C6AB2D17B786
            (5555015450206474705931523770666229092208 / 10 ^ 40 : ℚ)
            (5555015450206474705939994100138772095632 / 10 ^ 40 : ℚ)
            (1248717148923965943020177711395715129790 / 10 ^ 40 : ℚ)
            (1248717148923965943028648040868258133191 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by rw [hv']; push_cast; exact hg.1) (by rw [hv']; push_cast; exact hg.2)
            (by decide +kernel)
          rw [LgammaEndEncl.fract_eq _ (3 / 4) (-3) (by rw [hv]; norm_num) (by norm_num)
            (by norm_num), LgammaEndEncl.sin_q3]
        · -- `x = -11/4`
          have hv : value x.toBits = -11 / 4 := by
            rw [abs_of_neg hneg] at hkv
            norm_num at hkv
            linarith
          have hv' : -value x.toBits = 11 / 4 := by rw [hv]; norm_num
          have he := e_n11 hAP
          have hg := e_p11 hAP
          refine neg_end hF hL hS x hx (by linarith) (by linarith) hint' ?_ (fh, fl, eps) hl
            (sh, sl) (sh2, sl2) (lh, ll) (dh, dl) hA.symm hB.symm hC.symm hD.symm _
            0x3F7261E6D250CF63
            (44878975359557733097675447434333695924 / 10 ^ 40 : ℚ)
            (44878975359557733131556765324505709514 / 10 ^ 40 : ℚ)
            (4752146669149371303114084005009202610636 / 10 ^ 40 : ℚ)
            (4752146669149371303147965322899374624209 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by rw [hv']; push_cast; exact hg.1) (by rw [hv']; push_cast; exact hg.2)
            (by decide +kernel)
          rw [LgammaEndEncl.fract_eq _ (1 / 4) (-3) (by rw [hv]; norm_num) (by norm_num)
            (by norm_num), LgammaEndEncl.sin_q1]
        · -- `x = -13/4`
          have hv : value x.toBits = -13 / 4 := by
            rw [abs_of_neg hneg] at hkv
            norm_num at hkv
            linarith
          have hv' : -value x.toBits = 13 / 4 := by rw [hv]; norm_num
          have he := e_n13 hAP
          have hg := e_p13 hAP
          refine neg_end hF hL hS x hx (by linarith) (by linarith) hint' ?_ (fh, fl, eps) hl
            (sh, sl) (sh2, sl2) (lh, ll) (dh, dl) hA.symm hB.symm hC.symm hD.symm _
            0xBFE3F0DF81BA05E0
            (-6231534513209986466258708215823425594335 / 10 ^ 40 : ℚ)
            (-6231534513209986466250237886350882590911 / 10 ^ 40 : ℚ)
            (9358019311087253582580440020682697861226 / 10 ^ 40 : ℚ)
            (9358019311087253582588910350155240864633 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by rw [hv']; push_cast; exact hg.1) (by rw [hv']; push_cast; exact hg.2)
            (by decide +kernel)
          rw [LgammaEndEncl.fract_eq _ (3 / 4) (-4) (by rw [hv]; norm_num) (by norm_num)
            (by norm_num), LgammaEndEncl.sin_q3]
      · intro hn
        have hpos : 0 < value x.toBits := by
          rcases lt_or_gt_of_ne hv0 with h | h
          · exact absurd (hsign.mpr h) hn
          · exact h
        rw [hax, abs_of_pos hpos] at hl
        interval_cases k
        · -- `x = 3/4`
          have hv : value x.toBits = 3 / 4 := by
            rw [abs_of_pos hpos] at hkv
            norm_num at hkv
            linarith
          have he := e_p3 hAP
          refine pos_end x (fh, fl, eps) (by rw [hv]; norm_num) hl 1.0 0x3FCA051C372609EE
            (2032809514312953714810094553888025495898 / 10 ^ 40 : ℚ)
            (2032809514312953714818564883360568499296 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by decide +kernel)
        · -- `x = 5/4`
          have hv : value x.toBits = 5 / 4 := by
            rw [abs_of_pos hpos] at hkv
            norm_num at hkv
            linarith
          have he := e_p5 hAP
          refine pos_end x (fh, fl, eps) (by rw [hv]; norm_num) hl 1.0 0xBFB92857D38CAF41
            (-982718364218131614642773191702629903955 / 10 ^ 40 : ℚ)
            (-982718364218131614634302862230086900557 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by decide +kernel)
        · -- `x = 7/4`
          have hv : value x.toBits = 7 / 4 := by
            rw [abs_of_pos hpos] at hkv
            norm_num at hkv
            linarith
          have he := e_p7 hAP
          refine pos_end x (fh, fl, eps) (by rw [hv]; norm_num) hl 1.0 0xBFB59B4FD6875A6E
            (-844011210204855559594801000259063324223 / 10 ^ 40 : ℚ)
            (-844011210204855559560919682368891310653 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by decide +kernel)
        · -- `x = 9/4`
          have hv : value x.toBits = 9 / 4 := by
            rw [abs_of_pos hpos] at hkv
            norm_num at hkv
            linarith
          have he := e_p9 hAP
          refine pos_end x (fh, fl, eps) (by rw [hv]; norm_num) hl 1.0 0x3FBFF797BBA88502
            (1248717148923965943020177711395715129790 / 10 ^ 40 : ℚ)
            (1248717148923965943028648040868258133191 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by decide +kernel)
        · -- `x = 11/4`
          have hv : value x.toBits = 11 / 4 := by
            rw [abs_of_pos hpos] at hkv
            norm_num at hkv
            linarith
          have he := e_p11 hAP
          refine pos_end x (fh, fl, eps) (by rw [hv]; norm_num) hl 1.0 0x3FDE69EAC73EAB05
            (4752146669149371303114084005009202610636 / 10 ^ 40 : ℚ)
            (4752146669149371303147965322899374624209 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by decide +kernel)
        · -- `x = 13/4`
          have hv : value x.toBits = 13 / 4 := by
            rw [abs_of_pos hpos] at hkv
            norm_num at hkv
            linarith
          have he := e_p13 hAP
          refine pos_end x (fh, fl, eps) (by rw [hv]; norm_num) hl 1.0 0x3FEDF216E434A8EC
            (9358019311087253582580440020682697861226 / 10 ^ 40 : ℚ)
            (9358019311087253582588910350155240864633 / 10 ^ 40 : ℚ)
            (by rw [hv]; push_cast; exact he.1) (by rw [hv]; push_cast; exact he.2)
            (by decide +kernel)

#print axioms end_of_check
#print axioms mid_end
#print axioms pos_end
#print axioms neg_end
#print axioms fast_ends

end Library.Numerics.Float64.Lgamma.LgammaEnds
