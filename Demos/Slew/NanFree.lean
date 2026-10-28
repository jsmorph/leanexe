import Demos.Slew.Safety
import Library.Numerics.Float64.Atan.AtanTheorem
import Library.Numerics.Float64.Atan.AtanTheoremSpecial
import Library.Numerics.Float64.Atan.AtanTwoQuot
import LeanExe.ProofKit.F64DivEnclosure

/-! NaN-freedom of the slew planner.  `plan_finite` states that every floating-point value that
`plan` computes from an input that passes `validInput` is finite, and so not a NaN.  The
statement lists the values as each function binds them: each `let` value, each operand of a
comparison, conversion, `min`, `max`, or `abs`, each divisor, each argument of a square root, and
the arguments and result of each call of `atan2`.  Every other operation lies inside one of these
expressions, as a sum, difference, product, or negation, and its result is finite whenever the
expression's is (`Valid.fin_add`, `Valid.fin_sub`, `Valid.fin_mul`).  The statement covers the
static check of every node and the edge check, relative quaternion, angle, duration, and output
axis of every pair of nodes, whether or not the search evaluates them, and the internal
operations of the library's `atan2` and `atan` lie outside it.

The bounds of the edge-check proofs give most of the values.  The duration `slewTicks` takes the
square root of `θ / a`, so the angle `2 atan2 s w` must not be negative: `atan2_nonneg` follows
the library's branches of `atan2` for a positive `s` and a `w` that is not negative, and
`atan_nonneg` shows that `atan` keeps the sign of its argument, from its small-argument branch and
from its accuracy within one step (`sign_of_within`). -/

namespace Demos.Slew.NanFree

open Demos.Slew.Spec Demos.Slew.Rounding Demos.Slew.Error Demos.Slew.Axis Demos.Slew.Cone
open Demos.Slew.Decide Demos.Slew.Check Demos.Slew.Valid Demos.Slew.Angle Demos.Slew.Relative
open Demos.Slew.Arc
open CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.F64Approx
open Library.Numerics.Float64.Atan.AtanTheoremBranches Library.Numerics.Float64.Atan.AtanTwoBranches

set_option exponentiation.threshold 4096

/-! ### Signs of `atan` and `atan2` -/

/-- A word within two steps of the reference of a number in `[2⁻¹⁰⁰⁰, 2]` has its sign bit
clear. -/
theorem sign_of_within {n : Nat} (hn : n ≤ 2) {y : ℝ} {w : UInt64} (hy1 : 1 / 2 ^ 1000 ≤ y)
    (hy2 : y ≤ 2) (h : F64SignedRounding.WithinSteps n y w) : Wasm.IEEE64.sign w = false := by
  obtain ⟨_, hpos⟩ := h
  have hy0 : 0 ≤ y := le_trans (by norm_num) hy1
  have hthr : y < F64PositiveRounding.overflowThreshold := by
    unfold F64PositiveRounding.overflowThreshold; norm_num; linarith
  have href : F64SignedRounding.roundNearestEven y = F64NearestEven.roundNearestEven y := by
    simp only [F64SignedRounding.roundNearestEven, hy0, ite_true,
      F64PositiveRounding.reference_finite y hthr]
  rw [href] at hpos
  have hnear := (F64NearestEven.roundNearestEven_spec y).1
  set r := F64NearestEven.roundNearestEven y
  have hrel := F64NearestHalf.nearest_relative y r hnear (le_trans (by norm_num) hy1)
    (by linarith)
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  rw [hu] at hrel
  have hrlim : r.toNat < 2 ^ 63 := hnear.1.trans (by decide)
  have hr3 : 3 ≤ r.toNat := by
    by_contra hc
    push Not at hc
    have := value_small_word (m := r.toNat) (by omega)
    rw [UInt64.ofNat_toNat] at this
    have := (abs_le.mp hrel).1
    have : (2 : ℝ) / 2 ^ 1074 < y - 1 / 2 ^ 53 * y := by nlinarith
    linarith
  rw [F64SignedRounding.position_of_lt r hrlim] at hpos
  by_contra hs
  have hs' : Wasm.IEEE64.sign w = true := by simpa using hs
  simp only [F64SignedRounding.position, hs', ite_true] at hpos
  have := abs_le.mp hpos
  omega

theorem atan_nonneg (q : Float) (hq : Finite q.toBits) (hs : Wasm.IEEE64.sign q.toBits = false) :
    0 ≤ value (Library.Numerics.Float64.Atan.atan q).toBits := by
  have hv0 := value_nonneg_of_sign hs
  by_cases h2 : ixOf q < 0x3e400000
  · have hs27 := (Library.Numerics.Float64.Atan.AtanTheorem.ix_27 q).mp h2
    rw [atan_tiny_eq q h2 (Library.Numerics.Float64.Atan.AtanTheorem.huge_gt q hq
      (hs27.trans (by norm_num)))]
    exact hv0
  · have hge : 1 / 2 ^ 27 ≤ |value q.toBits| :=
      not_lt.mp (fun h => h2 ((Library.Numerics.Float64.Atan.AtanTheorem.ix_27 q).mpr h))
    rw [abs_of_nonneg hv0] at hge
    have ha := Library.Numerics.Float64.Atan.AtanTheorem.atan_within_one q hq
    have hlo : 1 / 2 ^ 1000 ≤ Real.arctan (value q.toBits) := by
      have h1 := Real.arctan_strictMono.monotone hge
      have h2 := Library.Numerics.Float64.Atan.AtanTheoremSmall.arctan_near (1 / 2 ^ 27)
        (by norm_num)
      have h3 := (abs_le.mp h2).1
      have h4 : |(1 : ℝ) / 2 ^ 27| ^ 3 / (1 - (1 / 2 ^ 27) ^ 2) ≤ 1 / 2 ^ 80 := by
        rw [abs_of_pos (by norm_num)]; norm_num
      have h5 : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 27 - 1 / 2 ^ 80 := by norm_num
      linarith
    have hhi : Real.arctan (value q.toBits) ≤ 2 :=
      (Real.arctan_lt_pi_div_two _).le.trans (by linarith [Real.pi_lt_four])
    exact value_nonneg_of_sign (sign_of_within (by norm_num) hlo hhi ha)

theorem sign_test' (x : Float) : (x.toBits >>> 32 >>> 31 == 1) = Wasm.IEEE64.sign x.toBits :=
  F64UpperWord.sign_test x.toBits

theorem mOf_zero {y x : Float} (hy : Wasm.IEEE64.sign y.toBits = false)
    (hx : Wasm.IEEE64.sign x.toBits = false) : mOf y x = 0 := by
  have hy63 : y.toBits.toNat < 2 ^ 63 := by simpa [Wasm.IEEE64.sign] using hy
  have hx63 : x.toBits.toNat < 2 ^ 63 := by simpa [Wasm.IEEE64.sign] using hx
  have e1 : y.toBits >>> 32 >>> 31 = 0 := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod,
      Nat.reducePow, Nat.div_div_eq_div_mul]
    omega
  have e2 : x.toBits >>> 32 >>> 30 = 0 ∨ x.toBits >>> 32 >>> 30 = 1 := by
    have : (x.toBits >>> 32 >>> 30).toNat ≤ 1 := by
      simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.shiftRight_eq_div_pow, Nat.reduceMod,
      Nat.reducePow, Nat.div_div_eq_div_mul]
      omega
    rcases Nat.lt_or_ge (x.toBits >>> 32 >>> 30).toNat 1 with h | h
    · left; apply UInt64.toNat_inj.mp; simp only [UInt64.reduceToNat]; omega
    · right; apply UInt64.toNat_inj.mp; simp only [UInt64.reduceToNat]; omega
  unfold mOf
  rw [e1]
  rcases e2 with e | e <;> rw [e] <;> decide

theorem quadTail_zero (z : Float) : quadTail z 0 = z := rfl

theorem half_pi_tiny_sign :
    Wasm.IEEE64.sign (Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x01A56E1FC2F8F359).toBits =
      false := by
  rw [F64Bits.toBits_add, F64Bits.toBits_ofBits, F64Bits.toBits_ofBits]
  decide +kernel

theorem half_pi_lo_sign :
    Wasm.IEEE64.sign (Float.ofBits 0x3FF921FB54442D18 + 0.5 * piLoF).toBits = false := by
  rw [F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_ofBits, piLoF,
    F64Bits.toBits_ofBits, show (0.5 : Float).toBits = 0x3FE0000000000000 from rfl]
  decide +kernel

/-- `atan2 y x` is not negative for a positive `y` and a `x` that is not negative. -/
theorem atan2_nonneg (y x : Float) (hy : Finite y.toBits) (hx : Finite x.toBits)
    (hys : Wasm.IEEE64.sign y.toBits = false) (hy0 : value y.toBits ≠ 0)
    (hx0 : 0 ≤ value x.toBits) :
    0 ≤ value (Library.Numerics.Float64.Atan.atan2 y x).toBits := by
  have hn := Library.Numerics.Float64.Atan.AtanTwoBits.not_nan y x hy hx
  by_cases h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = true
  · rw [atan2_one_eq y x hn h1]; exact atan_nonneg y hy hys
  have h1' : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false := by simpa using h1
  have h2 : (ixOf y ||| lxOf y == 0) = false := by
    rw [Library.Numerics.Float64.Atan.AtanTwoBits.zero_test, decide_eq_false_iff_not]; exact hy0
  by_cases h3 : (ixOf x ||| lxOf x == 0) = true
  · rw [atan2_xzero_eq y x hn h1' h2 h3, sign_test', hys]
    exact value_nonneg_of_sign half_pi_tiny_sign
  have h3' : (ixOf x ||| lxOf x == 0) = false := by simpa using h3
  have hxne : value x.toBits ≠ 0 := by
    intro e
    rw [Library.Numerics.Float64.Atan.AtanTwoBits.zero_test, e] at h3'
    simp at h3'
  have hxs : Wasm.IEEE64.sign x.toBits = false := by
    by_contra hc
    have := value_nonpos_of_sign (by simpa using hc)
    exact hxne (le_antisymm this hx0)
  have hm := mOf_zero hys hxs
  have h4 := Library.Numerics.Float64.Atan.AtanTwoBits.inf_test x hx
  have h5 := Library.Numerics.Float64.Atan.AtanTwoBits.inf_test y hy
  by_cases h6 : (kOf2 y x >>> 63 == 0 && decide (kOf2 y x > 60)) = true
  · rw [atan2_big_eq y x hn h1' h2 h3' h4 h5 h6, hm, show (0 : UInt64) &&& 1 = 0 from rfl,
      quadTail_zero]
    exact value_nonneg_of_sign half_pi_lo_sign
  have h6' : (kOf2 y x >>> 63 == 0 && decide (kOf2 y x > 60)) = false := by simpa using h6
  have h7 : (x.toBits >>> 32 >>> 31 == 1 && kOf2 y x >>> 63 == 1 &&
      decide (kOf2 y x < 0xFFFFFFFFFFFFFFC4)) = false := by
    rw [sign_test', hxs]; rfl
  rw [atan2_gen_eq y x hn h1' h2 h3' h4 h5 h6' h7, hm, quadTail_zero]
  obtain ⟨hqf, _⟩ := Library.Numerics.Float64.Atan.AtanTwoQuot.quot_facts y x hy hx hxne
    (Library.Numerics.Float64.Atan.AtanTwoTheorem.quot_lt y x hy hxne
      (Library.Numerics.Float64.Atan.AtanTwoBits.nbig_cond y x h6'))
  have hqs : Wasm.IEEE64.sign (y / x).abs.toBits = false := by
    rw [F64Bits.toBits_abs]; exact (F64Sign.fields_abs _).2.2
  exact atan_nonneg _ hqf hqs

/-! ### Finite values -/

theorem fin_abs {x : Float} (h : Rounding.Fin x) : Rounding.Fin x.abs := by
  have he := (F64Sign.fields_abs x.toBits).1
  simp only [Rounding.Fin, F64Bits.toBits_abs, CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite,
    he] at h ⊢
  exact h

theorem fin_toFloat (n : UInt64) : Rounding.Fin n.toFloat := by
  simp only [Rounding.Fin, F64Convert.toBits_toFloat, Wasm.IEEE64.convertI64U,
    Wasm.IEEE64.fromInt]
  have := n.toNat_lt
  exact (F64Packing.pack_spec _ _ (by simp; omega)).1

/-- A word whose value is at least `-2⁻¹⁰⁷⁵` has a value that is not negative. -/
theorem value_nonneg_of_ge {w : UInt64} (h : -(1 / 2 ^ 1075) ≤ value w) : 0 ≤ value w := by
  simp only [value] at h ⊢
  have hp : (0 : ℝ) < 2 ^ 1074 := by positivity
  rw [le_div_iff₀ hp] at h
  have : (-1 : ℤ) < Wasm.IEEE64.scaledValue w := by
    have : (-1 : ℝ) < Wasm.IEEE64.scaledValue w := by
      have : -(1 / 2 ^ 1075) * (2 : ℝ) ^ 1074 = -1 / 2 := by norm_num
      linarith
    exact_mod_cast this
  have : (0 : ℝ) ≤ Wasm.IEEE64.scaledValue w := by exact_mod_cast (by omega : (0 : ℤ) ≤ _)
  positivity

theorem one_thousand_val : Rounding.Fin (1000.0 : Float) ∧ val (1000.0 : Float) = 1000 := by
  have hb : (1000.0 : Float).toBits = 0x408F400000000000 := rfl
  have hs : Wasm.IEEE64.scaledValue 0x408F400000000000 = 1000 * 2 ^ 1074 := by decide +kernel
  refine ⟨?_, ?_⟩
  · simp only [Rounding.Fin, hb]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [val, hb, value, hs]; push_cast; ring

theorem rateMin_val : Rounding.Fin Demos.Slew.rateMin ∧ 0.9999e-5 ≤ val Demos.Slew.rateMin := by
  have hb : Demos.Slew.rateMin.toBits = 0x3EE4F8B588E368F1 := rfl
  have hs : Wasm.IEEE64.scaledValue 0x3EE4F8B588E368F1 = (2 ^ 52 + 0x4F8B588E368F1) * 2 ^ 1005 := by
    decide +kernel
  refine ⟨?_, ?_⟩
  · simp only [Rounding.Fin, hb]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [val, hb, value, hs]; norm_num

theorem accelMin_val : Rounding.Fin Demos.Slew.accelMin ∧ 0.9999e-7 ≤ val Demos.Slew.accelMin :=
  ⟨sMin_val.1, sMin_bounds.1⟩

/-- A bounded quotient, with the absolute error of `fapprox_div`. -/
theorem Bnd.div {a b : Float} {A B ea eb Ma mb : ℝ} (e : ℝ) (ha : Bnd a A ea Ma)
    (hb : Bnd b B eb 1) (hmb : mb ≤ |B|) (hebm : eb < mb) (hbig : (Ma + ea) / (mb - eb) < 2 ^ 1022)
    (he : (ea + Ma * eb / mb) / (mb - eb) + (Ma + ea) / (mb - eb) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ e) :
    Bnd (a / b) (A / B) e (Ma / mb) := by
  have hmb0 : 0 < mb := lt_of_le_of_lt (Bnd.err_nonneg hb) hebm
  refine ⟨Approx.mono (fapprox_div ha.1 hb.1 Ma mb ha.2 hmb hebm _ le_rfl hbig) he, ?_⟩
  rw [abs_div, div_le_div_iff₀ (lt_of_lt_of_le hmb0 hmb) hmb0]
  exact mul_le_mul ha.2 hmb hmb0.le (Bnd.bound_nonneg ha)

/-- A quotient of a value that is not negative by a positive one is not negative. -/
theorem div_nonneg' {a b : Float} (ha : Rounding.Fin a) (hb : Rounding.Fin b)
    (hr : Rounding.Fin (a / b)) (h0a : 0 ≤ val a) (h0b : 0 < val b) : 0 ≤ val (a / b) := by
  have hrb : Finite (Wasm.IEEE64.div a.toBits b.toBits) := by
    rw [← F64Bits.toBits_div]; exact hr
  have hv : val (a / b) = value (Wasm.IEEE64.div a.toBits b.toBits) := by
    simp only [val, F64Bits.toBits_div]
  rw [hv]
  simp only [val] at h0a h0b
  have hbm : Wasm.IEEE64.scaledMagnitude b.toBits ≠ 0 := by
    intro hm
    have : value b.toBits = 0 := by
      simp only [value, Wasm.IEEE64.scaledValue, hm]; simp
    linarith
  rcases lt_or_eq_of_le h0a with hpos | hz
  · exact nonneg_of_enclosure (F64Adjacent.div_enclosure a.toBits b.toBits ha hb hbm hrb).2
      (div_pos hpos h0b)
  · have ham : Wasm.IEEE64.scaledMagnitude a.toBits = 0 := by
      have hv0 := hz.symm
      simp only [value, Wasm.IEEE64.scaledValue] at hv0
      split at hv0 <;> simp at hv0 <;> exact_mod_cast hv0
    have hna := not_nan_of_finite ha
    have hnb := not_nan_of_finite hb
    have hia : Wasm.IEEE64.isInfinite a.toBits = false := by
      by_contra hc; exact not_finite_of_infinite (by simpa using hc) ha
    have hib : Wasm.IEEE64.isInfinite b.toBits = false := by
      by_contra hc; exact not_finite_of_infinite (by simpa using hc) hb
    have e : Wasm.IEEE64.div a.toBits b.toBits =
        Wasm.IEEE64.signMask (Wasm.IEEE64.sign a.toBits != Wasm.IEEE64.sign b.toBits) := by
      simp [Wasm.IEEE64.div, hna, hnb, hia, hib, ham, hbm]
    rw [e]
    have hs : ∀ s : Bool, Wasm.IEEE64.scaledValue (Wasm.IEEE64.signMask s) = 0 := by
      intro s; cases s <;> decide
    simp only [value, hs]; simp

/-- The square root of a finite value that is not negative is finite, not negative, and at
most `1.001 √x`. -/
theorem sqrt_facts {a : Float} (ha : Rounding.Fin a) (h0 : 0 ≤ val a) :
    Rounding.Fin (Float.sqrt a) ∧ 0 ≤ val (Float.sqrt a) ∧
      val (Float.sqrt a) ≤ 1.001 * √(val a) := by
  rcases sqrt_cases ha with ⟨hz, he⟩ | ⟨_, hneg⟩ | ⟨_, hfin, hb⟩
  · rw [he, hz]; exact ⟨ha, le_refl _, by simp⟩
  · linarith
  · have := abs_le.mp hb
    have h1 := Real.sqrt_nonneg (val a)
    refine ⟨hfin, by nlinarith, by nlinarith⟩

/-! ### The duration of a rotation -/

/-- The values of `slewTicks theta wmax amax` and of the `ceilMs` of its result. -/
def SlewClean (theta wmax amax : Float) : Prop :=
  let lim := wmax * wmax / amax
  let t := if theta ≥ lim then theta / wmax + wmax / amax else 2.0 * Float.sqrt (theta / amax)
  let y := t * 1000.0
  0 < val wmax ∧ 0 < val amax ∧ Rounding.Fin (wmax * wmax) ∧ Rounding.Fin lim ∧
    Rounding.Fin (theta / wmax) ∧ Rounding.Fin (wmax / amax) ∧
    Rounding.Fin (theta / wmax + wmax / amax) ∧ Rounding.Fin (theta / amax) ∧
    0 ≤ val (theta / amax) ∧ Rounding.Fin (Float.sqrt (theta / amax)) ∧
    Rounding.Fin (2.0 * Float.sqrt (theta / amax)) ∧ Rounding.Fin y

theorem slew_clean {theta wmax amax : Float} (ht : Rounding.Fin theta) (ht0 : 0 ≤ val theta)
    (ht1 : val theta ≤ 4.1) (hw : Rounding.Fin wmax) (hw0 : 0.9999e-5 ≤ val wmax)
    (hw1 : val wmax ≤ 1) (ha : Rounding.Fin amax) (ha0 : 0.9999e-7 ≤ val amax)
    (ha1 : val amax ≤ 1) : SlewClean theta wmax amax := by
  have Bt := Bnd.of_val ht (M := 4.1) (by rw [abs_of_nonneg ht0]; exact ht1)
  have Bw := Bnd.of_val hw (M := 1) (by rw [abs_of_nonneg (by linarith)]; exact hw1)
  have Ba := Bnd.of_val ha (M := 1) (by rw [abs_of_nonneg (by linarith)]; exact ha1)
  have hwa : 0.9999e-5 ≤ |val wmax| := by rw [abs_of_nonneg (by linarith)]; exact hw0
  have haa : 0.9999e-7 ≤ |val amax| := by rw [abs_of_nonneg (by linarith)]; exact ha0
  have w2 := Bnd.mul (1.001 / 2 ^ 53) Bw Bw (by norm_num) (by norm_num)
  have lim := Bnd.div 1e-8 w2 Ba haa (by norm_num) (by norm_num) (by norm_num)
  have t1 := Bnd.div 1e-9 Bt Bw hwa (by norm_num) (by norm_num) (by norm_num)
  have t2 := Bnd.div 1e-8 Bw Ba haa (by norm_num) (by norm_num) (by norm_num)
  have s := Bnd.add 1e-7 t1 t2 (by norm_num) (by norm_num)
  have q := Bnd.div 1e-8 Bt Ba haa (by norm_num) (by norm_num) (by norm_num)
  have q0 := div_nonneg' ht ha q.1.1 ht0 (by linarith)
  obtain ⟨fr, r0, r1⟩ := sqrt_facts q.1.1 q0
  have hq1 : val (theta / amax) ≤ 4.2e7 := by
    have := q.upper; have := q.2
    have h2 : (4.1 : ℝ) / 0.9999e-7 ≤ 4.11e7 := by norm_num
    have := abs_le.mp q.2
    linarith
  have hr1 : val (Float.sqrt (theta / amax)) ≤ 7000 := by
    have : √(val (theta / amax)) ≤ 6481 := by
      rw [show (6481 : ℝ) = √(6481 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  have Br := Bnd.of_val fr (M := 7000) (by rw [abs_of_nonneg r0]; exact hr1)
  have t3 := Bnd.mul (14001 / 2 ^ 53) Bnd.two Br (by norm_num) (by norm_num)
  have Bk : Bnd (1000.0 : Float) 1000 0 1000 := by
    have h := Bnd.of_val one_thousand_val.1 (M := 1000) (by rw [one_thousand_val.2]; norm_num)
    rwa [one_thousand_val.2] at h
  refine ⟨by linarith, by linarith, w2.1.1, lim.1.1, t1.1.1, t2.1.1, s.1.1, q.1.1, q0, fr,
    t3.1.1, ?_⟩
  split
  · exact (Bnd.mul 1e-3 s Bk (by norm_num) (by norm_num)).1.1
  · exact (Bnd.mul 1e-3 t3 Bk (by norm_num) (by norm_num)).1.1

theorem mul_nonneg_val {a b : Float} (ha : Rounding.Fin a) (hb : Rounding.Fin b)
    (hr : Rounding.Fin (a * b)) (h0a : 0 ≤ val a) (h0b : 0 ≤ val b) : 0 ≤ val (a * b) := by
  have hrb : Finite (Wasm.IEEE64.mul a.toBits b.toBits) := by
    rw [← F64Bits.toBits_mul]; exact hr
  have hv : val (a * b) = value (Wasm.IEEE64.mul a.toBits b.toBits) := by
    simp only [val, F64Bits.toBits_mul]
  rw [hv]
  simp only [val] at h0a h0b
  rcases lt_or_eq_of_le (mul_nonneg h0a h0b) with hpos | hz
  · exact nonneg_of_enclosure (F64Adjacent.mul_enclosure a.toBits b.toBits ha hb hrb).2 hpos
  · have hm : Wasm.IEEE64.scaledMagnitude a.toBits * Wasm.IEEE64.scaledMagnitude b.toBits = 0 := by
      have := F64MulBounds.product_abs_scaled a.toBits b.toBits
      rw [← hz, abs_zero] at this
      have h2 : (0 : ℝ) < 2 ^ 2148 := by positivity
      have : ((Wasm.IEEE64.scaledMagnitude a.toBits * Wasm.IEEE64.scaledMagnitude b.toBits : ℕ) : ℝ)
          = 0 := by
        rw [eq_comm, div_eq_zero_iff] at this
        rcases this with h | h
        · exact h
        · exact absurd h h2.ne'
      exact_mod_cast this
    have h := F64MulBounds.mul_real_adaptive a.toBits b.toBits ha hb (by rw [← hz]; norm_num)
    have hb0 : |value (Wasm.IEEE64.mul a.toBits b.toBits) - value a.toBits * value b.toBits| ≤ 0 := by
      refine h.2.trans (le_of_eq ?_)
      simp [hm]
    rw [← hz, sub_zero] at hb0
    rw [abs_nonpos_iff.mp hb0]

/-! ### The statement -/

/-- The values of the static check of every cone at attitude `q` with `slack`, as `attitudeOk`
binds them. -/
def StaticClean (xs : Array Float) (d : Dims) (q : Q4) (slack : Float) : Prop :=
  ∀ k : Nat, k < d.nc.toNat →
    let b := coneBody xs d (UInt64.ofNat k)
    let u := coneAxis xs d (UInt64.ofNat k)
    let c := coneCos xs d (UInt64.ofNat k)
    let v := qrot q b
    Rounding.Fin v.x ∧ Rounding.Fin v.y ∧ Rounding.Fin v.z ∧ Rounding.Fin (dot u v) ∧
      Rounding.Fin (c - margin - slack) ∧ Rounding.Fin (c + margin + slack)

/-- The values of one cone of the edge check, as `edgeOk` binds them. -/
def ConeClean (n : V3) (ct st : Float) (qa : Q4) (b u : V3) (c : Float) : Prop :=
  let v0 := qrot qa b
  let nu := dot n u
  let nv := dot n v0
  let f0 := dot u v0
  let aa := f0 - nu * nv
  let bb := dot u (cross n v0)
  let cc := nu * nv
  let f1 := aa * ct + bb * st + cc
  let d1 := bb * ct - aa * st
  let r := Float.sqrt (aa * aa + bb * bb)
  Rounding.Fin v0.x ∧ Rounding.Fin v0.y ∧ Rounding.Fin v0.z ∧ Rounding.Fin nu ∧
    Rounding.Fin nv ∧ Rounding.Fin f0 ∧ Rounding.Fin aa ∧ Rounding.Fin bb ∧ Rounding.Fin cc ∧
    Rounding.Fin f1 ∧ Rounding.Fin d1 ∧ Rounding.Fin (aa * aa + bb * bb) ∧
    0 ≤ val (aa * aa + bb * bb) ∧ Rounding.Fin r ∧ Rounding.Fin (cc + r) ∧
    Rounding.Fin (cc - r) ∧ Rounding.Fin (c - margin) ∧ Rounding.Fin (c + margin)

/-- The values of the edge check of the rotation `rel` from `qa`, as `edgeOk` binds them, in the
branch that it evaluates. -/
def EdgeClean (xs : Array Float) (d : Dims) (qa rel : Q4) : Prop :=
  let s := Float.sqrt (rel.x * rel.x + rel.y * rel.y + rel.z * rel.z)
  Rounding.Fin (rel.x * rel.x + rel.y * rel.y + rel.z * rel.z) ∧ Rounding.Fin s ∧
    (s < sMin → Rounding.Fin (2.125 * s) ∧ StaticClean xs d qa (2.125 * s)) ∧
    (¬ s < sMin →
      let n : V3 := ⟨rel.x / s, rel.y / s, rel.z / s⟩
      let ct := rel.w * rel.w - s * s
      let st := 2.0 * rel.w * s
      0 < val s ∧ Rounding.Fin n.x ∧ Rounding.Fin n.y ∧ Rounding.Fin n.z ∧ Rounding.Fin ct ∧
        Rounding.Fin st ∧ ∀ k : Nat, k < d.nc.toNat →
          ConeClean n ct st qa (coneBody xs d (UInt64.ofNat k)) (coneAxis xs d (UInt64.ofNat k))
            (coneCos xs d (UInt64.ofNat k)))

/-- The values of the relative quaternion, the angle, the duration, and the output axis of the
segment from `qa` to `qb`, as `relative`, `angleOf`, `slewTicks`, `ceilMs`, and `segmentField`
bind them. -/
def SegClean (xs : Array Float) (qa qb : Q4) : Prop :=
  let rel := relative qa qb
  let sn := Float.sqrt (rel.x * rel.x + rel.y * rel.y + rel.z * rel.z)
  let a := Library.Numerics.Float64.Atan.atan2 sn rel.w
  let theta := 2.0 * a
  Rounding.Fin (relW qa qb) ∧ Rounding.Fin (relX qa qb) ∧ Rounding.Fin (relY qa qb) ∧
    Rounding.Fin (relZ qa qb) ∧ Rounding.Fin rel.w ∧ Rounding.Fin rel.x ∧ Rounding.Fin rel.y ∧
    Rounding.Fin rel.z ∧ Rounding.Fin sn ∧ Rounding.Fin a ∧ Rounding.Fin theta ∧
    0 ≤ val theta ∧
    (Demos.Slew.axisMin ≤ sn → 0 < val sn ∧ Rounding.Fin (rel.x / sn) ∧
      Rounding.Fin (rel.y / sn) ∧ Rounding.Fin (rel.z / sn)) ∧
    SlewClean theta (rd xs 4) (rd xs 5)

/-- The values of a norm test of a quaternion and of a vector. -/
def QuatTestClean (q : Q4) : Prop :=
  Rounding.Fin (q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z - 1.0) ∧
    Rounding.Fin (q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z - 1.0).abs

def VecTestClean (v : V3) : Prop :=
  Rounding.Fin (dot v v - 1.0) ∧ Rounding.Fin (dot v v - 1.0).abs

/-- The values that `validInput` computes from an input that passes it, and the settling time
in milliseconds. -/
def InputClean (xs : Array Float) : Prop :=
  let d := dims xs
  (∀ i : UInt64, i.toNat < xs.size.toUInt64.toNat →
      Rounding.Fin (rd xs i) ∧ Rounding.Fin (rd xs i).abs) ∧
    QuatTestClean (q4At xs 8) ∧ QuatTestClean (q4At xs 12) ∧
    (∀ k : Nat, k < d.nw.toNat → QuatTestClean (q4At xs (d.wayOff + 4 * UInt64.ofNat k))) ∧
    (∀ k : Nat, k < d.nb.toNat → VecTestClean (v3At xs (16 + 3 * UInt64.ofNat k))) ∧
    (∀ k : Nat, k < d.nc.toNat → VecTestClean (v3At xs (d.coneOff + 6 * UInt64.ofNat k + 1))) ∧
    Rounding.Fin (rd xs 6 * 1000.0)

/-! ### Proofs -/

theorem sqrt_bnd {a : Float} {A e M : ℝ} (h : Bnd a A e M) (h0 : 0 ≤ val a) (hM : M + e ≤ 5.2) :
    Bnd (Float.sqrt a) (val (Float.sqrt a)) 0 3 := by
  obtain ⟨fr, r0, r1⟩ := sqrt_facts h.1.1 h0
  refine Bnd.of_val fr ?_
  rw [abs_of_nonneg r0]
  have h1 := h.upper
  have h2 := abs_le.mp h.2
  have h3 : √(val a) ≤ 2.3 := by
    rw [show (2.3 : ℝ) = √(2.3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  linarith

theorem static_clean {xs : Array Float} {d : Dims} {q : Q4} {slack : Float} (hq : GoodQ q)
    (hcones : ∀ k : Nat, k < d.nc.toNat → ConeGood xs d (UInt64.ofNat k))
    (hsl : Rounding.Fin slack) (hsl1 : |val slack| ≤ 1e-6) : StaticClean xs d q slack := by
  intro k hk
  obtain ⟨hb, hu, hc, hc1⟩ := hcones k hk
  obtain ⟨vx, vy, vz⟩ := v0_bnd hq hb
  have f := f0_bnd hq hb hu
  have lo := Bnd.sub (2.1 / 2 ^ 53) (low_limit hc hc1) (Bnd.of_val hsl hsl1) (by norm_num)
    (by norm_num)
  have hi := Bnd.add (2.1 / 2 ^ 53) (high_limit hc hc1) (Bnd.of_val hsl hsl1) (by norm_num)
    (by norm_num)
  exact ⟨vx.1.1, vy.1.1, vz.1.1, f.1.1, lo.1.1, hi.1.1⟩

theorem cone_clean {qa : Q4} {b u n : V3} {ct st c : Float} {N : Vec} {CT ST : ℝ}
    (hq : GoodQ qa) (hb : GoodV b) (hu : GoodV u) (hc : Rounding.Fin c) (hc1 : |val c| ≤ 1)
    (hn : Bnd3 n N (5.2 / 2 ^ 53) 1) (hN : Vec.dot N N = 1)
    (hct : Bnd ct CT (12.5 / 2 ^ 53) 1.0001) (hst : Bnd st ST (12.5 / 2 ^ 53) 1.0001) :
    ConeClean n ct st qa b u c := by
  obtain ⟨f0, bb, cc, aa, f1, d1⟩ := cone_values hq hb hu hn hN hct hst
  obtain ⟨vx, vy, vz⟩ := v0_bnd hq hb
  obtain ⟨fnu, fnv⟩ := fin_mul cc.1.1
  have sa := Bnd.mul (2050 / 2 ^ 53) aa aa (by norm_num) (by norm_num)
  have sb := Bnd.mul (1010 / 2 ^ 53) bb bb (by norm_num) (by norm_num)
  have rad := Bnd.add (3100 / 2 ^ 53) sa sb (by norm_num) (by norm_num)
  have rad0 := add_nonneg' sa.1.1 sb.1.1 rad.1.1 (mul_self_nonneg' aa.1.1 sa.1.1)
    (mul_self_nonneg' bb.1.1 sb.1.1)
  have Br := sqrt_bnd rad rad0 (by norm_num)
  have top := Bnd.add (300 / 2 ^ 53) cc Br (by norm_num) (by norm_num)
  have bot := Bnd.sub (300 / 2 ^ 53) cc Br (by norm_num) (by norm_num)
  simp only [ConeClean]
  exact ⟨vx.1.1, vy.1.1, vz.1.1, fnu, fnv, f0.1.1, aa.1.1, bb.1.1, cc.1.1, f1.1.1, d1.1.1,
    rad.1.1, rad0, Br.1.1, top.1.1, bot.1.1, (low_limit hc hc1).1.1, (high_limit hc hc1).1.1⟩

theorem edge_clean {xs : Array Float} {d : Dims} {qa rel : Q4} (hq : GoodQ qa) (hr : GoodRel rel)
    (hcones : ∀ k : Nat, k < d.nc.toNat → ConeGood xs d (UInt64.ofNat k)) :
    EdgeClean xs d qa rel := by
  obtain ⟨fs, _, _⟩ := s_facts' hr
  simp only [EdgeClean]
  refine ⟨hr.fin_radicand, fs, fun hs => ?_, fun hs => ?_⟩
  · obtain ⟨fsl, sl1, _⟩ := slack_facts hr hs
    exact ⟨fsl, static_clean hq hcones fsl sl1⟩
  · have hbig : 1 / 2 ^ 1000 ≤ s2 rel := by
      rcases main_cases hr hs with hn | h
      · exact absurd hn (not_nan_of_fin fs)
      · exact h
    have hsv : 0 < val (sOf rel) := by
      have : ¬ sOf rel < sMin := hs
      rw [lt_iff_val fs sMin_val.1, not_lt] at this
      linarith [sMin_bounds.1]
    obtain ⟨bx, byy, bz, bw⟩ := hr.components
    have hSpos : 0 < √(s2 rel) := Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) hbig)
    have hSS : √(s2 rel) * √(s2 rel) = s2 rel := Real.mul_self_sqrt (s2_nonneg rel)
    have hQn := abs_le.mp hr.norm
    have hS1 : √(s2 rel) ≤ 1.0001 := by nlinarith [mul_self_nonneg (val rel.w)]
    have hsa := s_approx rel hr.fx hr.fy hr.fz (by linarith) (by linarith) (by linarith) hbig
    have hsB : Bnd (sOf rel) (√(s2 rel)) (4.2 / 2 ^ 53) 1.0001 :=
      ⟨Approx.mono hsa (by nlinarith), by rw [abs_of_pos hSpos]; exact hS1⟩
    have hQ1 : val rel.w * val rel.w + √(s2 rel) * √(s2 rel) ≤ 1.0001 := by rw [hSS]; linarith
    have hn : Bnd3 (axisF rel) (axisR rel) (5.2 / 2 ^ 53) 1 :=
      axis_bnd rel hr.fx hr.fy hr.fz hSpos hsa
    have hN : Vec.dot (axisR rel) (axisR rel) = 1 :=
      dot_unit_self (vecPart rel) (by rw [norm_vecPart]; exact hSpos)
    have hct := ct_bnd (Bnd.of_val hr.fw bw) hsB hQ1
    have hst := st_bnd (Bnd.of_val hr.fw bw) hsB hQ1
    refine ⟨hsv, hn.1.1.1, hn.2.1.1.1, hn.2.2.1.1, hct.1.1, hst.1.1, fun k hk => ?_⟩
    obtain ⟨hb, hu, hc, hc1⟩ := hcones k hk
    exact cone_clean hq hb hu hc hc1 hn hN hct hst

theorem seg_clean {xs : Array Float} {qa qb : Q4} (hqa : GoodQ qa) (hqb : GoodQ qb)
    (hw : Rounding.Fin (rd xs 4)) (hw0 : 0.9999e-5 ≤ val (rd xs 4)) (hw1 : val (rd xs 4) ≤ 1)
    (ha : Rounding.Fin (rd xs 5)) (ha0 : 0.9999e-7 ≤ val (rd xs 5)) (ha1 : val (rd xs 5) ≤ 1) :
    SegClean xs qa qb := by
  obtain ⟨w, x, y, z⟩ := rel_values hqa hqb
  have hr := relative_good hqa hqb
  set rel := relative qa qb
  obtain ⟨fs, s0, sclose⟩ := s_facts' hr
  obtain ⟨fθ, hθ⟩ := angle_out hr
  rw [angleOf_eq] at fθ hθ
  have fa := (fin_mul fθ).2
  have hA0 : 0 ≤ val (Library.Numerics.Float64.Atan.atan2 (sOf rel) rel.w) := by
    by_cases hz : val (sOf rel) = 0
    · have hbits := zero_bits_of hz
      have hd := abs_le.mp sclose
      have hQ := abs_le.mp hr.norm
      have hwpos : 0 < val rel.w := by
        have hS : √(s2 rel) ≤ 1e-100 := by
          rw [hz] at hd
          have : (1 : ℝ) / 2 ^ 499 ≤ 1e-120 := by norm_num
          have : (4.1 : ℝ) / 2 ^ 53 ≤ 1e-15 := by norm_num
          nlinarith [Real.sqrt_nonneg (s2 rel)]
        have hSS : √(s2 rel) * √(s2 rel) = s2 rel := Real.mul_self_sqrt (s2_nonneg rel)
        have : s2 rel ≤ 1e-200 := by nlinarith [Real.sqrt_nonneg (s2 rel)]
        nlinarith [hr.w_nonneg]
      have hws : Wasm.IEEE64.sign rel.w.toBits = false := by
        by_contra hc
        have := value_nonpos_of_sign (by simpa using hc)
        simp only [val] at hwpos; linarith
      have hat := Library.Numerics.Float64.Atan.AtanTwoSpecial.atan2_zero (sOf rel) rel.w hbits
        (not_nan_of_finite hr.fw)
      rw [hws] at hat
      simp only [Bool.false_eq_true, ite_false] at hat
      simp only [val, hat]
      exact le_of_eq hz.symm
    · have hpos : 0 < val (sOf rel) := lt_of_le_of_ne s0 (Ne.symm hz)
      have hss : Wasm.IEEE64.sign (sOf rel).toBits = false := by
        by_contra hc
        have := value_nonpos_of_sign (by simpa using hc)
        simp only [val] at hpos; linarith
      exact atan2_nonneg _ _ fs hr.fw hss hz hr.w_nonneg
  have hθ0 : 0 ≤ val (2.0 * Library.Numerics.Float64.Atan.atan2 (sOf rel) rel.w) :=
    mul_nonneg_val two_val.1 fa fθ (by rw [two_val.2]; norm_num) hA0
  have hθ1 : val (2.0 * Library.Numerics.Float64.Atan.atan2 (sOf rel) rel.w) ≤ 4.1 := by
    have h1 := (abs_le.mp hθ).2
    have h2 : angleR rel ≤ Real.pi := angle_le_pi _ _
    have h3 := Real.pi_lt_four
    linarith
  simp only [SegClean]
  refine ⟨w.1.1, x.1.1, y.1.1, z.1.1, hr.fw, hr.fx, hr.fy, hr.fz, fs, fa, fθ, hθ0,
    fun hb => ?_, slew_clean fθ hθ0 hθ1 hw hw0 hw1 ha ha0 ha1⟩
  have hbig := (axis_out hr).1 hb
  have hsv : 0 < val (sOf rel) := by
    have : val Demos.Slew.axisMin ≤ val (sOf rel) := le_val_of_le hb
    linarith [axisMin_val.2.1]
  have hSpos : 0 < √(s2 rel) := Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) hbig)
  obtain ⟨bx, byy, bz, _⟩ := hr.components
  have hsa := s_approx rel hr.fx hr.fy hr.fz (by linarith) (by linarith) (by linarith) hbig
  obtain ⟨cx, cy, cz⟩ := axis_bnd rel hr.fx hr.fy hr.fz hSpos hsa
  exact ⟨hsv, cx.1.1, cy.1.1, cz.1.1⟩

/-- The limits that `validInput` checks. -/
theorem limits_of {xs : Array Float} (h : validInput xs = true) :
    Demos.Slew.rateMin ≤ rd xs 4 ∧ rd xs 4 ≤ 1.0 ∧ Demos.Slew.accelMin ≤ rd xs 5 ∧
      rd xs 5 ≤ 1.0 ∧ 0.0 ≤ rd xs 6 ∧ rd xs 6 ≤ 3600.0 := by
  unfold validInput at h
  dsimp only at h
  split at h
  · exact absurd h (by decide)
  split at h
  · exact absurd h (by decide)
  split at h
  · exact absurd h (by decide)
  split at h
  · exact absurd h (by decide)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2⟩

theorem quat_test_clean {q : Q4} (h : unitQ q = true) : QuatTestClean q := by
  simp only [unitQ, decide_eq_true_eq] at h
  have hf := (norm_test h).1
  exact ⟨hf, fin_abs hf⟩

theorem vec_test_clean {v : V3} (h : unitV v = true) : VecTestClean v := by
  have h' : (v.x * v.x + v.y * v.y + v.z * v.z - 1.0).abs ≤ Demos.Slew.tolNorm :=
    of_decide_eq_true h
  have hf := (norm_test h').1
  exact ⟨hf, fin_abs hf⟩

theorem three_thousand_six_hundred_val : val (3600.0 : Float) = 3600 := by
  have hb : (3600.0 : Float).toBits = 0x40AC200000000000 := rfl
  have hs : Wasm.IEEE64.scaledValue 0x40AC200000000000 = 3600 * 2 ^ 1074 := by decide +kernel
  simp only [val, hb, value, hs]; push_cast; ring

theorem input_clean {xs : Array Float} (h : validInput xs = true) : InputClean xs := by
  have hv := facts_of h
  have t := dims_facts hv
  obtain ⟨_, _, _, _, l6a, l6b⟩ := limits_of h
  have f6 : Rounding.Fin (rd xs 6) := fin_at hv (by simp only [UInt64.reduceToNat]; omega)
  have h6a : 0 ≤ val (rd xs 6) := by have := le_val_of_le l6a; rwa [zero_val.2] at this
  have h6b : val (rd xs 6) ≤ 3600 := by
    have := le_val_of_le l6b; rwa [three_thousand_six_hundred_val] at this
  have B6 := Bnd.of_val f6 (M := 3600) (by rw [abs_of_nonneg h6a]; exact h6b)
  have Bk : Bnd (1000.0 : Float) 1000 0 1000 := by
    have h := Bnd.of_val one_thousand_val.1 (M := 1000) (by rw [one_thousand_val.2]; norm_num)
    rwa [one_thousand_val.2] at h
  have hways := loop_all_of (Q := fun k => unitQ (q4At xs ((dims xs).wayOff + 4 * k)) = true)
    hv.ways (by intro k ok hk; simpa only [Bool.and_eq_true] using hk)
  have hbodies := loop_all_of (Q := fun k => unitV (v3At xs (16 + 3 * k)) = true) hv.bodies
    (by intro k ok hk; simpa only [Bool.and_eq_true] using hk)
  have haxes := loop_all_of
    (Q := fun k => unitV (v3At xs ((dims xs).coneOff + 6 * k + 1)) = true) hv.cones (by
      intro j ok hj
      simp only [Bool.and_eq_true] at hj
      exact ⟨hj.1.1.1.1.1, hj.1.1.1.2⟩)
  simp only [InputClean]
  exact ⟨fun i hi => ⟨fin_rd hv.finite hi, fin_abs (fin_rd hv.finite hi)⟩,
    quat_test_clean hv.start, quat_test_clean hv.goal, fun k hk => quat_test_clean (hways k hk),
    fun k hk => vec_test_clean (hbodies k hk), fun k hk => vec_test_clean (haxes k hk),
    (Bnd.mul 1e-6 B6 Bk (by norm_num) (by norm_num)).1.1⟩

/-- **NaN-freedom of the slew planner.**  For an input that passes `validInput`, every
floating-point value that `plan` computes is finite: the values that `validInput` computes, every
conversion of a word to a float, the static check of every node with no slack, and, for every
pair of nodes, the edge check of their rotation, the relative quaternion, its angle and its
`atan2`, the duration of the rotation, and the output axis.  The search evaluates these
functions only for some nodes and pairs, and the theorem covers all of them. -/
theorem plan_finite {xs : Array Float} (h : validInput xs = true) :
    InputClean xs ∧ (∀ m : UInt64, Rounding.Fin m.toFloat) ∧
      (∀ i : UInt64, i.toNat < (dims xs).nw.toNat + 2 →
        StaticClean xs (dims xs) (nodeAt xs (dims xs) i) 0.0) ∧
      ∀ a b : UInt64, a.toNat < (dims xs).nw.toNat + 2 → b.toNat < (dims xs).nw.toNat + 2 →
        EdgeClean xs (dims xs) (nodeAt xs (dims xs) a)
            (relative (nodeAt xs (dims xs) a) (nodeAt xs (dims xs) b)) ∧
          SegClean xs (nodeAt xs (dims xs) a) (nodeAt xs (dims xs) b) := by
  obtain ⟨hnodes, hcones, _⟩ := valid_good h
  have hv := facts_of h
  have t := dims_facts hv
  obtain ⟨r4a, r4b, r5a, r5b, _, _⟩ := limits_of h
  have f4 : Rounding.Fin (rd xs 4) := fin_at hv (by simp only [UInt64.reduceToNat]; omega)
  have f5 : Rounding.Fin (rd xs 5) := fin_at hv (by simp only [UInt64.reduceToNat]; omega)
  have hw0 : 0.9999e-5 ≤ val (rd xs 4) := rateMin_val.2.trans (le_val_of_le r4a)
  have hw1 : val (rd xs 4) ≤ 1 := by have := le_val_of_le r4b; rwa [one_val.2] at this
  have ha0 : 0.9999e-7 ≤ val (rd xs 5) := accelMin_val.2.trans (le_val_of_le r5a)
  have ha1 : val (rd xs 5) ≤ 1 := by have := le_val_of_le r5b; rwa [one_val.2] at this
  refine ⟨input_clean h, fin_toFloat, fun i hi => static_clean (hnodes i hi) hcones zero_val.1
    (by rw [zero_val.2]; norm_num), fun a b ha hb => ⟨edge_clean (hnodes a ha)
      (relative_good (hnodes a ha) (hnodes b hb)) hcones,
      seg_clean (hnodes a ha) (hnodes b hb) f4 hw0 hw1 f5 ha0 ha1⟩⟩

end Demos.Slew.NanFree
