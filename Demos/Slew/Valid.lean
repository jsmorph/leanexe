import Demos.Slew.Relative
import LeanExe.ProofKit.F64MulEnclosure
import LeanExe.ProofKit.F64AddEnclosure
import LeanExe.ProofKit.F64UpperWord
import LeanExe.ProofKit.F64NegateOps
import LeanExe.ProofKit.F64MulBounds
import LeanExe.ProofKit.F64AddBounds

/-! The hypotheses of the edge check from `validInput`.  A norm test
`(q.w q.w + q.x q.x + q.y q.y + q.z q.z - 1).abs ≤ tolNorm` that holds has finite operands and
intermediate results, since an infinite or NaN operand of a sum, difference, or product gives an
infinite or NaN result (`finite_of_add`, `finite_of_mul`), and the absolute value of either
exceeds `tolNorm`.  A component above 2 in magnitude makes the computed sum of squares at least
`4 - 60 u` (`mul_self_lower`, `add_lower`), from the enclosure of a finite rounded result between
its neighbors (`lower_of_enclosure`), so the test fails.  With every component at most 2, the
rounding errors of the test stay below `70 u`, and the squared norm lies within `3e-12` of 1
(`unitQ_good`, `unitV_good`).  `valid_good` collects `GoodQ` for every node and `ConeGood` for every
cone of a validated input. -/

namespace Demos.Slew.Valid

open Demos.Slew.Spec Demos.Slew.Rounding Demos.Slew.Error Demos.Slew.Axis Demos.Slew.Cone
open Demos.Slew.Decide Demos.Slew.Check
open CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.F64Approx

set_option exponentiation.threshold 4096

/-! ### Words -/

theorem not_finite_cases {x : UInt64} (h : ¬ Finite x) :
    Wasm.IEEE64.isNaN x = true ∨ Wasm.IEEE64.isInfinite x = true := by
  simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq,
    not_not] at h
  by_cases hf : Wasm.IEEE64.fraction x = 0
  · right; simp [Wasm.IEEE64.isInfinite, h, hf]
  · left; simp [Wasm.IEEE64.isNaN, h, hf]

theorem finite_of_not {x : UInt64} (hn : ¬ Wasm.IEEE64.isNaN x = true)
    (hi : ¬ Wasm.IEEE64.isInfinite x = true) : Finite x := by
  by_contra h
  rcases not_finite_cases h with h1 | h1
  · exact hn h1
  · exact hi h1

theorem not_finite_of_nan {x : UInt64} (h : Wasm.IEEE64.isNaN x = true) : ¬ Finite x := by
  simp only [Wasm.IEEE64.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  simp [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, h.1]

theorem not_finite_of_infinite {x : UInt64} (h : Wasm.IEEE64.isInfinite x = true) : ¬ Finite x := by
  simp only [Wasm.IEEE64.isInfinite, Bool.and_eq_true, beq_iff_eq] at h
  simp [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, h.1]

theorem nan_not_finite : ¬ Finite Wasm.IEEE64.canonicalNaN := by
  unfold CodeLib.IEEE64.Finite; decide

theorem infinity_not_finite (s : Bool) : ¬ Finite (Wasm.IEEE64.infinity s) := by
  unfold CodeLib.IEEE64.Finite; cases s <;> decide

theorem finite_of_add {a b : UInt64} (h : Finite (Wasm.IEEE64.add a b)) : Finite a ∧ Finite b := by
  unfold Wasm.IEEE64.add at h
  by_cases ha : Wasm.IEEE64.isNaN a = true
  · simp [ha] at h; exact absurd h nan_not_finite
  by_cases hb : Wasm.IEEE64.isNaN b = true
  · simp [hb] at h; exact absurd h nan_not_finite
  by_cases hia : Wasm.IEEE64.isInfinite a = true
  · simp only [ha, hb, Bool.or_self, Bool.false_eq_true, ite_false, hia, ite_true] at h
    split at h
    · exact absurd h nan_not_finite
    · exact absurd h (not_finite_of_infinite hia)
  by_cases hib : Wasm.IEEE64.isInfinite b = true
  · simp only [ha, hb, Bool.or_self, Bool.false_eq_true, ite_false, hia, hib, ite_true] at h
    exact absurd h (not_finite_of_infinite hib)
  exact ⟨finite_of_not ha hia, finite_of_not hb hib⟩

theorem finite_of_mul {a b : UInt64} (h : Finite (Wasm.IEEE64.mul a b)) : Finite a ∧ Finite b := by
  unfold Wasm.IEEE64.mul at h
  by_cases ha : Wasm.IEEE64.isNaN a = true
  · simp [ha] at h; exact absurd h nan_not_finite
  by_cases hb : Wasm.IEEE64.isNaN b = true
  · simp [hb] at h; exact absurd h nan_not_finite
  by_cases hia : Wasm.IEEE64.isInfinite a = true
  · simp only [ha, hb, Bool.or_self, Bool.false_eq_true, ite_false, hia, ite_true] at h
    split at h
    · exact absurd h nan_not_finite
    · exact absurd h (infinity_not_finite _)
  by_cases hib : Wasm.IEEE64.isInfinite b = true
  · simp only [ha, hb, Bool.or_self, Bool.false_eq_true, ite_false, hia, hib, ite_true] at h
    split at h
    · exact absurd h nan_not_finite
    · exact absurd h (infinity_not_finite _)
  exact ⟨finite_of_not ha hia, finite_of_not hb hib⟩

theorem finite_of_negate {b : UInt64} (h : Finite (Wasm.IEEE64.negate b)) : Finite b := by
  have := F64NegateOps.finite_negate _ h
  rwa [F64RelativeStep.negate_negate] at this

theorem finite_of_sub {a b : UInt64} (h : Finite (Wasm.IEEE64.sub a b)) : Finite a ∧ Finite b := by
  have := finite_of_add (show Finite (Wasm.IEEE64.add a (Wasm.IEEE64.negate b)) from h)
  exact ⟨this.1, finite_of_negate this.2⟩

/-- A word whose absolute value is at most a constant below the infinities is finite. -/
theorem finite_of_abs_le {w c : UInt64} (hc : Wasm.IEEE64.le 0x7FF0000000000000 c = false)
    (h : Wasm.IEEE64.le (Wasm.IEEE64.abs w) c = true) : Finite w := by
  by_contra hw
  rcases not_finite_cases hw with hn | hi
  · have hna : Wasm.IEEE64.isNaN (Wasm.IEEE64.abs w) = true := by rw [F64Sign.isNaN_abs]; exact hn
    simp [Wasm.IEEE64.le, hna] at h
  · have e : Wasm.IEEE64.abs w = 0x7FF0000000000000 := by
      apply UInt64.toNat_inj.mp
      rw [F64UpperWord.abs_toNat]
      simp only [Wasm.IEEE64.isInfinite, Bool.and_eq_true, beq_iff_eq, Wasm.IEEE64.exponent,
        Wasm.IEEE64.fraction] at hi
      simp only [UInt64.reduceToNat]
      omega
    rw [e, hc] at h
    exact absurd h (by decide)

/-! ### Lower bounds of rounded results -/

theorem value_nonneg_of_sign {w : UInt64} (h : Wasm.IEEE64.sign w = false) : 0 ≤ value w := by
  simp only [value, Wasm.IEEE64.scaledValue, h, Bool.false_eq_true, ite_false]
  positivity

theorem value_nonpos_of_sign {w : UInt64} (h : Wasm.IEEE64.sign w = true) : value w ≤ 0 := by
  simp only [value, Wasm.IEEE64.scaledValue, h, ite_true]
  have : (0 : ℝ) ≤ (Wasm.IEEE64.scaledMagnitude w : ℝ) / 2 ^ 1074 := by positivity
  push_cast
  rw [neg_div]; linarith

theorem absBits_self {w : UInt64} (h : w.toNat < 2 ^ 63) : F64Order.absBits w = w := by
  apply UInt64.toNat_inj.mp
  rw [F64Order.absBits_toNat, Nat.mod_eq_of_lt h]

theorem value_one_word : value (1 : UInt64) = 1 / 2 ^ 1074 := by
  have : Wasm.IEEE64.scaledValue (1 : UInt64) = 1 := by decide
  simp only [value, this]; norm_num

/-- A finite rounded result whose upper neighbor bounds the exact value `e` from above is at
least any nonnegative float of value at least `2⁻¹⁰⁷⁴` below `e`. -/
theorem lower_of_enclosure {r F : UInt64} {e : ℝ} (hFs : Wasm.IEEE64.sign F = false)
    (hF1 : 1 / 2 ^ 1074 ≤ value F) (he : e ≤ value (F64Adjacent.nextUp r)) (hlt : value F < e) :
    value F ≤ value r := by
  by_contra hlt2
  push Not at hlt2
  have hFlt : F.toNat < 2 ^ 63 := by simpa [Wasm.IEEE64.sign] using hFs
  by_cases hs : Wasm.IEEE64.sign r = true
  · have hr63 : 2 ^ 63 ≤ r.toNat := by simpa [Wasm.IEEE64.sign] using hs
    by_cases h0 : r = 0x8000000000000000
    · have : F64Adjacent.nextUp r = 1 := by simp [F64Adjacent.nextUp, h0]
      rw [this, value_one_word] at he
      linarith
    · have hgt : 2 ^ 63 < r.toNat := by
        rcases lt_or_eq_of_le hr63 with h | h
        · exact h
        · exfalso; apply h0; apply UInt64.toNat_inj.mp; rw [← h]; rfl
      have hn : F64Adjacent.nextUp r = r - 1 := by
        have hlt' : ¬ r < 0x8000000000000000 := by
          rw [UInt64.lt_iff_toNat_lt]; simp only [UInt64.reduceToNat]; omega
        simp [F64Adjacent.nextUp, h0, hlt']
      have hs' : Wasm.IEEE64.sign (r - 1) = true := by
        simp only [Wasm.IEEE64.sign, decide_eq_true_eq]
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]
        simp; omega
      rw [hn] at he
      have := value_nonpos_of_sign hs'
      linarith
  · have hs0 : Wasm.IEEE64.sign r = false := by simpa using hs
    have hrlt : r.toNat < 2 ^ 63 := by simpa [Wasm.IEEE64.sign] using hs0
    have hord : r.toNat < F.toNat := by
      by_contra hn
      push Not at hn
      have hm := F64Order.abs_value_mono F r (by
        rw [absBits_self hFlt, absBits_self hrlt, UInt64.le_iff_toNat_le]; exact hn)
      rw [abs_of_nonneg (value_nonneg_of_sign hFs), abs_of_nonneg (value_nonneg_of_sign hs0)] at hm
      linarith
    have hn : F64Adjacent.nextUp r = r + 1 := F64Adjacent.nextUp_nonnegative_eq r hrlt
    have hr1 : (r + 1).toNat = r.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
    have hs1 : Wasm.IEEE64.sign (r + 1) = false := by
      simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le, hr1]; omega
    have hm := F64Order.abs_value_mono (r + 1) F (by
      rw [absBits_self (by omega), absBits_self hFlt, UInt64.le_iff_toNat_le, hr1]; omega)
    rw [abs_of_nonneg (value_nonneg_of_sign hs1), abs_of_nonneg (value_nonneg_of_sign hFs)] at hm
    rw [hn] at he
    linarith

def fourWord : UInt64 := 0x4010000000000000

theorem fourWord_facts : Wasm.IEEE64.sign fourWord = false ∧ value fourWord = 4 := by
  have hs : Wasm.IEEE64.scaledValue fourWord = 2 ^ 1076 := by decide +kernel
  refine ⟨by decide, ?_⟩
  simp only [value, hs]; norm_num

theorem add_lower {a b : Float} (ha : Fin a) (hb : Fin b) (hr : Fin (a + b)) {L : ℝ}
    (hL : L ≤ val a + val b) (hL4 : L ≤ 4) (hL1 : -1 ≤ L) : L - 8 / 2 ^ 53 ≤ val (a + b) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hrb : Finite (Wasm.IEEE64.add a.toBits b.toBits) := by
    rw [← F64Bits.toBits_add]; exact hr
  have hv : val (a + b) = value (Wasm.IEEE64.add a.toBits b.toBits) := by
    simp only [val, F64Bits.toBits_add]
  rw [hv]
  by_cases hbig : val a + val b ≤ 8
  · have h := F64AddBounds.add_real_relative a.toBits b.toBits ha hb
      (by simp only [val] at hL hbig; rw [abs_lt]; constructor <;> linarith)
    have := (abs_le.mp h.2).1
    simp only [val] at hL hbig
    rw [hu] at this
    have habs : |value a.toBits + value b.toBits| ≤ 8 := by rw [abs_le]; constructor <;> linarith
    nlinarith
  · obtain ⟨hs4, hv4⟩ := fourWord_facts
    have he := (F64Adjacent.add_enclosure a.toBits b.toBits ha hb hrb).2
    have := lower_of_enclosure hs4 (by rw [hv4]; norm_num) he
      (by rw [hv4]; simp only [val] at hbig; linarith)
    rw [hv4] at this
    linarith

theorem sub_lower {a b : Float} (ha : Fin a) (hb : Fin b) (hr : Fin (a - b)) {L : ℝ}
    (hL : L ≤ val a - val b) (hL4 : L ≤ 4) (hL1 : -1 ≤ L) : L - 8 / 2 ^ 53 ≤ val (a - b) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hrb : Finite (Wasm.IEEE64.sub a.toBits b.toBits) := by
    rw [← F64Bits.toBits_sub]; exact hr
  have hv : val (a - b) = value (Wasm.IEEE64.sub a.toBits b.toBits) := by
    simp only [val, F64Bits.toBits_sub]
  rw [hv]
  by_cases hbig : val a - val b ≤ 8
  · have h := F64AddBounds.sub_real_relative a.toBits b.toBits ha hb
      (by simp only [val] at hL hbig; rw [abs_lt]; constructor <;> linarith)
    have := (abs_le.mp h.2).1
    simp only [val] at hL hbig
    rw [hu] at this
    have habs : |value a.toBits - value b.toBits| ≤ 8 := by rw [abs_le]; constructor <;> linarith
    nlinarith
  · obtain ⟨hs4, hv4⟩ := fourWord_facts
    have he := (F64Adjacent.sub_enclosure a.toBits b.toBits ha hb hrb).2
    have := lower_of_enclosure hs4 (by rw [hv4]; norm_num) he
      (by rw [hv4]; simp only [val] at hbig; linarith)
    rw [hv4] at this
    linarith

/-- The computed square of a finite float is above `-9 u`, and at least `4 - 9 u` when the float
exceeds 2 in magnitude. -/
theorem mul_self_lower {c : Float} (hc : Fin c) (hr : Fin (c * c)) :
    -9 / 2 ^ 53 ≤ val (c * c) ∧ (2 < |val c| → 4 - 9 / 2 ^ 53 ≤ val (c * c)) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have hm : minNormal64 = 1 / 2 ^ 1022 := rfl
  have hrb : Finite (Wasm.IEEE64.mul c.toBits c.toBits) := by
    rw [← F64Bits.toBits_mul]; exact hr
  have hv : val (c * c) = value (Wasm.IEEE64.mul c.toBits c.toBits) := by
    simp only [val, F64Bits.toBits_mul]
  rw [hv]
  have hsq := mul_self_nonneg (value c.toBits)
  obtain ⟨hs4, hv4⟩ := fourWord_facts
  have big : 8 < value c.toBits * value c.toBits →
      4 ≤ value (Wasm.IEEE64.mul c.toBits c.toBits) := by
    intro h8
    have he := (F64Adjacent.mul_enclosure c.toBits c.toBits hc hc hrb).2
    have := lower_of_enclosure hs4 (by rw [hv4]; norm_num) he (by rw [hv4]; linarith)
    rwa [hv4] at this
  have small : value c.toBits * value c.toBits ≤ 8 →
      value c.toBits * value c.toBits - 9 / 2 ^ 53 ≤ value (Wasm.IEEE64.mul c.toBits c.toBits) := by
    intro h8
    have h := F64MulBounds.mul_real_adaptive c.toBits c.toBits hc hc
      (by rw [abs_of_nonneg hsq]; linarith)
    have hb : (let n := Wasm.IEEE64.scaledMagnitude c.toBits * Wasm.IEEE64.scaledMagnitude c.toBits
        if n = 0 then (0 : ℝ) else max |value c.toBits * value c.toBits| minNormal64) ≤ 9 := by
      simp only
      split
      · norm_num
      · rw [abs_of_nonneg hsq, hm]
        exact max_le (by linarith) (by norm_num)
    have := (abs_le.mp h.2).1
    rw [hu] at this
    nlinarith [hb]
  constructor
  · by_cases h8 : value c.toBits * value c.toBits ≤ 8
    · have := small h8; linarith
    · have := big (by linarith); linarith
  · intro h2
    simp only [val] at h2
    by_cases h8 : value c.toBits * value c.toBits ≤ 8
    · have := small h8
      have h4 : 4 < value c.toBits * value c.toBits := by
        have := sq_abs (value c.toBits)
        nlinarith [abs_nonneg (value c.toBits)]
      linarith
    · have := big (by linarith); linarith

/-! ### The norm tests -/

theorem fin_add {a b : Float} (h : Fin (a + b)) : Fin a ∧ Fin b :=
  finite_of_add (by simpa only [Rounding.Fin, F64Bits.toBits_add] using h)

theorem fin_sub {a b : Float} (h : Fin (a - b)) : Fin a ∧ Fin b :=
  finite_of_sub (by simpa only [Rounding.Fin, F64Bits.toBits_sub] using h)

theorem fin_mul {a b : Float} (h : Fin (a * b)) : Fin a ∧ Fin b :=
  finite_of_mul (by simpa only [Rounding.Fin, F64Bits.toBits_mul] using h)

theorem tolNorm_bits : Demos.Slew.tolNorm.toBits = 0x3D719799812DEA11 := rfl

theorem tolNorm_bounds : val Demos.Slew.tolNorm ≤ 1.0001e-12 := eta_bounds.2

theorem tolNorm_le : Wasm.IEEE64.le 0x7FF0000000000000 Demos.Slew.tolNorm.toBits = false := by
  rw [tolNorm_bits]; decide

theorem one_bits : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl

theorem one_val : Fin (1.0 : Float) ∧ val (1.0 : Float) = 1 := by
  have hs : Wasm.IEEE64.scaledValue 0x3FF0000000000000 = 2 ^ 1074 := by decide +kernel
  refine ⟨?_, ?_⟩
  · simp only [Rounding.Fin, one_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [val, one_bits, value, hs]; push_cast; ring

theorem Bnd.one : Bnd (1.0 : Float) 1 0 1 := by
  have h := Bnd.of_val one_val.1 (M := 1) (by rw [one_val.2]; norm_num)
  rwa [one_val.2] at h

/-- A passed norm test `(t - 1).abs ≤ tolNorm` makes `t - 1` finite with `|t - 1| ≤ tolNorm`. -/
theorem norm_test {t : Float} (h : (t - 1.0).abs ≤ Demos.Slew.tolNorm) :
    Rounding.Fin (t - 1.0) ∧ |val (t - 1.0)| ≤ 1.0001e-12 := by
  have hle := (F64Bits.le_iff _ _).mp h
  rw [F64Bits.toBits_abs] at hle
  refine ⟨finite_of_abs_le tolNorm_le hle, ?_⟩
  have := le_bits_true hle
  rw [F64UpperWord.value_abs] at this
  exact this.trans tolNorm_bounds

/-- A computed difference that is at least 2 fails the norm test. -/
theorem norm_test_big {t : Float} (ft : Rounding.Fin t) (fr : Rounding.Fin (t - 1.0))
    (hr : |val (t - 1.0)| ≤ 1.0001e-12) (ht : 4 - 60 / 2 ^ 53 ≤ val t) : False := by
  have := sub_lower ft one_val.1 fr (L := 3 - 60 / 2 ^ 53) (by rw [one_val.2]; linarith)
    (by norm_num) (by norm_num)
  have := (abs_le.mp hr).2
  norm_num at *
  linarith

theorem unitQ_good {q : Q4} (hw : Fin q.w) (hx : Fin q.x) (hy : Fin q.y) (hz : Fin q.z)
    (h : unitQ q = true) : GoodQ q := by
  simp only [unitQ, decide_eq_true_eq] at h
  obtain ⟨fr, hr⟩ := norm_test h
  obtain ⟨ft, _⟩ := fin_sub fr
  obtain ⟨f3, fzz⟩ := fin_add ft
  obtain ⟨f2, fyy⟩ := fin_add f3
  obtain ⟨fww, fxx⟩ := fin_add f2
  have hsmall : |val q.w| ≤ 2 ∧ |val q.x| ≤ 2 ∧ |val q.y| ≤ 2 ∧ |val q.z| ≤ 2 := by
    obtain ⟨lw, bw⟩ := mul_self_lower hw fww
    obtain ⟨lx, bx⟩ := mul_self_lower hx fxx
    obtain ⟨ly, by'⟩ := mul_self_lower hy fyy
    obtain ⟨lz, bz⟩ := mul_self_lower hz fzz
    by_contra hc
    simp only [not_and_or, not_le] at hc
    rcases hc with c | c | c | c
    · have s1 := add_lower fww fxx f2 (L := 4 - 18 / 2 ^ 53) (by linarith [bw c]) (by norm_num)
        (by norm_num)
      have s2 := add_lower f2 fyy f3 (L := 4 - 35 / 2 ^ 53) (by linarith) (by norm_num) (by norm_num)
      have s3 := add_lower f3 fzz ft (L := 4 - 52 / 2 ^ 53) (by linarith) (by norm_num) (by norm_num)
      exact norm_test_big ft fr hr (by linarith)
    · have s1 := add_lower fww fxx f2 (L := 4 - 18 / 2 ^ 53) (by linarith [bx c]) (by norm_num)
        (by norm_num)
      have s2 := add_lower f2 fyy f3 (L := 4 - 35 / 2 ^ 53) (by linarith) (by norm_num) (by norm_num)
      have s3 := add_lower f3 fzz ft (L := 4 - 52 / 2 ^ 53) (by linarith) (by norm_num) (by norm_num)
      exact norm_test_big ft fr hr (by linarith)
    · have s1 := add_lower fww fxx f2 (L := -18 / 2 ^ 53) (by linarith) (by norm_num) (by norm_num)
      have s2 := add_lower f2 fyy f3 (L := 4 - 35 / 2 ^ 53) (by linarith [by' c]) (by norm_num)
        (by norm_num)
      have s3 := add_lower f3 fzz ft (L := 4 - 52 / 2 ^ 53) (by linarith) (by norm_num) (by norm_num)
      exact norm_test_big ft fr hr (by linarith)
    · have s1 := add_lower fww fxx f2 (L := -18 / 2 ^ 53) (by linarith) (by norm_num) (by norm_num)
      have s2 := add_lower f2 fyy f3 (L := -35 / 2 ^ 53) (by linarith) (by norm_num) (by norm_num)
      have s3 := add_lower f3 fzz ft (L := 4 - 52 / 2 ^ 53) (by linarith [bz c]) (by norm_num)
        (by norm_num)
      exact norm_test_big ft fr hr (by linarith)
  obtain ⟨bw, bx, by', bz⟩ := hsmall
  have sw := Bnd.mul (4.001 / 2 ^ 53) (Bnd.of_val hw bw) (Bnd.of_val hw bw) (by norm_num)
    (by norm_num)
  have sx := Bnd.mul (4.001 / 2 ^ 53) (Bnd.of_val hx bx) (Bnd.of_val hx bx) (by norm_num)
    (by norm_num)
  have sy := Bnd.mul (4.001 / 2 ^ 53) (Bnd.of_val hy by') (Bnd.of_val hy by') (by norm_num)
    (by norm_num)
  have sz := Bnd.mul (4.001 / 2 ^ 53) (Bnd.of_val hz bz) (Bnd.of_val hz bz) (by norm_num)
    (by norm_num)
  have s1 := Bnd.add (16.01 / 2 ^ 53) sw sx (by norm_num) (by norm_num)
  have s2 := Bnd.add (32.02 / 2 ^ 53) s1 sy (by norm_num) (by norm_num)
  have s3 := Bnd.add (52.03 / 2 ^ 53) s2 sz (by norm_num) (by norm_num)
  have rr := Bnd.sub (69.1 / 2 ^ 53) s3 Bnd.one (by norm_num) (by norm_num)
  have he : |val (q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z - 1.0) -
      (val q.w * val q.w + val q.x * val q.x + val q.y * val q.y + val q.z * val q.z - 1)| ≤
      69.1 / 2 ^ 53 := rr.1.2
  refine ⟨hw, hx, hy, hz, ?_⟩
  simp only [Quat.norm2, quatOf]
  rw [abs_le] at he hr ⊢
  constructor <;> norm_num at he hr ⊢ <;> linarith [he.1, he.2, hr.1, hr.2]

theorem unitV_good {v : V3} (hx : Fin v.x) (hy : Fin v.y) (hz : Fin v.z)
    (h : unitV v = true) : GoodV v := by
  have h' : (v.x * v.x + v.y * v.y + v.z * v.z - 1.0).abs ≤ Demos.Slew.tolNorm := of_decide_eq_true h
  obtain ⟨fr, hr⟩ := norm_test h'
  obtain ⟨ft, _⟩ := fin_sub fr
  obtain ⟨f2, fzz⟩ := fin_add ft
  obtain ⟨fxx, fyy⟩ := fin_add f2
  have hsmall : |val v.x| ≤ 2 ∧ |val v.y| ≤ 2 ∧ |val v.z| ≤ 2 := by
    obtain ⟨lx, bx⟩ := mul_self_lower hx fxx
    obtain ⟨ly, by'⟩ := mul_self_lower hy fyy
    obtain ⟨lz, bz⟩ := mul_self_lower hz fzz
    by_contra hc
    simp only [not_and_or, not_le] at hc
    rcases hc with c | c | c
    · have s1 := add_lower fxx fyy f2 (L := 4 - 18 / 2 ^ 53) (by linarith [bx c]) (by norm_num)
        (by norm_num)
      have s2 := add_lower f2 fzz ft (L := 4 - 35 / 2 ^ 53) (by linarith) (by norm_num) (by norm_num)
      exact norm_test_big ft fr hr (by linarith)
    · have s1 := add_lower fxx fyy f2 (L := 4 - 18 / 2 ^ 53) (by linarith [by' c]) (by norm_num)
        (by norm_num)
      have s2 := add_lower f2 fzz ft (L := 4 - 35 / 2 ^ 53) (by linarith) (by norm_num) (by norm_num)
      exact norm_test_big ft fr hr (by linarith)
    · have s1 := add_lower fxx fyy f2 (L := -18 / 2 ^ 53) (by linarith) (by norm_num) (by norm_num)
      have s2 := add_lower f2 fzz ft (L := 4 - 35 / 2 ^ 53) (by linarith [bz c]) (by norm_num)
        (by norm_num)
      exact norm_test_big ft fr hr (by linarith)
  obtain ⟨bx, by', bz⟩ := hsmall
  have sx := Bnd.mul (4.001 / 2 ^ 53) (Bnd.of_val hx bx) (Bnd.of_val hx bx) (by norm_num)
    (by norm_num)
  have sy := Bnd.mul (4.001 / 2 ^ 53) (Bnd.of_val hy by') (Bnd.of_val hy by') (by norm_num)
    (by norm_num)
  have sz := Bnd.mul (4.001 / 2 ^ 53) (Bnd.of_val hz bz) (Bnd.of_val hz bz) (by norm_num)
    (by norm_num)
  have s1 := Bnd.add (16.01 / 2 ^ 53) sx sy (by norm_num) (by norm_num)
  have s2 := Bnd.add (32.02 / 2 ^ 53) s1 sz (by norm_num) (by norm_num)
  have rr := Bnd.sub (49.1 / 2 ^ 53) s2 Bnd.one (by norm_num) (by norm_num)
  have he : |val (v.x * v.x + v.y * v.y + v.z * v.z - 1.0) -
      (val v.x * val v.x + val v.y * val v.y + val v.z * val v.z - 1)| ≤ 49.1 / 2 ^ 53 := rr.1.2
  refine ⟨hx, hy, hz, ?_⟩
  simp only [Vec.dot, vecOf]
  rw [abs_le] at he hr ⊢
  constructor <;> norm_num at he hr ⊢ <;> linarith [he.1, he.2, hr.1, hr.2]

/-! ### The input -/

/-- A loop from `true` whose step is true only when its state is true and `Q` holds of the index
accepts every index. -/
theorem loop_all_of {n : UInt64} {f : UInt64 → Bool → Bool} {Q : UInt64 → Prop}
    (h : LeanExe.loop n true f = true) (hf : ∀ k ok, f k ok = true → ok = true ∧ Q k) :
    ∀ k : Nat, k < n.toNat → Q (UInt64.ofNat k) := by
  have key := LeanExe.Dialect.loop_induction (n := n) (init := true) (f := f)
    (fun m s => s = true → ∀ k, k < m → Q (UInt64.ofNat k))
    (fun _ k hk => absurd hk (Nat.not_lt_zero k))
    (fun m s _ ih hs k hk => by
      obtain ⟨hs0, hq⟩ := hf _ _ hs
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · exact ih hs0 k hk
      · exact hq)
  exact key h

theorem isWord_bounds {x : Float} {lo hi : UInt64} (h : isWord x lo hi = true) :
    lo.toNat ≤ x.toUInt64.toNat ∧ x.toUInt64.toNat ≤ hi.toNat := by
  simp only [isWord, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨UInt64.le_iff_toNat_le.mp h.1.2, UInt64.le_iff_toNat_le.mp h.2⟩

theorem maxFinite_le : Wasm.IEEE64.le 0x7FF0000000000000 Demos.Slew.maxFinite.toBits = false := by
  rw [show Demos.Slew.maxFinite.toBits = 0x7FEFFFFFFFFFFFFF from rfl]; decide

theorem fin_rd {xs : Array Float} (h : allFinite xs = true) {j : UInt64}
    (hj : j.toNat < xs.size.toUInt64.toNat) : Rounding.Fin (rd xs j) := by
  have hall := loop_all_of (Q := fun i => (rd xs i).abs ≤ Demos.Slew.maxFinite) h (by
    intro k ok hk; simpa only [Bool.and_eq_true, decide_eq_true_eq] using hk)
  have := hall j.toNat hj
  rw [UInt64.ofNat_toNat] at this
  have hle := (F64Bits.le_iff _ _).mp this
  rw [F64Bits.toBits_abs] at hle
  exact finite_of_abs_le maxFinite_le hle

/-- The parts of `validInput` that the safety theorem uses. -/
structure Facts (xs : Array Float) : Prop where
  word1 : isWord (rd xs 1) 1 8 = true
  word2 : isWord (rd xs 2) 0 16 = true
  word3 : isWord (rd xs 3) 0 1024 = true
  size : xs.size.toUInt64 = (dims xs).total
  finite : allFinite xs = true
  start : unitQ (q4At xs 8) = true
  goal : unitQ (q4At xs 12) = true
  bodies : bodiesOk xs (dims xs) = true
  cones : conesOk xs (dims xs) = true
  ways : waysOk xs (dims xs) = true

theorem facts_of {xs : Array Float} (h : validInput xs = true) : Facts xs := by
  unfold validInput at h
  dsimp only at h
  split at h
  · exact absurd h (by decide)
  split at h
  · exact absurd h (by decide)
  rename_i h2
  split at h
  · exact absurd h (by decide)
  rename_i h3
  split at h
  · exact absurd h (by decide)
  rename_i h4
  simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at h2
  simp only [bne_iff_ne, ne_eq, not_not] at h3
  simp only [Bool.not_eq_true', Bool.not_eq_false] at h4
  simp only [Bool.and_eq_true] at h
  exact ⟨h2.1.1.2, h2.1.2, h2.2, h3, h4, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- The sizes of a validated input. -/
theorem dims_facts {xs : Array Float} (hv : Facts xs) :
    let d := dims xs
    1 ≤ d.nb.toNat ∧ d.nb.toNat ≤ 8 ∧ d.nc.toNat ≤ 16 ∧ d.nw.toNat ≤ 1024 ∧
      d.coneOff.toNat = 16 + 3 * d.nb.toNat ∧ d.wayOff.toNat = d.coneOff.toNat + 6 * d.nc.toNat ∧
      d.total.toNat = d.wayOff.toNat + 4 * d.nw.toNat ∧ xs.size.toUInt64.toNat = d.total.toNat := by
  intro d
  have b1 := isWord_bounds hv.word1
  have b2 := isWord_bounds hv.word2
  have b3 := isWord_bounds hv.word3
  simp only [UInt64.reduceToNat] at b1 b2 b3
  have e1 : d.nb = (rd xs 1).toUInt64 := rfl
  have e2 : d.nc = (rd xs 2).toUInt64 := rfl
  have e3 : d.nw = (rd xs 3).toUInt64 := rfl
  have e4 : d.coneOff = 16 + 3 * d.nb := rfl
  have e5 : d.wayOff = d.coneOff + 6 * d.nc := rfl
  have e6 : d.total = d.wayOff + 4 * d.nw := rfl
  rw [← e1] at b1
  rw [← e2] at b2
  rw [← e3] at b3
  have c4 : d.coneOff.toNat = 16 + 3 * d.nb.toNat := by
    rw [e4, UInt64.toNat_add, UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  have c5 : d.wayOff.toNat = d.coneOff.toNat + 6 * d.nc.toNat := by
    rw [e5, UInt64.toNat_add, UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  have c6 : d.total.toNat = d.wayOff.toNat + 4 * d.nw.toNat := by
    rw [e6, UInt64.toNat_add, UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  exact ⟨b1.1, b1.2, b2.2, b3.2, c4, c5, c6, by rw [hv.size]⟩

theorem fin_at {xs : Array Float} (hv : Facts xs) {j : UInt64}
    (hj : j.toNat < (dims xs).total.toNat) : Rounding.Fin (rd xs j) :=
  fin_rd hv.finite (by rw [(dims_facts hv).2.2.2.2.2.2.2]; exact hj)

theorem toNat_add_small {b : UInt64} {i : Nat} (hb : b.toNat + i < 2 ^ 32) (hi : i < 2 ^ 32) :
    (b + UInt64.ofNat i).toNat = b.toNat + i := by
  rw [UInt64.toNat_add,
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; omega)]
  omega

theorem goodQ_at {xs : Array Float} (hv : Facts xs) {b : UInt64}
    (hb : b.toNat + 3 < (dims xs).total.toNat) (hu : unitQ (q4At xs b) = true) :
    GoodQ (q4At xs b) := by
  have t := dims_facts hv
  have f : ∀ i : Nat, i ≤ 3 → Rounding.Fin (rd xs (b + UInt64.ofNat i)) := by
    intro i hi
    apply fin_at hv
    rw [toNat_add_small (by omega) (by omega)]
    omega
  have f0 : Rounding.Fin (rd xs b) := fin_at hv (by omega)
  exact unitQ_good f0 (f 1 (by norm_num)) (f 2 (by norm_num)) (f 3 (by norm_num)) hu

theorem goodV_at {xs : Array Float} (hv : Facts xs) {b : UInt64}
    (hb : b.toNat + 2 < (dims xs).total.toNat) (hu : unitV (v3At xs b) = true) :
    GoodV (v3At xs b) := by
  have t := dims_facts hv
  have f : ∀ i : Nat, i ≤ 2 → Rounding.Fin (rd xs (b + UInt64.ofNat i)) := by
    intro i hi
    apply fin_at hv
    rw [toNat_add_small (by omega) (by omega)]
    omega
  have f0 : Rounding.Fin (rd xs b) := fin_at hv (by omega)
  exact unitV_good f0 (f 1 (by norm_num)) (f 2 (by norm_num)) hu

theorem toNat_lin {a c : UInt64} {k : Nat} (h : a.toNat + c.toNat * k < 2 ^ 32) (hk : k < 2 ^ 32) :
    (a + c * UInt64.ofNat k).toNat = a.toNat + c.toNat * k := by
  rw [UInt64.toNat_add, UInt64.toNat_mul,
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 2 ^ 64 from rfl]; omega)]
  have : c.toNat * k < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- Every node of a validated input has a good attitude. -/
theorem node_good {xs : Array Float} (hv : Facts xs) {i : UInt64}
    (hi : i.toNat < (dims xs).nw.toNat + 2) : GoodQ (nodeAt xs (dims xs) i) := by
  have t := dims_facts hv
  unfold nodeAt
  by_cases h0 : (i == 0) = true
  · rw [ite_eq_left h0]; exact goodQ_at hv (by simp only [UInt64.reduceToNat]; omega) hv.start
  rw [ite_eq_right h0]
  by_cases h1 : (i == 1) = true
  · rw [ite_eq_left h1]; exact goodQ_at hv (by simp only [UInt64.reduceToNat]; omega) hv.goal
  rw [ite_eq_right h1]
  have hi0 : i.toNat ≠ 0 := by
    intro h; apply h0; simp only [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [h]; rfl
  have hi1 : i.toNat ≠ 1 := by
    intro h; apply h1; simp only [beq_iff_eq]; apply UInt64.toNat_inj.mp; rw [h]; rfl
  have hk : (i - 2).toNat = i.toNat - 2 :=
    UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp only [UInt64.reduceToNat]; omega)
  have hw := loop_all_of (Q := fun k => unitQ (q4At xs ((dims xs).wayOff + 4 * k)) = true) hv.ways
    (by intro k ok hk; simpa only [Bool.and_eq_true] using hk) (i - 2).toNat (by omega)
  rw [UInt64.ofNat_toNat] at hw
  refine goodQ_at hv ?_ hw
  have e : ((dims xs).wayOff + 4 * (i - 2)).toNat = (dims xs).wayOff.toNat + 4 * (i - 2).toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  rw [e]; omega

/-- Every cone of a validated input is good. -/
theorem cone_good {xs : Array Float} (hv : Facts xs) {k : Nat} (hk : k < (dims xs).nc.toNat) :
    ConeGood xs (dims xs) (UInt64.ofNat k) := by
  have t := dims_facts hv
  have hc := loop_all_of (Q := fun k => isWord (rd xs ((dims xs).coneOff + 6 * k)) 0
      ((dims xs).nb - 1) = true ∧ unitV (v3At xs ((dims xs).coneOff + 6 * k + 1)) = true ∧
      -1.0 ≤ rd xs ((dims xs).coneOff + 6 * k + 4) ∧ rd xs ((dims xs).coneOff + 6 * k + 4) ≤ 1.0)
    hv.cones (by
      intro j ok hj
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
      exact ⟨hj.1.1.1.1.1, hj.1.1.1.1.2, hj.1.1.1.2, hj.1.1.2, hj.1.2⟩)
    k hk
  obtain ⟨hword, haxis, hlo, hhi⟩ := hc
  have ho : ((dims xs).coneOff + 6 * UInt64.ofNat k).toNat = (dims xs).coneOff.toNat + 6 * k :=
    toNat_lin (by simp only [UInt64.reduceToNat]; omega) (by omega)
  have hb := isWord_bounds hword
  have hnb1 : ((dims xs).nb - 1).toNat = (dims xs).nb.toNat - 1 :=
    UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp only [UInt64.reduceToNat]; omega)
  rw [hnb1] at hb
  have hbody := loop_all_of (Q := fun j => unitV (v3At xs (16 + 3 * j)) = true) hv.bodies
    (by intro j ok hj; simpa only [Bool.and_eq_true] using hj)
    (rd xs ((dims xs).coneOff + 6 * UInt64.ofNat k)).toUInt64.toNat (by omega)
  rw [UInt64.ofNat_toNat] at hbody
  have hbi : (16 + 3 * (rd xs ((dims xs).coneOff + 6 * UInt64.ofNat k)).toUInt64).toNat =
      16 + 3 * (rd xs ((dims xs).coneOff + 6 * UInt64.ofNat k)).toUInt64.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  have h1 : ((dims xs).coneOff + 6 * UInt64.ofNat k + 1).toNat =
      (dims xs).coneOff.toNat + 6 * k + 1 := by
    rw [UInt64.toNat_add, ho]; simp only [UInt64.reduceToNat]; omega
  have h4 : ((dims xs).coneOff + 6 * UInt64.ofNat k + 4).toNat =
      (dims xs).coneOff.toNat + 6 * k + 4 := by
    rw [UInt64.toNat_add, ho]; simp only [UInt64.reduceToNat]; omega
  refine ⟨goodV_at hv (by rw [hbi]; omega) hbody, goodV_at hv (by rw [h1]; omega) haxis,
    fin_at hv (by rw [h4]; omega), ?_⟩
  have hl := le_val_of_le hlo
  have hh := le_val_of_le hhi
  rw [(neg_val one_val.1).2, one_val.2] at hl
  rw [one_val.2] at hh
  exact abs_le.mpr ⟨hl, hh⟩

/-- The hypotheses of the edge check for every node and cone of a validated input. -/
theorem valid_good {xs : Array Float} (h : validInput xs = true) :
    (∀ i : UInt64, i.toNat < (dims xs).nw.toNat + 2 → GoodQ (nodeAt xs (dims xs) i)) ∧
      (∀ k : Nat, k < (dims xs).nc.toNat → ConeGood xs (dims xs) (UInt64.ofNat k)) ∧
      (dims xs).nw.toNat ≤ 1024 :=
  ⟨fun _ hi => node_good (facts_of h) hi, fun _ hk => cone_good (facts_of h) hk,
    (dims_facts (facts_of h)).2.2.2.1⟩

end Demos.Slew.Valid
