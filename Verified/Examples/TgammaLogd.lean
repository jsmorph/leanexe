import Verified.Examples.TgammaLogdTail
import Verified.Examples.TgammaApprox
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
**`Tgamma.asLogd` within `2^-69 + |log x| 2^-78` of `log x`** for every positive normal double `x`
(`asLogd_spec`), with the low part below `2^-22 + |lh|/2^52`, from `TgammaApprox.LogFact` and
`FmaSpec.FmaNearest`.  The code writes `x = 2^E t` with `1 ≤ t < 2`, selects `r = r1 r2` with
`|r t - 1| ≤ 1/2400` (`TgammaLogdRed.red_sound`), and adds the table logarithms `l1 ≈ -log r1` and
`l2 ≈ -log r2`, `E ln 2`, and the kernel `log (1 + Z) ≈ Z + Z² P(Z)` for `Z = r t - 1`
(`TgammaLogdTail.logTail_spec`).  `LogFact` bounds the kernel by `2^-70` and each table entry and
`ln 2` by `2^-80`, and the roundings add `2^-71 + |E| 2^-85`.  The bound covers the call of
`asLgammaAsym` at `4 ≤ x ≤ 186`, where it is below `2^-68.98`.  `Lgamma.asLogd` applies the same
operations after its own reduction, which also normalizes subnormal arguments.
-/

namespace Verified.Examples.TgammaLogd
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx TgammaFloor TgammaLogdTab TgammaLogdParts
  TgammaLogdTail TgammaLogdRed
open Verified.Examples.Tgamma (entry)

set_option exponentiation.threshold 4096

theorem asLogd_eq (tab : Array UInt64) (x : Float) :
    Tgamma.asLogd tab x =
      let u := x.toBits
      let ex := u >>> 52
      let ed := if ex ≥ 0x3ff then (ex - 0x3ff).toFloat else -((0x3ff - ex).toFloat)
      let m := u &&& 0xFFFFFFFFFFFFF
      let j := jOf tab m
      let t := Float.ofBits (m ||| 0x3FF0000000000000)
      let i1 := j >>> 5
      let i2 := j &&& 0x1f
      logTail (entry tab (64 + i1) * entry tab (97 + i2)) t ed (entry tab (130 + 2 * i1 + 1))
        (entry tab (196 + 2 * i2 + 1)) (entry tab (130 + 2 * i1)) (entry tab (196 + 2 * i2))
        (entry tab 260) (entry tab 261) (entry tab 262) (entry tab 263) := rfl

#print axioms asLogd_eq

/-! ### Words and values -/

theorem entry_bits (tab : Array UInt64) (k : UInt64) (h : Finite tab[k.toNat]!) :
    (entry tab k).toBits = tab[k.toNat]! := by
  unfold Tgamma.entry
  rw [F64Bits.toBits_ofBits, not_nan_of_finite h]
  simp only [Bool.false_eq_true, ite_false]

/-- A normal positive double is `2^e/2^1023 (1 + m/2^52)`. -/
theorem decode (x : Float) (hx : Finite x.toBits) (hpos : 0 < value x.toBits)
    (hnorm : 1 ≤ Wasm.IEEE64.exponent x.toBits) :
    x.toBits.toNat < 2 ^ 63 ∧ 1 ≤ x.toBits.toNat / 2 ^ 52 ∧ x.toBits.toNat / 2 ^ 52 ≤ 2046 ∧
      value x.toBits = 2 ^ (x.toBits.toNat / 2 ^ 52) / 2 ^ 1023 *
        (1 + ((x.toBits.toNat % 2 ^ 52 : ℕ) : ℝ) / 2 ^ 52) := by
  have hs := F64Exact.sign_of_pos _ hpos
  have hlt : x.toBits.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have he : Wasm.IEEE64.exponent x.toBits = x.toBits.toNat / 2 ^ 52 := by
    unfold Wasm.IEEE64.exponent; omega
  have hfin : Wasm.IEEE64.exponent x.toBits ≠ 0x7FF := by
    simpa [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite] using hx
  refine ⟨hlt, by omega, by omega, ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, x.toBits.toNat / 2 ^ 52 = k + 1 := ⟨x.toBits.toNat / 2 ^ 52 - 1, by omega⟩
  rw [F64Adjacent.unsigned_word_value _ hlt]
  unfold F64Order.unsignedScaled
  rw [hk, ite_eq_right (by omega), show k + 1 - 1 = k by omega, Nat.cast_mul, Nat.cast_add,
    Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  field_simp
  ring

/-- The double `1.m` of the code. -/
theorem t_value (m : UInt64) (hm : m.toNat < 2 ^ 52) :
    Finite (Float.ofBits (m ||| 0x3FF0000000000000)).toBits ∧
      value (Float.ofBits (m ||| 0x3FF0000000000000)).toBits = 1 + (m.toNat : ℝ) / 2 ^ 52 := by
  have hn : (m ||| 0x3FF0000000000000).toNat = 2 ^ 52 * 1023 + m.toNat := by
    rw [UInt64.toNat_or, show (0x3FF0000000000000 : UInt64).toNat = 2 ^ 52 * 1023 by rfl,
      Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt hm]
  have hf : CodeLib.IEEE64.Finite (m ||| 0x3FF0000000000000) := by
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite Wasm.IEEE64.exponent
    rw [hn]; simp only [bne_iff_ne]; omega
  rw [F64Bits.toBits_ofBits, not_nan_of_finite hf]
  simp only [Bool.false_eq_true, ite_false]
  refine ⟨hf, ?_⟩
  rw [F64Adjacent.unsigned_word_value _ (by rw [hn]; omega), hn]
  unfold F64Order.unsignedScaled
  rw [ite_eq_right (by omega), show (2 ^ 52 * 1023 + m.toNat) / 2 ^ 52 - 1 = 1022 by omega,
    show (2 ^ 52 * 1023 + m.toNat) % 2 ^ 52 = m.toNat by omega]
  push_cast
  field_simp
  ring


/-! ### The words of `logdTable` -/

def coefOK (tab : Array UInt64) : Bool :=
  decide (tab[260]!.toNat % 2 ^ 63 < 0x7FF0000000000000) &&
  decide (tab[261]!.toNat % 2 ^ 63 < 0x7FF0000000000000) &&
  decide (tab[262]!.toNat % 2 ^ 63 < 0x7FF0000000000000) &&
  decide (tab[263]!.toNat % 2 ^ 63 < 0x7FF0000000000000) &&
  decide (2 * |sv tab[260]!| ≤ 2 ^ 1074) && decide (100 * |sv tab[261]!| ≤ 34 * 2 ^ 1074) &&
  decide (100 * |sv tab[262]!| ≤ 26 * 2 ^ 1074) && decide (100 * |sv tab[263]!| ≤ 21 * 2 ^ 1074)

theorem coefOK_logd : coefOK Tgamma.logdTable = true := by decide +kernel

theorem tab_parts (h : tabOK Tgamma.logdTable = true) :
    (∀ i < 33, rWord 36 Tgamma.logdTable[64 + i]! = true) ∧
      (∀ i < 32, rWord 35 Tgamma.logdTable[97 + i]! = true) ∧
      (∀ i < 33, hiWord (6932 * 2 ^ 1074 / 10000) Tgamma.logdTable[131 + 2 * i]! = true) ∧
      (∀ i < 32, hiWord (21 * 2 ^ 1074 / 1000) Tgamma.logdTable[197 + 2 * i]! = true) ∧
      (∀ i < 33, loWord Tgamma.logdTable[130 + 2 * i]! = true) ∧
      (∀ i < 32, loWord Tgamma.logdTable[196 + 2 * i]! = true) := by
  unfold tabOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem hiWord_spec (B : ℤ) (w : UInt64) (h : hiWord B w = true) :
    CodeLib.IEEE64.Finite w ∧ sv w = (sv w / 2 ^ 1040) * 2 ^ 1040 ∧ |sv w| ≤ B := by
  unfold hiWord at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hf, hd⟩, hb⟩ := h
  exact ⟨finite_of_lt w hf, (Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hd)).symm, hb⟩

theorem loWord_spec (w : UInt64) (h : loWord w = true) :
    CodeLib.IEEE64.Finite w ∧ |value w| ≤ 1 / 2 ^ 35 := by
  unfold loWord at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hf, hb⟩ := h
  refine ⟨finite_of_lt w hf, ?_⟩
  rw [value_eq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), div_le_div_iff₀
    (by positivity) (by positivity)]
  have : ((|sv w| : ℤ) : ℝ) ≤ 2 ^ 1039 := by exact_mod_cast hb
  rw [← Int.cast_abs]
  calc ((|sv w| : ℤ) : ℝ) * 2 ^ 35 ≤ 2 ^ 1039 * 2 ^ 35 :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = 1 * 2 ^ 1074 := by norm_num

theorem ltOK_spec (E : ℤ) (h : ltOK Tgamma.logdTable E = true) (a b : ℕ) (ha : a < 33)
    (hb : b < 32) :
    sv Tgamma.logdTable[131 + 2 * a]! / 2 ^ 1040 + sv Tgamma.logdTable[197 + 2 * b]! / 2 ^ 1040 +
        E * 11908177887 = 0 ∨
      2 ^ 34 ≤ 1475 * |sv Tgamma.logdTable[131 + 2 * a]! / 2 ^ 1040 +
        sv Tgamma.logdTable[197 + 2 * b]! / 2 ^ 1040 + E * 11908177887| := by
  unfold ltOK at h
  simp only [List.all_eq_true, List.mem_range] at h
  have h' := h a ha b hb
  unfold ltWord at h'
  simp only [decide_eq_true_eq] at h'
  rw [ln2h_sv, Int.mul_ediv_cancel _ (by positivity)] at h'
  exact h'

theorem logPoly_eq (z : ℝ) : TgammaApprox.logPoly z = value Tgamma.logdTable[260]! +
    z * (value Tgamma.logdTable[261]! + z * (value Tgamma.logdTable[262]! +
      z * value Tgamma.logdTable[263]!)) := by
  have hc : TgammaApprox.coeffs Tgamma.logdTable 260 1 4 = [TgammaApprox.q Tgamma.logdTable 260,
      TgammaApprox.q Tgamma.logdTable 261, TgammaApprox.q Tgamma.logdTable 262,
      TgammaApprox.q Tgamma.logdTable 263] := rfl
  rw [TgammaApprox.logPoly, hc]
  simp only [PolyBound.eval_cons, PolyBound.eval_nil, mul_zero, add_zero, TgammaApprox.q,
    PolyBound.ratOfWord_cast]

#print axioms coefOK_logd

theorem ix64 (a : UInt64) (ha : a.toNat ≤ 1024) : (64 + a).toNat = 64 + a.toNat := by
  rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
theorem ix97 (a : UInt64) (ha : a.toNat ≤ 1024) : (97 + a).toNat = 97 + a.toNat := by
  rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
theorem ix130 (a : UInt64) (ha : a.toNat ≤ 1024) : (130 + 2 * a).toNat = 130 + 2 * a.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
theorem ix131 (a : UInt64) (ha : a.toNat ≤ 1024) :
    (130 + 2 * a + 1).toNat = 131 + 2 * a.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
theorem ix196 (a : UInt64) (ha : a.toNat ≤ 1024) : (196 + 2 * a).toNat = 196 + 2 * a.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
theorem ix197 (a : UInt64) (ha : a.toNat ≤ 1024) :
    (196 + 2 * a + 1).toNat = 197 + 2 * a.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega

theorem value_us (w : UInt64) (h : w.toNat < 2 ^ 63) : value w = (us w : ℝ) / 2 ^ 1074 := by
  rw [F64Adjacent.unsigned_word_value _ h]; rfl

theorem rWord_lt (k : ℕ) (w : UInt64) (h : rWord k w = true) : w.toNat < 2 ^ 63 := by
  unfold rWord at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  omega

#print axioms ix131

set_option maxHeartbeats 4000000 in
/-- **The core of `asLogd`**: the code after the exponent and the mantissa, for any `X = 2^E (1 + m/2^52)`
with `|E| ≤ 1074`, which covers the normal arguments of `Tgamma.asLogd` and, after
`Lgamma.logReduce`, the subnormal ones of `Lgamma.asLogd`. -/
theorem logd_core (hF : FmaSpec.FmaNearest) (hL : TgammaApprox.LogFact) (m : UInt64)
    (hm52 : m.toNat < 2 ^ 52) (ed : Float) (E : ℤ)
    (hed : CodeLib.IEEE64.Finite ed.toBits ∧ sv ed.toBits = E * 2 ^ 1074) (hEb : |E| ≤ 1074)
    (X : ℝ) (hX : X = (2 : ℝ) ^ E * (1 + (m.toNat : ℝ) / 2 ^ 52)) :
    let j := jOf Tgamma.logdTable m
    let t := Float.ofBits (m ||| 0x3FF0000000000000)
    let i1 := j >>> 5
    let i2 := j &&& 0x1f
    let q := logTail (entry Tgamma.logdTable (64 + i1) * entry Tgamma.logdTable (97 + i2)) t ed
      (entry Tgamma.logdTable (130 + 2 * i1 + 1)) (entry Tgamma.logdTable (196 + 2 * i2 + 1))
      (entry Tgamma.logdTable (130 + 2 * i1)) (entry Tgamma.logdTable (196 + 2 * i2))
      (entry Tgamma.logdTable 260) (entry Tgamma.logdTable 261) (entry Tgamma.logdTable 262)
      (entry Tgamma.logdTable 263)
    Finite q.1.toBits ∧ Finite q.2.toBits ∧
      |value q.1.toBits + value q.2.toBits - Real.log X| ≤ 1 / 2 ^ 69 + |Real.log X| / 2 ^ 78 ∧
      |value q.2.toBits| ≤ 1 / 2 ^ 22 + |value q.1.toBits| / 2 ^ 52 := by
  intro j t i1 i2 q
  obtain ⟨T1, T2, T3, T4, T5, T6⟩ := tab_parts tabOK_logd
  have hcoef := coefOK_logd
  unfold coefOK at hcoef
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcoef
  obtain ⟨⟨⟨⟨⟨⟨⟨hf260, hf261⟩, hf262⟩, hf263⟩, hb260⟩, hb261⟩, hb262⟩, hb263⟩ := hcoef
  have ht : CodeLib.IEEE64.Finite t.toBits ∧ value t.toBits = 1 + (m.toNat : ℝ) / 2 ^ 52 :=
    t_value m hm52
  -- the reduction
  obtain ⟨hj1024, hred⟩ := red_sound Tgamma.logdTable TgammaLogdCheck.iCheck_logd m hm52
  obtain ⟨jN, hjN⟩ : ∃ jN, (jOf Tgamma.logdTable m).toNat = jN := ⟨_, rfl⟩
  rw [hjN] at hj1024 hred
  have hjv : j.toNat = jN := hjN
  have hi1 : i1.toNat = jN / 32 := by
    show (j >>> 5).toNat = _
    rw [UInt64.toNat_shiftRight, hjv]; simp only [UInt64.reduceToNat, Nat.reduceMod,
      Nat.shiftRight_eq_div_pow]
  have hi2 : i2.toNat = jN % 32 := by
    show (j &&& 0x1f).toNat = _
    rw [UInt64.toNat_and, hjv, show (0x1f : UInt64).toNat = 2 ^ 5 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hi1b : jN / 32 < 33 := by omega
  have hi2b : jN % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have hi1t : i1.toNat ≤ 1024 := by omega
  have hi2t : i2.toNat ≤ 1024 := by omega
  -- the words
  have hr1 := T1 _ hi1b
  have hr2 := T2 _ hi2b
  have hh1 := hiWord_spec _ _ (T3 _ hi1b)
  have hh2 := hiWord_spec _ _ (T4 _ hi2b)
  have hg1 := loWord_spec _ (T5 _ hi1b)
  have hg2 := loWord_spec _ (T6 _ hi2b)
  obtain ⟨hw1f, hw2f, hw1p, hw2p, hrf, hrv⟩ := r_exact _ _ hr1 hr2
  have e64 : (entry Tgamma.logdTable (64 + i1)).toBits = Tgamma.logdTable[64 + jN / 32]! := by
    rw [entry_bits _ _ (by rw [ix64 i1 hi1t, hi1]; exact hw1f), ix64 i1 hi1t, hi1]
  have e97 : (entry Tgamma.logdTable (97 + i2)).toBits = Tgamma.logdTable[97 + jN % 32]! := by
    rw [entry_bits _ _ (by rw [ix97 i2 hi2t, hi2]; exact hw2f), ix97 i2 hi2t, hi2]
  have e131 : (entry Tgamma.logdTable (130 + 2 * i1 + 1)).toBits =
      Tgamma.logdTable[131 + 2 * (jN / 32)]! := by
    rw [entry_bits _ _ (by rw [ix131 i1 hi1t, hi1]; exact hh1.1), ix131 i1 hi1t, hi1]
  have e197 : (entry Tgamma.logdTable (196 + 2 * i2 + 1)).toBits =
      Tgamma.logdTable[197 + 2 * (jN % 32)]! := by
    rw [entry_bits _ _ (by rw [ix197 i2 hi2t, hi2]; exact hh2.1), ix197 i2 hi2t, hi2]
  have e130 : (entry Tgamma.logdTable (130 + 2 * i1)).toBits =
      Tgamma.logdTable[130 + 2 * (jN / 32)]! := by
    rw [entry_bits _ _ (by rw [ix130 i1 hi1t, hi1]; exact hg1.1), ix130 i1 hi1t, hi1]
  have e196 : (entry Tgamma.logdTable (196 + 2 * i2)).toBits =
      Tgamma.logdTable[196 + 2 * (jN % 32)]! := by
    rw [entry_bits _ _ (by rw [ix196 i2 hi2t, hi2]; exact hg2.1), ix196 i2 hi2t, hi2]
  have ec : ∀ k : UInt64, k.toNat < 264 → CodeLib.IEEE64.Finite Tgamma.logdTable[k.toNat]! →
      (entry Tgamma.logdTable k).toBits = Tgamma.logdTable[k.toNat]! :=
    fun k _ hk => entry_bits _ _ hk
  have hr : (entry Tgamma.logdTable (64 + i1) * entry Tgamma.logdTable (97 + i2)).toBits =
      Wasm.IEEE64.mul Tgamma.logdTable[64 + jN / 32]! Tgamma.logdTable[97 + jN % 32]! := by
    rw [F64Bits.toBits_mul, e64, e97]
  -- the reduction factor
  have hw1lt := rWord_lt _ _ hr1
  have hw2lt := rWord_lt _ _ hr2
  have hrval : value (entry Tgamma.logdTable (64 + i1) * entry Tgamma.logdTable (97 + i2)).toBits =
      value Tgamma.logdTable[64 + jN / 32]! * value Tgamma.logdTable[97 + jN % 32]! := by
    rw [hr, hrv]
  have hrP : value Tgamma.logdTable[64 + jN / 32]! * value Tgamma.logdTable[97 + jN % 32]! =
      (Pof Tgamma.logdTable jN : ℝ) / 2 ^ 2148 := by
    rw [value_us _ hw1lt, value_us _ hw2lt]; unfold Pof; push_cast; ring
  have hz : |value (entry Tgamma.logdTable (64 + i1) * entry Tgamma.logdTable (97 + i2)).toBits *
      value t.toBits - 1| ≤ 1 / 2400 := by
    rw [hrval, hrP, ht.2]; exact hred
  -- the high parts
  obtain ⟨z1, hz1d⟩ : ∃ z1, z1 = sv Tgamma.logdTable[131 + 2 * (jN / 32)]! / 2 ^ 1040 := ⟨_, rfl⟩
  obtain ⟨z2, hz2d⟩ : ∃ z2, z2 = sv Tgamma.logdTable[197 + 2 * (jN % 32)]! / 2 ^ 1040 := ⟨_, rfl⟩
  have hv1 : sv (entry Tgamma.logdTable (130 + 2 * i1 + 1)).toBits = z1 * 2 ^ 1040 := by
    rw [e131, hz1d]; exact hh1.2.1
  have hv2 : sv (entry Tgamma.logdTable (196 + 2 * i2 + 1)).toBits = z2 * 2 ^ 1040 := by
    rw [e197, hz2d]; exact hh2.2.1
  have hz1b : 10000 * |z1| ≤ 6932 * 2 ^ 34 := by
    have h := hh1.2.2
    rw [hh1.2.1, ← hz1d] at h
    obtain ⟨hl, hu⟩ := abs_le.mp h
    rcases abs_cases z1 with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h'] <;> omega
  have hz2b : 1000 * |z2| ≤ 21 * 2 ^ 34 := by
    have h := hh2.2.2
    rw [hh2.2.1, ← hz2d] at h
    obtain ⟨hl, hu⟩ := abs_le.mp h
    rcases abs_cases z2 with ⟨h', _⟩ | ⟨h', _⟩ <;> rw [h'] <;> omega
  have hsmall : |E| ≤ 1 → (z1 + z2 + E * 11908177887 = 0 ∨
      2 ^ 34 ≤ 1475 * |z1 + z2 + E * 11908177887|) := by
    intro hE1
    rw [hz1d, hz2d]
    rcases (show E = -1 ∨ E = 0 ∨ E = 1 by rw [abs_le] at hE1; omega) with h | h | h <;> rw [h]
    · exact ltOK_spec (-1) ltOK_m1 _ _ hi1b hi2b
    · exact ltOK_spec 0 ltOK_0 _ _ hi1b hi2b
    · exact ltOK_spec 1 ltOK_1 _ _ hi1b hi2b
  -- the coefficients and the low parts
  have ek : ∀ (k : UInt64) (i : ℕ), k.toNat = i → CodeLib.IEEE64.Finite Tgamma.logdTable[i]! →
      (entry Tgamma.logdTable k).toBits = Tgamma.logdTable[i]! := by
    intro k i hki hf
    rw [entry_bits _ _ (by rw [hki]; exact hf), hki]
  have hc0 := ek 260 260 rfl (finite_of_lt _ hf260)
  have hc1 := ek 261 261 rfl (finite_of_lt _ hf261)
  have hc2 := ek 262 262 rfl (finite_of_lt _ hf262)
  have hc3 := ek 263 263 rfl (finite_of_lt _ hf263)
  have cb : ∀ (w : UInt64) (k c : ℕ), 0 < k → (k : ℤ) * |sv w| ≤ c * 2 ^ 1074 →
      |value w| ≤ (c : ℝ) / k := by
    intro w k c hk h
    rw [value_eq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      div_le_div_iff₀ (by positivity) (by exact_mod_cast hk)]
    rw [← Int.cast_abs]
    have : ((k : ℤ) : ℝ) * ((|sv w| : ℤ) : ℝ) ≤ ((c * 2 ^ 1074 : ℤ) : ℝ) := by exact_mod_cast h
    rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast, Int.cast_natCast] at this
    linarith
  have hcb0 : |value (entry Tgamma.logdTable 260).toBits| ≤ 1 / 2 := by
    rw [hc0]; have := cb _ 2 1 (by norm_num) (by exact_mod_cast hb260)
    norm_num at this ⊢; exact this
  have hcb1 : |value (entry Tgamma.logdTable 261).toBits| ≤ 34 / 100 := by
    rw [hc1]; have := cb _ 100 34 (by norm_num) (by exact_mod_cast hb261)
    norm_num at this ⊢; exact this
  have hcb2 : |value (entry Tgamma.logdTable 262).toBits| ≤ 26 / 100 := by
    rw [hc2]; have := cb _ 100 26 (by norm_num) (by exact_mod_cast hb262)
    norm_num at this ⊢; exact this
  have hcb3 : |value (entry Tgamma.logdTable 263).toBits| ≤ 21 / 100 := by
    rw [hc3]; have := cb _ 100 21 (by norm_num) (by exact_mod_cast hb263)
    norm_num at this ⊢; exact this
  have hT := logTail_spec hF (entry Tgamma.logdTable (64 + i1) * entry Tgamma.logdTable (97 + i2))
    t ed (entry Tgamma.logdTable (130 + 2 * i1 + 1)) (entry Tgamma.logdTable (196 + 2 * i2 + 1))
    (entry Tgamma.logdTable (130 + 2 * i1)) (entry Tgamma.logdTable (196 + 2 * i2))
    (entry Tgamma.logdTable 260) (entry Tgamma.logdTable 261) (entry Tgamma.logdTable 262)
    (entry Tgamma.logdTable 263) E z1 z2 (by rw [hr]; exact hrf) ht.1 hz
    (by rw [hc0]; exact finite_of_lt _ hf260) (by rw [hc1]; exact finite_of_lt _ hf261)
    (by rw [hc2]; exact finite_of_lt _ hf262) (by rw [hc3]; exact finite_of_lt _ hf263)
    hcb0 hcb1 hcb2 hcb3
    hed.1 hed.2 hEb (by rw [e131]; exact hh1.1) (by rw [e197]; exact hh2.1) hv1 hv2 hz1b hz2b hsmall
    (by rw [e130]; exact hg1.1) (by rw [e196]; exact hg2.1) (by rw [e130]; exact hg1.2)
    (by rw [e196]; exact hg2.2)
  obtain ⟨hqf1, hqf2, hqe, hql⟩ : Finite q.1.toBits ∧ Finite q.2.toBits ∧
      |value q.1.toBits + value q.2.toBits - _| ≤ _ ∧ |value q.2.toBits| ≤ _ := hT
  refine ⟨hqf1, hqf2, ?_, hql⟩
  -- the values of the words
  rw [e130, e196, hc0, hc1, hc2, hc3, hrval] at hqe
  rw [hrval] at hz
  obtain ⟨vw1, hvw1⟩ : ∃ v, v = value Tgamma.logdTable[64 + jN / 32]! := ⟨_, rfl⟩
  obtain ⟨vw2, hvw2⟩ : ∃ v, v = value Tgamma.logdTable[97 + jN % 32]! := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ v, v = value t.toBits := ⟨_, rfl⟩
  rw [← hvw1, ← hvw2, ← hτ] at hqe hz
  rw [← hvw1] at hw1p
  rw [← hvw2] at hw2p
  have hτv : τ = 1 + (m.toNat : ℝ) / 2 ^ 52 := by rw [hτ, ht.2]
  have hτ1 : 1 ≤ τ := by
    rw [hτv]
    have : (0 : ℝ) ≤ (m.toNat : ℝ) / 2 ^ 52 := div_nonneg (Nat.cast_nonneg _) (by norm_num)
    linarith
  have hτ2 : τ < 2 := by
    rw [hτv]
    have h1 : (m.toNat : ℝ) < 2 ^ 52 := by exact_mod_cast hm52
    have h2 : (m.toNat : ℝ) / 2 ^ 52 < 1 := by
      rw [div_lt_one (by positivity)]; exact h1
    linarith
  -- `log x = E log 2 + log τ`
  have hlogx : Real.log X = E * Real.log 2 + Real.log τ := by
    rw [hX, ← hτv, Real.log_mul (zpow_ne_zero _ two_ne_zero) (by linarith), Real.log_zpow]
  have hlτ0 : 0 ≤ Real.log τ := Real.log_nonneg hτ1
  have hlτ2 : Real.log τ < Real.log 2 := Real.log_lt_log (by linarith) hτ2
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hEl : |(E : ℝ)| * 0.6931471803 ≤ |Real.log X| + 0.6931471808 := by
    have h0 : (E : ℝ) * Real.log 2 = Real.log X - Real.log τ := by
      rw [hlogx]; ring
    have h1 : |(E : ℝ) * Real.log 2| ≤ |Real.log X| + Real.log 2 := by
      rw [h0]
      have := abs_sub (Real.log X) (Real.log τ)
      rw [abs_of_nonneg hlτ0] at this
      linarith
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < Real.log 2)] at h1
    have h2 : |(E : ℝ)| * 0.6931471803 ≤ |(E : ℝ)| * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2a.le (abs_nonneg _)
    linarith
  -- `log (1 + Z) = log r1 + log r2 + log τ`
  have hlog1 : Real.log (1 + (vw1 * vw2 * τ - 1)) = Real.log vw1 + Real.log vw2 + Real.log τ := by
    rw [add_sub_cancel, Real.log_mul (by positivity) (by linarith), Real.log_mul (by positivity)
      (by positivity)]
  -- the facts
  have hK := hL.1 _ hz
  rw [logPoly_eq] at hK
  have hT1 := hL.2.1 _ hi1b
  have hT2 := hL.2.2.1 _ hi2b
  have hLn := hL.2.2.2
  simp only [TgammaApprox.l1, TgammaApprox.l2, TgammaApprox.r1, TgammaApprox.r2, TgammaApprox.q,
    TgammaApprox.ln2, Rat.cast_add, PolyBound.ratOfWord_cast] at hT1 hT2 hLn
  rw [← hvw1] at hT1
  rw [← hvw2] at hT2
  have hv131 : value Tgamma.logdTable[131 + 2 * (jN / 32)]! = (z1 : ℝ) / 2 ^ 34 := by
    rw [value_eq, hh1.2.1, ← hz1d, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      div_eq_div_iff (by positivity) (by positivity)]
    rewrite [mul_assoc, ← pow_add]; norm_num
  have hv197 : value Tgamma.logdTable[197 + 2 * (jN % 32)]! = (z2 : ℝ) / 2 ^ 34 := by
    rw [value_eq, hh2.2.1, ← hz2d, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      div_eq_div_iff (by positivity) (by positivity)]
    rewrite [mul_assoc, ← pow_add]; norm_num
  have hvln : value (0x3FE62E42FEF80000 : UInt64) = 11908177887 / 2 ^ 34 := by
    rw [value_eq, ln2h_sv, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
      div_eq_div_iff (by positivity) (by positivity)]
    push_cast
    rewrite [mul_assoc, ← pow_add]; norm_num
  rw [hv131] at hT1
  rw [hv197] at hT2
  have hlnw : value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits = value (0x3DB1CF79ABC9E3B4 : UInt64) := by
    rw [F64Bits.toBits_ofBits, show Wasm.IEEE64.isNaN 0x3DB1CF79ABC9E3B4 = false by decide]
    simp only [Bool.false_eq_true, ite_false]
  rw [hvln, ← hlnw] at hLn
  have hzc : ((z1 + z2 + E * 11908177887 : ℤ) : ℝ) / 2 ^ 34 =
      (z1 : ℝ) / 2 ^ 34 + (z2 : ℝ) / 2 ^ 34 + E * (11908177887 / 2 ^ 34) := by push_cast; ring
  rw [hzc] at hqe
  rw [hlog1] at hK
  -- the sum
  obtain ⟨Lx, hLx⟩ : ∃ L, L = Real.log X := ⟨_, rfl⟩
  rw [← hLx] at hEl hlogx ⊢
  have hEe : |(E : ℝ)| * (1 / 2 ^ 80) ≥ |(E : ℝ) * ((11908177887 / 2 ^ 34 +
      value (Float.ofBits 0x3DB1CF79ABC9E3B4).toBits) - Real.log 2)| := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hLn (abs_nonneg _)
  rw [abs_le] at hqe hK hT1 hT2 ⊢
  obtain ⟨hEe1, hEe2⟩ := abs_le.mp (le_of_le_of_eq hEe.le rfl)
  obtain ⟨hq1, hq2⟩ := hqe
  obtain ⟨hK1, hK2⟩ := hK
  obtain ⟨hT11, hT12⟩ := hT1
  obtain ⟨hT21, hT22⟩ := hT2
  have hE0 := abs_nonneg (E : ℝ)
  have hL0 := abs_nonneg Lx
  constructor
  · linarith only [hq1, hK2, hT11, hT21, hEe1, hlogx, hEl, hE0, hL0]
  · linarith only [hq2, hK1, hT12, hT22, hEe2, hlogx, hEl, hE0, hL0]

set_option maxHeartbeats 1000000 in
/-- **`asLogd` within `2^-69 + |log x| 2^-78` of `log x`** for every positive normal `x`, with the
low part below `2^-22 + |lh|/2^52`. -/
theorem asLogd_spec (hF : FmaSpec.FmaNearest) (hL : TgammaApprox.LogFact) (x : Float)
    (hx : Finite x.toBits) (hpos : 0 < value x.toBits) (hnorm : 1 ≤ Wasm.IEEE64.exponent x.toBits) :
    Finite (Tgamma.asLogd Tgamma.logdTable x).1.toBits ∧
      Finite (Tgamma.asLogd Tgamma.logdTable x).2.toBits ∧
      |value (Tgamma.asLogd Tgamma.logdTable x).1.toBits +
          value (Tgamma.asLogd Tgamma.logdTable x).2.toBits - Real.log (value x.toBits)| ≤
        1 / 2 ^ 69 + |Real.log (value x.toBits)| / 2 ^ 78 ∧
      |value (Tgamma.asLogd Tgamma.logdTable x).2.toBits| ≤
        1 / 2 ^ 22 + |value (Tgamma.asLogd Tgamma.logdTable x).1.toBits| / 2 ^ 52 := by
  obtain ⟨hlt63, he1, he2, hxv⟩ := decode x hx hpos hnorm
  obtain ⟨q, hq⟩ : ∃ q, Tgamma.asLogd Tgamma.logdTable x = q := ⟨_, rfl⟩
  rw [hq]
  rw [asLogd_eq] at hq
  extract_lets u ex ed m j t i1 i2 at hq
  have hex : ex.toNat = x.toBits.toNat / 2 ^ 52 := by
    show (x.toBits >>> 52).toNat = _
    rw [UInt64.toNat_shiftRight]; simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  have hed : CodeLib.IEEE64.Finite ed.toBits ∧ sv ed.toBits = ((ex.toNat : ℤ) - 1023) * 2 ^ 1074 :=
    ed_spec ex (by rw [hex]; exact he1) (by rw [hex]; exact he2)
  rw [hex] at hed
  obtain ⟨E, hE⟩ : ∃ E : ℤ, E = ((x.toBits.toNat / 2 ^ 52 : ℕ) : ℤ) - 1023 := ⟨_, rfl⟩
  rw [← hE] at hed
  have hEb : |E| ≤ 1074 := by rw [hE, abs_le]; constructor <;> omega
  have hm : m.toNat = x.toBits.toNat % 2 ^ 52 := by
    show (x.toBits &&& 0xFFFFFFFFFFFFF).toNat = _
    rw [UInt64.toNat_and, show (0xFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 52 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hm52 : m.toNat < 2 ^ 52 := by rw [hm]; omega
  have hX : value x.toBits = (2 : ℝ) ^ E * (1 + (m.toNat : ℝ) / 2 ^ 52) := by
    rw [hxv, hm, hE, zpow_sub₀ two_ne_zero, zpow_natCast]
    norm_num
  have h := logd_core hF hL m hm52 ed E hed hEb (value x.toBits) hX
  rw [← hq]
  exact h

#print axioms logd_core
#print axioms asLogd_spec

end Verified.Examples.TgammaLogd
