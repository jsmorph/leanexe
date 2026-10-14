import Verified.Examples.LgammaLogd

/-!
The reduction `Lgamma.logReduce` that `Lgamma.asLogdAccurate` shares with `Lgamma.asLogd`, for
every positive finite double `x`: `x = 2^E t` with `t` in `[1, 2)`, the exponent `ed` with value
`E`, `|E| ≤ 1074`, the indices `i1 < 33` and `i2 < 32`, and `r = r1 i1 · r2 i2` exact with
`|r t - 1| ≤ 1/2400` (`reduce_spec`).  The proof is the reduction part of `TgammaLogd.logd_core`,
with the subnormal arguments of `LgammaLogd.subnormal_parts`.
-/

namespace Verified.Examples.LgammaLogAccRed
open CodeLib.IEEE64 LeanExe.ProofKit TgammaLogdTab TgammaLogdParts TgammaLogdTail TgammaLogdRed
  TgammaLogd

set_option exponentiation.threshold 4096

/-- The code of `Lgamma.logReduce` with the mantissa and the exponent written out. -/
theorem logReduce_eq (tab : Array UInt64) (x : Float) :
    Lgamma.logReduce tab x =
      let u := x.toBits
      let ex := u >>> 52
      let p : UInt64 × Float :=
        if ex == 0 then
          (u <<< (63 - Fma.msb64 u - 11), -((63 - Fma.msb64 u + 1011).toFloat))
        else (u, if ex ≥ 0x3ff then (ex - 0x3ff).toFloat else -((0x3ff - ex).toFloat))
      let m := p.1 &&& 0xFFFFFFFFFFFFF
      let j := jOf tab m
      (Float.ofBits (m ||| 0x3FF0000000000000), Tgamma.entry tab ((64 : UInt64) + (j >>> 5)) * Tgamma.entry tab (97 + (j &&& 0x1f)),
        p.2, j >>> 5, j &&& 0x1f) := rfl

/-- The facts of the reduction, from the mantissa `m` and the exponent `ed` with value `E`. -/
theorem core (m : UInt64) (hm52 : m.toNat < 2 ^ 52) (ed : Float) (E : ℤ)
    (hed : Finite ed.toBits ∧ sv ed.toBits = E * 2 ^ 1074) :
    let j := jOf Tgamma.logdTable m
    let t := Float.ofBits (m ||| 0x3FF0000000000000)
    let r := Tgamma.entry Tgamma.logdTable ((64 : UInt64) + (j >>> 5)) * Tgamma.entry Tgamma.logdTable (97 + (j &&& 0x1f))
    Finite t.toBits ∧ value t.toBits = 1 + (m.toNat : ℝ) / 2 ^ 52 ∧
      Finite r.toBits ∧
      value r.toBits = ((LgammaApprox.r1 (j >>> 5).toNat : ℚ) : ℝ) *
        ((LgammaApprox.r2 (j &&& 0x1f).toNat : ℚ) : ℝ) ∧
      |value r.toBits * value t.toBits - 1| ≤ 1 / 2400 ∧
      Finite ed.toBits ∧ value ed.toBits = E ∧ (j >>> 5).toNat < 33 ∧ (j &&& 0x1f).toNat < 32 := by
  intro j t r
  obtain ⟨T1, T2, -, -, -, -⟩ := tab_parts tabOK_logd
  have ht : Finite t.toBits ∧ value t.toBits = 1 + (m.toNat : ℝ) / 2 ^ 52 := t_value m hm52
  obtain ⟨hj1024, hred⟩ := red_sound Tgamma.logdTable TgammaLogdCheck.iCheck_logd m hm52
  obtain ⟨jN, hjN⟩ : ∃ jN, (jOf Tgamma.logdTable m).toNat = jN := ⟨_, rfl⟩
  rw [hjN] at hj1024 hred
  have hjv : j.toNat = jN := hjN
  have hi1 : (j >>> 5).toNat = jN / 32 := by
    rw [UInt64.toNat_shiftRight, hjv]; simp only [UInt64.reduceToNat, Nat.reduceMod,
      Nat.shiftRight_eq_div_pow]
  have hi2 : (j &&& 0x1f).toNat = jN % 32 := by
    rw [UInt64.toNat_and, hjv, show (0x1f : UInt64).toNat = 2 ^ 5 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  have hi1b : jN / 32 < 33 := by omega
  have hi2b : jN % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have hi1t : (j >>> 5).toNat ≤ 1024 := by omega
  have hi2t : (j &&& 0x1f).toNat ≤ 1024 := by omega
  have hr1 := T1 _ hi1b
  have hr2 := T2 _ hi2b
  obtain ⟨hw1f, hw2f, hw1p, hw2p, hrf, hrv⟩ := r_exact _ _ hr1 hr2
  have e64 : (Tgamma.entry Tgamma.logdTable ((64 : UInt64) + (j >>> 5))).toBits = Tgamma.logdTable[64 + jN / 32]! := by
    rw [entry_bits _ _ (by rw [ix64 _ hi1t, hi1]; exact hw1f), ix64 _ hi1t, hi1]
  have e97 : (Tgamma.entry Tgamma.logdTable (97 + (j &&& 0x1f))).toBits =
      Tgamma.logdTable[97 + jN % 32]! := by
    rw [entry_bits _ _ (by rw [ix97 _ hi2t, hi2]; exact hw2f), ix97 _ hi2t, hi2]
  have hr : r.toBits = Wasm.IEEE64.mul Tgamma.logdTable[64 + jN / 32]!
      Tgamma.logdTable[97 + jN % 32]! := by
    show (Tgamma.entry Tgamma.logdTable ((64 : UInt64) + (j >>> 5)) * Tgamma.entry Tgamma.logdTable (97 + (j &&& 0x1f))).toBits = _
    rw [F64Bits.toBits_mul, e64, e97]
  have hw1lt := rWord_lt _ _ hr1
  have hw2lt := rWord_lt _ _ hr2
  have hrval : value r.toBits =
      value Tgamma.logdTable[64 + jN / 32]! * value Tgamma.logdTable[97 + jN % 32]! := by
    rw [hr, hrv]
  have hrP : value Tgamma.logdTable[64 + jN / 32]! * value Tgamma.logdTable[97 + jN % 32]! =
      (Pof Tgamma.logdTable jN : ℝ) / 2 ^ 2148 := by
    rw [value_us _ hw1lt, value_us _ hw2lt]; unfold Pof; push_cast; ring
  refine ⟨ht.1, ht.2, by rw [hr]; exact hrf, ?_, ?_, hed.1, ?_, by omega, by omega⟩
  · rw [hrval, hi1, hi2, LgammaApprox.r1, LgammaApprox.r2, LgammaApprox.q, LgammaApprox.q,
      PolyBound.ratOfWord_cast, PolyBound.ratOfWord_cast]
  · rw [hrval, hrP, ht.2]; exact hred
  · rw [value_eq, hed.2]; push_cast; norm_num

/-- **The reduction** of `Lgamma.logReduce Tgamma.logdTable x` for a positive finite `x`. -/
theorem reduce_spec (x : Float) (hx : Finite x.toBits) (hpos : 0 < value x.toBits) :
    ∃ E : ℤ, |E| ≤ 1074 ∧
      Finite (Lgamma.logReduce Tgamma.logdTable x).1.toBits ∧
      1 ≤ value (Lgamma.logReduce Tgamma.logdTable x).1.toBits ∧
      value (Lgamma.logReduce Tgamma.logdTable x).1.toBits < 2 ∧
      Finite (Lgamma.logReduce Tgamma.logdTable x).2.1.toBits ∧
      value (Lgamma.logReduce Tgamma.logdTable x).2.1.toBits =
        ((LgammaApprox.r1 (Lgamma.logReduce Tgamma.logdTable x).2.2.2.1.toNat : ℚ) : ℝ) *
          ((LgammaApprox.r2 (Lgamma.logReduce Tgamma.logdTable x).2.2.2.2.toNat : ℚ) : ℝ) ∧
      |value (Lgamma.logReduce Tgamma.logdTable x).2.1.toBits *
          value (Lgamma.logReduce Tgamma.logdTable x).1.toBits - 1| ≤ 1 / 2400 ∧
      Finite (Lgamma.logReduce Tgamma.logdTable x).2.2.1.toBits ∧
      value (Lgamma.logReduce Tgamma.logdTable x).2.2.1.toBits = E ∧
      (Lgamma.logReduce Tgamma.logdTable x).2.2.2.1.toNat < 33 ∧
      (Lgamma.logReduce Tgamma.logdTable x).2.2.2.2.toNat < 32 ∧
      value x.toBits = 2 ^ E * value (Lgamma.logReduce Tgamma.logdTable x).1.toBits := by
  have hs := F64Exact.sign_of_pos _ hpos
  have hlt63 : x.toBits.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have hexn : (x.toBits >>> 52).toNat = x.toBits.toNat / 2 ^ 52 := by
    rw [UInt64.toNat_shiftRight]; simp only [UInt64.reduceToNat, Nat.reduceMod,
      Nat.shiftRight_eq_div_pow]
  rw [logReduce_eq]
  dsimp only
  rcases hb : (x.toBits >>> 52 == 0) with _ | _
  · -- a normal argument
    rw [ite_eq_right (by decide)]
    dsimp only
    have hne : x.toBits.toNat / 2 ^ 52 ≠ 0 := by
      intro h0
      have : x.toBits >>> 52 = 0 := UInt64.toNat_inj.mp (by rw [hexn, h0]; rfl)
      rw [this] at hb
      exact absurd hb (by decide)
    have hexp : Wasm.IEEE64.exponent x.toBits = x.toBits.toNat / 2 ^ 52 := by
      unfold Wasm.IEEE64.exponent; omega
    obtain ⟨-, he1, he2, hxv⟩ := decode x hx hpos (by omega)
    have hed := ed_spec (x.toBits >>> 52) (by rw [hexn]; exact he1) (by rw [hexn]; exact he2)
    rw [hexn] at hed
    obtain ⟨E, hE⟩ : ∃ E : ℤ, E = ((x.toBits.toNat / 2 ^ 52 : ℕ) : ℤ) - 1023 := ⟨_, rfl⟩
    rw [← hE] at hed
    have hm : (x.toBits &&& 0xFFFFFFFFFFFFF).toNat = x.toBits.toNat % 2 ^ 52 := by
      rw [UInt64.toNat_and, show (0xFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 52 - 1 by rfl,
        Nat.and_two_pow_sub_one_eq_mod]
    have hm52 : (x.toBits &&& 0xFFFFFFFFFFFFF).toNat < 2 ^ 52 := by rw [hm]; omega
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := core _ hm52 _ E hed
    refine ⟨E, by rw [hE, abs_le]; constructor <;> omega, h1, ?_, ?_, h3, h4, h5, h6, h7, h8, h9,
      ?_⟩
    · rw [h2]; have : (0 : ℝ) ≤ ((x.toBits &&& 0xFFFFFFFFFFFFF).toNat : ℝ) / 2 ^ 52 := by
        positivity
      linarith
    · rw [h2]
      have : ((x.toBits &&& 0xFFFFFFFFFFFFF).toNat : ℝ) < 2 ^ 52 := by exact_mod_cast hm52
      have : ((x.toBits &&& 0xFFFFFFFFFFFFF).toNat : ℝ) / 2 ^ 52 < 1 := by
        rw [div_lt_one (by positivity)]; exact this
      linarith
    · rw [h2, hxv, hm, hE, zpow_sub₀ two_ne_zero, zpow_natCast]
      norm_num
  · -- a subnormal argument
    rw [ite_eq_left rfl]
    dsimp only
    have h0 : x.toBits >>> 52 = 0 := by simpa using hb
    have hlt : x.toBits.toNat < 2 ^ 52 := by
      have : (x.toBits >>> 52).toNat = 0 := by rw [h0]; rfl
      rw [hexn] at this
      omega
    obtain ⟨P, hP52, hp1, hp2, hm, hedf, hedsv⟩ := LgammaLogd.subnormal_parts x hpos hlt
    have hm52 : ((x.toBits <<< (63 - Fma.msb64 x.toBits - 11)) &&& 0xFFFFFFFFFFFFF).toNat <
        2 ^ 52 := by
      rw [hm]
      have : x.toBits.toNat * 2 ^ (52 - P) < 2 ^ (P + 1) * 2 ^ (52 - P) :=
        Nat.mul_lt_mul_of_pos_right hp2 (by positivity)
      rw [← pow_add, show P + 1 + (52 - P) = 53 by omega] at this
      omega
    have h1' : 2 ^ 52 ≤ x.toBits.toNat * 2 ^ (52 - P) := by
      calc 2 ^ 52 = 2 ^ P * 2 ^ (52 - P) := by rw [← pow_add]; congr 1; omega
        _ ≤ _ := Nat.mul_le_mul_right _ hp1
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := core _ hm52 _ ((P : ℤ) - 1074) ⟨hedf, hedsv⟩
    refine ⟨(P : ℤ) - 1074, by rw [abs_le]; constructor <;> omega, h1, ?_, ?_, h3, h4, h5, h6,
      h7, h8, h9, ?_⟩
    · rw [h2]; have : (0 : ℝ) ≤ (((x.toBits <<< (63 - Fma.msb64 x.toBits - 11)) &&&
          0xFFFFFFFFFFFFF).toNat : ℝ) / 2 ^ 52 := div_nonneg (Nat.cast_nonneg _) (by norm_num)
      linarith
    · rw [h2]
      have : ((((x.toBits <<< (63 - Fma.msb64 x.toBits - 11)) &&& 0xFFFFFFFFFFFFF).toNat : ℕ) : ℝ) <
          2 ^ 52 := by exact_mod_cast hm52
      have : ((((x.toBits <<< (63 - Fma.msb64 x.toBits - 11)) &&& 0xFFFFFFFFFFFFF).toNat : ℕ) :
          ℝ) / 2 ^ 52 < 1 := by rw [div_lt_one (by positivity)]; exact this
      linarith
    · have hv : value x.toBits = (x.toBits.toNat : ℝ) / 2 ^ 1074 := by
        rw [F64Adjacent.unsigned_word_value _ (by omega)]
        unfold F64Order.unsignedScaled
        rw [ite_eq_left (by omega), Nat.mod_eq_of_lt hlt]
      have hmv : ((((x.toBits <<< (63 - Fma.msb64 x.toBits - 11)) &&& 0xFFFFFFFFFFFFF).toNat :
          ℕ) : ℝ) = (x.toBits.toNat : ℝ) * 2 ^ (52 - P) - 2 ^ 52 := by
        rw [hm, Nat.cast_sub h1']
        push_cast
        ring
      have hpw : (2 : ℝ) ^ P * 2 ^ (52 - P) = 2 ^ 52 := by rw [← pow_add]; congr 1; omega
      rw [h2, hv, hmv, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_ofNat]
      field_simp
      rw [← hpw]
      ring

#print axioms reduce_spec

end Verified.Examples.LgammaLogAccRed
