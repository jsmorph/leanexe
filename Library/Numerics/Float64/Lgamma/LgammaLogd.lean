import Library.Numerics.Float64.Tgamma.TgammaLogd
import Library.Numerics.Arithmetic.Fma.FmaWords
import Library.Numerics.Float64.Lgamma.LgammaApprox

/-!
**`Lgamma.asLogd` within `2^-69 + |log x| 2^-78` of `log x`** for every positive finite double `x`
(`asLogd_spec`), with the low part below `2^-22 + |lh|/2^52`, from `LgammaApprox.LogFact` and
`Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest`.  `Lgamma.asLogd` applies the operations of `Tgamma.asLogd` after
`Lgamma.logReduce`, which leaves a normal argument as it is (`asLogd_normal`) and writes a subnormal
`x = f 2^-1074` with the highest set bit of `f` at position `P` as `2^(P - 1074) t` with
`t = f 2^-P` in `[1, 2)`, by shifting `f` left by `52 - P` and taking `ed = -(1074 - P)`.  The
bound then follows from `Library.Numerics.Float64.Tgamma.TgammaLogd.logd_core` with the exponent `P - 1074` (`subnormal_core`).
-/

namespace Library.Numerics.Float64.Lgamma.LgammaLogd
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Tgamma.TgammaLogdTab Library.Numerics.Float64.Tgamma.TgammaLogdParts Library.Numerics.Float64.Tgamma.TgammaLogdTail Library.Numerics.Float64.Tgamma.TgammaLogdRed
  TgammaLogd
open Library.Numerics.Float64.Tgamma (entry)

set_option exponentiation.threshold 4096

/-- The code of `Lgamma.asLogd` with the reduction written out. -/
theorem asLogd_eq (tab : Array UInt64) (x : Float) :
    Lgamma.asLogd tab x =
      let u := x.toBits
      let ex := u >>> 52
      let p : UInt64 × Float :=
        if ex == 0 then
          (u <<< (63 - Library.Numerics.Arithmetic.Fma.msb64 u - 11), -((63 - Library.Numerics.Arithmetic.Fma.msb64 u + 1011).toFloat))
        else (u, if ex ≥ 0x3ff then (ex - 0x3ff).toFloat else -((0x3ff - ex).toFloat))
      let m := p.1 &&& 0xFFFFFFFFFFFFF
      let ed := p.2
      let j := jOf tab m
      let t := Float.ofBits (m ||| 0x3FF0000000000000)
      let i1 := j >>> 5
      let i2 := j &&& 0x1f
      logTail (entry tab (64 + i1) * entry tab (97 + i2)) t ed (entry tab (130 + 2 * i1 + 1))
        (entry tab (196 + 2 * i2 + 1)) (entry tab (130 + 2 * i1)) (entry tab (196 + 2 * i2))
        (entry tab 260) (entry tab 261) (entry tab 262) (entry tab 263) := rfl

#print axioms asLogd_eq

/-- **A normal argument**: `Lgamma.asLogd` is `Tgamma.asLogd`. -/
theorem asLogd_normal (tab : Array UInt64) (x : Float) (h : (x.toBits >>> 52 == 0) = false) :
    Lgamma.asLogd tab x = Tgamma.asLogd tab x := by
  rw [asLogd_eq, Library.Numerics.Float64.Tgamma.TgammaLogd.asLogd_eq]
  simp only [h, Bool.false_eq_true, ite_false]

#print axioms asLogd_normal

/-- **A subnormal argument**: the reduced mantissa and exponent. -/
theorem subnormal_parts (x : Float) (hpos : 0 < value x.toBits) (hlt : x.toBits.toNat < 2 ^ 52) :
    ∃ P : ℕ, P < 52 ∧ 2 ^ P ≤ x.toBits.toNat ∧ x.toBits.toNat < 2 ^ (P + 1) ∧
      ((x.toBits <<< (63 - Library.Numerics.Arithmetic.Fma.msb64 x.toBits - 11)) &&& 0xFFFFFFFFFFFFF).toNat =
        x.toBits.toNat * 2 ^ (52 - P) - 2 ^ 52 ∧
      Finite (-((63 - Library.Numerics.Arithmetic.Fma.msb64 x.toBits + 1011).toFloat)).toBits ∧
      sv (-((63 - Library.Numerics.Arithmetic.Fma.msb64 x.toBits + 1011).toFloat)).toBits = ((P : ℤ) - 1074) * 2 ^ 1074 := by
  have hne : x.toBits.toNat ≠ 0 := by
    intro h0
    have : value x.toBits = 0 := by
      rw [F64Adjacent.unsigned_word_value _ (by omega), h0]
      simp [F64Order.unsignedScaled]
    linarith
  obtain ⟨hp64, hp1, hp2⟩ := Library.Numerics.Arithmetic.Fma.FmaWords.msb64_spec x.toBits hne
  obtain ⟨P, hP⟩ : ∃ P, (Library.Numerics.Arithmetic.Fma.msb64 x.toBits).toNat = P := ⟨_, rfl⟩
  rw [hP] at hp64 hp1 hp2
  have hP52 : P < 52 := by
    by_contra hc
    have : 2 ^ 52 ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hk : (63 - Library.Numerics.Arithmetic.Fma.msb64 x.toBits).toNat = 63 - P := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hP]; simp only [UInt64.reduceToNat]; omega), hP]
    simp only [UInt64.reduceToNat]
  have hs : (63 - Library.Numerics.Arithmetic.Fma.msb64 x.toBits - 11).toNat = 52 - P := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hk]; simp only [UInt64.reduceToNat]; omega), hk]
    simp only [UInt64.reduceToNat]
    omega
  refine ⟨P, hP52, hp1, hp2, ?_, ?_⟩
  · have h1 : 2 ^ 52 ≤ x.toBits.toNat * 2 ^ (52 - P) := by
      calc 2 ^ 52 = 2 ^ P * 2 ^ (52 - P) := by rw [← pow_add]; congr 1; omega
        _ ≤ _ := Nat.mul_le_mul_right _ hp1
    have h2 : x.toBits.toNat * 2 ^ (52 - P) < 2 ^ 53 := by
      calc x.toBits.toNat * 2 ^ (52 - P) < 2 ^ (P + 1) * 2 ^ (52 - P) :=
            Nat.mul_lt_mul_of_pos_right hp2 (by positivity)
        _ = 2 ^ 53 := by rw [← pow_add]; congr 1; omega
    rw [UInt64.toNat_and, show (0xFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 52 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_shiftLeft, hs,
      show (52 - P) % 64 = 52 - P by omega, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : x.toBits.toNat * 2 ^ (52 - P) < 2 ^ 64)]
    omega
  · have hn : (63 - Library.Numerics.Arithmetic.Fma.msb64 x.toBits + 1011).toNat = 1074 - P := by
      rw [UInt64.toNat_add, hk]; simp only [UInt64.reduceToNat]; omega
    obtain ⟨hf, hsv⟩ := toFloat_value (63 - Library.Numerics.Arithmetic.Fma.msb64 x.toBits + 1011) (by rw [hn]; omega)
    obtain ⟨hnf, hnsv⟩ := neg_sv _ hf
    refine ⟨hnf, ?_⟩
    rw [hnsv, hsv, hn]
    push_cast [show P ≤ 1074 by omega]
    ring

/-- `logd_core` at a subnormal argument. -/
theorem subnormal_core (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : Library.Numerics.Float64.Tgamma.TgammaApprox.LogFact) (x : Float)
    (hpos : 0 < value x.toBits) (hlt : x.toBits.toNat < 2 ^ 52) :
    let m := (x.toBits <<< (63 - Library.Numerics.Arithmetic.Fma.msb64 x.toBits - 11)) &&& 0xFFFFFFFFFFFFF
    let ed := -((63 - Library.Numerics.Arithmetic.Fma.msb64 x.toBits + 1011).toFloat)
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
      |value q.1.toBits + value q.2.toBits - Real.log (value x.toBits)| ≤
        1 / 2 ^ 69 + |Real.log (value x.toBits)| / 2 ^ 78 ∧
      |value q.2.toBits| ≤ 1 / 2 ^ 22 + |value q.1.toBits| / 2 ^ 52 := by
  intro m ed j t i1 i2 q
  obtain ⟨P, hP52, hp1, hp2, hm, hedf, hedsv⟩ := subnormal_parts x hpos hlt
  have hm52 : m.toNat < 2 ^ 52 := by
    show ((x.toBits <<< (63 - Library.Numerics.Arithmetic.Fma.msb64 x.toBits - 11)) &&& 0xFFFFFFFFFFFFF).toNat < 2 ^ 52
    rw [hm]
    have : x.toBits.toNat * 2 ^ (52 - P) < 2 ^ (P + 1) * 2 ^ (52 - P) :=
      Nat.mul_lt_mul_of_pos_right hp2 (by positivity)
    rw [← pow_add, show P + 1 + (52 - P) = 53 by omega] at this
    omega
  have h1 : 2 ^ 52 ≤ x.toBits.toNat * 2 ^ (52 - P) := by
    calc 2 ^ 52 = 2 ^ P * 2 ^ (52 - P) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hp1
  have hX : value x.toBits = (2 : ℝ) ^ ((P : ℤ) - 1074) * (1 + (m.toNat : ℝ) / 2 ^ 52) := by
    have hv : value x.toBits = (x.toBits.toNat : ℝ) / 2 ^ 1074 := by
      rw [F64Adjacent.unsigned_word_value _ (by omega)]
      unfold F64Order.unsignedScaled
      rw [ite_eq_left (by omega), Nat.mod_eq_of_lt hlt]
    have hmv : (m.toNat : ℝ) = (x.toBits.toNat : ℝ) * 2 ^ (52 - P) - 2 ^ 52 := by
      show (((x.toBits <<< (63 - Library.Numerics.Arithmetic.Fma.msb64 x.toBits - 11)) &&& 0xFFFFFFFFFFFFF).toNat : ℝ) = _
      rw [hm, Nat.cast_sub h1]
      push_cast
      ring
    have hpw : (2 : ℝ) ^ P * 2 ^ (52 - P) = 2 ^ 52 := by rw [← pow_add]; congr 1; omega
    rw [hv, hmv, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_ofNat]
    field_simp
    rw [← hpw]
    ring
  exact logd_core hF hL m hm52 ed ((P : ℤ) - 1074) ⟨hedf, hedsv⟩
    (by rw [abs_le]; constructor <;> omega) (value x.toBits) hX

#print axioms subnormal_core

/-- **`Lgamma.asLogd` within `2^-69 + |log x| 2^-78` of `log x`** for every positive finite `x`,
with the low part below `2^-22 + |lh|/2^52`. -/
theorem asLogd_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact) (x : Float)
    (hx : Finite x.toBits) (hpos : 0 < value x.toBits) :
    Finite (Lgamma.asLogd Tgamma.logdTable x).1.toBits ∧
      Finite (Lgamma.asLogd Tgamma.logdTable x).2.toBits ∧
      |value (Lgamma.asLogd Tgamma.logdTable x).1.toBits +
          value (Lgamma.asLogd Tgamma.logdTable x).2.toBits - Real.log (value x.toBits)| ≤
        1 / 2 ^ 69 + |Real.log (value x.toBits)| / 2 ^ 78 ∧
      |value (Lgamma.asLogd Tgamma.logdTable x).2.toBits| ≤
        1 / 2 ^ 22 + |value (Lgamma.asLogd Tgamma.logdTable x).1.toBits| / 2 ^ 52 := by
  have hL' : Library.Numerics.Float64.Tgamma.TgammaApprox.LogFact := hL
  have hs := F64Exact.sign_of_pos _ hpos
  have hlt63 : x.toBits.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have hexn : (x.toBits >>> 52).toNat = x.toBits.toNat / 2 ^ 52 := by
    rw [UInt64.toNat_shiftRight]; simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  rcases hb : (x.toBits >>> 52 == 0) with _ | _
  · rw [asLogd_normal _ _ hb]
    have hne : x.toBits.toNat / 2 ^ 52 ≠ 0 := by
      intro h0
      have : x.toBits >>> 52 = 0 := UInt64.toNat_inj.mp (by rw [hexn, h0]; rfl)
      rw [this] at hb
      exact absurd hb (by decide)
    have hexp : Wasm.IEEE64.exponent x.toBits = x.toBits.toNat / 2 ^ 52 := by
      unfold Wasm.IEEE64.exponent; omega
    exact Library.Numerics.Float64.Tgamma.TgammaLogd.asLogd_spec hF hL' x hx hpos (by omega)
  · have h0 : x.toBits >>> 52 = 0 := by simpa using hb
    have hlt : x.toBits.toNat < 2 ^ 52 := by
      have : (x.toBits >>> 52).toNat = 0 := by rw [h0]; rfl
      rw [hexn] at this
      omega
    rw [asLogd_eq]
    dsimp only
    rw [ite_eq_left hb]
    exact subnormal_core hF hL' x hpos hlt

#print axioms asLogd_spec

end Library.Numerics.Float64.Lgamma.LgammaLogd
