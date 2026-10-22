import Library.Numerics.Float64.Log2.Log2Main

/-!
`Log2.log2 (2 ^ k) = k` for every power of two `2 ^ k` other than 1, subnormal ones included.
Such an argument reaches `Log2.log2Core` with `z = 1` in subinterval 40, where `r`, `logc`, and
every word of `Log2CoreFinal.final2Word` that does not depend on `kd` are fixed words; `powStep`
is the arithmetic that remains.  The kernel evaluates it for each `k` from -1074 to 1025, in
chunks of 50, and the result is the word of `kd`, whose value is `k`.  The checks take about six
minutes.
-/

namespace Library.Numerics.Float64.Log2.Log2Power
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Log.LogCoreBits Log2CoreBits Log2CoreFinal

set_option exponentiation.threshold 4096

-- The 42 kernel checks below each hold a large reduction cache; checked in parallel they exhaust
-- the memory of the build machine, so this file elaborates its declarations in order.
set_option Elab.async false

/-- The bits of `Library.Numerics.Float64.Log.LogCoreBits.kdOf K`. -/
def kdBits (K : UInt64) : UInt64 :=
  if K >>> 63 == 1 then Wasm.IEEE64.sub 0x8000000000000000 (Wasm.IEEE64.convertI64U (0 - K))
  else Wasm.IEEE64.convertI64U K

theorem kd_bits (K : UInt64) : (kdOf K).toBits = kdBits K := by
  unfold kdOf kdBits
  split_ifs <;> simp only [F64Bits.toBits_neg, F64Convert.toBits_toFloat]

/-- `final2Word` for `z = 1` in subinterval 40, after the words that do not depend on `kd`. -/
def powStep (K : UInt64) : UInt64 :=
  let t3 := Wasm.IEEE64.add K 0x3F86FE53B1500000
  let hi := Wasm.IEEE64.add t3 0xBF86E77B557205FB
  Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.sub t3 hi)
    0xBF86E77B557205FB) 0xBE0348FE46B8E4E9) 0xBF06D84894FBBE41) hi

/-- The word of `k = j - 1074` as `Library.Numerics.Float64.Log.LogCoreBits.kOf` gives it. -/
def kOfIndex (j : Nat) : UInt64 := UInt64.ofNat ((j + 18446744073709550542) % 18446744073709551616)

def powCheck (j : Nat) : Bool :=
  j == 1074 || powStep (kdBits (kOfIndex j)) == kdBits (kOfIndex j)

theorem chunk0 : ∀ i : Fin 50, powCheck (50 * 0 + i.val) = true := by
  decide +kernel

theorem chunk1 : ∀ i : Fin 50, powCheck (50 * 1 + i.val) = true := by
  decide +kernel

theorem chunk2 : ∀ i : Fin 50, powCheck (50 * 2 + i.val) = true := by
  decide +kernel

theorem chunk3 : ∀ i : Fin 50, powCheck (50 * 3 + i.val) = true := by
  decide +kernel

theorem chunk4 : ∀ i : Fin 50, powCheck (50 * 4 + i.val) = true := by
  decide +kernel

theorem chunk5 : ∀ i : Fin 50, powCheck (50 * 5 + i.val) = true := by
  decide +kernel

theorem chunk6 : ∀ i : Fin 50, powCheck (50 * 6 + i.val) = true := by
  decide +kernel

theorem chunk7 : ∀ i : Fin 50, powCheck (50 * 7 + i.val) = true := by
  decide +kernel

theorem chunk8 : ∀ i : Fin 50, powCheck (50 * 8 + i.val) = true := by
  decide +kernel

theorem chunk9 : ∀ i : Fin 50, powCheck (50 * 9 + i.val) = true := by
  decide +kernel

theorem chunk10 : ∀ i : Fin 50, powCheck (50 * 10 + i.val) = true := by
  decide +kernel

theorem chunk11 : ∀ i : Fin 50, powCheck (50 * 11 + i.val) = true := by
  decide +kernel

theorem chunk12 : ∀ i : Fin 50, powCheck (50 * 12 + i.val) = true := by
  decide +kernel

theorem chunk13 : ∀ i : Fin 50, powCheck (50 * 13 + i.val) = true := by
  decide +kernel

theorem chunk14 : ∀ i : Fin 50, powCheck (50 * 14 + i.val) = true := by
  decide +kernel

theorem chunk15 : ∀ i : Fin 50, powCheck (50 * 15 + i.val) = true := by
  decide +kernel

theorem chunk16 : ∀ i : Fin 50, powCheck (50 * 16 + i.val) = true := by
  decide +kernel

theorem chunk17 : ∀ i : Fin 50, powCheck (50 * 17 + i.val) = true := by
  decide +kernel

theorem chunk18 : ∀ i : Fin 50, powCheck (50 * 18 + i.val) = true := by
  decide +kernel

theorem chunk19 : ∀ i : Fin 50, powCheck (50 * 19 + i.val) = true := by
  decide +kernel

theorem chunk20 : ∀ i : Fin 50, powCheck (50 * 20 + i.val) = true := by
  decide +kernel

theorem chunk21 : ∀ i : Fin 50, powCheck (50 * 21 + i.val) = true := by
  decide +kernel

theorem chunk22 : ∀ i : Fin 50, powCheck (50 * 22 + i.val) = true := by
  decide +kernel

theorem chunk23 : ∀ i : Fin 50, powCheck (50 * 23 + i.val) = true := by
  decide +kernel

theorem chunk24 : ∀ i : Fin 50, powCheck (50 * 24 + i.val) = true := by
  decide +kernel

theorem chunk25 : ∀ i : Fin 50, powCheck (50 * 25 + i.val) = true := by
  decide +kernel

theorem chunk26 : ∀ i : Fin 50, powCheck (50 * 26 + i.val) = true := by
  decide +kernel

theorem chunk27 : ∀ i : Fin 50, powCheck (50 * 27 + i.val) = true := by
  decide +kernel

theorem chunk28 : ∀ i : Fin 50, powCheck (50 * 28 + i.val) = true := by
  decide +kernel

theorem chunk29 : ∀ i : Fin 50, powCheck (50 * 29 + i.val) = true := by
  decide +kernel

theorem chunk30 : ∀ i : Fin 50, powCheck (50 * 30 + i.val) = true := by
  decide +kernel

theorem chunk31 : ∀ i : Fin 50, powCheck (50 * 31 + i.val) = true := by
  decide +kernel

theorem chunk32 : ∀ i : Fin 50, powCheck (50 * 32 + i.val) = true := by
  decide +kernel

theorem chunk33 : ∀ i : Fin 50, powCheck (50 * 33 + i.val) = true := by
  decide +kernel

theorem chunk34 : ∀ i : Fin 50, powCheck (50 * 34 + i.val) = true := by
  decide +kernel

theorem chunk35 : ∀ i : Fin 50, powCheck (50 * 35 + i.val) = true := by
  decide +kernel

theorem chunk36 : ∀ i : Fin 50, powCheck (50 * 36 + i.val) = true := by
  decide +kernel

theorem chunk37 : ∀ i : Fin 50, powCheck (50 * 37 + i.val) = true := by
  decide +kernel

theorem chunk38 : ∀ i : Fin 50, powCheck (50 * 38 + i.val) = true := by
  decide +kernel

theorem chunk39 : ∀ i : Fin 50, powCheck (50 * 39 + i.val) = true := by
  decide +kernel

theorem chunk40 : ∀ i : Fin 50, powCheck (50 * 40 + i.val) = true := by
  decide +kernel

theorem chunk41 : ∀ i : Fin 50, powCheck (50 * 41 + i.val) = true := by
  decide +kernel

theorem pow_check (j : Nat) (hj : j < 2100) : powCheck j = true := by
  have key : ∀ c < 42, ∀ i < 50, powCheck (50 * c + i) = true := by
    intro c hc
    interval_cases c
    · exact fun i hi => chunk0 ⟨i, hi⟩
    · exact fun i hi => chunk1 ⟨i, hi⟩
    · exact fun i hi => chunk2 ⟨i, hi⟩
    · exact fun i hi => chunk3 ⟨i, hi⟩
    · exact fun i hi => chunk4 ⟨i, hi⟩
    · exact fun i hi => chunk5 ⟨i, hi⟩
    · exact fun i hi => chunk6 ⟨i, hi⟩
    · exact fun i hi => chunk7 ⟨i, hi⟩
    · exact fun i hi => chunk8 ⟨i, hi⟩
    · exact fun i hi => chunk9 ⟨i, hi⟩
    · exact fun i hi => chunk10 ⟨i, hi⟩
    · exact fun i hi => chunk11 ⟨i, hi⟩
    · exact fun i hi => chunk12 ⟨i, hi⟩
    · exact fun i hi => chunk13 ⟨i, hi⟩
    · exact fun i hi => chunk14 ⟨i, hi⟩
    · exact fun i hi => chunk15 ⟨i, hi⟩
    · exact fun i hi => chunk16 ⟨i, hi⟩
    · exact fun i hi => chunk17 ⟨i, hi⟩
    · exact fun i hi => chunk18 ⟨i, hi⟩
    · exact fun i hi => chunk19 ⟨i, hi⟩
    · exact fun i hi => chunk20 ⟨i, hi⟩
    · exact fun i hi => chunk21 ⟨i, hi⟩
    · exact fun i hi => chunk22 ⟨i, hi⟩
    · exact fun i hi => chunk23 ⟨i, hi⟩
    · exact fun i hi => chunk24 ⟨i, hi⟩
    · exact fun i hi => chunk25 ⟨i, hi⟩
    · exact fun i hi => chunk26 ⟨i, hi⟩
    · exact fun i hi => chunk27 ⟨i, hi⟩
    · exact fun i hi => chunk28 ⟨i, hi⟩
    · exact fun i hi => chunk29 ⟨i, hi⟩
    · exact fun i hi => chunk30 ⟨i, hi⟩
    · exact fun i hi => chunk31 ⟨i, hi⟩
    · exact fun i hi => chunk32 ⟨i, hi⟩
    · exact fun i hi => chunk33 ⟨i, hi⟩
    · exact fun i hi => chunk34 ⟨i, hi⟩
    · exact fun i hi => chunk35 ⟨i, hi⟩
    · exact fun i hi => chunk36 ⟨i, hi⟩
    · exact fun i hi => chunk37 ⟨i, hi⟩
    · exact fun i hi => chunk38 ⟨i, hi⟩
    · exact fun i hi => chunk39 ⟨i, hi⟩
    · exact fun i hi => chunk40 ⟨i, hi⟩
    · exact fun i hi => chunk41 ⟨i, hi⟩
  have h := key (j / 50) (by omega) (j % 50) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at h

theorem r40_eq : Wasm.IEEE64.mul (Wasm.IEEE64.sub (Wasm.IEEE64.sub 0x3FF0000000000000
    0x3FF0200004292367) 0x3C9B7FF365324681) 0x3FEFC07EF9CAA76B = 0xBF7FC0831AAC4A80 := by
  decide +kernel

theorem final_pow (K : UInt64) :
    final2Word 0xBF7FC0831AAC4A80 K 0x3F86FE53B1500000 = powStep K := by
  have e1 : Wasm.IEEE64.mul (F64HighWord.high 0xBF7FC0831AAC4A80) 0x3FF7154765200000 =
      0xBF86E77B557205FB := by decide +kernel
  have e2 : Wasm.IEEE64.add (Wasm.IEEE64.mul (Wasm.IEEE64.sub 0xBF7FC0831AAC4A80
      (F64HighWord.high 0xBF7FC0831AAC4A80)) 0x3FF7154765200000)
      (Wasm.IEEE64.mul 0xBF7FC0831AAC4A80 0x3DE705FC2EEFA200) = 0xBE0348FE46B8E4E9 := by
    decide +kernel
  have e3 : Wasm.IEEE64.mul (Wasm.IEEE64.mul 0xBF7FC0831AAC4A80 0xBF7FC0831AAC4A80)
      (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add 0xBFE71547652B8339
        (Wasm.IEEE64.mul 0xBF7FC0831AAC4A80 0x3FDEC709DC3A04BE))
        (Wasm.IEEE64.mul (Wasm.IEEE64.mul 0xBF7FC0831AAC4A80 0xBF7FC0831AAC4A80)
          (Wasm.IEEE64.add 0xBFD7154764702FFB
            (Wasm.IEEE64.mul 0xBF7FC0831AAC4A80 0x3FD2776C50034C48))))
        (Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul 0xBF7FC0831AAC4A80 0xBF7FC0831AAC4A80)
          (Wasm.IEEE64.mul 0xBF7FC0831AAC4A80 0xBF7FC0831AAC4A80))
          (Wasm.IEEE64.add 0xBFCEC7B328EA92BC
            (Wasm.IEEE64.mul 0xBF7FC0831AAC4A80 0x3FCA6225E117F92E)))) =
      0xBF06D84894FBBE41 := by
    decide +kernel
  simp only [final2Word, powStep, e1, e2, e3]

/-- `Log2.log2Core` on the word `E 2 ^ 52 mod 2 ^ 64`, the argument `2 ^ (E - 1023)` or its
scaled form, gives exactly `E - 1023` for `E ≠ 1023`. -/
theorem core2_power (ix : UInt64) (E : Int) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046) (hE0 : E ≠ 1023)
    (hix : (ix.toNat : Int) = E * 4503599627370496 % 18446744073709551616) :
    Finite (Log2.log2Core Log2.log2Table Log2.log2Table2 ix).toBits ∧
      value (Log2.log2Core Log2.log2Table Log2.log2Table2 ix).toBits = ((E - 1023 : Int) : ℝ) := by
  have hix' : (ix.toNat : Int) = (E * 4503599627370496 + ((0 : Nat) : Int)) % 18446744073709551616 := by
    rw [Nat.cast_zero, add_zero]
    exact hix
  obtain ⟨hz, -, hk⟩ := fields_lower ix E 0 hE1 hE2 (by norm_num) hix'
  have hi := index2_lower ix E 0 hE1 hE2 (by norm_num) hix'
  rw [Nat.zero_div, zero_add] at hi
  have hz' : zOf ix = 0x3FF0000000000000 := UInt64.toNat_inj.mp (by rw [hz]; rfl)
  have e80 : Log2.log2Table2[2 * 40]! = 0x3FF0200004292367 := by decide +kernel
  have e81 : Log2.log2Table2[2 * 40 + 1]! = 0x3C9B7FF365324681 := by decide +kernel
  have f80 : Log2.log2Table[2 * 40]! = 0x3FEFC07EF9CAA76B := by decide +kernel
  have f81 : Log2.log2Table[2 * 40 + 1]! = 0x3F86FE53B1500000 := by decide +kernel
  have hzf : Finite (zOf ix) := by
    rw [hz']
    unfold CodeLib.IEEE64.Finite
    decide
  have hrf : Finite (Wasm.IEEE64.mul (Wasm.IEEE64.sub (Wasm.IEEE64.sub (zOf ix)
      Log2.log2Table2[2 * 40]!) Log2.log2Table2[2 * 40 + 1]!) Log2.log2Table[2 * 40]!) := by
    rw [hz', e80, e81, f80, r40_eq]
    unfold CodeLib.IEEE64.Finite
    decide
  have hw := Log2CoreStep.core2_word ix 40 (by norm_num) hi hzf hrf
  rw [hz', e80, e81, f80, f81, r40_eq, final_pow, kd_bits] at hw
  have hK : kOf ix = kOfIndex (E + 51).toNat := by
    apply UInt64.toNat_inj.mp
    simp only [kOfIndex, UInt64.toNat_ofNat', Nat.reducePow]
    omega
  have hc := pow_check (E + 51).toNat (by omega)
  simp only [powCheck, Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with hc | hc
  · omega
  · rw [← hK] at hc
    rw [hw, hc, ← kd_bits]
    exact Library.Numerics.Float64.Log.LogCoreBits.kd_value (kOf ix) (E - 1023) (by omega) (by omega) hk

/-- The scaled word of a subnormal power of two `2 ^ (j - 1074)`. -/
theorem scaled_power : ∀ j : Fin 52,
    (Wasm.IEEE64.mul (UInt64.ofNat (2 ^ j.val)) 0x4330000000000000 - (52 : UInt64) <<< 52).toNat =
      (j.val + 4045) % 4096 * 4503599627370496 := by
  decide +kernel

/-- `Log2.log2 (2 ^ k) = k` for every power of two other than 1. -/
theorem log2_power (x : Float) (k : Int) (hk1 : -1074 ≤ k) (hk2 : k ≤ 1023) (hk0 : k ≠ 0)
    (hx : value x.toBits = 2 ^ k) :
    Finite (Log2.log2 x).toBits ∧ value (Log2.log2 x).toBits = k := by
  have hpos : 0 < value x.toBits := by
    rw [hx]
    exact zpow_pos (by norm_num) k
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude x.toBits) with h | h
    · exfalso
      have : value x.toBits = 0 := by
        simp only [value, Wasm.IEEE64.scaledValue, h]
        split <;> simp
      linarith
    · exact h
  have hs : Wasm.IEEE64.sign x.toBits = false := by
    cases h : Wasm.IEEE64.sign x.toBits
    · rfl
    · exact absurd ((F64Magnitude.sign_value _ hmag).mp h) (not_lt.mpr hpos.le)
  have hlt : x.toBits.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  -- the bits of `x` from its value
  have hbits : ∀ w : UInt64, w.toNat < 2 ^ 63 → value w = 2 ^ k → x.toBits.toNat = w.toNat := by
    intro w hw hwv
    rcases lt_trichotomy x.toBits.toNat w.toNat with h | h | h
    · have := F64PositiveOrder.value_strict (left := x.toBits) (right := w) hw h
      linarith
    · exact h
    · have := F64PositiveOrder.value_strict (left := w) (right := x.toBits) hlt h
      linarith
  have hfin : (k : ℝ) = ((k + 1023 - 1023 : Int) : ℝ) := by push_cast; ring
  by_cases hnorm : -1022 ≤ k
  · set e := (k + 1023).toNat with he
    have hwn : (UInt64.ofNat (e * 4503599627370496)).toNat = e * 4503599627370496 := by
      rw [UInt64.toNat_ofNat']
      apply Nat.mod_eq_of_lt
      simp only [Nat.reducePow]
      omega
    have hws : Wasm.IEEE64.sign (UInt64.ofNat (e * 4503599627370496)) = false := by
      simp only [Wasm.IEEE64.sign, hwn, decide_eq_false_iff_not, not_le]
      omega
    have hwe : Wasm.IEEE64.exponent (UInt64.ofNat (e * 4503599627370496)) = e := by
      simp only [Wasm.IEEE64.exponent, hwn]
      omega
    have hwf : Wasm.IEEE64.fraction (UInt64.ofNat (e * 4503599627370496)) = 0 := by
      simp only [Wasm.IEEE64.fraction, hwn]
      omega
    have hwv : value (UInt64.ofNat (e * 4503599627370496)) = 2 ^ k := by
      rw [Library.Numerics.Float64.Log.LogMain.normal_form _ hws (by rw [hwe]; omega), hwe, hwf, Nat.cast_zero, add_zero,
        show k = ((52 : Nat) : Int) + ((e : Int) - 1075) by omega, zpow_add₀ two_ne_zero,
        zpow_natCast]
    have hxn := hbits _ (by rw [hwn]; simp only [Nat.reducePow]; omega) hwv
    rw [hwn] at hxn
    have hlo : 4503599627370496 ≤ x.toBits.toNat := by omega
    have hhi : x.toBits.toNat < 9218868437227405312 := by omega
    have hnear : x.toBits.toNat < 4606800540372828160 ∨ 4607381812656734208 ≤ x.toBits.toNat := by
      omega
    rw [Log2.log2, Log2Branches.normal_selected _ _ x hlo hhi hnear, hfin]
    exact core2_power x.toBits (k + 1023) (by omega) (by omega) (by omega) (by omega)
  · set j := (k + 1074).toNat with hj
    have hj52 : j < 52 := by omega
    have hp0 : 0 < 2 ^ j := Nat.two_pow_pos j
    have hp : 2 ^ j < 4503599627370496 := by
      calc 2 ^ j < 2 ^ 52 := Nat.pow_lt_pow_right (by norm_num) hj52
        _ = 4503599627370496 := by norm_num
    have hwn : (UInt64.ofNat (2 ^ j)).toNat = 2 ^ j := by
      rw [UInt64.toNat_ofNat']
      apply Nat.mod_eq_of_lt
      simp only [Nat.reducePow]
      omega
    have hws : Wasm.IEEE64.sign (UInt64.ofNat (2 ^ j)) = false := by
      simp only [Wasm.IEEE64.sign, hwn, decide_eq_false_iff_not, not_le]
      omega
    have hwe : Wasm.IEEE64.exponent (UInt64.ofNat (2 ^ j)) = 0 := by
      simp only [Wasm.IEEE64.exponent, hwn]
      omega
    have hwf : Wasm.IEEE64.fraction (UInt64.ofNat (2 ^ j)) = 2 ^ j := by
      simp only [Wasm.IEEE64.fraction, hwn]
      omega
    have hwv : value (UInt64.ofNat (2 ^ j)) = 2 ^ k := by
      simp only [value, Wasm.IEEE64.scaledValue, hws, Bool.false_eq_true, ite_false,
        Wasm.IEEE64.scaledMagnitude, hwe, hwf, beq_self_eq_true, ↓reduceIte]
      push_cast
      rw [show k = ((j : Nat) : Int) - ((1074 : Nat) : Int) by omega, zpow_sub₀ two_ne_zero,
        zpow_natCast, zpow_natCast]
    have hxn := hbits _ (by rw [hwn]; simp only [Nat.reducePow]; omega) hwv
    rw [hwn] at hxn
    have hxb : x.toBits = UInt64.ofNat (2 ^ j) := UInt64.toNat_inj.mp (by rw [hxn, hwn])
    have hcn : Wasm.IEEE64.isNaN 0x4330000000000000 = false := by decide
    have hmul : (x * Float.ofBits 0x4330000000000000).toBits =
        Wasm.IEEE64.mul x.toBits 0x4330000000000000 := by
      rw [F64Bits.toBits_mul, F64Bits.toBits_ofBits, hcn]
      rfl
    rw [Log2.log2, Log2Branches.subnormal_selected _ _ x (by omega) (by omega), hmul, hxb, hfin]
    apply core2_power _ (k + 1023) (by omega) (by omega) (by omega)
    have hsp := scaled_power ⟨j, hj52⟩
    simp only at hsp
    rw [hsp]
    push_cast
    omega

#print axioms kd_bits
#print axioms pow_check
#print axioms final_pow
#print axioms core2_power
#print axioms scaled_power
#print axioms log2_power

end Library.Numerics.Float64.Log2.Log2Power
