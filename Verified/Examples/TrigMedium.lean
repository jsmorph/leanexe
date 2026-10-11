import Verified.Examples.TrigMediumA
import Verified.Examples.TrigMediumC
import Verified.Examples.TrigWords
import LeanExe.ProofKit.F64Convert
import LeanExe.ProofKit.F64PositiveOrder

/-!
The accuracy of `Trig.remMedium`.  For a positive double `x` with `1 ≤ x` and high word below
`0x413921fb`, the returned count `N` gives `r = x - N π/2` with `2 ^ -63 ≤ |r|` and
`|r| ≤ π/4 + 2 ^ -28`, and `y0 + y1` lies within `|r| / 2 ^ 60` of `r`, with `|y1| ≤ |y0| / 2 ^ 52`.
-/

namespace Verified.Examples.TrigMedium

open CodeLib.IEEE64 LeanExe.ProofKit TrigFloatTools TrigNearest TrigSmall TrigMediumConst
  TrigMediumFn TrigMediumCases TrigMediumA TrigMediumB TrigMediumC

/-- `remMedium` on words. -/
def remMediumW (X ix : UInt64) : UInt64 × UInt64 × UInt64 :=
  let F := Wasm.IEEE64.sub (Wasm.IEEE64.add (Wasm.IEEE64.mul X invpio2) shifter) shifter
  if ((Y0 X F >>> 52) &&& (0x7ff : UInt64)) + (16 : UInt64) < ix >>> (20 : UInt64) then
    if ((Y0b X F >>> 52) &&& (0x7ff : UInt64)) + (49 : UInt64) < ix >>> (20 : UInt64) then
      (Wasm.IEEE64.truncSatI64U F, Y0c X F,
        Wasm.IEEE64.sub (Wasm.IEEE64.sub (R3 X F) (Y0c X F)) (W3' X F))
    else (Wasm.IEEE64.truncSatI64U F, Y0b X F,
      Wasm.IEEE64.sub (Wasm.IEEE64.sub (R2 X F) (Y0b X F)) (W2' X F))
  else (Wasm.IEEE64.truncSatI64U F, Y0 X F,
    Wasm.IEEE64.sub (Wasm.IEEE64.sub (R1 X F) (Y0 X F)) (W1 F))

theorem const_bits :
    (Float.ofBits 0x3FE45F306DC9C883).toBits = invpio2 ∧
      (Float.ofBits 0x3FF921FB54400000).toBits = pio2_1 ∧
      (Float.ofBits 0x3DD0B4611A626331).toBits = pio2_1t ∧
      (Float.ofBits 0x3DD0B4611A600000).toBits = pio2_2 ∧
      (Float.ofBits 0x3BA3198A2E037073).toBits = pio2_2t ∧
      (Float.ofBits 0x3BA3198A2E000000).toBits = pio2_3 ∧
      (Float.ofBits 0x397B839A252049C1).toBits = pio2_3t ∧
      (6755399441055744.0 : Float).toBits = shifter := by
  simp only [F64Bits.toBits_ofBits]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem remMedium_bits (x : Float) (ix : UInt64) :
    (Trig.remMedium x ix).1 = (remMediumW x.toBits ix).1 ∧
      (Trig.remMedium x ix).2.1.toBits = (remMediumW x.toBits ix).2.1 ∧
      (Trig.remMedium x ix).2.2.toBits = (remMediumW x.toBits ix).2.2 := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := const_bits
  unfold Trig.remMedium remMediumW Y0c Y0b Y0 W3' W2' R3 R2 R1 A3 A2 W3 W2 W1
  simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_add, F64Convert.toUInt64_eq,
    c0, c1, c2, c3, c4, c7]
  split_ifs <;> simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_add,
    c0, c1, c2, c3, c4, c5, c6, c7, and_self]

/-- The exponent test of `remMedium` compares exponent fields. -/
theorem cond_iff (Y X k : UInt64) (hk : k.toNat < 2 ^ 11) (hX : X.toNat < 2 ^ 63) :
    ((Y >>> 52) &&& (0x7ff : UInt64)) + k < (X >>> 32) >>> 20 ↔
      Wasm.IEEE64.exponent Y + k.toNat < Wasm.IEEE64.exponent X := by
  have hY : ((Y >>> 52) &&& (0x7ff : UInt64)).toNat = Wasm.IEEE64.exponent Y := by
    rw [UInt64.toNat_and, TrigWords.shr_toNat]
    unfold Wasm.IEEE64.exponent
    have h1 : (0x7ff : UInt64).toNat = 2 ^ 11 - 1 := rfl
    have h2 : (52 : UInt64).toNat % 64 = 52 := rfl
    rw [h1, h2, Nat.and_two_pow_sub_one_eq_mod]
  have hXe : ((X >>> 32) >>> 20).toNat = Wasm.IEEE64.exponent X := by
    rw [TrigWords.shr_toNat, TrigWords.shr_toNat]
    have h1 : (32 : UInt64).toNat % 64 = 32 := rfl
    have h2 : (20 : UInt64).toNat % 64 = 20 := rfl
    rw [h1, h2, Nat.div_div_eq_div_mul, ← pow_add]
    unfold Wasm.IEEE64.exponent
    rw [Nat.mod_eq_of_lt (by omega)]
  have he : Wasm.IEEE64.exponent Y < 2 ^ 11 := Nat.mod_lt _ (by norm_num)
  have hsum : Wasm.IEEE64.exponent Y + k.toNat < 2 ^ 64 :=
    lt_of_lt_of_le (Nat.add_lt_add he hk) (by norm_num)
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, hY, hXe, Nat.mod_eq_of_lt hsum]

/-- The saturating conversion of a positive integral double below `2 ^ 20` is its value. -/
theorem trunc_count (F : UInt64) (N : Nat) (hF : CodeLib.IEEE64.Finite F) (hN1 : 1 ≤ N) (hN2 : N ≤ 2 ^ 20)
    (hv : Wasm.IEEE64.scaledValue F = (N : Int) * 2 ^ 1074) :
    (Wasm.IEEE64.truncSatI64U F).toNat = N := by
  have hfin : Wasm.IEEE64.isFinite F = true := hF
  have hnan : Wasm.IEEE64.isNaN F = false := by
    unfold Wasm.IEEE64.isFinite at hfin
    unfold Wasm.IEEE64.isNaN
    simp only [bne_iff_ne, ne_eq] at hfin
    simp [hfin]
  have hsign : Wasm.IEEE64.sign F = false := by
    by_contra hs
    rw [Bool.not_eq_false] at hs
    unfold Wasm.IEEE64.scaledValue at hv
    simp only [hs, ite_true] at hv
    have h0 : (0 : Int) ≤ (Wasm.IEEE64.scaledMagnitude F : Int) := Nat.cast_nonneg _
    have h1 : (0 : Int) < (N : Int) * 2 ^ 1074 := by positivity
    generalize (N : Int) * 2 ^ 1074 = P at hv h1
    omega
  have hmag : Wasm.IEEE64.scaledMagnitude F = N * 2 ^ 1074 := by
    unfold Wasm.IEEE64.scaledValue at hv
    simp only [hsign, Bool.false_eq_true, ite_false] at hv
    exact_mod_cast hv
  have hN : (N : Int) < 2 ^ 64 - 1 := by
    have : (N : Int) ≤ 2 ^ 20 := by exact_mod_cast hN2
    linarith
  unfold Wasm.IEEE64.truncSatI64U Wasm.IEEE64.truncatedInt
  simp only [hnan, hfin, hsign, hmag, Bool.false_eq_true, ite_true, ite_false,
    Nat.mul_div_cancel _ (show 0 < 2 ^ 1074 by positivity)]
  split_ifs with h1 h2
  · clear hv hmag
    omega
  · exact absurd h2 (not_le.mpr hN)
  · unfold Wasm.IEEE64.intToUInt64
    split_ifs with h3
    · clear hv hmag
      omega
    · rw [Int.natAbs_natCast, UInt64.toNat_ofNat_of_lt']
      exact lt_of_le_of_lt hN2 (by norm_num)

/-- The value of a positive normal double. -/
theorem value_normal (X : UInt64) (hs : X.toNat < 2 ^ 63) (he : 1 ≤ Wasm.IEEE64.exponent X) :
    value X = ((X.toNat % 2 ^ 52 + 2 ^ 52 : Nat) : ℝ) * 2 ^ Wasm.IEEE64.exponent X / 2 ^ 1075 := by
  have hsign : Wasm.IEEE64.sign X = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
    omega
  rw [F64Magnitude.normal_value X hsign (by omega)]
  unfold Wasm.IEEE64.fraction
  have h2 : (2 : ℝ) ^ Wasm.IEEE64.exponent X = 2 ^ (Wasm.IEEE64.exponent X - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel he]
  rw [h2]
  push_cast
  field_simp
  ring

/-- The accuracy of `remMedium` on a positive double from 1 to below `0x413921FB00000000`. -/
theorem remMedium_spec (x : Float) (hs : x.toBits.toNat < 2 ^ 63)
    (hlo : 0x3FF0000000000000 ≤ x.toBits.toNat) (hhi : x.toBits.toNat < 0x413921FB00000000) :
    ∃ N : Nat, (Trig.remMedium x (x.toBits >>> 32)).1.toNat = N ∧
      CodeLib.IEEE64.Finite (Trig.remMedium x (x.toBits >>> 32)).2.1.toBits ∧
      CodeLib.IEEE64.Finite (Trig.remMedium x (x.toBits >>> 32)).2.2.toBits ∧
      |value (Trig.remMedium x (x.toBits >>> 32)).2.1.toBits +
          value (Trig.remMedium x (x.toBits >>> 32)).2.2.toBits -
          (value x.toBits - N * (Real.pi / 2))| ≤ |value x.toBits - N * (Real.pi / 2)| / 2 ^ 60 ∧
      |value (Trig.remMedium x (x.toBits >>> 32)).2.2.toBits| ≤
        |value (Trig.remMedium x (x.toBits >>> 32)).2.1.toBits| / 2 ^ 52 ∧
      1 / 2 ^ 63 ≤ |value x.toBits - N * (Real.pi / 2)| ∧
      |value x.toBits - N * (Real.pi / 2)| ≤ Real.pi / 4 + 1 / 2 ^ 28 := by
  obtain ⟨b1, b2, b3⟩ := remMedium_bits x (x.toBits >>> 32)
  rw [b1, b2, b3]
  generalize x.toBits = X at hs hlo hhi ⊢
  have hXf : CodeLib.IEEE64.Finite X := by
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite Wasm.IEEE64.exponent
    simp only [bne_iff_ne, ne_eq]
    omega
  have hE1 : 1023 ≤ Wasm.IEEE64.exponent X := by unfold Wasm.IEEE64.exponent; omega
  have hE2 : Wasm.IEEE64.exponent X ≤ 1043 := by unfold Wasm.IEEE64.exponent; omega
  obtain ⟨c1, c2⟩ : Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) = 2 ^ 1074 ∧
      Wasm.IEEE64.scaledValue (0x413921FB00000000 : UInt64) = 1647099 * 2 ^ 1074 := by
    constructor <;> decide +kernel
  have hx1 : (1 : ℝ) ≤ value X := by
    have h := (F64PositiveOrder.value_le_iff (left := 0x3FF0000000000000) (right := X)
      (by decide) hs).mpr hlo
    rw [TrigSmall.value_of_scaled 0x3FF0000000000000, c1] at h
    push_cast at h
    rwa [div_self (by positivity)] at h
  have hx2 : value X * (2 / Real.pi) ≤ 2 ^ 20 := by
    have h := F64PositiveOrder.value_strict (left := X) (right := 0x413921FB00000000)
      (by decide) hhi
    rw [TrigSmall.value_of_scaled 0x413921FB00000000, c2] at h
    push_cast at h
    rw [mul_div_assoc, div_self (by positivity), mul_one] at h
    have hpi : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    linarith
  obtain ⟨hFf, N, hN1, hN2, hFv, hNx⟩ := fn_spec X hXf hx1 hx2
  have hdist : 1 / 2 ^ 63 < |value X * (2 / Real.pi) - N| := by
    rw [value_normal X hs (by omega)]
    have h := TrigDistance.quadrant_distance (Wasm.IEEE64.exponent X) (X.toNat % 2 ^ 52 + 2 ^ 52)
      (by omega) (by omega) (by omega) (by omega) (N : Int)
    rwa [Int.cast_natCast] at h
  refine ⟨N, ?_⟩
  unfold remMediumW
  dsimp only
  set F := Wasm.IEEE64.sub (Wasm.IEEE64.add (Wasm.IEEE64.mul X invpio2) shifter) shifter
    with hFdef
  have hM : Med X F N := ⟨hXf, hx1, hx2, hFf, hN1, hN2, hFv, hNx, hdist⟩
  obtain ⟨hrl, hru, -⟩ := med_common X F N hM
  have hcount := trunc_count F N hFf hN1 hN2 hFv
  have hk16 := cond_iff (Y0 X F) X 16 (by decide) hs
  have hk49 := cond_iff (Y0b X F) X 49 (by decide) hs
  rw [show (16 : UInt64).toNat = 16 from rfl] at hk16
  rw [show (49 : UInt64).toNat = 49 from rfl] at hk49
  simp only [hk16, hk49]
  split_ifs with hA hB
  · obtain ⟨f1, f2, e1, e2⟩ := caseC X F N hM hA hB
    exact ⟨hcount, f1, f2, e1, e2, hrl, hru⟩
  · obtain ⟨f1, f2, e1, e2⟩ := caseB X F N hM hA (by omega)
    exact ⟨hcount, f1, f2, e1, e2, hrl, hru⟩
  · obtain ⟨f1, f2, e1, e2⟩ := caseA X F N hM (by omega)
    exact ⟨hcount, f1, f2, e1, e2, hrl, hru⟩

#print axioms const_bits
#print axioms remMedium_bits
#print axioms cond_iff
#print axioms trunc_count
#print axioms value_normal
#print axioms remMedium_spec

end Verified.Examples.TrigMedium
