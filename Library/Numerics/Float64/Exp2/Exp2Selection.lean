import Library.Numerics.Float64.Exp2.Compiled
import Library.Numerics.Float64.Exp.ExpIntegerSelection
import LeanExe.ProofKit.F64BinadeWord
import LeanExe.ProofKit.F64ErrorTrack
import LeanExe.ProofKit.F64Magnitude

/-!
The reduction of `Exp2.exp2Core`.  Adding `0x1.8p52 / 128 = 3 · 2 ^ 44` to `x` rounds `x` to the
nearest multiple `k / 128`: for `|x| ≤ 2 ^ 12` the sum lies in the binade `[2 ^ 45, 2 ^ 46)`,
whose spacing is `2 ^ -7`.  The bits of the sum are `0x42C8000000000000 + k`, subtracting the
shift gives `k / 128` exactly, and `x - k / 128` is exact, with magnitude at most `1/256`.
-/

namespace Library.Numerics.Float64.Exp2.Exp2Selection
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- `x + 0x1.8p52 / 128`, rounded. -/
def shifted (x : UInt64) : UInt64 := Wasm.IEEE64.add x 0x42C8000000000000

/-- The multiple of `1/128` that the shift selects. -/
def selected (x : UInt64) : UInt64 := Wasm.IEEE64.sub (shifted x) 0x42C8000000000000

/-- `x` less the selected multiple. -/
def residual (x : UInt64) : UInt64 := Wasm.IEEE64.sub x (selected x)

theorem shift_values :
    Finite 0x42C8000000000000 ∧ Wasm.IEEE64.sign 0x42C8000000000000 = false ∧
    Wasm.IEEE64.scaledValue 0x42C8000000000000 = (3 : Int) * 2 ^ 1118 ∧
    value 0x42C8000000000000 = (3 : ℝ) * 2 ^ 44 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold CodeLib.IEEE64.Finite
    decide +kernel
  · decide +kernel
  · norm_num [Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.sign,
      Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  · norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

/-- Rounding a scaled magnitude in the binade `[2 ^ 1119, 2 ^ 1120)`, whose spacing is
`2 ^ 1067` scaled units. -/
theorem packing_binade (n : Nat) (hl : 2 ^ 1119 ≤ n) (hu : n < 2 ^ 1120) :
    Finite (Wasm.IEEE64.roundScaledMagnitude false n) ∧
    Wasm.IEEE64.sign (Wasm.IEEE64.roundScaledMagnitude false n) = false ∧
    ∃ R : Nat,
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude false n) =
        (R : Int) * 2 ^ 1067 ∧
      |(R : ℝ) * (2 : ℝ) ^ 1067 - (n : ℝ)| ≤ (2 : ℝ) ^ 1067 / 2 := by
  have hn : n ≠ 0 := by omega
  have h53 : 2 ^ 53 ≤ n := (by norm_num : (2 : Nat) ^ 53 ≤ 2 ^ 1119).trans hl
  have hmax : n < 2 ^ 2097 := hu.trans_le (by norm_num)
  have hlog : Nat.log2 n = 1119 := (Nat.log2_eq_iff hn).mpr ⟨hl, hu⟩
  let R := Wasm.IEEE32.roundShift n 1067
  have hr : roundedMagnitude n = R * 2 ^ 1067 := by
    simpa only [hlog, show 1119 - 52 = 1067 by decide] using
      F64Packing.roundedMagnitude_eq_shift n h53
  have hp := F64Packing.pack_spec false n hmax
  have hv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude false n) =
      (R : Int) * 2 ^ 1067 := by
    simp only [Wasm.IEEE64.scaledValue, hp.2.1, hp.2.2, hr,
      Bool.false_eq_true, ite_false, Int.natCast_mul, Int.natCast_pow, Nat.cast_ofNat]
  have he : |(R : ℝ) * (2 : ℝ) ^ 1067 - (n : ℝ)| ≤ (2 : ℝ) ^ 1067 / 2 := by
    simpa only [hr, hlog, show 1119 - 52 = 1067 by decide,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using F64Packing.roundedMagnitude_error n
  exact ⟨hp.1, hp.2.2, R, hv, he⟩

/-- The sum `x + 3 · 2 ^ 44` lies in the binade `[2 ^ 45, 2 ^ 46)`. -/
theorem shifted_sum_binade (x : UInt64) (hx : |value x| ≤ (2 : ℝ) ^ 12) :
    (2 : Int) ^ 1119 ≤ Wasm.IEEE64.scaledValue x + Wasm.IEEE64.scaledValue 0x42C8000000000000 ∧
    Wasm.IEEE64.scaledValue x + Wasm.IEEE64.scaledValue 0x42C8000000000000 <
      (2 : Int) ^ 1120 := by
  have hp : 0 < (2 : ℝ) ^ 1074 := by positivity
  have hzr : |(Wasm.IEEE64.scaledValue x : ℝ)| ≤ (2 : ℝ) ^ 1086 := by
    rw [value, abs_div, abs_of_pos hp] at hx
    calc
      _ ≤ (2 : ℝ) ^ 12 * (2 : ℝ) ^ 1074 := (div_le_iff₀ hp).mp hx
      _ = (2 : ℝ) ^ 1086 := by rw [← pow_add]
  have hzi : |Wasm.IEEE64.scaledValue x| ≤ (2 : Int) ^ 1086 := by exact_mod_cast hzr
  have hb := abs_le.mp hzi
  rw [shift_values.2.2.1]
  norm_num at hb ⊢
  constructor <;> omega

/-- The shifted sum: its scaled value is `(3 · 2 ^ 51 + k) · 2 ^ 1067`, its bits are
`0x42C8000000000000 + k`, and `k` is within `1/2` of `128 x`. -/
theorem shifted_state (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ (2 : ℝ) ^ 12) :
    ∃ k : Int, Finite (shifted x) ∧
      Wasm.IEEE64.scaledValue (shifted x) = (3 * 2 ^ 51 + k) * 2 ^ 1067 ∧
      ((shifted x).toNat : Int) = (0x42C8000000000000 : Int) + k ∧
      |(k : ℝ) - 128 * value x| ≤ 1 / 2 ∧ k.natAbs ≤ 2 ^ 20 := by
  let S := Wasm.IEEE64.scaledValue x + Wasm.IEEE64.scaledValue 0x42C8000000000000
  have hb := shifted_sum_binade x hx
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num) hb.1
  have hS0 : S ≠ 0 := ne_of_gt hSpos
  have hSn : ¬S < 0 := not_lt_of_ge hSpos.le
  dsimp only [S] at hS0 hSn
  have hcast : (S.natAbs : Int) = S := (Int.eq_natAbs_of_nonneg hSpos.le).symm
  have hl : 2 ^ 1119 ≤ S.natAbs := by
    have h : (2 : Int) ^ 1119 ≤ (S.natAbs : Int) := by rw [hcast]; exact hb.1
    exact_mod_cast h
  have hu : S.natAbs < 2 ^ 1120 := by
    have h : (S.natAbs : Int) < (2 : Int) ^ 1120 := by rw [hcast]; exact hb.2
    exact_mod_cast h
  have hm := shift_values.1
  have ha : shifted x = Wasm.IEEE64.roundScaledMagnitude false S.natAbs := by
    simp [shifted, Wasm.IEEE64.add, not_nan_of_finite hxf, not_nan_of_finite hm,
      not_infinite_of_finite hxf, not_infinite_of_finite hm, S, hS0, hSn]
  obtain ⟨hf, hs, R, hv, he⟩ := packing_binade S.natAbs hl hu
  rw [← ha] at hf hs hv
  have hcastR : (S.natAbs : ℝ) = (S : ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun x : Int => (x : ℝ)) hcast
  rw [hcastR] at he
  have hSR : (S : ℝ) = (Wasm.IEEE64.scaledValue x : ℝ) + 3 * (2 : ℝ) ^ 1118 := by
    simp only [S, Int.cast_add, shift_values.2.2.1, Int.cast_mul, Int.cast_pow,
      Int.cast_ofNat]
  have hxv : (Wasm.IEEE64.scaledValue x : ℝ) = value x * (2 : ℝ) ^ 1074 := by
    rw [value]
    field_simp
  rw [hSR, hxv] at he
  have hkR : |((R : ℝ) - 3 * 2 ^ 51) - 128 * value x| ≤ 1 / 2 := by
    have h1067 : (2 : ℝ) ^ 1067 * 128 = (2 : ℝ) ^ 1074 := by norm_num
    have h1118 : (2 : ℝ) ^ 1118 = 2 ^ 51 * 2 ^ 1067 := by rw [← pow_add]
    have hid : (R : ℝ) * (2 : ℝ) ^ 1067 - (value x * (2 : ℝ) ^ 1074 + 3 * (2 : ℝ) ^ 1118) =
        (2 : ℝ) ^ 1067 * (((R : ℝ) - 3 * 2 ^ 51) - 128 * value x) := by
      rw [h1118, ← h1067]
      ring
    rw [hid, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ 1067)] at he
    have hpos : (0 : ℝ) < (2 : ℝ) ^ 1067 := by positivity
    nlinarith only [he, hpos, abs_nonneg (((R : ℝ) - 3 * 2 ^ 51) - 128 * value x)]
  have hxb : |128 * value x| ≤ (2 : ℝ) ^ 19 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 128)]
    calc
      _ ≤ 128 * (2 : ℝ) ^ 12 := mul_le_mul_of_nonneg_left hx (by norm_num)
      _ = (2 : ℝ) ^ 19 := by norm_num
  have hRlo : (2 : ℝ) ^ 52 ≤ R := by
    have h1 := (abs_le.mp hkR).1
    have h2 := (abs_le.mp hxb).1
    norm_num at h1 h2
    rw [show (2 : ℝ) ^ 52 = 4503599627370496 by norm_num]
    linarith
  have hRhi : (R : ℝ) < 2 ^ 53 := by
    have h1 := (abs_le.mp hkR).2
    have h2 := (abs_le.mp hxb).2
    norm_num at h1 h2
    rw [show (2 : ℝ) ^ 53 = 9007199254740992 by norm_num]
    linarith
  have hRlo' : 2 ^ 52 ≤ R := by exact_mod_cast hRlo
  have hRhi' : R < 2 ^ 53 := by exact_mod_cast hRhi
  let k : Int := (R : Int) - 3 * 2 ^ 51
  have hbits := F64BinadeWord.binade_word_toNat (shifted x) R 1067 hs hv hRlo' hRhi'
  refine ⟨k, hf, ?_, ?_, ?_, ?_⟩
  · rw [hv]
    dsimp only [k]
    ring
  · rw [hbits]
    dsimp only [k]
    push_cast
    omega
  · have hk : (k : ℝ) = (R : ℝ) - 3 * 2 ^ 51 := by
      dsimp only [k]
      push_cast
      ring
    rw [hk]
    exact hkR
  · have hk : |(k : ℝ)| ≤ (2 : ℝ) ^ 19 + 1 / 2 := by
      have hk' : (k : ℝ) = (R : ℝ) - 3 * 2 ^ 51 := by
        dsimp only [k]
        push_cast
        ring
      rw [hk']
      calc
        _ = |(((R : ℝ) - 3 * 2 ^ 51) - 128 * value x) + 128 * value x| := by ring_nf
        _ ≤ _ := abs_add_le _ _
        _ ≤ 1 / 2 + (2 : ℝ) ^ 19 := add_le_add hkR hxb
        _ = _ := by ring
    have habsR : |(k : ℝ)| = (k.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]
      norm_num
    rw [habsR] at hk
    have hk2 : (2 : ℝ) * (k.natAbs : ℝ) ≤ 2 * (2 : ℝ) ^ 19 + 1 := by linarith
    have hk2' : 2 * k.natAbs ≤ 2 * (2 : Nat) ^ 19 + 1 := by exact_mod_cast hk2
    omega

/-- The selected multiple is `k / 128`, exactly. -/
theorem selected_value (x : UInt64) (k : Int) (hf : Finite (shifted x))
    (hv : Wasm.IEEE64.scaledValue (shifted x) = (3 * 2 ^ 51 + k) * 2 ^ 1067)
    (hk : k.natAbs ≤ 2 ^ 20) :
    Finite (selected x) ∧ Wasm.IEEE64.scaledValue (selected x) = k * 2 ^ 1067 ∧
      value (selected x) = (k : ℝ) / 128 := by
  have hdiff : Wasm.IEEE64.scaledValue (shifted x) -
      Wasm.IEEE64.scaledValue 0x42C8000000000000 = k * 2 ^ 1067 := by
    rw [hv, shift_values.2.2.1]
    ring
  obtain ⟨hsf, hsv⟩ := F64GridExact.sub_grid_exact (shifted x) 0x42C8000000000000 hf
    shift_values.1 k 1067 hdiff (hk.trans (by norm_num)) (by norm_num)
  have hsv' : Wasm.IEEE64.scaledValue (selected x) = k * 2 ^ 1067 := by
    rw [selected, hsv, hdiff]
  refine ⟨hsf, hsv', ?_⟩
  rw [value, hsv', Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    show (2 : ℝ) ^ 1074 = 128 * (2 : ℝ) ^ 1067 by norm_num, mul_div_mul_right _ _
      (by positivity : (2 : ℝ) ^ 1067 ≠ 0)]

/-- A finite word of magnitude at least `2 ^ -8` has a scaled value divisible by
`2 ^ 1014`. -/
theorem scaled_dvd (x : UInt64) (hx : (1 : ℝ) / 2 ^ 8 ≤ |value x|) :
    (2 : Int) ^ 1014 ∣ Wasm.IEEE64.scaledValue x := by
  have he : 1015 ≤ Wasm.IEEE64.exponent x := by
    by_contra hn
    have h := F64Magnitude.magnitude_lt x 1015 (-8) (by norm_num) (by norm_num) (by omega)
    norm_num at h
    linarith
  have hm : Wasm.IEEE64.scaledMagnitude x =
      (2 ^ 52 + Wasm.IEEE64.fraction x) * 2 ^ (Wasm.IEEE64.exponent x - 1 - 1014) * 2 ^ 1014 := by
    have h0 : Wasm.IEEE64.exponent x ≠ 0 := by omega
    simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, h0, ite_false]
    rw [mul_assoc, ← pow_add]
    congr 2
    omega
  have hdN : 2 ^ 1014 ∣ Wasm.IEEE64.scaledMagnitude x := by
    rw [hm]
    exact Dvd.intro_left _ rfl
  have hd : (2 : Int) ^ 1014 ∣ (Wasm.IEEE64.scaledMagnitude x : Int) := by
    exact_mod_cast hdN
  unfold Wasm.IEEE64.scaledValue
  split
  · exact (Int.dvd_neg).mpr hd
  · exact hd

/-- A word's scaled value lies on the grid of `2 ^ (e - 1)` scaled units, `e` its exponent
field, with fewer than 53 bits there. -/
theorem word_grid (x : UInt64) :
    (2 : Int) ^ (Wasm.IEEE64.exponent x - 1) ∣ Wasm.IEEE64.scaledValue x ∧
      |Wasm.IEEE64.scaledValue x| ≤ 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent x - 1) := by
  have hf : Wasm.IEEE64.fraction x < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hm : (2 : Nat) ^ (Wasm.IEEE64.exponent x - 1) ∣ Wasm.IEEE64.scaledMagnitude x ∧
      Wasm.IEEE64.scaledMagnitude x ≤ 2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent x - 1) := by
    by_cases h0 : Wasm.IEEE64.exponent x = 0
    · simp only [Wasm.IEEE64.scaledMagnitude, h0, beq_self_eq_true, ite_true, Nat.zero_sub,
        pow_zero, one_dvd, mul_one, true_and]
      omega
    · simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, h0, ite_false]
      refine ⟨Dvd.intro_left _ rfl, ?_⟩
      exact Nat.mul_le_mul_right _ (by omega)
  have hd : (2 : Int) ^ (Wasm.IEEE64.exponent x - 1) ∣ (Wasm.IEEE64.scaledMagnitude x : Int) := by
    exact_mod_cast hm.1
  have hb : ((Wasm.IEEE64.scaledMagnitude x : Nat) : Int) ≤
      2 ^ 53 * 2 ^ (Wasm.IEEE64.exponent x - 1) := by exact_mod_cast hm.2
  unfold Wasm.IEEE64.scaledValue
  split
  · refine ⟨(Int.dvd_neg).mpr hd, ?_⟩
    rw [abs_neg, abs_of_nonneg (by positivity)]
    exact hb
  · refine ⟨hd, ?_⟩
    rw [abs_of_nonneg (by positivity)]
    exact hb

/-- The residual `x - k / 128` is exact, with magnitude at most `1/256`. -/
theorem residual_value (x : UInt64) (k : Int) (hxf : Finite x)
    (hsf : Finite (selected x)) (hsv : Wasm.IEEE64.scaledValue (selected x) = k * 2 ^ 1067)
    (hsval : value (selected x) = (k : ℝ) / 128)
    (hk : |(k : ℝ) - 128 * value x| ≤ 1 / 2) :
    Finite (residual x) ∧ value (residual x) = value x - (k : ℝ) / 128 ∧
      |value (residual x)| ≤ 1 / 256 := by
  have hr : |value x - (k : ℝ) / 128| ≤ 1 / 256 := by
    have hid : value x - (k : ℝ) / 128 = -((k : ℝ) - 128 * value x) / 128 := by ring
    rw [hid, abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 128)]
    linarith
  have hexact : Finite (residual x) ∧ value (residual x) = value x - value (selected x) := by
    by_cases hk0 : k = 0
    · subst hk0
      have hs0 : Wasm.IEEE64.scaledValue (selected x) = 0 := by rw [hsv]; ring
      have hx8 : |value x| ≤ 1 / 256 := by
        have h := abs_le.mp hk
        rw [abs_le]
        push_cast at h
        constructor <;> linarith
      have he : Wasm.IEEE64.exponent x ≤ 1015 := by
        by_contra hn
        have h := F64Magnitude.magnitude_ge x 1016 (-7) (by norm_num) (by norm_num)
          (by norm_num) (by omega)
        norm_num at h
        linarith
      obtain ⟨hd, hb⟩ := word_grid x
      exact F64ErrorTrack.sub_exact_grid x (selected x) hxf hsf _ (by omega) hd
        (by rw [hs0]; exact dvd_zero _) (by rw [hs0, sub_zero]; exact hb)
    · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        have : (1 : Int) ≤ |k| := Int.one_le_abs hk0
        exact_mod_cast this
      have hx8 : (1 : ℝ) / 2 ^ 8 ≤ |value x| := by
        have h1 := abs_sub_abs_le_abs_sub (k : ℝ) (128 * value x)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 128)] at h1
        norm_num
        linarith
      have hd : (2 : Int) ^ 1014 ∣ Wasm.IEEE64.scaledValue (selected x) := by
        rw [hsv]
        exact ⟨k * 2 ^ 53, by ring⟩
      have hb : |Wasm.IEEE64.scaledValue x - Wasm.IEEE64.scaledValue (selected x)| ≤
          2 ^ 53 * 2 ^ 1014 := by
        have hR : |(Wasm.IEEE64.scaledValue x : ℝ) - (Wasm.IEEE64.scaledValue (selected x) : ℝ)| ≤
            (2 : ℝ) ^ 53 * 2 ^ 1014 := by
          have hxv : (Wasm.IEEE64.scaledValue x : ℝ) = value x * (2 : ℝ) ^ 1074 := by
            rw [value]
            field_simp
          have hsv' : (Wasm.IEEE64.scaledValue (selected x) : ℝ) =
              (k : ℝ) / 128 * (2 : ℝ) ^ 1074 := by
            rw [← hsval, value]
            field_simp
          rw [hxv, hsv', ← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074)]
          calc
            _ ≤ 1 / 256 * (2 : ℝ) ^ 1074 := mul_le_mul_of_nonneg_right hr (by positivity)
            _ ≤ _ := by norm_num
        exact_mod_cast hR
      exact F64ErrorTrack.sub_exact_grid x (selected x) hxf hsf 1014 (by norm_num)
        (scaled_dvd x hx8) hd hb
  refine ⟨hexact.1, by rw [hexact.2, hsval], ?_⟩
  rw [hexact.2, hsval]
  exact hr

#print axioms shift_values
#print axioms packing_binade
#print axioms shifted_state
#print axioms selected_value
#print axioms scaled_dvd
#print axioms word_grid
#print axioms residual_value

end Library.Numerics.Float64.Exp2.Exp2Selection
