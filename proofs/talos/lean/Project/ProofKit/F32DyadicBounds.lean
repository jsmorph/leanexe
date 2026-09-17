import Project.ProofKit.F32Packing
import CodeLib.IEEE32.Rounders

namespace Project.ProofKit.F32DyadicBounds
open CodeLib.IEEE32

set_option exponentiation.threshold 512

theorem dyadic_zero (negative : Bool) (frac : Nat) :
    Finite (Wasm.IEEE32.roundDyadicMagnitude negative 0 frac) ∧
    Wasm.IEEE32.sign (Wasm.IEEE32.roundDyadicMagnitude negative 0 frac) = negative ∧
    Wasm.IEEE32.scaledMagnitude (Wasm.IEEE32.roundDyadicMagnitude negative 0 frac) = 0 := by
  have ha : Wasm.IEEE32.roundDyadicMagnitude negative 0 frac =
      Wasm.IEEE32.encodeFinite negative 0 0 := by
    simp only [Wasm.IEEE32.roundDyadicMagnitude, beq_self_eq_true, ite_true]
    cases negative <;> apply UInt32.toNat_inj.mp <;>
      norm_num [Wasm.IEEE32.signMask, Wasm.IEEE32.encodeFinite, UInt32.toNat_ofNat]
  rw [ha]
  exact ⟨finite_encodeFinite negative 0 0 (by decide) (by decide),
    sign_encodeFinite negative 0 0 (by decide) (by decide),
    by simpa only [Nat.zero_mul, ite_true] using
      scaledMagnitude_encodeFinite negative 0 0 (by decide) (by decide)⟩

theorem half_scaled (s : Nat) (hs : 0 < s) :
    ((2^s / 2 : Nat) : Int) * 2^24 = (2^(s+23) : Nat) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  rw [pow_succ, Nat.mul_div_left _ (by omega)]
  push_cast
  rw [pow_add]
  norm_num
  ring

theorem small_spec (negative : Bool) (n frac : Nat) (hf : 0 < frac)
    (hn : n ≠ 0) (hl : Nat.log2 n ≤ frac + 23) :
    Finite (Wasm.IEEE32.roundDyadicMagnitude negative n frac) ∧
    Wasm.IEEE32.sign (Wasm.IEEE32.roundDyadicMagnitude negative n frac) = negative ∧
    |((Wasm.IEEE32.scaledMagnitude (Wasm.IEEE32.roundDyadicMagnitude negative n frac) *
      2^frac : Nat) : Int) - n| * (2^24 : Int) ≤ (max n (2^(frac+23)) : Nat) := by
  have hlt : n < 2^(frac+24) :=
    Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hq : n / 2^frac < 2^24 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).2
    rw [← pow_add, Nat.add_comm]
    exact hlt
  have hb := roundShift_bounds n frac
  have hr : Wasm.IEEE32.roundShift n frac ≤ 2^24 := by omega
  have hp := roundScaledMagnitude_exact negative _ hr
  have ha : Wasm.IEEE32.roundDyadicMagnitude negative n frac =
      Wasm.IEEE32.roundScaledMagnitude negative (Wasm.IEEE32.roundShift n frac) := by
    simp only [Wasm.IEEE32.roundDyadicMagnitude, beq_iff_eq, if_neg hn,
      show Nat.log2 n - (frac + 23) = 0 by omega, ite_true, if_neg (by omega : frac ≠ 0)]
  rw [ha]
  refine ⟨hp.1, hp.2.2, ?_⟩
  rw [hp.2.1]
  have he := abs_int_sub_le_of_error_cases _ _ _ (roundShift_error_cases n frac hf)
  calc
    _ ≤ ((2^frac / 2 : Nat) : Int) * 2^24 :=
      mul_le_mul_of_nonneg_right he (by positivity)
    _ = (2^(frac+23) : Nat) := half_scaled frac hf
    _ ≤ (max n (2^(frac+23)) : Nat) := by exact_mod_cast Nat.le_max_right _ _

/-- One rounding with arbitrary extra fractional bits. The second error term
is half a subnormal unit; the first is the usual relative rounding bound. -/
theorem dyadic_relative (negative : Bool) (n frac : Nat) (hf : 0 < frac)
    (hmax : n < 2^(frac + 276)) :
    Finite (Wasm.IEEE32.roundDyadicMagnitude negative n frac) ∧
    Wasm.IEEE32.sign (Wasm.IEEE32.roundDyadicMagnitude negative n frac) = negative ∧
    |((Wasm.IEEE32.scaledMagnitude (Wasm.IEEE32.roundDyadicMagnitude negative n frac) *
      2^frac : Nat) : Int) - n| * (2^24 : Int) ≤ (max n (2^(frac+23)) : Nat) := by
  by_cases hn : n = 0
  · subst n
    have hp := dyadic_zero negative frac
    refine ⟨hp.1, hp.2.1, ?_⟩
    rw [hp.2.2]
    simp only [Nat.zero_mul, Nat.cast_zero, sub_zero, abs_zero, zero_mul]
    exact_mod_cast Nat.zero_le (max 0 (2^(frac+23)))
  let shift := Nat.log2 n - (frac + 23)
  let total := frac + shift
  let rounded := Wasm.IEEE32.roundShift n total
  by_cases hz : shift = 0
  · exact small_spec negative n frac hf hn (by dsimp [shift] at hz; omega)
  have hs : 0 < shift := by omega
  have hl : frac + 24 ≤ Nat.log2 n := by dsimp [shift] at hz; omega
  have hu : Nat.log2 n < frac + 276 := (Nat.log2_lt hn).2 hmax
  have hsm : shift ≤ 252 := by dsimp [shift]; omega
  have heq : 23 + total = Nat.log2 n := by dsimp [total, shift]; omega
  have hpLower : 2^23 * 2^total ≤ n := by
    rw [← pow_add, heq]
    exact Nat.log2_self_le hn
  have hpUpper : n < 2^24 * 2^total := by
    rw [← pow_add, show 24 + total = Nat.log2 n + 1 by omega]
    exact Nat.lt_log2_self
  have hqLower : 2^23 ≤ n / 2^total := (Nat.le_div_iff_mul_le (by positivity)).2 hpLower
  have hqUpper : n / 2^total < 2^24 := (Nat.div_lt_iff_lt_mul (by positivity)).2 hpUpper
  have hr := roundShift_bounds n total
  have hrLower : 2^23 ≤ rounded := by dsimp [rounded]; omega
  have hrUpper : rounded ≤ 2^24 := by dsimp [rounded]; omega
  have he := abs_int_sub_le_of_error_cases _ _ _
    (roundShift_error_cases n total (by dsimp [total]; omega))
  have herr : |((rounded * 2^shift * 2^frac : Nat) : Int) - n| * 2^24 ≤
      (max n (2^(frac+23)) : Nat) := by
    rw [show rounded * 2^shift * 2^frac = rounded * 2^total by
      dsimp [total]; rw [pow_add]; ring]
    calc
      _ ≤ ((2^total / 2 : Nat) : Int) * 2^24 :=
        mul_le_mul_of_nonneg_right he (by positivity)
      _ = (2^(total+23) : Nat) := half_scaled total (by dsimp [total]; omega)
      _ = (2^23 * 2^total : Nat) := by rw [← pow_add, Nat.add_comm]
      _ ≤ n := by exact_mod_cast hpLower
      _ ≤ (max n (2^(frac+23)) : Nat) := by exact_mod_cast Nat.le_max_left _ _
  by_cases hc : rounded = 2^24
  · have hcn : Wasm.IEEE32.roundShift n (frac+shift) = 16777216 := by
      simpa [rounded, total] using hc
    have hp := finite_encodeFinite negative (shift+2) 0 (by omega) (by norm_num)
    have hsign := sign_encodeFinite negative (shift+2) 0 (by omega) (by norm_num)
    have hmag := scaledMagnitude_encodeFinite negative (shift+2) 0 (by omega) (by norm_num)
    have ha : Wasm.IEEE32.roundDyadicMagnitude negative n frac =
        Wasm.IEEE32.encodeFinite negative (shift+2) 0 := by
      simp [Wasm.IEEE32.roundDyadicMagnitude, hn, shift, hz, hcn,
        show ¬253 ≤ shift by omega, Nat.add_assoc]
    rw [ha]
    refine ⟨hp, hsign, ?_⟩
    have hm : Wasm.IEEE32.scaledMagnitude (Wasm.IEEE32.encodeFinite negative (shift+2) 0) =
        rounded * 2^shift := by
      rw [hmag]
      simp only [if_neg (by omega : shift+2 ≠ 0), Nat.add_zero]
      rw [show shift+2-1 = shift+1 by omega, hc, pow_succ]
      ring
    rw [hm]
    exact herr
  · have hfr : rounded-2^23 < 2^23 := by omega
    have hcn : ¬Wasm.IEEE32.roundShift n (frac+shift) = 16777216 := by
      simpa [rounded, total] using hc
    have hp := finite_encodeFinite negative (shift+1) (rounded-2^23) (by omega) hfr
    have hsign := sign_encodeFinite negative (shift+1) (rounded-2^23) (by omega) hfr
    have hmag := scaledMagnitude_encodeFinite negative (shift+1) (rounded-2^23) (by omega) hfr
    have ha : Wasm.IEEE32.roundDyadicMagnitude negative n frac =
        Wasm.IEEE32.encodeFinite negative (shift+1) (rounded-2^23) := by
      simp [Wasm.IEEE32.roundDyadicMagnitude, hn, shift, hz, hcn,
        show ¬254 ≤ shift by omega, rounded, total]
    rw [ha]
    refine ⟨hp, hsign, ?_⟩
    rw [hmag]
    simp only [if_neg (by omega : shift+1 ≠ 0)]
    rw [show shift+1-1 = shift by omega, show 2^23+(rounded-2^23)=rounded by omega]
    exact herr

#print axioms dyadic_relative
end Project.ProofKit.F32DyadicBounds
