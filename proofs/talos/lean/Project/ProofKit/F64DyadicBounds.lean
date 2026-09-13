import Project.ProofKit.F64Packing
import CodeLib.IEEE64.Rounders

namespace Project.ProofKit.F64DyadicBounds
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem log2_mul_two_pow (n shift : Nat) (hn : n ≠ 0) :
    Nat.log2 (n * 2^shift) = Nat.log2 n + shift := by
  induction shift with
  | zero => simp
  | succ shift ih =>
    rw [pow_succ, show n * (2^shift * 2) = 2 * (n * 2^shift) by ring,
      Nat.log2_two_mul (Nat.mul_ne_zero hn (by positivity)), ih]
    omega

theorem roundShift_mul_two_pow (n shift : Nat) (hshift : 0 < shift) :
    Wasm.IEEE32.roundShift (n * 2^shift) shift = n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : shift ≠ 0)
  simp [Wasm.IEEE32.roundShift, pow_succ]

theorem roundedMagnitude_shifted (rounded shift : Nat)
    (hlower : 2^52 ≤ rounded) (hupper : rounded ≤ 2^53) :
    roundedMagnitude (rounded * 2^shift) = rounded * 2^shift := by
  by_cases hshift : shift = 0
  · subst shift
    simpa using roundedMagnitude_eq_self hupper
  · have hshiftPos : 0 < shift := Nat.pos_of_ne_zero hshift
    have hroundedNe : rounded ≠ 0 := by omega
    have hlarge : ¬rounded * 2^shift < 2^53 := by
      have hp : 2^52 * 2^1 ≤ rounded * 2^shift :=
        Nat.mul_le_mul hlower (Nat.pow_le_pow_right (by omega) (by omega))
      norm_num [← pow_add] at hp ⊢
      exact hp
    by_cases hcarry : rounded = 2^53
    · subst rounded
      have hlog := log2_mul_two_pow (2^53) shift (by positivity)
      have hcandidate : 2^53 * 2^shift = 2^52 * 2^(shift + 1) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      have hactualShift : Nat.log2 (2^53 * 2^shift) - 52 = shift + 1 := by
        rw [hlog, Nat.log2_two_pow]
        omega
      simp only [roundedMagnitude, if_neg hlarge]
      rw [hactualShift, hcandidate, roundShift_mul_two_pow _ _ (by omega)]
      norm_num
    · have hroundedLt : rounded < 2^53 := by omega
      have hlogRounded : Nat.log2 rounded = 52 :=
        (Nat.log2_eq_iff hroundedNe).2 ⟨hlower, by simpa using hroundedLt⟩
      have hlog := log2_mul_two_pow rounded shift hroundedNe
      have hactualShift : Nat.log2 (rounded * 2^shift) - 52 = shift := by
        rw [hlog, hlogRounded]
        omega
      simp only [roundedMagnitude, if_neg hlarge]
      rw [hactualShift, roundShift_mul_two_pow _ _ hshiftPos]
      simp only [beq_iff_eq, if_neg hcarry]

theorem dyadic_relative (negative : Bool) (n : Nat) (hmax : n < 2^3170) :
    Finite (Wasm.IEEE64.roundDyadicMagnitude negative n 1074) ∧
    Wasm.IEEE64.sign (Wasm.IEEE64.roundDyadicMagnitude negative n 1074) = negative ∧
    |((Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundDyadicMagnitude negative n 1074) *
      2^1074 : Nat) : Int) - n| * (2^53 : Int) ≤
      (if n = 0 then 0 else max n (2^1126) : Nat) := by
  by_cases hsmall : n < 2^2149
  · exact roundDyadicMagnitude1074_adaptive_spec negative n hsmall
  have hn : n ≠ 0 := by omega
  let outputShift := Nat.log2 n - 1126
  have hlogLower : 2149 ≤ Nat.log2 n := (Nat.le_log2 hn).2 (by omega)
  have hlogUpper : Nat.log2 n < 3170 := (Nat.log2_lt hn).2 hmax
  have hshift : 0 < outputShift := by dsimp [outputShift]; omega
  have hshiftMax : outputShift ≤ 2043 := by dsimp [outputShift]; omega
  have hshiftEq : 1126 + outputShift = Nat.log2 n := by dsimp [outputShift]; omega
  let totalShift := 1074 + outputShift
  let rounded := Wasm.IEEE32.roundShift n totalShift
  let candidate := rounded * 2^outputShift
  have hpowLower : 2^52 * 2^totalShift ≤ n := by
    rw [← pow_add, show 52 + totalShift = Nat.log2 n by dsimp [totalShift]; omega]
    exact Nat.log2_self_le hn
  have hpowUpper : n < 2^53 * 2^totalShift := by
    rw [← pow_add, show 53 + totalShift = Nat.log2 n + 1 by dsimp [totalShift]; omega]
    exact Nat.lt_log2_self
  have hquotLower : 2^52 ≤ n / 2^totalShift :=
    (Nat.le_div_iff_mul_le (by positivity)).2 hpowLower
  have hquotUpper : n / 2^totalShift < 2^53 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).2 hpowUpper
  have hroundBounds := CodeLib.IEEE32.roundShift_bounds n totalShift
  have hroundedLower : 2^52 ≤ rounded := by dsimp [rounded]; omega
  have hroundedUpper : rounded ≤ 2^53 := by dsimp [rounded]; omega
  have hrepresentable : roundedMagnitude candidate = candidate :=
    roundedMagnitude_shifted rounded outputShift hroundedLower hroundedUpper
  have hcandidateMax : candidate < 2^2097 := by
    calc
      candidate ≤ 2^53 * 2^2043 :=
        Nat.mul_le_mul hroundedUpper (Nat.pow_le_pow_right (by omega) hshiftMax)
      _ = 2^2096 := by rw [← pow_add]
      _ < 2^2097 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hpack := F64Packing.pack_spec negative candidate hcandidateMax
  have hactual : Wasm.IEEE64.roundDyadicMagnitude negative n 1074 =
      Wasm.IEEE64.roundScaledMagnitude negative candidate := by
    simp only [Wasm.IEEE64.roundDyadicMagnitude, beq_iff_eq, if_neg hn]
    rw [show Nat.log2 n - (1074 + 52) = outputShift by simp [outputShift],
      if_neg (by omega : outputShift ≠ 0)]
  have herrorCases := CodeLib.IEEE32.roundShift_error_cases n totalShift (by dsimp [totalShift]; omega)
  have herrHalf : |((rounded * 2^totalShift : Nat) : Int) - n| ≤ (2^totalShift / 2 : Nat) :=
    CodeLib.IEEE32.abs_int_sub_le_of_error_cases _ _ _ herrorCases
  have hhalfScaled : ((2^totalShift / 2 : Nat) : Int) * (2^53 : Int) =
      (2^52 * 2^totalShift : Nat) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (by dsimp [totalShift]; omega : totalShift ≠ 0)
    rw [hk, pow_succ, Nat.mul_div_left _ (by omega)]
    push_cast
    ring
  rw [hactual]
  refine ⟨hpack.1, hpack.2.2, ?_⟩
  rw [hpack.2.1, hrepresentable]
  have hcandidateEq : candidate * 2^1074 = rounded * 2^totalShift := by
    simp [candidate, totalShift, pow_add]
    ring
  rw [hcandidateEq]
  calc
    |((rounded * 2^totalShift : Nat) : Int) - n| * (2^53 : Int) ≤
        ((2^totalShift / 2 : Nat) : Int) * (2^53 : Int) :=
      mul_le_mul_of_nonneg_right herrHalf (by positivity)
    _ = (2^52 * 2^totalShift : Nat) := hhalfScaled
    _ ≤ n := by exact_mod_cast hpowLower
    _ ≤ (if n = 0 then 0 else max n (2^1126) : Nat) := by simp [hn]

#print axioms roundedMagnitude_shifted
#print axioms dyadic_relative
end Project.ProofKit.F64DyadicBounds
