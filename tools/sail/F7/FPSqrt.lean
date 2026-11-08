import F7.FPMul
import F7.RoundR

/-!
FPSqrt of Sail's Lean translation of the Armv9.4-A model, at 64 bits under FPCR 0x02000000,
returns Talos's `f64Sqrt` of its operand for every word and sets in FPSR the bits of `sqrtMask`,
from every state that satisfies `Hyp`.

For a positive finite operand of magnitude `N` in units of 2^-1074, FPSqrt rounds
`√(N · 2^-1074) = √R · 2^-1074` with the radicand `R = N · 2^1074` (`sqrt_val`).  Talos's
`roundSqrtMagnitude N` takes `r = Nat.sqrt R`, the shift `k = log2 r − 52` (`rootShift`), and the
lower mantissa `l = r / 2^k`, rounds `l` up when `4 · R` exceeds `(2 · l + 1)^2 · 2^(2k)` or equals
it with `l` odd (`rsi_eq`), and packs the result times `2^k` with `roundScaledMagnitude`
(`tSqrt_eq`).  The result is normal: for `R` in `[2^1074, 2^3172)`, `2^(k+52) ≤ r < 2^(k+53)` and
`k + 2 < 2047` (`root_facts`).  The scaled mantissa of FPRoundBase__1 is `√R / 2^k`, whose floor
is `l` by Mathlib's `Real.floor_real_sqrt_eq_nat_sqrt`, and the comparisons of its error with 1/2
and 0 become Talos's comparisons of `4 · R` with `(2 · l + 1)^2 · 2^(2k)` and of `R` with
`l^2 · 2^(2k)`, so `round_normalR` (`F7/RoundR.lean`) gives Talos's word and the FPSR bits of
`rootMask R` (`round_root`, `fpRound_sqrt`).
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

/-! ## The square root on the reals -/

theorem sqrt_val (N : ℕ) :
    sqrt_real (((N : ℤ) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) =
      √((N * 2 ^ 1074 : ℕ) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) := by
  have e : ((N : ℤ) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) =
      ((N * 2 ^ 1074 : ℕ) : ℝ) * ((2 : ℝ) ^ (-1074 : ℤ)) ^ 2 := by
    rw [← zpow_natCast ((2 : ℝ) ^ (-1074 : ℤ)) 2, ← zpow_mul]
    push_cast
    rw [mul_assoc, ← zpow_natCast (2 : ℝ) 1074, ← zpow_add₀ two_ne_zero]
    norm_num
  rw [sqrt_real, e, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (zpow_nonneg (by norm_num) _)]

/-- `c / 2 < √A` for naturals `A` and `c` is `c^2 < 4 · A`. -/
theorem half_lt_sqrt (A c : ℕ) : ((c : ℝ) / 2 < √(A : ℝ)) ↔ c ^ 2 < 4 * A := by
  rw [Real.lt_sqrt (by positivity), div_pow, div_lt_iff₀ (by norm_num)]
  constructor
  · intro h; have : ((c ^ 2 : ℕ) : ℝ) < ((4 * A : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h; have : ((c ^ 2 : ℕ) : ℝ) < ((4 * A : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith

/-- `√A = c / 2` for naturals `A` and `c` is `4 · A = c^2`. -/
theorem sqrt_eq_half (A c : ℕ) : (√(A : ℝ) = (c : ℝ) / 2) ↔ 4 * A = c ^ 2 := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  constructor
  · intro h; have : ((4 * A : ℕ) : ℝ) = ((c ^ 2 : ℕ) : ℝ) := by push_cast; rw [h]; ring
    exact_mod_cast this
  · intro h; have : ((4 * A : ℕ) : ℝ) = ((c ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith

/-- `√A = c` for naturals `A` and `c` is `A = c^2`. -/
theorem sqrt_eq_nat (A c : ℕ) : (√(A : ℝ) = (c : ℝ)) ↔ A = c ^ 2 := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  constructor
  · intro h; have : ((A : ℕ) : ℝ) = ((c ^ 2 : ℕ) : ℝ) := by push_cast; rw [h]; ring
    exact_mod_cast this
  · intro h; rw [h]; push_cast; ring

theorem sq_shift (c k : ℕ) : (c * 2 ^ k) ^ 2 = c ^ 2 * 2 ^ (2 * k) := by
  rw [mul_pow, ← pow_mul, Nat.mul_comm k 2]

/-! ## Talos's rounding of a square root -/

theorem rsi_eq (R k : ℕ) :
    Wasm.IEEE32.roundSqrtIntegral R k =
      if (2 * (Nat.sqrt R / 2 ^ k) + 1) ^ 2 * 2 ^ (2 * k) < 4 * R ∨
          4 * R = (2 * (Nat.sqrt R / 2 ^ k) + 1) ^ 2 * 2 ^ (2 * k) ∧ Nat.sqrt R / 2 ^ k % 2 = 1
      then Nat.sqrt R / 2 ^ k + 1 else Nat.sqrt R / 2 ^ k := by
  simp only [Wasm.IEEE32.roundSqrtIntegral]
  generalize Nat.sqrt R / 2 ^ k = l
  generalize (2 * l + 1) ^ 2 * 2 ^ (2 * k) = m
  generalize 4 * R = f
  simp only [beq_iff_eq]
  split_ifs <;> omega

/-- Talos's shift of the integer square root of the radicand `R`: `log2 (Nat.sqrt R) − 52`. -/
def rootShift (R : ℕ) : ℕ := Nat.log2 (Nat.sqrt R) - 52

/-- The bits of FPSR that FPRoundBase__1 sets for the square root of the radicand `R`: IXC when the
root is inexact. -/
def rootMask (R : ℕ) : BitVec 64 :=
  if (Nat.sqrt R / 2 ^ rootShift R) ^ 2 * 2 ^ (2 * rootShift R) = R then 0#64 else 0x10#64

/-- The integer square root of a radicand in `[2^1074, 2^3172)` has 53 bits after the shift
`rootShift R`, and the exponent field of the result is below 2045. -/
theorem root_facts (R : ℕ) (hR1 : 2 ^ 1074 ≤ R) (hR2 : R < 2 ^ 3172) :
    2 ^ (rootShift R + 52) ≤ Nat.sqrt R ∧ Nat.sqrt R < 2 ^ (rootShift R + 53) ∧
      rootShift R + 2 < 2047 := by
  have h1 : 2 ^ 537 ≤ Nat.sqrt R := by
    apply Nat.le_sqrt'.mpr
    rw [← pow_mul]
    exact hR1
  have h2 : Nat.sqrt R < 2 ^ 1586 := by
    apply Nat.sqrt_lt'.mpr
    rw [← pow_mul]
    exact hR2
  unfold rootShift
  generalize Nat.sqrt R = r at *
  have hr0 : r ≠ 0 := by have := Nat.one_le_two_pow (n := 537); omega
  have hl1 : 537 ≤ Nat.log2 r := (Nat.le_log2 hr0).mpr h1
  have hl2 : Nat.log2 r < 1586 := (Nat.log2_lt hr0).mpr h2
  refine ⟨?_, ?_, by omega⟩
  · rw [show Nat.log2 r - 52 + 52 = Nat.log2 r by omega]
    exact Nat.log2_self_le hr0
  · rw [show Nat.log2 r - 52 + 53 = Nat.log2 r + 1 by omega]
    exact Nat.lt_log2_self

theorem maskN_small (q j : ℕ) (up exact : Prop) [Decidable up] [Decidable exact]
    (hj : j + 2 < 2047) : maskN q j up exact = if exact then 0#64 else 0x10#64 := by
  unfold maskN
  rw [if_neg (by split_ifs <;> omega)]

/-- Talos's `roundSqrtMagnitude N` for a nonzero `N`: the radicand `N · 2^1074`, its rounded
integer root at the shift `rootShift`, and `roundScaledMagnitude`.  Lean's core library, in which
Talos is written, and Mathlib elaborate `2 ^ 1074 : ℕ` with different instances of `Pow`, so the
two sides differ syntactically.  The statement compares words rather than their bit vectors: the
kernel reduces a projection of a word by evaluating the word, and the evaluation unfolds
`N * 2 ^ 1074` one successor at a time. -/
theorem tSqrtU (N : ℕ) (hN : 0 < N) :
    Wasm.IEEE64.roundSqrtMagnitude N =
      Wasm.IEEE64.roundScaledMagnitude false
        (Wasm.IEEE32.roundSqrtIntegral (N * 2 ^ 1074) (rootShift (N * 2 ^ 1074)) *
          2 ^ rootShift (N * 2 ^ 1074)) := by
  have hN0 : (N == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  unfold rootShift
  rw [Wasm.IEEE64.roundSqrtMagnitude, hN0, if_neg Bool.false_ne_true]

theorem tSqrt_eq (N : ℕ) (hN : 0 < N) :
    (Wasm.IEEE64.roundSqrtMagnitude N).toBitVec =
      tRound false (Wasm.IEEE32.roundSqrtIntegral (N * 2 ^ 1074) (rootShift (N * 2 ^ 1074)) *
        2 ^ rootShift (N * 2 ^ 1074)) := by
  rw [tSqrtU N hN, tRound]

/-! ## FPRound__2 on a square root -/

/-- FPRound__2 at 64 bits under FPCR 0x02000000, rounding to nearest even, on `√R · 2^-1074` for a
radicand `R` in `[2^1074, 2^3172)`: Talos's rounded root and the FPSR bits of `rootMask R`. -/
theorem round_root (R : ℕ) (hR1 : 2 ^ 1074 ≤ R) (hR2 : R < 2 ^ 3172)
    {R0 : Std.ExtDHashMap Register RegisterType} (h : Hyp R0 fi ps fpsr) (hs : s.regs = R0) :
    ∃ s', (FPRound__2 (√(R : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (tRound false (Wasm.IEEE32.roundSqrtIntegral R (rootShift R) * 2 ^ rootShift R)) s' ∧
      s'.regs = R0.insert .FPSR (fpsr ||| rootMask R) ∧ Frame s s' := by
  obtain ⟨hr1, hr2, hk2⟩ := root_facts R hR1 hR2
  unfold rootMask
  rw [rsi_eq]
  generalize hk : rootShift R = k at *
  generalize hl : Nat.sqrt R / 2 ^ k = l
  have hl1 : 2 ^ 52 ≤ l := by
    rw [← hl, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← pow_add, Nat.add_comm 52 k]; exact hr1
  have hl2 : l < 2 ^ 53 := by
    rw [← hl, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_comm 53 k]; exact hr2
  have hR0 : 0 < R := lt_of_lt_of_le (Nat.two_pow_pos _) hR1
  have hD : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hs1 : ((Nat.sqrt R : ℕ) : ℝ) ≤ √(R : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hs2 : √(R : ℝ) < (Nat.sqrt R : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hM : (0 : ℝ) < √(R : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) :=
    mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hR0)) (zpow_pos (by norm_num) _)
  have hman : mult_real (√(R : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) * 2 ^ (-((k : ℤ) - 1022)))
      (real_power 2 52) = √(R : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
    simp only [mult_real, real_power]
    rw [mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero, div_eq_mul_inv]
    congr 1
    push_cast
    rw [← zpow_natCast, ← zpow_neg]
    congr 1
    omega
  have hx1 : (2 : ℝ) ^ 52 ≤ √(R : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
    rw [le_div_iff₀ hD]
    have : (((2 ^ (k + 52) : ℕ) : ℝ)) ≤ ((Nat.sqrt R : ℕ) : ℝ) := by exact_mod_cast hr1
    calc (2 : ℝ) ^ 52 * ((2 ^ k : ℕ) : ℝ) = ((2 ^ (k + 52) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ √(R : ℝ) := this.trans hs1
  have hx2 : √(R : ℝ) / ((2 ^ k : ℕ) : ℝ) < (2 : ℝ) ^ 53 := by
    rw [div_lt_iff₀ hD]
    have : ((Nat.sqrt R : ℕ) : ℝ) + 1 ≤ ((2 ^ (k + 53) : ℕ) : ℝ) := by exact_mod_cast hr2
    calc √(R : ℝ) < (Nat.sqrt R : ℝ) + 1 := hs2
      _ ≤ ((2 ^ (k + 53) : ℕ) : ℝ) := this
      _ = (2 : ℝ) ^ 53 * ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
  have hm52 : √(R : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) * 2 ^ (-((k : ℤ) - 1022)) =
      √(R : ℝ) / ((2 ^ k : ℕ) : ℝ) / (2 : ℝ) ^ 52 := by
    rw [← hman]
    simp only [mult_real, real_power, zpow_ofNat]
    field_simp
  have h1 : 1 ≤ √(R : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) * 2 ^ (-((k : ℤ) - 1022)) := by
    rw [hm52, le_div_iff₀ (by positivity), one_mul]; exact hx1
  have h2 : √(R : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) * 2 ^ (-((k : ℤ) - 1022)) < 2 := by
    rw [hm52, div_lt_iff₀ (by positivity)]
    calc _ < (2 : ℝ) ^ 53 := hx2
      _ = 2 * 2 ^ 52 := by norm_num
  have hfl : round_down (√(R : ℝ) / ((2 ^ k : ℕ) : ℝ)) = (l : ℤ) := by
    simp only [round_down]
    rw [Int.floor_div_natCast, Real.floor_real_sqrt_eq_nat_sqrt, ← hl]
    push_cast; rfl
  have herr : sub_real (√(R : ℝ) / ((2 ^ k : ℕ) : ℝ)) (to_real (l : ℤ)) =
      √(R : ℝ) / ((2 ^ k : ℕ) : ℝ) - l := by
    simp only [sub_real, to_real, Int.cast_natCast]
  have hU : gt_real (√(R : ℝ) / ((2 ^ k : ℕ) : ℝ) - l) (1 / 2) =
      decide ((2 * l + 1) ^ 2 * 2 ^ (2 * k) < 4 * R) := by
    simp only [gt_real, gt_iff_lt, decide_eq_decide]
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hD, ← sq_shift, ← half_lt_sqrt]
    constructor <;> intro h' <;> push_cast at h' ⊢ <;> linarith
  have hT : eq_real (√(R : ℝ) / ((2 ^ k : ℕ) : ℝ) - l) (1 / 2) =
      decide (4 * R = (2 * l + 1) ^ 2 * 2 ^ (2 * k)) := by
    simp only [eq_real, decide_eq_decide]
    rw [sub_eq_iff_eq_add, div_eq_iff hD.ne', ← sq_shift, ← sqrt_eq_half]
    constructor <;> intro h' <;> push_cast at h' ⊢ <;> linarith
  have hZ : ((√(R : ℝ) / ((2 ^ k : ℕ) : ℝ) - l) == 0) = decide (l ^ 2 * 2 ^ (2 * k) = R) := by
    rw [beq_eq_decide]
    apply decide_eq_decide.mpr
    rw [sub_eq_zero, div_eq_iff hD.ne', ← sq_shift, eq_comm (a := (l * 2 ^ k) ^ 2),
      ← sqrt_eq_nat]
    push_cast
    exact Iff.rfl
  obtain ⟨s', e1, e2, e3⟩ := round_normalR _ _ _ ((k : ℤ) - 1022) l k
    ((2 * l + 1) ^ 2 * 2 ^ (2 * k) < 4 * R) (4 * R = (2 * l + 1) ^ 2 * 2 ^ (2 * k))
    (l ^ 2 * 2 ^ (2 * k) = R) hM h1 h2 rfl hman hfl hl1 hl2 herr hU hT hZ h hs
  refine ⟨s', e1, ?_, e3⟩
  rw [e2, maskN_small _ _ _ _ hk2]

/-- FPRound__2 at 64 bits under FPCR 0x02000000, rounding to nearest even, on the square root of
the positive finite value `N · 2^-1074` returns Talos's `roundSqrtMagnitude N` and sets the FPSR
bits of `rootMask (N · 2^1074)`. -/
theorem fpRound_sqrt (N : ℕ) (hN : 0 < N) (hN2 : N < 2 ^ 2098)
    {R0 : Std.ExtDHashMap Register RegisterType} (h : Hyp R0 fi ps fpsr) (hs : s.regs = R0) :
    ∃ s', (FPRound__2 (sqrt_real (((N : ℤ) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ))) fpcrV
        .FPRounding_TIEEVEN true 64).run s =
      .ok (Wasm.IEEE64.roundSqrtMagnitude N).toBitVec s' ∧
      s'.regs = R0.insert .FPSR (fpsr ||| rootMask (N * 2 ^ 1074)) ∧ Frame s s' := by
  have hR1 : 2 ^ 1074 ≤ N * 2 ^ 1074 := Nat.le_mul_of_pos_left _ hN
  have hR2 : N * 2 ^ 1074 < 2 ^ 3172 := by
    rw [show 3172 = 2098 + 1074 from rfl, pow_add]
    exact Nat.mul_lt_mul_of_pos_right hN2 (Nat.two_pow_pos _)
  rw [sqrt_val, tSqrt_eq N hN]
  exact round_root (N * 2 ^ 1074) hR1 hR2 h hs

/-! ## FPSqrt -/

theorem zero_word (x : BitVec 64) (h : ty64 x = .FPType_Zero) :
    x = if sg x then 0x8000000000000000#64 else 0#64 := by
  have hz : ex x = 0 ∧ fr x = 0 := by
    unfold ty64 at h
    split_ifs at h with h0 h1
    exact ⟨h0, h1⟩
  obtain ⟨he, hf⟩ := hz
  have hx := x.isLt
  unfold ex at he
  unfold fr at hf
  apply BitVec.eq_of_toNat_eq
  unfold sg
  split <;> simp_all <;> omega

/-- The magnitude of a finite word lies below 2^2098. -/
theorem mag_lt (x : BitVec 64) (hf : ex x ≠ 2047) :
    Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) < 2 ^ 2098 := by
  have he : ex x < 2048 := Nat.mod_lt _ (by decide)
  have hfr : fr x < 2 ^ 52 := Nat.mod_lt _ (by decide)
  simp only [Wasm.IEEE64.scaledMagnitude, t_exp, t_frac]
  split
  · exact lt_of_lt_of_le hfr (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  · calc (2 ^ 52 + fr x) * 2 ^ (ex x - 1) < 2 ^ 53 * 2 ^ (ex x - 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
      _ = 2 ^ (53 + (ex x - 1)) := (pow_add _ _ _).symm
      _ ≤ 2 ^ 2098 := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem canonicalNaN_bv : Wasm.IEEE64.canonicalNaN.toBitVec = 0x7FF8000000000000#64 := rfl

/-- The bits of FPSR that FPSqrt sets at 64 bits under FPCR 0x02000000: IOC for a signaling NaN
and for a negative operand other than a zero or a NaN, and IXC for an inexact root. -/
def sqrtMask (a : BitVec 64) : BitVec 64 :=
  if ty64 a == .FPType_SNaN then 1#64
  else if ty64 a == .FPType_QNaN || ty64 a == .FPType_Zero then 0#64
  else if sg a then 1#64
  else if ty64 a == .FPType_Infinity then 0#64
  else rootMask (Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec a) * 2 ^ 1074)

theorem fpSqrt_run (a : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPSqrt a fpcrV).run s = .ok (Wasm.f64Sqrt (.ofBitVec a)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| sqrtMask a) ∧ Frame s s' := by
  subst hs
  simp only [FPSqrt, fpUnpack_eq]
  sail_simp []
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  simp only [Wasm.f64Sqrt, Wasm.IEEE64.sqrt, t_isNaN, t_isInf, t_sign, mag_beq_zero, sqrtMask]
  have hioc : ioc fpsr = fpsr ||| 1#64 := by
    rw [ioc, upd_or _ _ (by norm_num), (or_masks _).2.2.1]
  cases ha : ty64 a <;> cases hsa : sg a <;>
    simp only [isNaNT, sgBit, hsa, ↓reduceIte, Bool.false_eq_true] <;> sail_simp []
  -- The finite positive operands.
  all_goals first
    | (have hfa : ex a ≠ 2047 :=
         ty_fin a (by rw [ha]; exact fun h => FPType.noConfusion h) (by rw [ha]; rfl)
       have hza : 0 < Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec a) := Nat.pos_of_ne_zero fun h0 => by
         have := (ty_zero a hfa).mp h0; rw [ha] at this; exact FPType.noConfusion this
       rw [val_fin a hfa, sv_eq, hsa]
       simp only [Bool.false_eq_true, ↓reduceIte]
       sail_simp [FPRound, FPRound__1, FPRoundingMode, FPDecodeRounding, fpcr_RMode]
       refine step ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩
         (fpRound_sqrt _ hza (mag_lt a hfa) h hr1) ?_
       intro σ2 hr2 hf2
       sail_simp [FPProcessDenorm, hr2, h.hfi, h.hps, h.nrw, h.aa64, h.fa]
       exact ⟨σ2, rfl, hr2, hf2⟩)
    | skip
  -- The other operands.  The width `Sail.BitVec.length a` that FPProcessNaN__1 passes to
  -- FPDefaultNaN__1 becomes 64 before FPDefaultNaN__1 unfolds, so that `decide` sees closed widths.
  all_goals (
    try simp only [FPProcessNaN, FPProcessNaN__1]
    try dsimp only [Sail.BitVec.length]
    try sail_simp [FPDefaultNaN__1, FPProcessException, FPZero, FPInfinity, hr1, h.hfi, h.hps,
      h.nrw, h.aa64, h.fa, h.hfpsr, setReg_regs, cast_eq, ite_self]
    try rw [zero_word a (by assumption)]
    try rw [inf_word a (by assumption)]
    try simp only [hsa, ↓reduceIte]
    try simp only [canonicalNaN_bv]
    refine ⟨_, ok_congr ?v, ?r, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
    case v => decide
    case r =>
      try simp only [setReg_regs, bump_regs, faS_regs, hr1]
      first
      | (rw [BitVec.or_zero]; exact (insert_self _ _ _ h.hfpsr).symm)
      | simp only [upd_or _ _ (by norm_num : 0 < 64), (or_masks _).2.2.1])

/-- FPSqrt at 64 bits under FPCR 0x02000000 returns Talos's `f64Sqrt` for every word from every
state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| sqrtMask a`, and the other
registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fpSqrt_eq_f64Sqrt (a : BitVec 64) (s : State) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPSqrt a fpcrV).run s = .ok (Wasm.f64Sqrt (UInt64.ofBitVec a)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| sqrtMask a) ∧ Frame s s' :=
  fpSqrt_run a h rfl

end F7
