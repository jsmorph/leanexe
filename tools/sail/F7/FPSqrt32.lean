import F7.FPMul32
import F7.FPSqrt

/-!
FPSqrt of Sail's Lean translation of the Armv9.4-A model, at 32 bits under FPCR 0x02000000,
returns Talos's `f32Sqrt` of its operand for every word and sets in FPSR the bits of
`sqrtMask32`, from every state that satisfies `Hyp`.  The proof follows `fpSqrt_run` of
`F7/FPSqrt.lean` with the binary32 constants.

For a positive finite operand of magnitude `N` in units of 2^-149, FPSqrt rounds
`√(N · 2^-149) = √R · 2^-149` with the radicand `R = N · 2^149` (`sqrt_val32`).  Talos's
`IEEE32.roundSqrtMagnitude N` takes `r = Nat.sqrt R`, the shift `k = log2 r − 23`
(`rootShift32`), and the lower mantissa `l = r / 2^k`, rounds `l` with `roundSqrtIntegral`
(`rsi_eq` of `F7/FPSqrt.lean`), and packs the result times `2^k` with `roundScaledMagnitude`
(`tSqrtU32`).  The result is normal: for `R` in `[2^149, 2^426)`, `2^(k+23) ≤ r < 2^(k+24)` and
`k + 2 < 255` (`root_facts32`).  `round_normalR32` states FPRoundBase__1's normal case at 32 bits
over the scaled mantissa, as `round_normalR` of `F7/RoundR.lean` does at 64 bits, and
`round_root32` applies it to the scaled mantissa `√R / 2^k`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

/-! ## FPRoundBase__1's normal case at 32 bits over a real scaled mantissa -/

/-- Talos's packing of the rounded integer mantissa `q` or `q + 1` times `2^j`, for
`2^23 ≤ q < 2^24`. -/
theorem tRound_normal32 (q j : ℕ) (up : Prop) [Decidable up] (hq1 : 2 ^ 23 ≤ q)
    (hq2 : q < 2 ^ 24) :
    (Wasm.IEEE32.roundScaledMagnitude false ((if up then q + 1 else q) * 2 ^ j)).toBitVec =
      (if up then
        (if q + 1 = 2 ^ 24 then
          (if 255 ≤ j + 2 then (Wasm.IEEE32.infinity false).toBitVec
           else (Wasm.IEEE32.encodeFinite false (j + 2) 0).toBitVec)
         else (if 255 ≤ j + 1 then (Wasm.IEEE32.infinity false).toBitVec
           else (Wasm.IEEE32.encodeFinite false (j + 1) (q + 1 - 2 ^ 23)).toBitVec))
       else (if 255 ≤ j + 1 then (Wasm.IEEE32.infinity false).toBitVec
         else (Wasm.IEEE32.encodeFinite false (j + 1) (q - 2 ^ 23)).toBitVec)) := by
  by_cases hup : up
  · rw [ite_eq_left hup, ite_eq_left hup]
    by_cases hc : q + 1 = 2 ^ 24
    · rw [ite_eq_left hc, hc, rsm_carry32]
      split_ifs <;> rfl
    · rw [ite_eq_right hc, rsm_exact32 false (q + 1) j (by omega) (by omega)]
      split_ifs <;> rfl
  · rw [ite_eq_right hup, ite_eq_right hup, rsm_exact32 false q j hq1 hq2]
    split_ifs <;> rfl

/-- The bits of FPSR that FPRoundBase__1 sets at 32 bits for a positive normal result with the
integer mantissa `q`, the exponent field `j + 1`, the direction `up`, and the exactness `exact`:
OFC and IXC on overflow, and IXC on an inexact result. -/
def maskN32 (q j : ℕ) (up exact : Prop) [Decidable up] [Decidable exact] : BitVec 64 :=
  if 255 ≤ (if up ∧ q + 1 = 2 ^ 24 then j + 2 else j + 1) then 0x14#64
  else if exact then 0#64 else 0x10#64

set_option maxHeartbeats 800000 in
/-- FPRound__2 at 32 bits under FPCR 0x02000000, rounding to nearest even, on a positive real `M`
with a normal result. -/
theorem round_normalR32 (M x err : ℝ) (E : ℤ) (q j : ℕ) (Pu Pt Pz : Prop) [Decidable Pu]
    [Decidable Pt] [Decidable Pz] (hM : 0 < M) (h1 : 1 ≤ M * 2 ^ (-E)) (h2 : M * 2 ^ (-E) < 2)
    (hj : E = (j : ℤ) - 126) (hman : mult_real (M * 2 ^ (-E)) (real_power 2 23) = x)
    (hfl : round_down x = (q : ℤ)) (hq1 : 2 ^ 23 ≤ q) (hq2 : q < 2 ^ 24)
    (herr : sub_real x (to_real (q : ℤ)) = err) (hU : gt_real err (1 / 2) = decide Pu)
    (hT : eq_real err (1 / 2) = decide Pt) (hZ : (err == 0) = decide Pz)
    {R : Std.ExtDHashMap Register RegisterType} (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 M fpcrV .FPRounding_TIEEVEN true 32).run s =
      .ok (Wasm.IEEE32.roundScaledMagnitude false
        ((if Pu ∨ Pt ∧ q % 2 = 1 then q + 1 else q) * 2 ^ j)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| maskN32 q j (Pu ∨ Pt ∧ q % 2 = 1) Pz) ∧
      Frame s s' := by
  subst hs
  obtain ⟨e, he, he1, he2⟩ := loops_eq' _ hM
  have hE : e = E := exp_unique M e E he1 he2 h1 h2
  subst hE
  have hlt : lt_real M 0 = false := by simp [lt_real, hM.le]
  have hne : (M == 0) = false := by simp [hM.ne']
  have hb : max (e - -126 + 1) 0 = (j : ℤ) + 1 := by omega
  have hb0 : ((j : ℤ) + 1 == 0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  rw [tRound_normal32 q j _ hq1 hq2]
  simp only [maskN32]
  sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self,
    whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt]
  rw [he]
  sail_simp [↓join1_beq, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self, hne, bne, hlt, hb,
    hb0, hman, hfl, herr, hU, hT, hZ, int_access]
  clear he he1 he2 hlt hne hb hb0 hman hfl herr hU hT h1 h2
  simp only [ipow, Int.reduceToNat, Int.reducePow, Int.reduceSub, Int.reduceAdd, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ge_iff_le]
  have hfd : fdiv_int ((q : ℤ) + 1) 2 = ((q : ℤ) + 1) / 2 := fdiv_two _ (by omega)
  have c2 : ((q : ℤ) + 1 = 8388608) = False := by simp; omega
  have o1 : (255 ≤ (j : ℤ) + 1 + 1) = (255 ≤ j + 2) := by
    apply propext; constructor <;> intro <;> omega
  have o2 : (255 ≤ (j : ℤ) + 1) = (255 ≤ j + 1) := by
    apply propext; constructor <;> intro <;> omega
  simp only [c2, ↓reduceIte]
  by_cases hup : (Pu ∨ Pt ∧ q % 2 = 1) <;>
  by_cases hc : q + 1 = 2 ^ 24 <;> by_cases hv1 : 255 ≤ j + 1 <;> by_cases hv2 : 255 ≤ j + 2 <;>
  by_cases hr0 : Pz
  all_goals first | (exfalso; omega) | skip
  all_goals (
    have hcI : ((q : ℤ) + 1 = 16777216) = (q + 1 = 2 ^ 24) := by
      apply propext; constructor <;> intro <;> omega
    have e1 := by first | exact eq_false hup | exact eq_true hup
    have e2 := by first | exact eq_false hc | exact eq_true hc
    have e3 := by first | exact eq_false hv1 | exact eq_true hv1
    have e4 := by first | exact eq_false hv2 | exact eq_true hv2
    have e5 := by first | exact eq_false hr0 | exact eq_true hr0
    simp only [hcI, e1, e2, e3, e4, e5, true_and, and_true, false_and,
      and_false, ↓reduceIte, decide_true, decide_false, Bool.not_true, Bool.not_false]
    try simp only [o1, o2, e3, e4, ↓reduceIte]
    apply exists_of_run'
    · sail_simp [FPInfinity, FPProcessException, h.hfi, h.hps, h.nrw, h.aa64, h.fa,
        h.hfpsr, ite_self, toBV_inf32, toBV_encode32, one_beq_zero, cast_eq, hZ, e5]
      refine ok_congr ?_
      first
      | decide
      | (rw [bits_eq32]
         · apply congrArg (BitVec.ofNat 32)
           simp only [BitVec.toNat_ofNat, Nat.zero_mod, zero_mul, zero_add, hfd, Nat.reducePow]
           omega
         all_goals first | decide | omega)
    · simp only [setReg_regs, bump_regs, faS_regs, insert_insert,
        upd_or _ _ (by norm_num : 2 < 64), upd_or _ _ (by norm_num : 4 < 64), (or_masks _).1,
        (or_masks _).2.1, BitVec.or_zero, cast_eq] <;>
        first | rfl | exact (insert_self _ _ _ h.hfpsr).symm
    · exact ⟨rfl, rfl, rfl, rfl⟩)

/-! ## The square root of a binary32 value -/

theorem sqrt_val32 (N : ℕ) :
    sqrt_real (((N : ℤ) : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) =
      √((N * 2 ^ 149 : ℕ) : ℝ) * (2 : ℝ) ^ (-149 : ℤ) := by
  have e : ((N : ℤ) : ℝ) * (2 : ℝ) ^ (-149 : ℤ) =
      ((N * 2 ^ 149 : ℕ) : ℝ) * ((2 : ℝ) ^ (-149 : ℤ)) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.cast_natCast, mul_assoc]
    congr 1
    rw [← zpow_natCast (2 : ℝ) 149, ← zpow_natCast ((2 : ℝ) ^ (-149 : ℤ)) 2, ← zpow_mul,
      ← zpow_add₀ two_ne_zero]
    norm_num
  rw [sqrt_real, e, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (zpow_nonneg (by norm_num) _)]

/-- Talos's shift of the integer square root of the radicand `R` at 32 bits:
`log2 (Nat.sqrt R) − 23`. -/
def rootShift32 (R : ℕ) : ℕ := Nat.log2 (Nat.sqrt R) - 23

/-- The bits of FPSR that FPRoundBase__1 sets at 32 bits for the square root of the radicand `R`:
IXC when the root is inexact. -/
def rootMask32 (R : ℕ) : BitVec 64 :=
  if (Nat.sqrt R / 2 ^ rootShift32 R) ^ 2 * 2 ^ (2 * rootShift32 R) = R then 0#64 else 0x10#64

/-- The integer square root of a radicand in `[2^149, 2^426)` has 24 bits after the shift
`rootShift32 R`, and the exponent field of the result is below 253. -/
theorem root_facts32 (R : ℕ) (hR1 : 2 ^ 149 ≤ R) (hR2 : R < 2 ^ 426) :
    2 ^ (rootShift32 R + 23) ≤ Nat.sqrt R ∧ Nat.sqrt R < 2 ^ (rootShift32 R + 24) ∧
      rootShift32 R + 2 < 255 := by
  have h1 : 2 ^ 74 ≤ Nat.sqrt R := by
    apply Nat.le_sqrt'.mpr
    rw [← pow_mul]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hR1
  have h2 : Nat.sqrt R < 2 ^ 213 := by
    apply Nat.sqrt_lt'.mpr
    rw [← pow_mul]
    exact hR2
  unfold rootShift32
  generalize Nat.sqrt R = r at *
  have hr0 : r ≠ 0 := by have := Nat.one_le_two_pow (n := 74); omega
  have hl1 : 74 ≤ Nat.log2 r := (Nat.le_log2 hr0).mpr h1
  have hl2 : Nat.log2 r < 213 := (Nat.log2_lt hr0).mpr h2
  refine ⟨?_, ?_, by omega⟩
  · rw [show Nat.log2 r - 23 + 23 = Nat.log2 r by omega]
    exact Nat.log2_self_le hr0
  · rw [show Nat.log2 r - 23 + 24 = Nat.log2 r + 1 by omega]
    exact Nat.lt_log2_self

theorem maskN32_small (q j : ℕ) (up exact : Prop) [Decidable up] [Decidable exact]
    (hj : j + 2 < 255) : maskN32 q j up exact = if exact then 0#64 else 0x10#64 := by
  unfold maskN32
  rw [ite_eq_right (by split_ifs <;> omega)]

/-- Talos's `IEEE32.roundSqrtMagnitude N` for a nonzero `N`: the radicand `N · 2^149`, its rounded
integer root at the shift `rootShift32`, and `roundScaledMagnitude`.  The statement compares
words, for the reason that `tSqrtU` of `F7/FPSqrt.lean` gives. -/
theorem tSqrtU32 (N : ℕ) (hN : 0 < N) :
    Wasm.IEEE32.roundSqrtMagnitude N =
      Wasm.IEEE32.roundScaledMagnitude false
        (Wasm.IEEE32.roundSqrtIntegral (N * 2 ^ 149) (rootShift32 (N * 2 ^ 149)) *
          2 ^ rootShift32 (N * 2 ^ 149)) := by
  have hN0 : (N == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  unfold rootShift32
  rw [Wasm.IEEE32.roundSqrtMagnitude, hN0, ite_eq_right Bool.false_ne_true]

/-- FPRound__2 at 32 bits under FPCR 0x02000000, rounding to nearest even, on `√R · 2^-149` for a
radicand `R` in `[2^149, 2^426)`: Talos's rounded root and the FPSR bits of `rootMask32 R`. -/
theorem round_root32 (R : ℕ) (hR1 : 2 ^ 149 ≤ R) (hR2 : R < 2 ^ 426)
    {R0 : Std.ExtDHashMap Register RegisterType} (h : Hyp R0 fi ps fpsr) (hs : s.regs = R0) :
    ∃ s', (FPRound__2 (√(R : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) fpcrV .FPRounding_TIEEVEN true 32).run s =
      .ok (Wasm.IEEE32.roundScaledMagnitude false
        (Wasm.IEEE32.roundSqrtIntegral R (rootShift32 R) * 2 ^ rootShift32 R)).toBitVec s' ∧
      s'.regs = R0.insert .FPSR (fpsr ||| rootMask32 R) ∧ Frame s s' := by
  obtain ⟨hr1, hr2, hk2⟩ := root_facts32 R hR1 hR2
  unfold rootMask32
  rw [rsi_eq]
  generalize hk : rootShift32 R = k at *
  generalize hl : Nat.sqrt R / 2 ^ k = l
  have hl1 : 2 ^ 23 ≤ l := by
    rw [← hl, Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← pow_add, Nat.add_comm 23 k]; exact hr1
  have hl2 : l < 2 ^ 24 := by
    rw [← hl, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_comm 24 k]; exact hr2
  have hR0 : 0 < R := lt_of_lt_of_le (Nat.two_pow_pos _) hR1
  have hD : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hs1 : ((Nat.sqrt R : ℕ) : ℝ) ≤ √(R : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hs2 : √(R : ℝ) < (Nat.sqrt R : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hM : (0 : ℝ) < √(R : ℝ) * (2 : ℝ) ^ (-149 : ℤ) :=
    mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast hR0)) (zpow_pos (by norm_num) _)
  have hman : mult_real (√(R : ℝ) * (2 : ℝ) ^ (-149 : ℤ) * 2 ^ (-((k : ℤ) - 126)))
      (real_power 2 23) = √(R : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
    simp only [mult_real, real_power]
    rw [mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero, div_eq_mul_inv]
    congr 1
    push_cast
    rw [← zpow_natCast, ← zpow_neg]
    congr 1
    omega
  have hx1 : (2 : ℝ) ^ 23 ≤ √(R : ℝ) / ((2 ^ k : ℕ) : ℝ) := by
    rw [le_div_iff₀ hD]
    have : (((2 ^ (k + 23) : ℕ) : ℝ)) ≤ ((Nat.sqrt R : ℕ) : ℝ) := by exact_mod_cast hr1
    calc (2 : ℝ) ^ 23 * ((2 ^ k : ℕ) : ℝ) = ((2 ^ (k + 23) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ √(R : ℝ) := this.trans hs1
  have hx2 : √(R : ℝ) / ((2 ^ k : ℕ) : ℝ) < (2 : ℝ) ^ 24 := by
    rw [div_lt_iff₀ hD]
    have : ((Nat.sqrt R : ℕ) : ℝ) + 1 ≤ ((2 ^ (k + 24) : ℕ) : ℝ) := by exact_mod_cast hr2
    calc √(R : ℝ) < (Nat.sqrt R : ℝ) + 1 := hs2
      _ ≤ ((2 ^ (k + 24) : ℕ) : ℝ) := this
      _ = (2 : ℝ) ^ 24 * ((2 ^ k : ℕ) : ℝ) := by push_cast; ring
  have hm23 : √(R : ℝ) * (2 : ℝ) ^ (-149 : ℤ) * 2 ^ (-((k : ℤ) - 126)) =
      √(R : ℝ) / ((2 ^ k : ℕ) : ℝ) / (2 : ℝ) ^ 23 := by
    rw [← hman]
    simp only [mult_real, real_power, zpow_ofNat]
    field_simp
  have h1 : 1 ≤ √(R : ℝ) * (2 : ℝ) ^ (-149 : ℤ) * 2 ^ (-((k : ℤ) - 126)) := by
    rw [hm23, le_div_iff₀ (by positivity), one_mul]; exact hx1
  have h2 : √(R : ℝ) * (2 : ℝ) ^ (-149 : ℤ) * 2 ^ (-((k : ℤ) - 126)) < 2 := by
    rw [hm23, div_lt_iff₀ (by positivity)]
    calc _ < (2 : ℝ) ^ 24 := hx2
      _ = 2 * 2 ^ 23 := by norm_num
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
  obtain ⟨s', e1, e2, e3⟩ := round_normalR32 _ _ _ ((k : ℤ) - 126) l k
    ((2 * l + 1) ^ 2 * 2 ^ (2 * k) < 4 * R) (4 * R = (2 * l + 1) ^ 2 * 2 ^ (2 * k))
    (l ^ 2 * 2 ^ (2 * k) = R) hM h1 h2 rfl hman hfl hl1 hl2 herr hU hT hZ h hs
  refine ⟨s', e1, ?_, e3⟩
  rw [e2, maskN32_small _ _ _ _ hk2]

/-- FPRound__2 at 32 bits under FPCR 0x02000000, rounding to nearest even, on the square root of
the positive finite value `N · 2^-149` returns Talos's `IEEE32.roundSqrtMagnitude N` and sets the
FPSR bits of `rootMask32 (N · 2^149)`. -/
theorem fpRound_sqrt32 (N : ℕ) (hN : 0 < N) (hN2 : N < 2 ^ 277)
    {R0 : Std.ExtDHashMap Register RegisterType} (h : Hyp R0 fi ps fpsr) (hs : s.regs = R0) :
    ∃ s', (FPRound__2 (sqrt_real (((N : ℤ) : ℝ) * (2 : ℝ) ^ (-149 : ℤ))) fpcrV
        .FPRounding_TIEEVEN true 32).run s =
      .ok (Wasm.IEEE32.roundSqrtMagnitude N).toBitVec s' ∧
      s'.regs = R0.insert .FPSR (fpsr ||| rootMask32 (N * 2 ^ 149)) ∧ Frame s s' := by
  have hR1 : 2 ^ 149 ≤ N * 2 ^ 149 := Nat.le_mul_of_pos_left _ hN
  have hR2 : N * 2 ^ 149 < 2 ^ 426 := by
    rw [show 426 = 277 + 149 from rfl, pow_add]
    exact Nat.mul_lt_mul_of_pos_right hN2 (Nat.two_pow_pos _)
  rw [sqrt_val32, tSqrtU32 N hN]
  exact round_root32 (N * 2 ^ 149) hR1 hR2 h hs

/-! ## FPSqrt -/

theorem zero_word32 (x : BitVec 32) (h : ty32 x = .FPType_Zero) :
    x = if sg32 x then 0x80000000#32 else 0#32 := by
  have hz : ex32 x = 0 ∧ fr32 x = 0 := by
    unfold ty32 at h
    split_ifs at h with h0 h1
    exact ⟨h0, h1⟩
  obtain ⟨he, hf⟩ := hz
  have hx := x.isLt
  unfold ex32 at he
  unfold fr32 at hf
  apply BitVec.eq_of_toNat_eq
  unfold sg32
  split <;> simp_all <;> omega

/-- The magnitude of a finite binary32 word lies below 2^277. -/
theorem mag32_lt (x : BitVec 32) (hf : ex32 x ≠ 255) :
    Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec x) < 2 ^ 277 := by
  have he : ex32 x < 256 := Nat.mod_lt _ (by decide)
  have hfr : fr32 x < 2 ^ 23 := Nat.mod_lt _ (by decide)
  simp only [Wasm.IEEE32.scaledMagnitude, t_exp32, t_frac32]
  split
  · exact lt_of_lt_of_le hfr (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  · calc (2 ^ 23 + fr32 x) * 2 ^ (ex32 x - 1) < 2 ^ 24 * 2 ^ (ex32 x - 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
      _ = 2 ^ (24 + (ex32 x - 1)) := (pow_add _ _ _).symm
      _ ≤ 2 ^ 277 := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem canonicalNaN32_bv : Wasm.IEEE32.canonicalNaN.toBitVec = 0x7FC00000#32 := rfl

/-- The bits of FPSR that FPSqrt sets at 32 bits under FPCR 0x02000000: IOC for a signaling NaN
and for a negative operand other than a zero or a NaN, and IXC for an inexact root. -/
def sqrtMask32 (a : BitVec 32) : BitVec 64 :=
  if ty32 a == .FPType_SNaN then 1#64
  else if ty32 a == .FPType_QNaN || ty32 a == .FPType_Zero then 0#64
  else if sg32 a then 1#64
  else if ty32 a == .FPType_Infinity then 0#64
  else rootMask32 (Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec a) * 2 ^ 149)

theorem fpSqrt32_run (a : BitVec 32) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPSqrt a fpcrV).run s = .ok (Wasm.f32Sqrt (.ofBitVec a)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| sqrtMask32 a) ∧ Frame s s' := by
  subst hs
  simp only [FPSqrt, fpUnpack_eq32]
  sail_simp []
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run32 a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  simp only [Wasm.f32Sqrt, Wasm.IEEE32.sqrt, t_isNaN32, t_isInf32, t_sign32, mag32_beq_zero,
    sqrtMask32]
  have hioc : ioc fpsr = fpsr ||| 1#64 := by
    rw [ioc, upd_or _ _ (by norm_num), (or_masks _).2.2.1]
  cases ha : ty32 a <;> cases hsa : sg32 a <;>
    simp only [isNaNT, sgBit32, hsa, ↓reduceIte, Bool.false_eq_true] <;> sail_simp []
  -- The finite positive operands.
  all_goals first
    | (have hfa : ex32 a ≠ 255 :=
         ty32_fin a (by rw [ha]; exact fun h => FPType.noConfusion h) (by rw [ha]; rfl)
       have hza : 0 < Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec a) :=
         Nat.pos_of_ne_zero fun h0 => by
           have := (ty32_zero a hfa).mp h0; rw [ha] at this; exact FPType.noConfusion this
       rw [val32_fin a hfa, sv32_eq, hsa]
       simp only [Bool.false_eq_true, ↓reduceIte]
       sail_simp [FPRound, FPRound__1, FPRoundingMode, FPDecodeRounding, fpcr_RMode]
       refine step ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩
         (fpRound_sqrt32 _ hza (mag32_lt a hfa) h hr1) ?_
       intro σ2 hr2 hf2
       sail_simp [FPProcessDenorm, hr2, h.hfi, h.hps, h.nrw, h.aa64, h.fa]
       exact ⟨σ2, rfl, hr2, hf2⟩)
    | skip
  -- The other operands.  The width `Sail.BitVec.length a` that FPProcessNaN__1 passes to
  -- FPDefaultNaN__1 becomes 32 before FPDefaultNaN__1 unfolds, so that `decide` sees closed widths.
  all_goals (
    try simp only [FPProcessNaN, FPProcessNaN__1]
    try dsimp only [Sail.BitVec.length]
    try sail_simp [FPDefaultNaN__1, FPProcessException, FPZero, FPInfinity, hr1, h.hfi, h.hps,
      h.nrw, h.aa64, h.fa, h.hfpsr, setReg_regs, cast_eq, ite_self]
    try rw [zero_word32 a (by assumption)]
    try rw [inf_word32 a (by assumption)]
    try simp only [hsa, ↓reduceIte]
    try simp only [canonicalNaN32_bv]
    refine ⟨_, ok_congr ?v, ?r, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
    case v => decide
    case r =>
      try simp only [setReg_regs, bump_regs, faS_regs, hr1]
      first
      | (rw [BitVec.or_zero]; exact (insert_self _ _ _ h.hfpsr).symm)
      | simp only [upd_or _ _ (by norm_num : 0 < 64), (or_masks _).2.2.1])

/-- FPSqrt at 32 bits under FPCR 0x02000000 returns Talos's `f32Sqrt` for every word from every
state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| sqrtMask32 a`, and the other
registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fpSqrt32_eq_f32Sqrt (a : BitVec 32) (s : State) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPSqrt a fpcrV).run s = .ok (Wasm.f32Sqrt (UInt32.ofBitVec a)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| sqrtMask32 a) ∧ Frame s s' :=
  fpSqrt32_run a h rfl

end F7
