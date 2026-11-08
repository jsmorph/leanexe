import F7.RoundQ
import F7.FPMul

/-!
FPDiv of Sail's Lean translation of the Armv9.4-A model, at 64 bits under FPCR 0x02000000,
returns Talos's `f64Div` of its operands for every pair of words and sets in FPSR the bits of
`divMask`, from every state that satisfies `Hyp`.  FPDiv calls FPUnpack and FPProcessNaNs, which
are FPUnpack__1 and FPProcessNaNs__1 with `fpexc` true, and FPRound, which reads the rounding mode
and calls FPRound__2.  The exact quotient of two finite nonzero operands is `±(A / B)` for their
magnitudes `A` and `B` in units of 2^-1074, which is `±((A · 2^1074) / B) · 2^-1074` (`div_val`),
so `fpRound_q` gives Talos's `roundRationalMagnitude` of `A · 2^1074` over `B`, the rounder of
`IEEE64.div`, and the FPSR bits of `maskQ`, among them UFC for an inexact subnormal quotient.
A finite nonzero dividend over a zero divisor gives an infinity and sets DZC.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

theorem qop_val (neg : Bool) (A B : ℕ) :
    qop neg (A * 2 ^ 1074) B 1074 = if neg then -((A : ℝ) / B) else (A : ℝ) / B := by
  have h : ((A * 2 ^ 1074 : ℕ) : ℝ) / (B : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) = (A : ℝ) / B := by
    rw [zpow_neg, zpow_ofNat, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      mul_div_right_comm, mul_inv_cancel_right₀ (pow_ne_zero _ two_ne_zero)]
  simp only [qop, h]

/-- The exact quotient of two finite operands. -/
theorem div_val (a b : BitVec 64) (hfa : ex a ≠ 2047) (hfb : ex b ≠ 2047) :
    div_real (val64 a) (val64 b) = qop (sg a != sg b) (mag a * 2 ^ 1074) (mag b) 1074 := by
  rw [qop_val, val_fin a hfa, val_fin b hfb, sv_eq, sv_eq]
  have ht : (2 : ℝ) ^ (-1074 : ℤ) ≠ 0 := zpow_ne_zero _ two_ne_zero
  cases sg a <;> cases sg b <;>
    simp (config := {decide := true}) only [div_real, ↓reduceIte, Int.cast_neg, Int.cast_natCast,
      neg_mul, neg_div, div_neg, neg_neg, mul_div_mul_right _ _ ht]

/-- The bits of FPSR that FPDiv sets at 64 bits under FPCR 0x02000000. -/
def divMask (a b : BitVec 64) : BitVec 64 :=
  if isNaNT (ty64 a) || isNaNT (ty64 b) then
    (if ty64 a == .FPType_SNaN || ty64 b == .FPType_SNaN then 1#64 else 0#64)
  else if (ty64 a == .FPType_Infinity && ty64 b == .FPType_Infinity) ||
      (ty64 a == .FPType_Zero && ty64 b == .FPType_Zero) then 1#64
  else if ty64 a == .FPType_Infinity then 0#64
  else if ty64 b == .FPType_Zero then 2#64
  else if ty64 a == .FPType_Zero || ty64 b == .FPType_Infinity then 0#64
  else maskQ (mag a * 2 ^ 1074) (mag b)

theorem or_dzc (v : BitVec 64) : v ||| 1#64 <<< 1 = v ||| 2#64 := by congr 1

set_option hygiene false in
macro "div_fin" : tactic => `(tactic| (
  have hfa : ex a ≠ 2047 :=
    ty_fin a (by rw [ha]; exact fun h => FPType.noConfusion h) (by rw [ha]; rfl)
  have hfb : ex b ≠ 2047 :=
    ty_fin b (by rw [hb]; exact fun h => FPType.noConfusion h) (by rw [hb]; rfl)
  have hza : 0 < mag a := Nat.pos_of_ne_zero fun h0 => by
    have := (ty_zero a hfa).mp h0; rw [ha] at this; exact FPType.noConfusion this
  have hzb : 0 < mag b := Nat.pos_of_ne_zero fun h0 => by
    have := (ty_zero b hfb).mp h0; rw [hb] at this; exact FPType.noConfusion this
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  rw [div_val a b hfa hfb]
  sail_simp [FPRound, FPRound__1, FPRoundingMode, FPDecodeRounding, fpcr_RMode]
  refine step hf3 (fpRound_q _ _ _ (Nat.mul_pos hza (Nat.two_pow_pos 1074)) hzb h hr3') ?_
  intro σ4 hr4 hf4
  sail_simp [FPProcessDenorms, hr4, h.hfi, h.hps, h.nrw, h.aa64, h.fa, Std.ExtDHashMap.get?_insert]
  exact ⟨σ4, rfl, hr4, hf4⟩))

set_option hygiene false in
macro "div_sgn" : tactic => `(tactic| (
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  cases hsa : sg a <;> cases hsb : sg b <;> (try simp only [sgBit, hsa, hsb, ↓reduceIte] at ⊢)
  all_goals try sail_simp [FPZero, FPInfinity, FPProcessDenorms, FPProcessException, hr3', h.hfi,
    h.hps, h.nrw, h.aa64, h.fa, h.hfpsr]
  all_goals try sail_simp [FPDefaultNaN__1, FPProcessException, FPProcessDenorms, hr3', h.hfi,
    h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, setReg_regs, cast_eq, ite_self]
  all_goals (
    refine ⟨_, ok_congr ?v, ?r, ⟨hf3.mem, hf3.tags, hf3.cyc, hf3.out⟩⟩
    case v => decide
    case r =>
      first
      | (rw [hr3', BitVec.or_zero]; exact (insert_self _ _ _ h.hfpsr).symm)
      | (simp only [setReg_regs, bump_regs, faS_regs, hr3', upd_or _ _ (by norm_num : 0 < 64),
          upd_or _ _ (by norm_num : 1 < 64), (or_masks _).2.2.1, or_dzc]; done))))

set_option maxHeartbeats 1000000 in
theorem fpDiv_run (a b : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPDiv a b fpcrV).run s = .ok (Wasm.f64Div (.ofBitVec a) (.ofBitVec b)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| divMask a b) ∧ Frame s s' := by
  subst hs
  simp only [FPDiv, fpUnpack_eq, fpProcessNaNs_eq]
  sail_simp []
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  refine step hf1 (fpUnpack_run b h hr1) ?_
  intro σ2 hr2 hf2
  sail_simp []
  refine step hf2 (fpProcessNaNs_run _ _ a b h hr2) ?_
  intro σ3 hr3 hf3
  simp only [Wasm.f64Div, Wasm.IEEE64.div, t_isNaN, t_isInf, t_sign, divMask]
  simp only [mag_beq_zero]
  have hioc : ioc fpsr = fpsr ||| 1#64 := by
    rw [ioc, upd_or _ _ (by norm_num), (or_masks _).2.2.1]
  cases ha : ty64 a <;> cases hb : ty64 b <;> simp only [isNaNT] at hr3 ⊢ <;> sail_simp []
  -- The NaN cases.
  all_goals first
    | (have hnan : (isNaNT (ty64 a) || isNaNT (ty64 b)) = true := by rw [ha, hb]; try decide
       refine ⟨σ3, ?_, ?_, hf3⟩
       · rfl
       · rw [hr3]
         simp only [ha, hb, ftb_SNaN_SNaN, ftb_QNaN_SNaN,
           ftb_Zero_SNaN, ftb_Denormal_SNaN,
           ftb_Nonzero_SNaN, ftb_Infinity_SNaN, Bool.or_true, Bool.or_false, ↓reduceIte,
           Bool.false_eq_true, hioc, BitVec.or_zero] <;> first | rfl | exact (insert_self _ _ _ h.hfpsr).symm)
    | skip
  all_goals first | div_fin | skip
  all_goals div_sgn

/-- FPDiv at 64 bits under FPCR 0x02000000 returns Talos's `f64Div` for every pair of words from
every state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| divMask a b`, and the
other registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fpDiv_eq_f64Div (a b : BitVec 64) (s : State) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPDiv a b fpcrV).run s =
        .ok (Wasm.f64Div (UInt64.ofBitVec a) (UInt64.ofBitVec b)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| divMask a b) ∧ Frame s s' :=
  fpDiv_run a b h rfl

end F7
