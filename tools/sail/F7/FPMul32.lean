import F7.Round32

/-!
FPMul of Sail's Lean translation of the Armv9.4-A model, at 32 bits under FPCR 0x02000000,
returns Talos's `f32Mul` of its operands for every pair of words and sets in FPSR the bits of
`mulMask32`, from every state that satisfies `Hyp`.  The proof follows `fpMul_run` of
`F7/FPMul.lean`.  The exact product of two finite nonzero operands is `±(A · B) · 2^-298` for their
magnitudes `A` and `B` in units of 2^-149, the rational `±((A · B) / 2^149) · 2^-149` (`mul_val32`),
so `fpRound32_q` gives Talos's `roundRationalMagnitude` of `A · B` over `2^149`, which
`rdm_eq_rrm32` equates with `roundDyadicMagnitude` of `A · B` with 149 fractional bits, the rounder
of `IEEE32.mul`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

theorem fpUnpack_eq32 (x : BitVec 32) : FPUnpack x fpcrV = FPUnpack__1 x fpcrV true := rfl

theorem fpProcessNaNs_eq32 (t1 t2 : FPType) (a b : BitVec 32) :
    FPProcessNaNs t1 t2 a b fpcrV = FPProcessNaNs__1 t1 t2 a b fpcrV true := rfl

/-- The exact product of two finite operands. -/
theorem mul_val32 (a b : BitVec 32) (hfa : ex32 a ≠ 255) (hfb : ex32 b ≠ 255) :
    mult_real (val32 a) (val32 b) = qop (sg32 a != sg32 b) (mag32 a * mag32 b) (2 ^ 149) 149 := by
  rw [val32_fin a hfa, val32_fin b hfb, sv32_eq, sv32_eq]
  cases sg32 a <;> cases sg32 b <;>
    simp (config := {decide := true}) only [qop, mult_real, ↓reduceIte, Bool.false_eq_true] <;>
    push_cast <;> simp only [zpow_neg, zpow_ofNat] <;> ring

/-- The bits of FPSR that FPMul sets at 32 bits under FPCR 0x02000000. -/
def mulMask32 (a b : BitVec 32) : BitVec 64 :=
  if isNaNT (ty32 a) || isNaNT (ty32 b) then
    (if ty32 a == .FPType_SNaN || ty32 b == .FPType_SNaN then 1#64 else 0#64)
  else if (ty32 a == .FPType_Infinity && ty32 b == .FPType_Zero) ||
      (ty32 a == .FPType_Zero && ty32 b == .FPType_Infinity) then 1#64
  else if ty32 a == .FPType_Infinity || ty32 b == .FPType_Infinity ||
      ty32 a == .FPType_Zero || ty32 b == .FPType_Zero then 0#64
  else maskQ32 (mag32 a * mag32 b) (2 ^ 149)

set_option hygiene false in
macro "mul_fin32" : tactic => `(tactic| (
  have hfa : ex32 a ≠ 255 :=
    ty32_fin a (by rw [ha]; exact fun h => FPType.noConfusion h) (by rw [ha]; rfl)
  have hfb : ex32 b ≠ 255 :=
    ty32_fin b (by rw [hb]; exact fun h => FPType.noConfusion h) (by rw [hb]; rfl)
  have hza : 0 < mag32 a := Nat.pos_of_ne_zero fun h0 => by
    have := (ty32_zero a hfa).mp h0; rw [ha] at this; exact FPType.noConfusion this
  have hzb : 0 < mag32 b := Nat.pos_of_ne_zero fun h0 => by
    have := (ty32_zero b hfb).mp h0; rw [hb] at this; exact FPType.noConfusion this
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  rw [mul_val32 a b hfa hfb]
  sail_simp [FPRound, FPRound__1, FPRoundingMode, FPDecodeRounding, fpcr_RMode]
  refine step hf3 (fpRound32_q _ _ _ (Nat.mul_pos hza hzb) (Nat.two_pow_pos 149) h hr3') ?_
  intro σ4 hr4 hf4
  sail_simp [FPProcessDenorms, hr4, h.hfi, h.hps, h.nrw, h.aa64, h.fa, Std.ExtDHashMap.get?_insert]
  rw [rdm_eq_rrm32]
  exact ⟨σ4, rfl, hr4, hf4⟩))

set_option hygiene false in
macro "mul_sgn32" : tactic => `(tactic| (
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  cases hsa : sg32 a <;> cases hsb : sg32 b <;> (try simp only [sgBit32, hsa, hsb, ↓reduceIte] at ⊢)
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
          (or_masks _).2.2.1]))))

set_option maxHeartbeats 1000000 in
theorem fpMul32_run (a b : BitVec 32) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPMul a b fpcrV).run s = .ok (Wasm.f32Mul (.ofBitVec a) (.ofBitVec b)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| mulMask32 a b) ∧ Frame s s' := by
  subst hs
  simp only [FPMul, fpUnpack_eq32, fpProcessNaNs_eq32]
  sail_simp []
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run32 a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  refine step hf1 (fpUnpack_run32 b h hr1) ?_
  intro σ2 hr2 hf2
  sail_simp []
  refine step hf2 (fpProcessNaNs_run32 _ _ a b h hr2) ?_
  intro σ3 hr3 hf3
  simp only [Wasm.f32Mul, Wasm.IEEE32.mul, t_isNaN32, t_isInf32, t_sign32, mulMask32]
  simp only [mag32_beq_zero]
  have hioc : ioc fpsr = fpsr ||| 1#64 := by
    rw [ioc, upd_or _ _ (by norm_num), (or_masks _).2.2.1]
  cases ha : ty32 a <;> cases hb : ty32 b <;> simp only [isNaNT] at hr3 ⊢ <;> sail_simp []
  -- The NaN cases.
  all_goals first
    | (refine ⟨σ3, ?_, ?_, hf3⟩
       · rfl
       · rw [hr3]
         simp only [ha, hb, ftb_SNaN_SNaN, ftb_QNaN_SNaN,
           ftb_Zero_SNaN, ftb_Denormal_SNaN,
           ftb_Nonzero_SNaN, ftb_Infinity_SNaN, Bool.or_true,
           Bool.true_or, Bool.or_false, Bool.false_or, ↓reduceIte, Bool.false_eq_true, hioc,
           BitVec.or_zero] <;> first | rfl | exact (insert_self _ _ _ h.hfpsr).symm)
    | skip
  all_goals first | mul_fin32 | skip
  all_goals mul_sgn32

/-- FPMul at 32 bits under FPCR 0x02000000 returns Talos's `f32Mul` for every pair of words from
every state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| mulMask32 a b`, and the
other registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fpMul32_eq_f32Mul (a b : BitVec 32) (s : State) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPMul a b fpcrV).run s =
        .ok (Wasm.f32Mul (UInt32.ofBitVec a) (UInt32.ofBitVec b)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| mulMask32 a b) ∧ Frame s s' :=
  fpMul32_run a b h rfl

end F7
