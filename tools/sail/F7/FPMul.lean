import F7.Round

/-!
FPMul of Sail's Lean translation of the Armv9.4-A model, at 64 bits under FPCR 0x02000000,
returns Talos's `f64Mul` of its operands for every pair of words and sets in FPSR the bits of
`mulMask`, from every state that satisfies `Hyp`.  FPMul calls FPUnpack and FPProcessNaNs, which
are FPUnpack__1 and FPProcessNaNs__1 with `fpexc` true, and FPRound, which reads the rounding mode
and calls FPRound__2.  The exact product of two finite nonzero operands is
`±(A · B) · 2^-2148` for their magnitudes `A` and `B` in units of 2^-1074 (`mul_val`), so
`fpRound_dy` with `X = 1074` gives Talos's `roundDyadicMagnitude` of `A · B` with 1074 fractional
bits, the rounder of `IEEE64.mul`, and the FPSR bits of `maskDy`, among them UFC for an inexact
subnormal product.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

theorem fpUnpack_eq (x : BitVec 64) : FPUnpack x fpcrV = FPUnpack__1 x fpcrV true := rfl

theorem fpProcessNaNs_eq (t1 t2 : FPType) (a b : BitVec 64) :
    FPProcessNaNs t1 t2 a b fpcrV = FPProcessNaNs__1 t1 t2 a b fpcrV true := rfl

/-- The magnitude of a word in units of 2^-1074, as Talos computes it. -/
abbrev mag (x : BitVec 64) : ℕ := Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x)

theorem mag_beq_zero (x : BitVec 64) :
    (Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) == 0) = (ty64 x == .FPType_Zero) := by
  by_cases hf : ex x = 2047
  · have hm : mag x ≠ 0 := by
      simp only [mag, Wasm.IEEE64.scaledMagnitude, t_exp, t_frac, hf]
      simp
    have ht : ty64 x ≠ .FPType_Zero := by
      unfold ty64; rw [if_neg (by omega), if_pos hf]; split_ifs <;> simp
    simp only [beq_eq_false_iff_ne.mpr hm]
    cases h : ty64 x <;> first | rfl | exact absurd h ht
  · by_cases hz : ty64 x = .FPType_Zero
    · rw [hz, (ty_zero x hf).mpr hz]; rfl
    · have hm : mag x ≠ 0 := fun h => hz ((ty_zero x hf).mp h)
      simp only [beq_eq_false_iff_ne.mpr hm]
      cases h : ty64 x <;> first | rfl | exact absurd h hz

/-- The exact product of two finite operands. -/
theorem mul_val (a b : BitVec 64) (hfa : ex a ≠ 2047) (hfb : ex b ≠ 2047) :
    mult_real (val64 a) (val64 b) = sop (sg a != sg b) (mag a * mag b) 2148 := by
  rw [val_fin a hfa, val_fin b hfb, sv_eq, sv_eq]
  have e : (2 : ℝ) ^ (-2148 : ℤ) = (2 : ℝ) ^ (-1074 : ℤ) * (2 : ℝ) ^ (-1074 : ℤ) := by
    rw [← zpow_add₀ two_ne_zero]; norm_num
  cases sg a <;> cases sg b <;>
    simp (config := {decide := true}) only [sop, mult_real, e, ↓reduceIte, Bool.false_eq_true] <;>
    push_cast <;> ring

/-- The bits of FPSR that FPMul sets at 64 bits under FPCR 0x02000000. -/
def mulMask (a b : BitVec 64) : BitVec 64 :=
  if isNaNT (ty64 a) || isNaNT (ty64 b) then
    (if ty64 a == .FPType_SNaN || ty64 b == .FPType_SNaN then 1#64 else 0#64)
  else if (ty64 a == .FPType_Infinity && ty64 b == .FPType_Zero) ||
      (ty64 a == .FPType_Zero && ty64 b == .FPType_Infinity) then 1#64
  else if ty64 a == .FPType_Infinity || ty64 b == .FPType_Infinity ||
      ty64 a == .FPType_Zero || ty64 b == .FPType_Zero then 0#64
  else maskDy (mag a * mag b) 1074

set_option hygiene false in
macro "mul_fin" : tactic => `(tactic| (
  have hfa : ex a ≠ 2047 :=
    ty_fin a (by rw [ha]; exact fun h => FPType.noConfusion h) (by rw [ha]; rfl)
  have hfb : ex b ≠ 2047 :=
    ty_fin b (by rw [hb]; exact fun h => FPType.noConfusion h) (by rw [hb]; rfl)
  have hza : 0 < mag a := Nat.pos_of_ne_zero fun h0 => by
    have := (ty_zero a hfa).mp h0; rw [ha] at this; exact FPType.noConfusion this
  have hzb : 0 < mag b := Nat.pos_of_ne_zero fun h0 => by
    have := (ty_zero b hfb).mp h0; rw [hb] at this; exact FPType.noConfusion this
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  rw [mul_val a b hfa hfb]
  sail_simp [FPRound, FPRound__1, FPRoundingMode, FPDecodeRounding, fpcr_RMode]
  refine step hf3 (fpRound_dy _ _ 1074 2148 (by norm_num) (Nat.mul_pos hza hzb) h hr3') ?_
  intro σ4 hr4 hf4
  sail_simp [FPProcessDenorms, hr4, h.hfi, h.hps, h.nrw, h.aa64, h.fa, Std.ExtDHashMap.get?_insert]
  exact ⟨σ4, rfl, hr4, hf4⟩))

set_option hygiene false in
macro "mul_sgn" : tactic => `(tactic| (
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
          (or_masks _).2.2.1]))))

set_option maxHeartbeats 1000000 in
theorem fpMul_run (a b : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPMul a b fpcrV).run s = .ok (Wasm.f64Mul (.ofBitVec a) (.ofBitVec b)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| mulMask a b) ∧ Frame s s' := by
  subst hs
  simp only [FPMul, fpUnpack_eq, fpProcessNaNs_eq]
  sail_simp []
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  refine step hf1 (fpUnpack_run b h hr1) ?_
  intro σ2 hr2 hf2
  sail_simp []
  refine step hf2 (fpProcessNaNs_run _ _ a b h hr2) ?_
  intro σ3 hr3 hf3
  simp only [Wasm.f64Mul, Wasm.IEEE64.mul, t_isNaN, t_isInf, t_sign, mulMask]
  simp only [mag_beq_zero]
  have hioc : ioc fpsr = fpsr ||| 1#64 := by
    rw [ioc, upd_or _ _ (by norm_num), (or_masks _).2.2.1]
  cases ha : ty64 a <;> cases hb : ty64 b <;> simp only [isNaNT] at hr3 ⊢ <;> sail_simp []
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
  all_goals first | mul_fin | skip
  all_goals mul_sgn

/-- FPMul at 64 bits under FPCR 0x02000000 returns Talos's `f64Mul` for every pair of words from
every state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| mulMask a b`, and the
other registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fpMul_eq_f64Mul (a b : BitVec 64) (s : State) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPMul a b fpcrV).run s =
        .ok (Wasm.f64Mul (UInt64.ofBitVec a) (UInt64.ofBitVec b)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| mulMask a b) ∧ Frame s s' :=
  fpMul_run a b h rfl

end F7
