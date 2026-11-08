import F7.FPAdd

/-!
FPSub of Sail's Lean translation of the Armv9.4-A model, at 64 bits under FPCR 0x02000000,
returns Talos's `f64Sub` of its operands for every pair of words and sets in FPSR the bits of
`subMask`, from every state that satisfies `Hyp`.  Talos's `sub a b` is `add a (negate b)`, and
`negW b`, the word of `negate b`, has the type and magnitude of `b` and the opposite sign
(`ty_negW`, `sg_negW`, `sv_negW`).  FPSub__1 differs from FPAdd__1 in the tests of the signs and in
`sub_real` in place of `add_real`, so `fpSub_run` follows `fpAdd_run` with the exact difference
`(sv a - sv b) · 2^-1074` (`sub_diff`) and `fpRound_run`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

/-- The word of Talos's `negate x`. -/
def negW (x : BitVec 64) : BitVec 64 := (Wasm.IEEE64.negate (UInt64.ofBitVec x)).toBitVec

theorem negate_eq (x : BitVec 64) :
    Wasm.IEEE64.negate (UInt64.ofBitVec x) = UInt64.ofBitVec (negW x) := by
  simp [negW]

theorem negW_toNat (x : BitVec 64) :
    (negW x).toNat = (if sg x then 0 else 2 ^ 63) + ex x * 2 ^ 52 + fr x := by
  have he : ex x < 2 ^ 11 := Nat.mod_lt _ (by decide)
  have hf : fr x < 2 ^ 52 := Nat.mod_lt _ (by decide)
  simp only [negW, Wasm.IEEE64.negate, toBV_encode, t_sign, t_exp, t_frac, BitVec.toNat_ofNat]
  generalize ex x = e at *
  generalize fr x = f at *
  cases sg x <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] <;>
    omega

theorem ex_negW (x : BitVec 64) : ex (negW x) = ex x := by
  have he : ex x < 2 ^ 11 := Nat.mod_lt _ (by decide)
  have hf : fr x < 2 ^ 52 := Nat.mod_lt _ (by decide)
  show (negW x).toNat / 2 ^ 52 % 2 ^ 11 = ex x
  rw [negW_toNat]
  generalize ex x = e at *
  generalize fr x = f at *
  cases sg x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem fr_negW (x : BitVec 64) : fr (negW x) = fr x := by
  have hf : fr x < 2 ^ 52 := Nat.mod_lt _ (by decide)
  show (negW x).toNat % 2 ^ 52 = fr x
  rw [negW_toNat]
  generalize ex x = e at *
  generalize fr x = f at *
  cases sg x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

theorem sg_negW (x : BitVec 64) : sg (negW x) = !sg x := by
  have he : ex x < 2 ^ 11 := Nat.mod_lt _ (by decide)
  have hf : fr x < 2 ^ 52 := Nat.mod_lt _ (by decide)
  show decide (2 ^ 63 ≤ (negW x).toNat) = !sg x
  rw [negW_toNat]
  generalize ex x = e at *
  generalize fr x = f at *
  cases sg x <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.not_false,
    decide_eq_true_eq, decide_eq_false_iff_not] <;> omega

theorem ty_negW (x : BitVec 64) : ty64 (negW x) = ty64 x := by
  unfold ty64
  rw [ex_negW, fr_negW]

theorem sv_negW (x : BitVec 64) :
    Wasm.IEEE64.scaledValue (UInt64.ofBitVec (negW x)) =
      -Wasm.IEEE64.scaledValue (UInt64.ofBitVec x) := by
  have hm : Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec (negW x)) =
      Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) := by
    simp only [Wasm.IEEE64.scaledMagnitude, t_exp, t_frac, ex_negW, fr_negW]
  rw [sv_eq, sv_eq, sg_negW, hm]
  cases sg x <;> simp

theorem inf_negW (x : BitVec 64) (h : ty64 x = .FPType_Infinity) :
    negW x = if sg x then 0x7FF0000000000000#64 else 0xFFF0000000000000#64 := by
  obtain ⟨he, hf⟩ := ty_inf x h
  apply BitVec.eq_of_toNat_eq
  rw [negW_toNat, he, hf]
  cases sg x <;> rfl

theorem sub_diff (A B : ℤ) :
    sub_real ((A : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) ((B : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) =
      ((A - B : ℤ) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) := by
  simp only [sub_real]; push_cast; ring

/-- Two finite operands, not both zeros, whose exact difference is zero, are not a negative
minuend and a positive subtrahend. -/
theorem not_neg_pos (a b : BitVec 64) (hfa : ex a ≠ 2047) (hfb : ex b ≠ 2047)
    (hz : ¬ (ty64 a = .FPType_Zero ∧ ty64 b = .FPType_Zero))
    (hs : Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) -
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) = 0) : (sg a && !sg b) = false := by
  have := not_both_neg a (negW b) hfa (by rw [ex_negW]; exact hfb) (by rw [ty_negW]; exact hz)
    (by rw [sv_negW]; omega)
  rwa [sg_negW] at this

theorem sub_real_zero : sub_real 0 0 = 0 := by simp [sub_real]

/-- The bits of FPSR that FPSub sets at 64 bits under FPCR 0x02000000. -/
def subMask (a b : BitVec 64) : BitVec 64 :=
  if isNaNT (ty64 a) || isNaNT (ty64 b) then
    (if ty64 a == .FPType_SNaN || ty64 b == .FPType_SNaN then 1#64 else 0#64)
  else if ty64 a == .FPType_Infinity || ty64 b == .FPType_Infinity then
    (if ty64 a == .FPType_Infinity && ty64 b == .FPType_Infinity && sg a == sg b then 1#64
     else 0#64)
  else
    let z := Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) -
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec b)
    if z = 0 then 0#64 else roundMask z.natAbs

set_option hygiene false in
macro "sub_fin" : tactic => `(tactic| (
  have hfa : ex a ≠ 2047 :=
    ty_fin a (by rw [ha]; exact fun h => FPType.noConfusion h) (by rw [ha]; rfl)
  have hfb : ex b ≠ 2047 :=
    ty_fin b (by rw [hb]; exact fun h => FPType.noConfusion h) (by rw [hb]; rfl)
  have hnz : ¬ (ty64 a = .FPType_Zero ∧ ty64 b = .FPType_Zero) := by
    rw [ha, hb]; intro ⟨h1, h2⟩; first | exact FPType.noConfusion h1 | exact FPType.noConfusion h2
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  rw [val_fin a hfa, val_fin b hfb, sub_diff, eq_sum]
  by_cases hz : Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) -
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) = 0
  · have hsg := not_neg_pos a b hfa hfb hnz hz
    sail_simp [hz, hsg, FPZero, FPProcessDenorms, hr3', h.hfi, h.hps, h.nrw, h.aa64, h.fa]
    refine ⟨_, rfl, ?_, hf3⟩
    rw [hr3', BitVec.or_zero]
    exact (insert_self _ _ _ h.hfpsr).symm
  · rw [sop_eq _ hz]
    sail_simp [hz]
    refine step hf3 (fpRound_run _ _ (Int.natAbs_pos.mpr hz) h hr3') ?_
    intro σ4 hr4 hf4
    sail_simp [FPProcessDenorms, hr4, h.hfi, h.hps, h.nrw, h.aa64, h.fa, Std.ExtDHashMap.get?_insert]
    have hz' : (Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) -
        Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) == 0) = false := by simpa using hz
    simp only [hz', Bool.false_eq_true, ↓reduceIte, tRound]
    exact ⟨σ4, rfl, hr4, hf4⟩))

set_option hygiene false in
macro "sub_sgn" : tactic => `(tactic| (
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  cases hsa : sg a <;> cases hsb : sg b <;> (try simp only [sgBit, hsa, hsb, ↓reduceIte] at ⊢)
  all_goals try sail_simp [FPZero, FPInfinity, FPProcessDenorms, FPProcessException, hr3', h.hfi,
    h.hps, h.nrw, h.aa64, h.fa, h.hfpsr]
  all_goals try sail_simp [FPDefaultNaN__1, FPProcessException, FPProcessDenorms, hr3', h.hfi,
    h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, setReg_regs, cast_eq, ite_self]
  all_goals try rw [inf_negW b (by assumption)]
  all_goals try rw [inf_word a (by assumption)]
  all_goals try rw [val_zero a (by assumption)]
  all_goals try rw [val_zero b (by assumption)]
  all_goals try rw [sv_zero a (by assumption)]
  all_goals try rw [sv_zero b (by assumption)]
  all_goals try simp only [hsa, hsb, ↓reduceIte, sub_real_zero, eq_real_zero, sub_zero,
    beq_self_eq_true, Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.and_self,
    Bool.not_true, Bool.not_false, Bool.and_true, Bool.true_and]
  all_goals try sail_simp [FPZero, FPProcessDenorms, hr3', h.hfi, h.hps, h.nrw, h.aa64, h.fa]
  all_goals (
    refine ⟨_, ok_congr ?v, ?r, ⟨hf3.mem, hf3.tags, hf3.cyc, hf3.out⟩⟩
    case v => decide
    case r =>
      first
      | (rw [hr3', BitVec.or_zero]; exact (insert_self _ _ _ h.hfpsr).symm)
      | (simp only [setReg_regs, bump_regs, faS_regs, hr3', upd_or _ _ (by norm_num : 0 < 64),
          (or_masks _).2.2.1]))))

set_option maxHeartbeats 900000 in
theorem fpSub_run (a b : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPSub a b fpcrV).run s = .ok (Wasm.f64Sub (.ofBitVec a) (.ofBitVec b)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| subMask a b) ∧ Frame s s' := by
  subst hs
  simp only [FPSub, FPSub__1]
  sail_simp [FPRoundingMode, FPDecodeRounding, fpcr_RMode]
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  refine step hf1 (fpUnpack_run b h hr1) ?_
  intro σ2 hr2 hf2
  sail_simp []
  refine step hf2 (fpProcessNaNs_run _ _ a b h hr2) ?_
  intro σ3 hr3 hf3
  simp only [Wasm.f64Sub, Wasm.IEEE64.sub, negate_eq, Wasm.IEEE64.add, t_isNaN, t_isInf, t_sign,
    ty_negW, sg_negW, sv_negW, ← sub_eq_add_neg, subMask]
  have hioc : ioc fpsr = fpsr ||| 1#64 := by rw [ioc, upd_or _ _ (by norm_num), (or_masks _).2.2.1]
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
  all_goals first | sub_fin | skip
  all_goals sub_sgn

/-- FPSub at 64 bits under FPCR 0x02000000 returns Talos's `f64Sub` for every pair of words from
every state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| subMask a b`, and the
other registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fpSub_eq_f64Sub (a b : BitVec 64) (s : State) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPSub a b fpcrV).run s =
        .ok (Wasm.f64Sub (UInt64.ofBitVec a) (UInt64.ofBitVec b)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| subMask a b) ∧ Frame s s' :=
  fpSub_run a b h rfl

end F7
