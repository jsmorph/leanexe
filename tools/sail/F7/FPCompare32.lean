import F7.FPCompare
import F7.FPSqrt32

/-!
FPCompare of Sail's Lean translation of the Armv9.4-A model, at 32 bits under FPCR 0x02000000
with `signal_nans` false, as FCMP S calls it, returns the flags `fcmpNZCV32` of the model's
`State.fcmpS` for every pair of words and sets FPSR.IOC for a signaling NaN operand, from every
state that satisfies `Hyp`.  The proof follows `fpCompare_run` of `F7/FPCompare.lean`.  FPUnpack
gives a finite word the value `scaledValue · 2^-149` and an infinity `±2^1000000`; Talos's `eq` and
`lt` compare `scaledValue`, which is `±2^277` for an infinity and smaller in magnitude for every
finite word.  `extV32` is strictly increasing on `[-2^277, 2^277]`, so the comparisons of the real
values equal Talos's comparisons (`val32_eq_sv`, `val32_lt_sv`).
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

set_option exponentiation.threshold 300 in
theorem mag32_inf_eq (x : BitVec 32) (h : ty32 x = .FPType_Infinity) : mag32 x = 2 ^ 277 := by
  obtain ⟨he, hf⟩ := ty32_inf x h
  simp only [mag32, Wasm.IEEE32.scaledMagnitude, t_exp32, t_frac32, he, hf]
  norm_num

/-- The real value that FPUnpack gives a binary32 word that is not a NaN, as a function of Talos's
`scaledValue`. -/
noncomputable def extV32 (z : ℤ) : ℝ :=
  if z = 2 ^ 277 then (2 : ℝ) ^ (1000000 : ℤ)
  else if z = -2 ^ 277 then -(2 : ℝ) ^ (1000000 : ℤ)
  else (z : ℝ) * (2 : ℝ) ^ (-149 : ℤ)

theorem sv32_bound (x : BitVec 32) (h : isNaNT (ty32 x) = false) :
    -2 ^ 277 ≤ Wasm.IEEE32.scaledValue (UInt32.ofBitVec x) ∧
      Wasm.IEEE32.scaledValue (UInt32.ofBitVec x) ≤ 2 ^ 277 := by
  rw [sv32_eq]
  by_cases hi : ty32 x = .FPType_Infinity
  · have := mag32_inf_eq x hi
    simp only [mag32] at this
    rw [this]
    split <;> constructor <;> norm_num
  · have := mag32_lt x (ty32_fin x hi h)
    split <;> constructor <;> omega

theorem val32_extV (x : BitVec 32) (h : isNaNT (ty32 x) = false) :
    val32 x = extV32 (Wasm.IEEE32.scaledValue (UInt32.ofBitVec x)) := by
  by_cases hi : ty32 x = .FPType_Infinity
  · obtain ⟨he, hf⟩ := ty32_inf x hi
    have hm := mag32_inf_eq x hi
    simp only [mag32] at hm
    have hT : ((2 ^ 277 : ℕ) : ℤ) = 2 ^ 277 := by rw [Nat.cast_pow, Nat.cast_ofNat]
    have hne : (-2 ^ 277 : ℤ) ≠ 2 ^ 277 := by
      have : (0 : ℤ) < 2 ^ 277 := by positivity
      omega
    rw [sv32_eq, hm, hT]
    unfold val32
    rw [ite_eq_left he, ite_eq_left hf]
    cases sg32 x
    · rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
      unfold extV32
      rw [ite_eq_left rfl]
    · rw [ite_eq_left rfl, ite_eq_left rfl]
      unfold extV32
      rw [ite_eq_right hne, ite_eq_left rfl]
  · have hfin := ty32_fin x hi h
    have hm := mag32_lt x hfin
    rw [val32_fin x hfin]
    unfold extV32
    rw [sv32_eq]
    split <;> rename_i hs <;> (rw [ite_eq_right (by omega), ite_eq_right (by omega)])

theorem extV32_strictMonoOn : StrictMonoOn extV32 (Set.Icc (-2 ^ 277) (2 ^ 277)) := by
  intro z hz w hw hzw
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hw1, hw2⟩ := hw
  have hc : (0 : ℝ) < (2 : ℝ) ^ (-149 : ℤ) := zpow_pos (by norm_num) _
  have hT : ((2 ^ 277 : ℤ) : ℝ) * (2 : ℝ) ^ (-149 : ℤ) = (2 : ℝ) ^ (128 : ℤ) := by
    rw [Int.cast_pow, Int.cast_ofNat, ← zpow_natCast, ← zpow_add₀ two_ne_zero]
    norm_num
  have hP : (2 : ℝ) ^ (128 : ℤ) < (2 : ℝ) ^ (1000000 : ℤ) :=
    zpow_lt_zpow_right₀ (by norm_num) (by norm_num)
  have hB : (0 : ℝ) < (2 : ℝ) ^ (128 : ℤ) := zpow_pos (by norm_num) _
  have lo : ∀ y : ℤ, -2 ^ 277 < y → -(2 : ℝ) ^ (128 : ℤ) < (y : ℝ) * (2 : ℝ) ^ (-149 : ℤ) := by
    intro y hy
    have h1 : ((-2 ^ 277 : ℤ) : ℝ) < y := by exact_mod_cast hy
    have h2 := mul_lt_mul_of_pos_right h1 hc
    rwa [Int.cast_neg, neg_mul, hT] at h2
  have hi : ∀ y : ℤ, y < 2 ^ 277 → (y : ℝ) * (2 : ℝ) ^ (-149 : ℤ) < (2 : ℝ) ^ (128 : ℤ) := by
    intro y hy
    have h1 : (y : ℝ) < ((2 ^ 277 : ℤ) : ℝ) := by exact_mod_cast hy
    have h2 := mul_lt_mul_of_pos_right h1 hc
    rwa [hT] at h2
  have mono : (z : ℝ) * (2 : ℝ) ^ (-149 : ℤ) < (w : ℝ) * (2 : ℝ) ^ (-149 : ℤ) :=
    mul_lt_mul_of_pos_right (by exact_mod_cast hzw) hc
  unfold extV32
  by_cases a1 : z = 2 ^ 277
  · omega
  by_cases b1 : w = 2 ^ 277
  · by_cases a2 : z = -2 ^ 277
    · rw [ite_eq_right a1, ite_eq_left a2, ite_eq_left b1]
      generalize (2 : ℝ) ^ (1000000 : ℤ) = P at *
      generalize (2 : ℝ) ^ (128 : ℤ) = B at *
      linarith
    · rw [ite_eq_right a1, ite_eq_right a2, ite_eq_left b1]
      have h3 := hi z (by omega)
      generalize (2 : ℝ) ^ (1000000 : ℤ) = P at *
      generalize (2 : ℝ) ^ (128 : ℤ) = B at *
      linarith
  · have b2 : w ≠ -2 ^ 277 := by omega
    rw [ite_eq_right b1, ite_eq_right b2]
    by_cases a2 : z = -2 ^ 277
    · rw [ite_eq_right a1, ite_eq_left a2]
      have h3 := lo w (by omega)
      generalize (2 : ℝ) ^ (1000000 : ℤ) = P at *
      generalize (2 : ℝ) ^ (128 : ℤ) = B at *
      linarith
    · rw [ite_eq_right a1, ite_eq_right a2]
      exact mono

theorem val32_lt_sv (a b : BitVec 32) (ha : isNaNT (ty32 a) = false)
    (hb : isNaNT (ty32 b) = false) :
    lt_real (val32 a) (val32 b) =
      decide (Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) <
        Wasm.IEEE32.scaledValue (UInt32.ofBitVec b)) := by
  rw [val32_extV a ha, val32_extV b hb]
  simp only [lt_real, decide_eq_decide]
  exact extV32_strictMonoOn.lt_iff_lt (sv32_bound a ha) (sv32_bound b hb)

theorem val32_eq_sv (a b : BitVec 32) (ha : isNaNT (ty32 a) = false)
    (hb : isNaNT (ty32 b) = false) :
    eq_real (val32 a) (val32 b) =
      decide (Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) =
        Wasm.IEEE32.scaledValue (UInt32.ofBitVec b)) := by
  rw [val32_extV a ha, val32_extV b hb]
  simp only [eq_real, decide_eq_decide]
  exact extV32_strictMonoOn.injOn.eq_iff (sv32_bound a ha) (sv32_bound b hb)

/-- The bits of FPSR that FPCompare sets at 32 bits under FPCR 0x02000000 with `signal_nans`
false: IOC for a signaling NaN operand. -/
def cmpMask32 (a b : BitVec 32) : BitVec 64 :=
  if ty32 a == .FPType_SNaN || ty32 b == .FPType_SNaN then 1#64 else 0#64

set_option maxHeartbeats 40000 in
theorem fpCompare32_run (a b : BitVec 32) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPCompare a b false fpcrV).run s =
        .ok (BitVec.ofNat 4 (LeanExe.A64.Isla.fcmpNZCV32 (.ofBitVec a) (.ofBitVec b))) s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| cmpMask32 a b) ∧ Frame s s' := by
  subst hs
  simp only [FPCompare, fpUnpack_eq32]
  sail_simp []
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run32 a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  refine step hf1 (fpUnpack_run32 b h hr1) ?_
  intro σ2 hr2 hf2
  sail_simp [ty_nan_or]
  by_cases hn : (isNaNT (ty32 a) || isNaNT (ty32 b)) = true
  · rw [ite_eq_left hn]
    have hnan :
        (Wasm.IEEE32.isNaN (.ofBitVec a) || Wasm.IEEE32.isNaN (.ofBitVec b)) = true := by
      rw [t_isNaN32, t_isNaN32]; exact hn
    have hv : LeanExe.A64.Isla.fcmpNZCV32 (.ofBitVec a) (.ofBitVec b) = 3 := by
      simp only [LeanExe.A64.Isla.fcmpNZCV32, Wasm.IEEE32.lt, Wasm.IEEE32.eq, hnan, ↓reduceIte]
      rfl
    rw [hv]
    by_cases hsn : (ty32 a == .FPType_SNaN || ty32 b == .FPType_SNaN) = true
    · rw [ite_eq_left hsn]
      sail_simp [FPProcessException, hr2, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr]
      refine ⟨_, rfl, ?_, ⟨hf2.mem, hf2.tags, hf2.cyc, hf2.out⟩⟩
      simp only [setReg_regs, bump_regs, faS_regs, hr2, cmpMask32, hsn, ↓reduceIte,
        upd_or _ _ (by norm_num : 0 < 64), (or_masks _).2.2.1]
    · rw [ite_eq_right hsn]
      refine ⟨_, rfl, ?_, ⟨hf2.mem, hf2.tags, hf2.cyc, hf2.out⟩⟩
      have hm : cmpMask32 a b = 0#64 := by
        unfold cmpMask32; rw [ite_eq_right hsn]
      rw [bump_regs, hr2, hm, BitVec.or_zero]
      exact (insert_self _ _ _ h.hfpsr).symm
  · rw [ite_eq_right hn]
    have ha : isNaNT (ty32 a) = false := by
      revert hn; cases isNaNT (ty32 a) <;> simp
    have hb : isNaNT (ty32 b) = false := by
      revert hn; cases isNaNT (ty32 b) <;> simp
    rw [val32_eq_sv a b ha hb, val32_lt_sv a b ha hb]
    sail_simp [FPProcessDenorms, hr2, h.hfi, h.hps, h.nrw, h.aa64]
    refine ⟨_, ok_congr ?_, ?_, ⟨hf2.mem, hf2.tags, hf2.cyc, hf2.out⟩⟩
    · simp only [LeanExe.A64.Isla.fcmpNZCV32, Wasm.IEEE32.lt, Wasm.IEEE32.eq, t_isNaN32, ha, hb,
        Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      generalize Wasm.IEEE32.scaledValue (UInt32.ofBitVec a) = x
      generalize Wasm.IEEE32.scaledValue (UInt32.ofBitVec b) = y
      by_cases e1 : x = y
      · subst e1; simp
      · have e3 : (x == y) = false := beq_eq_false_iff_ne.mpr e1
        by_cases e2 : x < y
        · simp [e1, e2, e3]
        · simp [e1, e2, e3]
    · have hm : cmpMask32 a b = 0#64 := by
        unfold cmpMask32; rw [snan_of_not_nan _ ha, snan_of_not_nan _ hb]; rfl
      simp only [bump_regs, hr2, hm, BitVec.or_zero]
      exact (insert_self _ _ _ h.hfpsr).symm

/-- FPCompare at 32 bits under FPCR 0x02000000 with `signal_nans` false returns the flags
`fcmpNZCV32` of `State.fcmpS` for every pair of words from every state that satisfies the state
hypothesis.  FPSR becomes `fpsr ||| cmpMask32 a b`, and the other registers, the memory, the tags,
the cycle count, and the output do not change. -/
theorem fpCompare32_eq_fcmpNZCV32 (a b : BitVec 32) (s : State) (fi : Vector Bool 259)
    (ps : ProcState) (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPCompare a b false fpcrV).run s =
        .ok (BitVec.ofNat 4
          (LeanExe.A64.Isla.fcmpNZCV32 (UInt32.ofBitVec a) (UInt32.ofBitVec b))) s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| cmpMask32 a b) ∧ Frame s s' :=
  fpCompare32_run a b h rfl

end F7
