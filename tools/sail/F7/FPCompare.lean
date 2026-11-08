import F7.FPToFixed
import LeanExe.A64.Isla.Float

/-!
FPCompare of Sail's Lean translation of the Armv9.4-A model, at 64 bits under FPCR 0x02000000
with `signal_nans` false, as FCMP D calls it, returns the flags `fcmpNZCV` of the model's
`State.fcmp` for every pair of words and sets FPSR.IOC for a signaling NaN operand, from every
state that satisfies `Hyp`.

FPCompare unpacks both operands and, unless one is a NaN, compares their real values, which
FPUnpack gives as `scaledValue · 2^-1074` for a finite word and as `±2^1000000` for an infinity.
Talos's `eq` and `lt` compare `scaledValue`, which is `±2^2098` for an infinity and smaller in
magnitude for every finite word.  `val_extV` writes FPUnpack's value of a word that is not a NaN as
`extV` of its `scaledValue`, and `extV` is strictly increasing on `[-2^2098, 2^2098]`
(`extV_strictMonoOn`), so the comparisons of the real values equal Talos's comparisons
(`val_eq_sv`, `val_lt_sv`).
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

theorem mag_fin_lt (x : BitVec 64) (h : ex x ≠ 2047) : mag x < 2 ^ 2098 := by
  simp only [mag, Wasm.IEEE64.scaledMagnitude, t_exp, t_frac]
  have hf : fr x < 2 ^ 52 := Nat.mod_lt _ (by norm_num)
  have he : ex x < 2048 := Nat.mod_lt _ (by norm_num)
  split
  · exact lt_trans hf (pow_lt_pow_right₀ (by norm_num) (by norm_num))
  · calc (2 ^ 52 + fr x) * 2 ^ (ex x - 1) < 2 ^ 53 * 2 ^ (ex x - 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
      _ ≤ 2 ^ 53 * 2 ^ 2045 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ = 2 ^ 2098 := by rw [← pow_add]

set_option exponentiation.threshold 2100 in
theorem mag_inf_eq (x : BitVec 64) (h : ty64 x = .FPType_Infinity) : mag x = 2 ^ 2098 := by
  obtain ⟨he, hf⟩ := ty_inf x h
  simp only [mag, Wasm.IEEE64.scaledMagnitude, t_exp, t_frac, he, hf]
  norm_num

/-- The real value that FPUnpack gives a word that is not a NaN, as a function of Talos's
`scaledValue`. -/
noncomputable def extV (z : ℤ) : ℝ :=
  if z = 2 ^ 2098 then (2 : ℝ) ^ (1000000 : ℤ)
  else if z = -2 ^ 2098 then -(2 : ℝ) ^ (1000000 : ℤ)
  else (z : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)

theorem sv_bound (x : BitVec 64) (h : isNaNT (ty64 x) = false) :
    -2 ^ 2098 ≤ Wasm.IEEE64.scaledValue (UInt64.ofBitVec x) ∧
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec x) ≤ 2 ^ 2098 := by
  rw [sv_eq]
  by_cases hi : ty64 x = .FPType_Infinity
  · have := mag_inf_eq x hi
    simp only [mag] at this
    rw [this]
    split <;> constructor <;> norm_num
  · have := mag_fin_lt x (ty_fin x hi h)
    simp only [mag] at this
    split <;> constructor <;> omega

theorem val_extV (x : BitVec 64) (h : isNaNT (ty64 x) = false) :
    val64 x = extV (Wasm.IEEE64.scaledValue (UInt64.ofBitVec x)) := by
  by_cases hi : ty64 x = .FPType_Infinity
  · obtain ⟨he, hf⟩ := ty_inf x hi
    have hm := mag_inf_eq x hi
    simp only [mag] at hm
    have hT : ((2 ^ 2098 : ℕ) : ℤ) = 2 ^ 2098 := by rw [Nat.cast_pow, Nat.cast_ofNat]
    have hne : (-2 ^ 2098 : ℤ) ≠ 2 ^ 2098 := by
      have : (0 : ℤ) < 2 ^ 2098 := by positivity
      omega
    rw [sv_eq, hm, hT]
    unfold val64
    rw [ite_eq_left he, ite_eq_left hf]
    cases sg x
    · rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
      unfold extV
      rw [ite_eq_left rfl]
    · rw [ite_eq_left rfl, ite_eq_left rfl]
      unfold extV
      rw [ite_eq_right hne, ite_eq_left rfl]
  · have hfin := ty_fin x hi h
    have hm := mag_fin_lt x hfin
    simp only [mag] at hm
    rw [val_fin x hfin]
    unfold extV
    rw [sv_eq]
    split <;> rename_i hs <;> (rw [ite_eq_right (by omega), ite_eq_right (by omega)])

theorem extV_strictMonoOn : StrictMonoOn extV (Set.Icc (-2 ^ 2098) (2 ^ 2098)) := by
  intro z hz w hw hzw
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hw1, hw2⟩ := hw
  have hc : (0 : ℝ) < (2 : ℝ) ^ (-1074 : ℤ) := zpow_pos (by norm_num) _
  have hT : ((2 ^ 2098 : ℤ) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) = (2 : ℝ) ^ (1024 : ℤ) := by
    rw [Int.cast_pow, Int.cast_ofNat, ← zpow_natCast, ← zpow_add₀ two_ne_zero]
    norm_num
  have hP : (2 : ℝ) ^ (1024 : ℤ) < (2 : ℝ) ^ (1000000 : ℤ) :=
    zpow_lt_zpow_right₀ (by norm_num) (by norm_num)
  have hB : (0 : ℝ) < (2 : ℝ) ^ (1024 : ℤ) := zpow_pos (by norm_num) _
  have lo : ∀ y : ℤ, -2 ^ 2098 < y → -(2 : ℝ) ^ (1024 : ℤ) < (y : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) := by
    intro y hy
    have h1 : ((-2 ^ 2098 : ℤ) : ℝ) < y := by exact_mod_cast hy
    have h2 := mul_lt_mul_of_pos_right h1 hc
    rwa [Int.cast_neg, neg_mul, hT] at h2
  have hi : ∀ y : ℤ, y < 2 ^ 2098 → (y : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) < (2 : ℝ) ^ (1024 : ℤ) := by
    intro y hy
    have h1 : (y : ℝ) < ((2 ^ 2098 : ℤ) : ℝ) := by exact_mod_cast hy
    have h2 := mul_lt_mul_of_pos_right h1 hc
    rwa [hT] at h2
  have mono : (z : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) < (w : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) :=
    mul_lt_mul_of_pos_right (by exact_mod_cast hzw) hc
  unfold extV
  by_cases a1 : z = 2 ^ 2098
  · omega
  by_cases b1 : w = 2 ^ 2098
  · by_cases a2 : z = -2 ^ 2098
    · rw [ite_eq_right a1, ite_eq_left a2, ite_eq_left b1]
      generalize (2 : ℝ) ^ (1000000 : ℤ) = P at *
      generalize (2 : ℝ) ^ (1024 : ℤ) = B at *
      linarith
    · rw [ite_eq_right a1, ite_eq_right a2, ite_eq_left b1]
      have h3 := hi z (by omega)
      generalize (2 : ℝ) ^ (1000000 : ℤ) = P at *
      generalize (2 : ℝ) ^ (1024 : ℤ) = B at *
      linarith
  · have b2 : w ≠ -2 ^ 2098 := by omega
    rw [ite_eq_right b1, ite_eq_right b2]
    by_cases a2 : z = -2 ^ 2098
    · rw [ite_eq_right a1, ite_eq_left a2]
      have h3 := lo w (by omega)
      generalize (2 : ℝ) ^ (1000000 : ℤ) = P at *
      generalize (2 : ℝ) ^ (1024 : ℤ) = B at *
      linarith
    · rw [ite_eq_right a1, ite_eq_right a2]
      exact mono

theorem val_lt_sv (a b : BitVec 64) (ha : isNaNT (ty64 a) = false) (hb : isNaNT (ty64 b) = false) :
    lt_real (val64 a) (val64 b) =
      decide (Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) <
        Wasm.IEEE64.scaledValue (UInt64.ofBitVec b)) := by
  rw [val_extV a ha, val_extV b hb]
  simp only [lt_real, decide_eq_decide]
  exact extV_strictMonoOn.lt_iff_lt (sv_bound a ha) (sv_bound b hb)

theorem val_eq_sv (a b : BitVec 64) (ha : isNaNT (ty64 a) = false) (hb : isNaNT (ty64 b) = false) :
    eq_real (val64 a) (val64 b) =
      decide (Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) =
        Wasm.IEEE64.scaledValue (UInt64.ofBitVec b)) := by
  rw [val_extV a ha, val_extV b hb]
  simp only [eq_real, decide_eq_decide]
  exact extV_strictMonoOn.injOn.eq_iff (sv_bound a ha) (sv_bound b hb)

/-- The bits of FPSR that FPCompare sets at 64 bits under FPCR 0x02000000 with `signal_nans`
false: IOC for a signaling NaN operand. -/
def cmpMask (a b : BitVec 64) : BitVec 64 :=
  if ty64 a == .FPType_SNaN || ty64 b == .FPType_SNaN then 1#64 else 0#64

theorem snan_of_not_nan (t : FPType) (h : isNaNT t = false) : (t == .FPType_SNaN) = false := by
  cases t <;> first | rfl | exact absurd h (by decide)

set_option maxHeartbeats 40000 in
theorem fpCompare_run (a b : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPCompare a b false fpcrV).run s =
        .ok (BitVec.ofNat 4 (LeanExe.A64.Isla.fcmpNZCV (.ofBitVec a) (.ofBitVec b))) s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| cmpMask a b) ∧ Frame s s' := by
  subst hs
  simp only [FPCompare, fpUnpack_eq]
  sail_simp []
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  refine step hf1 (fpUnpack_run b h hr1) ?_
  intro σ2 hr2 hf2
  sail_simp [ty_nan_or]
  by_cases hn : (isNaNT (ty64 a) || isNaNT (ty64 b)) = true
  · rw [ite_eq_left hn]
    have hnan : (Wasm.IEEE64.isNaN (.ofBitVec a) || Wasm.IEEE64.isNaN (.ofBitVec b)) = true := by
      rw [t_isNaN, t_isNaN]; exact hn
    have hv : LeanExe.A64.Isla.fcmpNZCV (.ofBitVec a) (.ofBitVec b) = 3 := by
      simp only [LeanExe.A64.Isla.fcmpNZCV, Wasm.IEEE64.lt, Wasm.IEEE64.eq, hnan, ↓reduceIte]
      rfl
    rw [hv]
    by_cases hsn : (ty64 a == .FPType_SNaN || ty64 b == .FPType_SNaN) = true
    · rw [ite_eq_left hsn]
      sail_simp [FPProcessException, hr2, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr]
      refine ⟨_, rfl, ?_, ⟨hf2.mem, hf2.tags, hf2.cyc, hf2.out⟩⟩
      simp only [setReg_regs, bump_regs, faS_regs, hr2, cmpMask, hsn, ↓reduceIte,
        upd_or _ _ (by norm_num : 0 < 64), (or_masks _).2.2.1]
    · rw [ite_eq_right hsn]
      refine ⟨_, rfl, ?_, ⟨hf2.mem, hf2.tags, hf2.cyc, hf2.out⟩⟩
      have hm : cmpMask a b = 0#64 := by
        unfold cmpMask; rw [ite_eq_right hsn]
      rw [bump_regs, hr2, hm, BitVec.or_zero]
      exact (insert_self _ _ _ h.hfpsr).symm
  · rw [ite_eq_right hn]
    have ha : isNaNT (ty64 a) = false := by
      revert hn; cases isNaNT (ty64 a) <;> simp
    have hb : isNaNT (ty64 b) = false := by
      revert hn; cases isNaNT (ty64 b) <;> simp
    rw [val_eq_sv a b ha hb, val_lt_sv a b ha hb]
    sail_simp [FPProcessDenorms, hr2, h.hfi, h.hps, h.nrw, h.aa64]
    refine ⟨_, ok_congr ?_, ?_, ⟨hf2.mem, hf2.tags, hf2.cyc, hf2.out⟩⟩
    · simp only [LeanExe.A64.Isla.fcmpNZCV, Wasm.IEEE64.lt, Wasm.IEEE64.eq, t_isNaN, ha, hb,
        Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      generalize Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) = x
      generalize Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) = y
      by_cases e1 : x = y
      · subst e1; simp
      · have e3 : (x == y) = false := beq_eq_false_iff_ne.mpr e1
        by_cases e2 : x < y
        · simp [e1, e2, e3]
        · simp [e1, e2, e3]
    · have hm : cmpMask a b = 0#64 := by
        unfold cmpMask; rw [snan_of_not_nan _ ha, snan_of_not_nan _ hb]; rfl
      simp only [bump_regs, hr2, hm, BitVec.or_zero]
      exact (insert_self _ _ _ h.hfpsr).symm

/-- FPCompare at 64 bits under FPCR 0x02000000 with `signal_nans` false returns the flags
`fcmpNZCV` of `State.fcmp` for every pair of words from every state that satisfies the state
hypothesis.  FPSR becomes `fpsr ||| cmpMask a b`, and the other registers, the memory, the tags,
the cycle count, and the output do not change. -/
theorem fpCompare_eq_fcmpNZCV (a b : BitVec 64) (s : State) (fi : Vector Bool 259)
    (ps : ProcState) (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPCompare a b false fpcrV).run s =
        .ok (BitVec.ofNat 4
          (LeanExe.A64.Isla.fcmpNZCV (UInt64.ofBitVec a) (UInt64.ofBitVec b))) s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| cmpMask a b) ∧ Frame s s' :=
  fpCompare_run a b h rfl

end F7
