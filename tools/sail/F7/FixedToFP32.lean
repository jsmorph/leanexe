import F7.Round32
import F7.FixedToFP

/-!
FixedToFP of Sail's Lean translation of the Armv9.4-A model at 32 bits, with no fraction bits
under FPCR 0x02000000 and rounding to nearest with ties to even, returns Talos's conversion to
binary32 for every word and sets in FPSR the bits of `cvtMask32`, from every state that satisfies
`Hyp`: `f32ConvertI64U` for a 64-bit unsigned operand, the call of the wrapper FixedToFP64_32 of
`tests/isla/armv9p4-checked-fp.diff` that UCVTF S←X uses, and `f32ConvertI32S` for a 32-bit signed
operand, the call of FixedToFP32_32 that SCVTF S←W uses.  FixedToFP reads the operand as the
integer `z`, returns +0 for `z = 0`, and otherwise rounds the real `z / 2^0`, which is the rational
`±(|z| · 2^149) / 1` of `fpRound32_q` (`cvt_val32`, `cvt_int32`), so `fpRound32_q` and
`rsm_eq_rrm32` give Talos's `roundScaledMagnitude` of `|z| · 2^149`, which is `fromInt z`.  The
signed theorem holds for the translation in which `asl_Int`'s `result` has the type Int
(`fix-output.sh`); with lean-sail v6's coercion `CoeT Int x Nat`, SInt of a negative operand was
0.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

theorem cvt_val32 (n : ℕ) :
    div_real (to_real (n : ℤ)) (real_power 2 0) = qop false (n * 2 ^ 149) 1 149 := by
  have e : ((n * 2 ^ 149 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(149 : ℤ)) = (n : ℝ) := by
    rw [Nat.cast_one, div_one, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc,
      ← zpow_natCast (2 : ℝ) 149, ← zpow_add₀ two_ne_zero]
    norm_num
  simp only [div_real, to_real, real_power, zpow_zero, div_one, Int.cast_natCast]
  unfold qop
  rw [e]
  rfl

/-- Talos's `IEEE32.fromInt` of a natural `n`: `roundScaledMagnitude` of `n · 2^149`.  The two
sides elaborate `2 ^ 149 : ℕ` with different instances of `Pow`; `congr 1` compares them below
`roundScaledMagnitude`, as `fromInt_nat` of `F7/FixedToFP.lean` does. -/
theorem fromInt32_nat (n : ℕ) :
    Wasm.IEEE32.fromInt (n : ℤ) = Wasm.IEEE32.roundScaledMagnitude false (n * 2 ^ 149) := by
  unfold Wasm.IEEE32.fromInt
  rw [Int.natAbs_natCast]
  congr 1

theorem cvtU32_talos (a : BitVec 64) :
    (Wasm.f32ConvertI64U (UInt64.ofBitVec a)).toBitVec =
      (Wasm.IEEE32.roundScaledMagnitude false (a.toNat * 2 ^ 149)).toBitVec := by
  rw [Wasm.f32ConvertI64U, Wasm.IEEE32.convertI64U, UInt64.toNat_ofBitVec, fromInt32_nat]

/-- The bits of FPSR that FixedToFP sets at 32 bits for the unsigned operand `a`: IXC on an
inexact result. -/
def cvtMask32 (a : BitVec 64) : BitVec 64 :=
  if a.toNat = 0 then 0#64 else maskQ32 (a.toNat * 2 ^ 149) 1

theorem fixedToFP32_run (a : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FixedToFP a 0 true fpcrV .FPRounding_TIEEVEN 32).run s =
        .ok (Wasm.f32ConvertI64U (.ofBitVec a)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| cvtMask32 a) ∧ Frame s s' := by
  subst hs
  rw [cvtU32_talos]
  simp only [FixedToFP, asl_Int, cvtMask32]
  sail_simp [bne, frb_TIEEVEN_ODD, cvt_zero]
  by_cases hn : a.toNat = 0
  · simp only [hn, decide_true, ↓reduceIte, Nat.zero_mul]
    sail_simp [FPZero]
    refine ⟨_, ok_congr ?_, ?_, ⟨rfl, rfl, rfl, rfl⟩⟩
    · decide
    · rw [BitVec.or_zero]
      exact (insert_self _ _ _ h.hfpsr).symm
  · have hp : 0 < a.toNat * 2 ^ 149 := Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.two_pow_pos _)
    simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte, FPRound__1, cvt_val32]
    rw [rsm_eq_rrm32 _ _ hp]
    obtain ⟨s', h1, h2, h3⟩ := fpRound32_q false (a.toNat * 2 ^ 149) 1 hp Nat.one_pos h
      (s := bump (.bitvector 32) s) rfl
    exact ⟨s', h1, h2, ⟨h3.mem, h3.tags, h3.cyc, h3.out⟩⟩

/-- FixedToFP of a 64-bit word as an unsigned integer with no fraction bits, at 32 bits under FPCR
0x02000000 and rounding to nearest with ties to even, returns Talos's `f32ConvertI64U` for every
word from every state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| cvtMask32 a`,
and the other registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fixedToFP32_eq_f32ConvertI64U (a : BitVec 64) (s : State) (fi : Vector Bool 259)
    (ps : ProcState) (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FixedToFP a 0 true fpcrV .FPRounding_TIEEVEN 32).run s =
        .ok (Wasm.f32ConvertI64U (UInt64.ofBitVec a)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| cvtMask32 a) ∧ Frame s s' :=
  fixedToFP32_run a h rfl

/-- A nonzero integer `z` divided by 2^0 as the rational of `fpRound32_q`. -/
theorem cvt_int32 (z : ℤ) :
    div_real (to_real z) (real_power 2 0) = qop (decide (z < 0)) (z.natAbs * 2 ^ 149) 1 149 := by
  have e : ((z.natAbs * 2 ^ 149 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(149 : ℤ)) =
      ((z.natAbs : ℕ) : ℝ) := by
    rw [Nat.cast_one, div_one, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc,
      ← zpow_natCast (2 : ℝ) 149, ← zpow_add₀ two_ne_zero]
    norm_num
  simp only [div_real, to_real, real_power, zpow_zero, div_one]
  unfold qop
  rw [e]
  by_cases hneg : z < 0
  · simp only [hneg, decide_true, ite_true]
    rw [Nat.cast_natAbs, abs_of_neg (by exact_mod_cast hneg)]
    push_cast; ring
  · simp only [hneg, decide_false, Bool.false_eq_true, ite_false]
    rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast (not_lt.mp hneg))]

theorem cvt_zero32 (z : ℤ) :
    eq_real (div_real (to_real z) (real_power 2 0)) 0 = decide (z = 0) := by
  simp [eq_real, div_real, to_real, real_power]

/-- Talos's `IEEE32.fromInt z`: `roundScaledMagnitude` of `|z| · 2^149` with the sign of `z`. -/
theorem fromInt32 (z : ℤ) :
    Wasm.IEEE32.fromInt z =
      Wasm.IEEE32.roundScaledMagnitude (decide (z < 0)) (z.natAbs * 2 ^ 149) := by
  unfold Wasm.IEEE32.fromInt
  congr 1

/-- The value of a 32-bit word as a signed integer, as Talos and Sail compute it. -/
theorem sint32 (x : BitVec 32) : Wasm.IEEE32.signedI32Value (UInt32.ofBitVec x) = x.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [Wasm.IEEE32.signedI32Value, Wasm.IEEE32.sign, UInt32.toNat_ofBitVec,
    decide_eq_true_eq]
  have := x.isLt
  split_ifs <;> push_cast <;> omega

theorem cvtS32_talos (a : BitVec 32) :
    (Wasm.f32ConvertI32S (UInt32.ofBitVec a)).toBitVec =
      (Wasm.IEEE32.roundScaledMagnitude (decide (a.toInt < 0))
        (a.toInt.natAbs * 2 ^ 149)).toBitVec := by
  rw [Wasm.f32ConvertI32S, Wasm.IEEE32.convertI32S, sint32, fromInt32]

/-- The bits of FPSR that FixedToFP sets at 32 bits for the signed operand `a`: IXC on an inexact
result. -/
def cvtMask32S (a : BitVec 32) : BitVec 64 :=
  if a.toInt = 0 then 0#64 else maskQ32 (a.toInt.natAbs * 2 ^ 149) 1

theorem fixedToFP32S_run (a : BitVec 32) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FixedToFP a 0 false fpcrV .FPRounding_TIEEVEN 32).run s =
        .ok (Wasm.f32ConvertI32S (.ofBitVec a)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| cvtMask32S a) ∧ Frame s s' := by
  subst hs
  rw [cvtS32_talos]
  simp only [FixedToFP, asl_Int, cvtMask32S]
  sail_simp [bne, frb_TIEEVEN_ODD, cvt_zero32]
  generalize a.toInt = z
  by_cases hz : z = 0
  · simp only [hz, decide_true, ↓reduceIte]
    sail_simp [FPZero]
    refine ⟨_, ok_congr ?_, ?_, ⟨rfl, rfl, rfl, rfl⟩⟩
    · decide
    · rw [BitVec.or_zero]
      exact (insert_self _ _ _ h.hfpsr).symm
  · have hp : 0 < z.natAbs * 2 ^ 149 := Nat.mul_pos (Int.natAbs_pos.mpr hz) (Nat.two_pow_pos _)
    simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte, FPRound__1, cvt_int32]
    rw [rsm_eq_rrm32 _ _ hp]
    obtain ⟨s', h1, h2, h3⟩ := fpRound32_q (decide (z < 0)) _ 1 hp Nat.one_pos h
      (s := bump (.bitvector 32) s) rfl
    exact ⟨s', h1, h2, ⟨h3.mem, h3.tags, h3.cyc, h3.out⟩⟩

/-- FixedToFP of a 32-bit word as a signed integer with no fraction bits, at 32 bits under FPCR
0x02000000 and rounding to nearest with ties to even, returns Talos's `f32ConvertI32S` for every
word from every state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| cvtMask32S a`,
and the other registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fixedToFP32_eq_f32ConvertI32S (a : BitVec 32) (s : State) (fi : Vector Bool 259)
    (ps : ProcState) (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FixedToFP a 0 false fpcrV .FPRounding_TIEEVEN 32).run s =
        .ok (Wasm.f32ConvertI32S (UInt32.ofBitVec a)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| cvtMask32S a) ∧ Frame s s' :=
  fixedToFP32S_run a h rfl

end F7
