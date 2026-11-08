import F7.Round

/-!
FixedToFP of Sail's Lean translation of the Armv9.4-A model, at 64 bits from a 64-bit unsigned
integer with no fraction bits under FPCR 0x02000000, rounding to nearest with ties to even, returns
Talos's `f64ConvertI64U` of its operand for every word and sets in FPSR the bits of `cvtMask`, from
every state that satisfies `Hyp`.  These are the arguments with which the wrapper FixedToFP64 of
`tests/isla/armv9p4-checked-fp.diff` serves UCVTF D←X.  FixedToFP reads the operand as the natural
number `n` and rounds the real `n / 2^0`, which is `n · 2^1074` in units of 2^-1074 (`cvt_val`), so
`fpRound_run` gives Talos's `roundScaledMagnitude` of `n · 2^1074`, which is `fromInt n`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

theorem cvt_val (n : ℕ) :
    div_real (to_real (n : ℤ)) (real_power 2 0) = sop false (n * 2 ^ 1074) 1074 := by
  simp only [div_real, to_real, real_power, sop, zpow_zero, div_one, Bool.false_eq_true,
    ↓reduceIte, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ two_ne_zero]
  norm_num

theorem cvt_zero (n : ℕ) :
    eq_real (div_real (to_real (n : ℤ)) (real_power 2 0)) 0 = decide (n = 0) := by
  simp [eq_real, div_real, to_real, real_power]

/-- Talos's `fromInt` of a natural `n`: `roundScaledMagnitude` of `n · 2^1074`.  Lean's core
library, in which Talos is written, and Mathlib elaborate `2 ^ 1074 : ℕ` with different instances
of `Pow`; `congr 1` compares the two sides below `roundScaledMagnitude`, where the kernel checks
the instances without evaluating the word. -/
theorem fromInt_nat (n : ℕ) :
    Wasm.IEEE64.fromInt (n : ℤ) = Wasm.IEEE64.roundScaledMagnitude false (n * 2 ^ 1074) := by
  unfold Wasm.IEEE64.fromInt
  rw [Int.natAbs_natCast]
  congr 1

theorem cvt_talos (a : BitVec 64) :
    (Wasm.f64ConvertI64U (UInt64.ofBitVec a)).toBitVec = tRound false (a.toNat * 2 ^ 1074) := by
  rw [Wasm.f64ConvertI64U, Wasm.IEEE64.convertI64U, UInt64.toNat_ofBitVec, fromInt_nat, tRound]

theorem tRound_zero : tRound false 0 = 0#64 := by decide

/-- The bits of FPSR that FixedToFP sets for the unsigned operand `a`: IXC on an inexact result. -/
def cvtMask (a : BitVec 64) : BitVec 64 :=
  if a.toNat = 0 then 0#64 else roundMask (a.toNat * 2 ^ 1074)

theorem fixedToFP_run (a : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FixedToFP a 0 true fpcrV .FPRounding_TIEEVEN 64).run s =
        .ok (Wasm.f64ConvertI64U (.ofBitVec a)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| cvtMask a) ∧ Frame s s' := by
  subst hs
  rw [cvt_talos]
  simp only [FixedToFP, asl_Int, cvtMask]
  sail_simp [bne, frb_TIEEVEN_ODD, cvt_zero]
  by_cases hn : a.toNat = 0
  · simp only [hn, decide_true, ↓reduceIte, Nat.zero_mul, tRound_zero]
    sail_simp [FPZero]
    refine ⟨_, ok_congr ?_, ?_, ⟨rfl, rfl, rfl, rfl⟩⟩
    · decide
    · rw [BitVec.or_zero]
      exact (insert_self _ _ _ h.hfpsr).symm
  · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte, FPRound__1, cvt_val]
    obtain ⟨s', h1, h2, h3⟩ := fpRound_run false (a.toNat * 2 ^ 1074)
      (Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.two_pow_pos _)) h
      (s := bump (.bitvector 64) s) rfl
    exact ⟨s', h1, h2, ⟨h3.mem, h3.tags, h3.cyc, h3.out⟩⟩

/-- FixedToFP of a 64-bit word as an unsigned integer with no fraction bits, at 64 bits under FPCR
0x02000000 and rounding to nearest with ties to even, returns Talos's `f64ConvertI64U` for every
word from every state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| cvtMask a`, and
the other registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fixedToFP_eq_f64ConvertI64U (a : BitVec 64) (s : State) (fi : Vector Bool 259)
    (ps : ProcState) (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FixedToFP a 0 true fpcrV .FPRounding_TIEEVEN 64).run s =
        .ok (Wasm.f64ConvertI64U (UInt64.ofBitVec a)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| cvtMask a) ∧ Frame s s' :=
  fixedToFP_run a h rfl

end F7
