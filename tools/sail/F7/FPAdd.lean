import F7.Base

/-!
FPAdd of Sail's Lean translation of the Armv9.4-A model, at 64 bits under FPCR 0x02000000,
returns Talos's `f64Add` of its operands for every pair of words and sets in FPSR the bits of
`addMask`, from every state that satisfies `Hyp`.  The proof runs the translated code:
`fpUnpack_run`, `fpProcessNaNs_run`, and `fpRound_run` state what FPUnpack__1, FPProcessNaNs__1,
and FPRound__2 return, and `fpAdd_run` puts them together case by case.  `Frame` states that
memory, tags, cycle count, and output do not change.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

theorem exp_eq (N : ℕ) (hN : 0 < N) (e : ℤ)
    (h1 : 1 ≤ (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) * 2 ^ (-e))
    (h2 : (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) * 2 ^ (-e) < 2) :
    e = (Nat.log2 N : ℤ) - 1074 := by
  have hL1 : 2 ^ Nat.log2 N ≤ N := Nat.log2_self_le (by omega)
  have hL2 : N < 2 ^ (Nat.log2 N + 1) := Nat.lt_log2_self
  have hr1 : ((2 : ℝ) ^ (Nat.log2 N : ℤ)) ≤ N := by
    rw [zpow_natCast]; exact_mod_cast hL1
  have hr2 : (N : ℝ) < (2 : ℝ) ^ ((Nat.log2 N : ℤ) + 1) := by
    rw [show ((Nat.log2 N : ℤ) + 1) = ((Nat.log2 N + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact_mod_cast hL2
  have ht : (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) * 2 ^ (-e) = N * 2 ^ (-1074 - e) := by
    rw [mul_assoc, ← zpow_add₀ two_ne_zero]; ring_nf
  rw [ht] at h1 h2
  have hpos : (0 : ℝ) < 2 ^ (-1074 - e) := zpow_pos (by norm_num) _
  have a1 : (2 : ℝ) ^ (0 : ℤ) < 2 ^ ((Nat.log2 N : ℤ) + 1 + (-1074 - e)) := by
    rw [zpow_add₀ two_ne_zero, zpow_zero]
    calc (1 : ℝ) ≤ N * 2 ^ (-1074 - e) := h1
      _ < 2 ^ ((Nat.log2 N : ℤ) + 1) * 2 ^ (-1074 - e) := by
        exact mul_lt_mul_of_pos_right hr2 hpos
  have a2 : (2 : ℝ) ^ ((Nat.log2 N : ℤ) + (-1074 - e)) < 2 ^ (1 : ℤ) := by
    rw [zpow_add₀ two_ne_zero, zpow_one]
    calc (2 : ℝ) ^ (Nat.log2 N : ℤ) * 2 ^ (-1074 - e) ≤ N * 2 ^ (-1074 - e) :=
          mul_le_mul_of_nonneg_right hr1 hpos.le
      _ < 2 := h2
  rw [zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)] at a1 a2
  omega

theorem join1_beq (b : BitVec 1) : (BitVec.join1 [b] == 1#1) = (b == 1#1) := by
  have hb : b = 0#1 ∨ b = 1#1 := by
    have h2 := b.isLt
    rcases (show b.toNat = 0 ∨ b.toNat = 1 by omega) with h0 | h0
    · left; exact BitVec.eq_of_toNat_eq (by simpa using h0)
    · right; exact BitVec.eq_of_toNat_eq (by simpa using h0)
  rcases hb with rfl | rfl <;> decide

theorem int_access (m : ℕ) : (integer_access (m : ℤ) 0 == 1#1) = decide (m % 2 = 1) := by
  simp [integer_access, integer_subrange, get_slice_int, BitVec.access]
  have h0 : (BitVec.ofNat 2 m)[0] = decide (m % 2 = 1) := by
    rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_eq_decide_div_mod_eq]
    apply decide_eq_decide.mpr
    simp only [pow_zero, Nat.div_one]
    omega
  rw [h0]
  by_cases hm : m % 2 = 1 <;> simp [*]

theorem man_normal (N : ℕ) (e : ℤ) (hE : e = (Nat.log2 N : ℤ) - 1074) (hL : 52 ≤ Nat.log2 N) :
    mult_real ((N : ℝ) * 2 ^ (-1074 : ℤ) * 2 ^ (-e)) (real_power 2 52) =
      (N : ℝ) / ((2 ^ (Nat.log2 N - 52) : ℕ) : ℝ) := by
  simp only [mult_real, real_power]
  rw [mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero, div_eq_mul_inv]
  congr 1
  push_cast
  rw [← zpow_natCast, ← zpow_neg]
  congr 1
  omega

theorem man_sub (N : ℕ) (e : ℤ) (hE : e = (Nat.log2 N : ℤ) - 1074) :
    mult_real (div_real ((N : ℝ) * 2 ^ (-1074 : ℤ) * 2 ^ (-e)) (real_power 2 (-1022 - e)))
      (real_power 2 52) = (N : ℝ) := by
  simp only [mult_real, div_real, real_power]
  rw [div_eq_mul_inv, ← zpow_neg, mul_assoc, mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero,
    ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
  rw [show (-1074 : ℤ) + (-e + (-(-1022 - e) + 52)) = 0 by omega, zpow_zero, mul_one]

theorem floor_div_nat (N d : ℕ) : round_down ((N : ℝ) / (d : ℝ)) = ((N / d : ℕ) : ℤ) := by
  simp only [round_down]
  rw [Int.floor_div_natCast, Int.floor_natCast]
  push_cast; rfl

theorem floor_nat (N : ℕ) : round_down (N : ℝ) = (N : ℤ) := by
  simp [round_down]

theorem err_div (N d : ℕ) (hd : 0 < d) :
    sub_real ((N : ℝ) / (d : ℝ)) (to_real ((N / d : ℕ) : ℤ)) = ((N % d : ℕ) : ℝ) / (d : ℝ) := by
  simp only [sub_real, to_real]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hN : (N : ℝ) = d * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N d).symm
  rw [eq_div_iff hd', sub_mul, div_mul_cancel₀ _ hd', Int.cast_natCast]
  rw [hN]
  ring

theorem gt_half (r d : ℕ) (hd : 0 < d) :
    gt_real ((r : ℝ) / (d : ℝ)) (1 / 2) = decide (d < 2 * r) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [gt_real, gt_iff_lt, decide_eq_decide]
  rw [lt_div_iff₀ hd']
  constructor
  · intro h; have : (d : ℝ) < 2 * r := by linarith
    exact_mod_cast this
  · intro h; have : (d : ℝ) < 2 * r := by exact_mod_cast h
    linarith

theorem eq_half (r d : ℕ) (hd : 0 < d) :
    eq_real ((r : ℝ) / (d : ℝ)) (1 / 2) = decide (2 * r = d) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [eq_real, decide_eq_decide]
  rw [div_eq_iff hd']
  constructor
  · intro h; have : (2 * r : ℝ) = d := by linarith
    exact_mod_cast this
  · intro h; have : (2 * r : ℝ) = d := by exact_mod_cast h
    linarith

theorem beq_zero_div (r d : ℕ) (hd : 0 < d) : (((r : ℝ) / (d : ℝ)) == 0) = decide (r = 0) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [beq_eq_decide]
  simp [hd']

theorem sub_self_nat (N : ℕ) : sub_real (N : ℝ) (to_real (N : ℤ)) = 0 := by
  simp [sub_real, to_real]

theorem subrange_toNat (x hi : ℤ) (hx : 0 ≤ x) (hh : 0 ≤ hi) :
    (integer_subrange x hi 0).toNat = x.toNat % 2 ^ ((hi - 0 + 1).toNat) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hh
  simp only [integer_subrange, get_slice_int]
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt]
  exact Nat.mod_mod_of_dvd m (Nat.pow_dvd_pow 2 (by omega))

set_option maxRecDepth 10000 in
theorem bits_eq (sb : BitVec 1) (be im hi1 hi2 : ℤ) (w0 : ℕ) (h1 : hi1 = 10) (h2 : hi2 = 51)
    (h0 : w0 = 0) (hbe : 0 ≤ be) (hbe' : be < 2047) (him : 2 ^ 52 ≤ im) (him' : im < 2 ^ 53) :
    BitVec.setWidth 64 (sb +++ integer_subrange be hi1 0 +++ integer_subrange im hi2 0 +++
      (Zeros (n := w0))) =
      BitVec.ofNat 64 (sb.toNat * 2 ^ 63 + be.toNat * 2 ^ 52 + (im.toNat - 2 ^ 52)) := by
  subst h1 h2 h0
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append, subrange_toNat be 10 hbe (by norm_num),
    subrange_toNat im 51 (by omega) (by norm_num), Zeros, BitVec.zero, BitVec.toNat_ofNat]
  have e11 : ((10 : ℤ) - 0 + 1).toNat = 11 := rfl
  have e52 : ((51 : ℤ) - 0 + 1).toNat = 52 := rfl
  have f11 : Int.toNat 10 - Int.toNat 0 + 1 = 11 := rfl
  have f52 : Int.toNat 51 - Int.toNat 0 + 1 = 52 := rfl
  rw [e11, e52, f11, f52]
  have hb1 : be.toNat < 2 ^ 11 := by omega
  have hi1 : 2 ^ 52 ≤ im.toNat := by omega
  have hi2 : im.toNat < 2 ^ 53 := by omega
  have hs : sb.toNat < 2 := sb.isLt
  have hm : im.toNat % 2 ^ 52 = im.toNat - 2 ^ 52 := by omega
  rw [Nat.mod_eq_of_lt hb1, hm]
  have o1 : sb.toNat <<< 11 ||| be.toNat = sb.toNat * 2 ^ 11 + be.toNat := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hb1, Nat.shiftLeft_eq]
  have o2 : (sb.toNat * 2 ^ 11 + be.toNat) <<< 52 ||| (im.toNat - 2 ^ 52) =
      (sb.toNat * 2 ^ 11 + be.toNat) * 2 ^ 52 + (im.toNat - 2 ^ 52) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  have z : ∀ x : BitVec 0, x.toNat = 0 := fun x => by have := x.isLt; simp at this; omega
  have o3 : (sb.toNat * 2 ^ 11 + be.toNat) * 2 ^ 52 = sb.toNat * 2 ^ 63 + be.toNat * 2 ^ 52 := by
    rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add]
  rw [o1, o2, Nat.shiftLeft_zero, z, Nat.or_zero, o3]

theorem one_beq_zero : ((1 : ℝ) == 0) = false := by simp

theorem ipow (x y : ℤ) : @HPow.hPow ℤ ℤ ℤ instHPowInt_sail x y = x ^ y.toNat := rfl

theorem fdiv_two (a : ℤ) (h : 0 ≤ a) : fdiv_int a 2 = a / 2 := by
  have h1 : (decide (a < 0) && decide ((2 : ℤ) > 0)) = false := by simp; omega
  have h2 : (decide (a > 0) && decide ((2 : ℤ) < 0)) = false := by simp
  simp only [fdiv_int, h1, h2, Bool.false_eq_true, ↓reduceIte]
  exact Int.tdiv_eq_ediv_of_nonneg h

/-- Talos's result of rounding the magnitude `N`, in units of 2^-1074, with the sign `neg`. -/
def tRound (neg : Bool) (N : ℕ) : BitVec 64 := (Wasm.IEEE64.roundScaledMagnitude neg N).toBitVec

theorem toBV_encode (neg : Bool) (e f : ℕ) :
    (Wasm.IEEE64.encodeFinite neg e f).toBitVec =
      BitVec.ofNat 64 ((if neg then 2 ^ 63 else 0) + e * 2 ^ 52 + f) := rfl

theorem toBV_inf (neg : Bool) :
    (Wasm.IEEE64.infinity neg).toBitVec =
      (if neg then 0xFFF0000000000000#64 else 0x7FF0000000000000#64) := by
  cases neg <;> rfl

theorem enc_congr {neg : Bool} {a a' b b' : ℕ} (h1 : a = a') (h2 : b = b') :
    (Wasm.IEEE64.encodeFinite neg a b).toBitVec = (Wasm.IEEE64.encodeFinite neg a' b').toBitVec := by
  subst h1 h2; rfl

set_option maxHeartbeats 1000000 in
theorem tRound_normal (neg : Bool) (N k q r : ℕ) (hk : Nat.log2 N = k + 52) (hq : N / 2 ^ k = q)
    (hr : N % 2 ^ k = r) (hq1 : 2 ^ 52 ≤ q) (hq2 : q < 2 ^ 53) (hrk : r < 2 ^ k)
    (hL1 : 2 ^ (k + 52) ≤ N) :
    tRound neg N =
      (if (2 ^ k < 2 * r ∨ 2 * r = 2 ^ k ∧ q % 2 = 1) then
        (if q + 1 = 2 ^ 53 then
          (if 2047 ≤ k + 2 then (Wasm.IEEE64.infinity neg).toBitVec
           else (Wasm.IEEE64.encodeFinite neg (k + 2) 0).toBitVec)
         else (if 2047 ≤ k + 1 then (Wasm.IEEE64.infinity neg).toBitVec
           else (Wasm.IEEE64.encodeFinite neg (k + 1) (q + 1 - 2 ^ 52)).toBitVec))
       else (if 2047 ≤ k + 1 then (Wasm.IEEE64.infinity neg).toBitVec
         else (Wasm.IEEE64.encodeFinite neg (k + 1) (q - 2 ^ 52)).toBitVec)) := by
  have hk2 : 2 ^ k * q + r = N := by rw [← hq, ← hr]; exact Nat.div_add_mod N (2 ^ k)
  unfold tRound Wasm.IEEE64.roundScaledMagnitude
  by_cases hN53 : N < 2 ^ 53
  · have hk0 : k = 0 := by
      by_contra hne
      have : 2 ^ 53 ≤ 2 ^ (k + 52) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hk0
    simp only [pow_zero, Nat.mod_one, Nat.div_one] at hq hr
    subst hq hr
    have h52 : ¬ N < 2 ^ 52 := by
      have : 2 ^ 52 ≤ N := by simpa using hL1
      omega
    simp only [h52, hN53, if_false, if_true]
    have hup : ¬ (2 ^ 0 < 2 * 0 ∨ 2 * 0 = 2 ^ 0 ∧ N % 2 = 1) := by omega
    rw [if_neg hup, if_neg (by omega)]
  · have h52 : ¬ N < 2 ^ 52 := by omega
    have hk1 : 1 ≤ k := by
      by_contra h0
      have : k = 0 := by omega
      subst this
      have := Nat.lt_log2_self (n := N)
      rw [hk] at this
      omega
    simp only [h52, hN53, if_false, hk, Nat.add_sub_cancel, Wasm.IEEE32.roundShift, hq, hr]
    have hhalf : 2 ^ k / 2 = 2 ^ (k - 1) := by
      rw [show k = k - 1 + 1 by omega, pow_succ]; simp
    have hpk : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hhalf]
    by_cases hup : (2 ^ k < 2 * r ∨ 2 * r = 2 ^ k ∧ q % 2 = 1)
    · simp only [hup, if_true]
      have hround : (if r < 2 ^ (k - 1) then q else if 2 ^ (k - 1) < r then q + 1
          else if q % 2 == 0 then q else q + 1) = q + 1 := by
        rcases hup with h | ⟨h, ho⟩
        · rw [if_neg (by omega), if_pos (by omega)]
        · rw [if_neg (by omega), if_neg (by omega)]
          simp [ho]
      rw [hround]
      by_cases hc : q + 1 = 2 ^ 53
      · simp only [hc, if_true, beq_self_eq_true]
        split_ifs <;> first | omega | (exact enc_congr (by omega) (by omega)) | rfl
      · have hc' : (q + 1 == 2 ^ 53) = false := by simpa using hc
        simp only [hc, hc', if_false, Bool.false_eq_true]
        split_ifs <;> first | omega | (exact enc_congr (by omega) (by omega)) | rfl
    · simp only [hup, if_false]
      have hround : (if r < 2 ^ (k - 1) then q else if 2 ^ (k - 1) < r then q + 1
          else if q % 2 == 0 then q else q + 1) = q := by
        simp only [not_or, not_and, not_lt] at hup
        by_cases h1 : r < 2 ^ (k - 1)
        · rw [if_pos h1]
        · rw [if_neg h1, if_neg (by omega)]
          have : q % 2 = 0 := by omega
          simp [this]
      rw [hround]
      have hc' : (q == 2 ^ 53) = false := by simp; omega
      simp only [hc', if_false, Bool.false_eq_true]
      split_ifs <;> first | omega | (exact enc_congr (by omega) (by omega)) | rfl

theorem insert_insert (R : Std.ExtDHashMap Register RegisterType) (r : Register)
    (v w : RegisterType r) : (R.insert r v).insert r w = R.insert r w := by
  apply Std.ExtDHashMap.ext_get?
  intro k
  simp only [Std.ExtDHashMap.get?_insert]
  split <;> rfl

theorem insert_self (R : Std.ExtDHashMap Register RegisterType) (r : Register) (v : RegisterType r)
    (h : R.get? r = some v) : R.insert r v = R := by
  apply Std.ExtDHashMap.ext_get?
  intro k
  simp only [Std.ExtDHashMap.get?_insert]
  split
  · rename_i hk
    have := eq_of_beq hk
    subst this
    simp [h]
  · rfl

theorem upd_or (v : BitVec 64) (k : ℕ) (hk : k < 64) :
    Sail.BitVec.update v k (Bit 1#1) = v ||| (1#64 <<< k) := by
  ext i hi
  simp [Sail.BitVec.update, Sail.BitVec.updateSubrange', Bit, BitVec.access]
  by_cases h1 : i < k <;> by_cases h2 : i - k = 0 <;> simp [h1, h2]

/-- The bits of FPSR that FPRoundBase__1 sets for the nonzero magnitude `N`, in units of
2^-1074, at 64 bits under FPCR 0x02000000: OFC and IXC on overflow, IXC on an inexact result. -/
def roundMask (N : ℕ) : BitVec 64 :=
  let k := Nat.log2 N - 52
  let q := N / 2 ^ k
  let r := N % 2 ^ k
  let be := if (2 ^ k < 2 * r ∨ 2 * r = 2 ^ k ∧ q % 2 = 1) ∧ q + 1 = 2 ^ 53 then k + 2 else k + 1
  if 2047 ≤ be then 0x14#64 else if r = 0 then 0#64 else 0x10#64

theorem or_masks (v : BitVec 64) :
    (v ||| 1#64 <<< 2) ||| 1#64 <<< 4 = v ||| 0x14#64 ∧ v ||| 1#64 <<< 4 = v ||| 0x10#64 ∧
      v ||| 1#64 <<< 0 = v ||| 1#64 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BitVec.or_assoc]; congr 1
  · congr 1
  · congr 1

/-- The real number `±N · 2^-1074`. -/
noncomputable def sop (neg : Bool) (N : ℕ) : ℝ :=
  if neg then -((N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) else (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)

theorem sop_facts (neg : Bool) (N : ℕ) (hN : 0 < N) :
    lt_real (sop neg N) 0 = neg ∧ (sop neg N == 0) = false ∧
      neg_real (-((N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ))) = (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) := by
  have hM : (0 : ℝ) < (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) :=
    mul_pos (by exact_mod_cast hN) (zpow_pos (by norm_num) _)
  refine ⟨?_, ?_, by simp [neg_real]⟩
  · cases neg <;> simp [sop, lt_real, hM, hM.le, hN]
  · cases neg <;> simp [sop, hM.ne', Nat.pos_iff_ne_zero.mp hN]

set_option maxHeartbeats 0 in
theorem round_normal (neg : Bool) (N : ℕ) (hN : 0 < N) (hL : 52 ≤ Nat.log2 N)
    {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (sop neg N) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (tRound neg N) s' ∧ s'.regs = R.insert .FPSR (fpsr ||| roundMask N) ∧ Frame s s' := by
  subst hs
  have hM : (0 : ℝ) < (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) :=
    mul_pos (by exact_mod_cast hN) (zpow_pos (by norm_num) _)
  obtain ⟨e, he, h1, h2⟩ := loops_eq' _ hM
  have hE := exp_eq N hN e h1 h2
  obtain ⟨hlt, hne, hneg⟩ := sop_facts neg N hN
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, sop] at hlt hne ⊢
  all_goals (
    have hb : max (e - -1022 + 1) 0 = (Nat.log2 N : ℤ) - 51 := by omega
    have hb0 : ((Nat.log2 N : ℤ) - 51 == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    have hd : 0 < 2 ^ (Nat.log2 N - 52) := Nat.two_pow_pos _
    sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self,
      whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt, hneg]
    rw [he]
    sail_simp [↓join1_beq, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self, hne, bne, hlt, hb,
      hb0, man_normal N e hE hL, floor_div_nat, err_div _ _ hd, gt_half _ _ hd, eq_half _ _ hd,
      beq_zero_div _ _ hd, int_access]
    have hL1 : 2 ^ Nat.log2 N ≤ N := Nat.log2_self_le (by omega)
    have hL2 : N < 2 ^ (Nat.log2 N + 1) := Nat.lt_log2_self
    obtain ⟨k, hk⟩ : ∃ k, Nat.log2 N = k + 52 := ⟨Nat.log2 N - 52, by omega⟩
    have hmask : roundMask N = (let q := N / 2 ^ k; let r := N % 2 ^ k
        let be := if (2 ^ k < 2 * r ∨ 2 * r = 2 ^ k ∧ q % 2 = 1) ∧ q + 1 = 2 ^ 53 then k + 2
          else k + 1
        if 2047 ≤ be then 0x14#64 else if r = 0 then 0#64 else 0x10#64) := by
      simp only [roundMask, hk, Nat.add_sub_cancel]
    rw [hk] at hL1 hL2 hd ⊢
    rw [hmask]
    simp only [Nat.add_sub_cancel] at hd ⊢
    have hq1 : 2 ^ 52 ≤ N / 2 ^ k := by
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos k)]; rw [pow_add] at hL1; linarith
    have hq2 : N / 2 ^ k < 2 ^ 53 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
      rw [show k + 52 + 1 = 53 + k by omega, pow_add] at hL2; linarith
    have hr : N % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    rw [tRound_normal _ N k (N / 2 ^ k) (N % 2 ^ k) hk rfl rfl hq1 hq2 hr hL1]
    generalize hq : N / 2 ^ k = q at *
    generalize hrr : N % 2 ^ k = r at *
    clear he h1 h2 hlt hne hb hb0 hmask hE
    simp only [ipow, Int.reduceToNat, Int.reducePow, Int.reduceSub, Int.reduceAdd, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ge_iff_le]
    have hfd : fdiv_int ((q : ℤ) + 1) 2 = ((q : ℤ) + 1) / 2 := fdiv_two _ (by omega)
    have c2 : ((q : ℤ) + 1 = 4503599627370496) = False := by simp; omega
    have o1 : (2047 ≤ (↑(k + 52) : ℤ) - 51 + 1) = (2047 ≤ k + 2) := by
      apply propext; constructor <;> intro <;> omega
    have o2 : (2047 ≤ (↑(k + 52) : ℤ) - 51) = (2047 ≤ k + 1) := by
      apply propext; constructor <;> intro <;> omega
    simp only [c2, o1, o2, ↓reduceIte]
    by_cases hup : (2 ^ k < 2 * r ∨ 2 * r = 2 ^ k ∧ q % 2 = 1) <;>
    by_cases hc : q + 1 = 2 ^ 53 <;> by_cases hv1 : 2047 ≤ k + 1 <;> by_cases hv2 : 2047 ≤ k + 2 <;>
    by_cases hr0 : r = 0
    all_goals first | (exfalso; omega) | skip
    all_goals (
      have hcI : ((q : ℤ) + 1 = 9007199254740992) = (q + 1 = 2 ^ 53) := by
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
          h.hfpsr, ite_self, toBV_inf, toBV_encode, one_beq_zero, beq_zero_div _ _ hd, cast_eq, e5]
        refine ok_congr ?_
        first
        | decide
        | (rw [bits_eq]
           · apply congrArg (BitVec.ofNat 64)
             simp only [BitVec.toNat_ofNat, Nat.zero_mod, zero_mul, zero_add, hfd, Nat.reducePow]
             omega
           all_goals first | decide | omega | (simp only [hfd, Int.reducePow]; omega))
      · simp only [setReg_regs, bump_regs, faS_regs, insert_insert, upd_or _ _ (by norm_num : 2 < 64),
          upd_or _ _ (by norm_num : 4 < 64), (or_masks _).1, (or_masks _).2.1, BitVec.or_zero,
          cast_eq] <;> first | rfl | exact (insert_self _ _ _ h.hfpsr).symm
      · exact ⟨rfl, rfl, rfl, rfl⟩))

set_option maxRecDepth 10000 in
theorem bits_sub (sb : BitVec 1) (be im hi1 hi2 : ℤ) (w0 : ℕ) (h1 : hi1 = 10) (h2 : hi2 = 51)
    (h0 : w0 = 0) (hbe : be = 0) (him : 0 ≤ im) (him' : im < 4503599627370496) :
    BitVec.setWidth 64 (sb +++ integer_subrange be hi1 0 +++ integer_subrange im hi2 0 +++
      (Zeros (n := w0))) = BitVec.ofNat 64 (sb.toNat * 2 ^ 63 + im.toNat) := by
  subst h1 h2 h0 hbe
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append, subrange_toNat 0 10 le_rfl (by norm_num),
    subrange_toNat im 51 him (by norm_num), Zeros, BitVec.zero, BitVec.toNat_ofNat]
  have e11 : ((10 : ℤ) - 0 + 1).toNat = 11 := rfl
  have e52 : ((51 : ℤ) - 0 + 1).toNat = 52 := rfl
  have f11 : Int.toNat 10 - Int.toNat 0 + 1 = 11 := rfl
  have f52 : Int.toNat 51 - Int.toNat 0 + 1 = 52 := rfl
  rw [e11, e52, f11, f52]
  have hi2 : im.toNat < 2 ^ 52 := by omega
  have hs : sb.toNat < 2 := sb.isLt
  have z : ∀ x : BitVec 0, x.toNat = 0 := fun x => by have := x.isLt; simp at this; omega
  rw [Nat.mod_eq_of_lt hi2]
  have o0 : Int.toNat 0 % 2 ^ 11 = 0 := rfl
  have o1 : sb.toNat <<< 11 ||| 0 = sb.toNat * 2 ^ 11 := by rw [Nat.or_zero, Nat.shiftLeft_eq]
  have o2 : (sb.toNat * 2 ^ 11) <<< 52 ||| im.toNat = sb.toNat * 2 ^ 11 * 2 ^ 52 + im.toNat := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hi2, Nat.shiftLeft_eq]
  rw [o0, o1, o2, Nat.shiftLeft_zero, z, Nat.or_zero, Nat.mul_assoc, ← Nat.pow_add]

theorem roundMask_small (N : ℕ) (hN : N < 2 ^ 53) : roundMask N = 0#64 := by
  have hl : Nat.log2 N < 53 := by
    rcases Nat.eq_zero_or_pos N with h0 | hp
    · subst h0; decide
    · exact (Nat.log2_lt hp.ne').mpr hN
  have hk : Nat.log2 N - 52 = 0 := by omega
  simp [roundMask, hk, Nat.mod_one]

theorem tRound_sub (neg : Bool) (N : ℕ) (hN : N < 2 ^ 52) :
    tRound neg N = (Wasm.IEEE64.encodeFinite neg 0 N).toBitVec := by
  simp [tRound, Wasm.IEEE64.roundScaledMagnitude, show N < 4503599627370496 from hN]

theorem gt_zero_half : gt_real 0 (1 / 2) = false := by simp [gt_real]
theorem eq_zero_half : eq_real 0 (1 / 2) = false := by simp [eq_real]
theorem zero_beq_zero : ((0 : ℝ) == 0) = true := by simp

set_option maxHeartbeats 0 in
theorem round_sub (neg : Bool) (N : ℕ) (hN : 0 < N) (hL : Nat.log2 N ≤ 51)
    {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (sop neg N) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (tRound neg N) s' ∧ s'.regs = R.insert .FPSR (fpsr ||| roundMask N) ∧ Frame s s' := by
  subst hs
  have hM : (0 : ℝ) < (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) :=
    mul_pos (by exact_mod_cast hN) (zpow_pos (by norm_num) _)
  obtain ⟨e, he, h1, h2⟩ := loops_eq' _ hM
  have hE := exp_eq N hN e h1 h2
  obtain ⟨hlt, hne, hneg⟩ := sop_facts neg N hN
  have hN52 : N < 2 ^ 52 := by
    have := Nat.lt_log2_self (n := N)
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [roundMask_small N (by omega), BitVec.or_zero, insert_self _ _ _ h.hfpsr, tRound_sub _ _ hN52]
  have hb : max (e - -1022 + 1) 0 = 0 := by omega
  have hNi : ((N : ℤ)) < 4503599627370496 := by omega
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, sop] at hlt hne ⊢
  all_goals (
    apply exists_of_run
    · sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr,
        ite_self, whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt, hneg]
      rw [he]
      sail_simp [↓join1_beq, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self, hne, bne, hlt,
        hb, man_sub N e hE, floor_nat, sub_self_nat, gt_zero_half, eq_zero_half, zero_beq_zero,
        FPZero, toBV_encode, ipow]
      refine ok_congr ?_
      rw [bits_sub]
      all_goals first | decide | omega | (apply congrArg (BitVec.ofNat 64); simp)
    · rfl
    · exact ⟨rfl, rfl, rfl, rfl⟩)

theorem fpRound_run (neg : Bool) (N : ℕ) (hN : 0 < N) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (sop neg N) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (tRound neg N) s' ∧ s'.regs = R.insert .FPSR (fpsr ||| roundMask N) ∧ Frame s s' := by
  by_cases hL : 52 ≤ Nat.log2 N
  · exact round_normal neg N hN hL h hs
  · exact round_sub neg N hN (by omega) h hs

theorem step {α β} {x : SailM α} {f : α → SailM β} {s0 σ : State} {a : α} {v : β}
    {R R' : Std.ExtDHashMap Register RegisterType} (hσ : Frame s0 σ)
    (hx : ∃ σ1, x.run σ = .ok a σ1 ∧ σ1.regs = R ∧ Frame σ σ1)
    (k : ∀ σ1, σ1.regs = R → Frame s0 σ1 →
      ∃ s', (f a).run σ1 = .ok v s' ∧ s'.regs = R' ∧ Frame s0 s') :
    ∃ s', (x >>= f).run σ = .ok v s' ∧ s'.regs = R' ∧ Frame s0 s' := by
  obtain ⟨σ1, h1, h2, h3⟩ := hx
  rw [bind_run h1]
  exact k σ1 h2 (hσ.trans h3)

theorem t_isNaN (x : BitVec 64) : Wasm.IEEE64.isNaN (UInt64.ofBitVec x) = isNaNT (ty64 x) := by
  simp only [Wasm.IEEE64.isNaN, t_exp, t_frac]
  unfold ty64
  by_cases h0 : ex x = 0
  · simp only [h0, if_true]
    split <;> rfl
  · by_cases h2 : ex x = 2047
    · by_cases h1 : fr x = 0
      · simp only [h0, h2, h1, if_true, if_false]; rfl
      · by_cases h3 : 2 ^ 51 ≤ fr x
        · have h1' : (fr x != 0) = true := by simpa using h1
          have h1'' : (fr x == 0) = false := by simpa using h1
          rw [if_neg h0, if_pos h2, if_neg h1, if_pos h3, h2]; simp only [h1', h1'']; rfl
        · have h1' : (fr x != 0) = true := by simpa using h1
          have h1'' : (fr x == 0) = false := by simpa using h1
          rw [if_neg h0, if_pos h2, if_neg h1, if_neg h3, h2]; simp only [h1', h1'']; rfl
    · have : (ex x == 0x7FF) = false := by simpa using h2
      simp only [h0, h2, this, if_false, Bool.false_and]; rfl

theorem t_isInf (x : BitVec 64) :
    Wasm.IEEE64.isInfinite (UInt64.ofBitVec x) = (ty64 x == .FPType_Infinity) := by
  simp only [Wasm.IEEE64.isInfinite, t_exp, t_frac]
  unfold ty64
  by_cases h0 : ex x = 0
  · simp only [h0, if_true]
    split <;> rfl
  · by_cases h2 : ex x = 2047
    · by_cases h1 : fr x = 0
      · simp only [h0, h2, h1, if_true, if_false]; rfl
      · by_cases h3 : 2 ^ 51 ≤ fr x
        · have h1' : (fr x != 0) = true := by simpa using h1
          have h1'' : (fr x == 0) = false := by simpa using h1
          rw [if_neg h0, if_pos h2, if_neg h1, if_pos h3, h2]; simp only [h1', h1'']; rfl
        · have h1' : (fr x != 0) = true := by simpa using h1
          have h1'' : (fr x == 0) = false := by simpa using h1
          rw [if_neg h0, if_pos h2, if_neg h1, if_neg h3, h2]; simp only [h1', h1'']; rfl
    · have : (ex x == 0x7FF) = false := by simpa using h2
      simp only [h0, h2, this, if_false, Bool.false_and]; rfl

theorem ty_inf (x : BitVec 64) (h : ty64 x = .FPType_Infinity) : ex x = 2047 ∧ fr x = 0 := by
  unfold ty64 at h
  split_ifs at h with h0 h1 h2 h3 <;> first | exact ⟨‹_›, ‹_›⟩ | cases h

theorem ty_fin (x : BitVec 64) (h1 : ty64 x ≠ .FPType_Infinity) (h2 : isNaNT (ty64 x) = false) :
    ex x ≠ 2047 := by
  intro he
  unfold ty64 at h1 h2
  have : ex x ≠ 0 := by omega
  simp only [this, he, if_false, if_true] at h1 h2
  split_ifs at h1 h2 <;> first | contradiction | exact h1 rfl | (exfalso; omega) | exact absurd h2 (by decide)

theorem ty_zero (x : BitVec 64) (hfin : ex x ≠ 2047) :
    Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) = 0 ↔ ty64 x = .FPType_Zero := by
  simp only [Wasm.IEEE64.scaledMagnitude, t_exp, t_frac]
  unfold ty64
  by_cases h0 : ex x = 0
  · simp only [h0, beq_self_eq_true, if_true]
    by_cases h1 : fr x = 0 <;> simp [h1]
  · have : (ex x == 0) = false := by simpa using h0
    simp only [this, if_false, Bool.false_eq_true, h0, hfin]
    constructor
    · intro hm; have := Nat.mul_eq_zero.mp hm; simp at this
    · intro hc; cases hc

theorem inf_word (x : BitVec 64) (h : ty64 x = .FPType_Infinity) :
    x = if sg x then 0xFFF0000000000000#64 else 0x7FF0000000000000#64 := by
  obtain ⟨he, hf⟩ := ty_inf x h
  have hx := x.isLt
  unfold ex at he
  unfold fr at hf
  apply BitVec.eq_of_toNat_eq
  unfold sg
  split <;> simp_all <;> omega

theorem val_fin (x : BitVec 64) (h : ex x ≠ 2047) :
    val64 x = (Wasm.IEEE64.scaledValue (UInt64.ofBitVec x) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) := by
  simp [val64, h]

theorem add_sum (A B : ℤ) :
    add_real ((A : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) ((B : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) =
      ((A + B : ℤ) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) := by
  simp only [add_real]; push_cast; ring

theorem eq_sum (z : ℤ) : eq_real ((z : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) 0 = decide (z = 0) := by
  simp [eq_real]

theorem sop_eq (z : ℤ) (hz : z ≠ 0) :
    (z : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) = sop (decide (z < 0)) z.natAbs := by
  by_cases hneg : z < 0
  · simp only [sop, hneg, decide_true, if_true]
    rw [Nat.cast_natAbs, abs_of_neg (by exact_mod_cast hneg)]
    push_cast; ring
  · simp only [sop, hneg, decide_false, Bool.false_eq_true, if_false]
    rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast (not_lt.mp hneg))]

theorem sv_eq (x : BitVec 64) : Wasm.IEEE64.scaledValue (UInt64.ofBitVec x) =
    if sg x then -(Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) : ℤ)
    else (Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) : ℤ) := by
  simp only [Wasm.IEEE64.scaledValue, t_sign]

/-- Two finite operands, not both zeros, whose exact sum is zero are not both negative. -/
theorem not_both_neg (a b : BitVec 64) (hfa : ex a ≠ 2047) (hfb : ex b ≠ 2047)
    (hz : ¬ (ty64 a = .FPType_Zero ∧ ty64 b = .FPType_Zero))
    (hs : Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) +
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) = 0) : (sg a && sg b) = false := by
  rw [sv_eq, sv_eq] at hs
  cases hsa : sg a <;> cases hsb : sg b <;> simp only [hsa, hsb, if_true, if_false,
    Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.and_self] at hs ⊢
  exfalso
  have ha0 : Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec a) = 0 := by omega
  have hb0 : Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec b) = 0 := by omega
  exact hz ⟨(ty_zero a hfa).mp ha0, (ty_zero b hfb).mp hb0⟩

/-- The bits of FPSR that FPAdd sets at 64 bits under FPCR 0x02000000. -/
def addMask (a b : BitVec 64) : BitVec 64 :=
  if isNaNT (ty64 a) || isNaNT (ty64 b) then
    (if ty64 a == .FPType_SNaN || ty64 b == .FPType_SNaN then 1#64 else 0#64)
  else if ty64 a == .FPType_Infinity || ty64 b == .FPType_Infinity then
    (if ty64 a == .FPType_Infinity && ty64 b == .FPType_Infinity && sg a != sg b then 1#64
     else 0#64)
  else
    let z := Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) +
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec b)
    if z = 0 then 0#64 else roundMask z.natAbs

set_option hygiene false in
macro "fin_script" : tactic => `(tactic| (
  have hfa : ex a ≠ 2047 := ty_fin a (by rw [ha]; exact fun h => FPType.noConfusion h) (by rw [ha]; rfl)
  have hfb : ex b ≠ 2047 := ty_fin b (by rw [hb]; exact fun h => FPType.noConfusion h) (by rw [hb]; rfl)
  have hnz : ¬ (ty64 a = .FPType_Zero ∧ ty64 b = .FPType_Zero) := by
    rw [ha, hb]; intro ⟨h1, h2⟩; first | exact FPType.noConfusion h1 | exact FPType.noConfusion h2
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  rw [val_fin a hfa, val_fin b hfb, add_sum, eq_sum]
  by_cases hz : Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) +
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) = 0
  · have hsg := not_both_neg a b hfa hfb hnz hz
    sail_simp [hz, hsg, FPZero, FPProcessDenorms, hr3', h.hfi, h.hps, h.nrw, h.aa64, h.fa]
    refine ⟨_, rfl, ?_, hf3⟩
    rw [hr3', BitVec.or_zero]
    exact (insert_self _ _ _ h.hfpsr).symm
  · rw [sop_eq _ hz]
    sail_simp [hz]
    refine step hf3 (fpRound_run _ _ (Int.natAbs_pos.mpr hz) h hr3') ?_
    intro σ4 hr4 hf4
    sail_simp [FPProcessDenorms, hr4, h.hfi, h.hps, h.nrw, h.aa64, h.fa, Std.ExtDHashMap.get?_insert]
    have hz' : (Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) +
        Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) == 0) = false := by simpa using hz
    simp only [hz', Bool.false_eq_true, ↓reduceIte, tRound]
    exact ⟨σ4, rfl, hr4, hf4⟩))

theorem val_zero (x : BitVec 64) (h : ty64 x = .FPType_Zero) : val64 x = 0 := by
  have hfin : ex x ≠ 2047 := ty_fin x (by rw [h]; exact fun h => FPType.noConfusion h) (by rw [h]; rfl)
  rw [val_fin x hfin, sv_eq, (ty_zero x hfin).mpr h]
  simp

theorem sv_zero (x : BitVec 64) (h : ty64 x = .FPType_Zero) :
    Wasm.IEEE64.scaledValue (UInt64.ofBitVec x) = 0 := by
  have hfin : ex x ≠ 2047 := ty_fin x (by rw [h]; exact fun h => FPType.noConfusion h) (by rw [h]; rfl)
  rw [sv_eq, (ty_zero x hfin).mpr h]
  simp

theorem add_real_zero : add_real 0 0 = 0 := by simp [add_real]
theorem eq_real_zero : eq_real 0 0 = true := by simp [eq_real]

set_option hygiene false in
macro "sgn_script" : tactic => `(tactic| (
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  cases hsa : sg a <;> cases hsb : sg b <;> (try simp only [sgBit, hsa, hsb, ↓reduceIte] at ⊢)
  all_goals try sail_simp [FPZero, FPInfinity, FPProcessDenorms, FPProcessException, hr3', h.hfi,
    h.hps, h.nrw, h.aa64, h.fa, h.hfpsr]
  all_goals try sail_simp [FPDefaultNaN__1, FPProcessException, FPProcessDenorms, hr3', h.hfi,
    h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, setReg_regs, cast_eq, ite_self]
  all_goals try rw [inf_word a (by assumption)]
  all_goals try rw [inf_word b (by assumption)]
  all_goals try rw [val_zero a (by assumption)]
  all_goals try rw [val_zero b (by assumption)]
  all_goals try rw [sv_zero a (by assumption)]
  all_goals try rw [sv_zero b (by assumption)]
  all_goals try simp only [hsa, hsb, ↓reduceIte, add_real_zero, eq_real_zero, add_zero,
    beq_self_eq_true, Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.and_self]
  all_goals try sail_simp [FPZero, FPProcessDenorms, hr3', h.hfi, h.hps, h.nrw, h.aa64, h.fa]
  all_goals (
    refine ⟨_, ok_congr ?v, ?r, ⟨hf3.mem, hf3.tags, hf3.cyc, hf3.out⟩⟩
    case v => decide
    case r =>
      first
      | (rw [hr3', BitVec.or_zero]; exact (insert_self _ _ _ h.hfpsr).symm)
      | (simp only [setReg_regs, bump_regs, faS_regs, hr3', upd_or _ _ (by norm_num : 0 < 64),
          (or_masks _).2.2]))))

set_option maxHeartbeats 0 in
theorem fpAdd_run (a b : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPAdd a b fpcrV).run s = .ok (Wasm.f64Add (.ofBitVec a) (.ofBitVec b)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| addMask a b) ∧ Frame s s' := by
  subst hs
  simp only [FPAdd, FPAdd__1]
  sail_simp [FPRoundingMode, FPDecodeRounding, fpcr_RMode]
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  refine step hf1 (fpUnpack_run b h hr1) ?_
  intro σ2 hr2 hf2
  sail_simp []
  refine step hf2 (fpProcessNaNs_run _ _ a b h hr2) ?_
  intro σ3 hr3 hf3
  simp only [Wasm.f64Add, Wasm.IEEE64.add, t_isNaN, t_isInf, t_sign, addMask]
  have hioc : ioc fpsr = fpsr ||| 1#64 := by rw [ioc, upd_or _ _ (by norm_num), (or_masks _).2.2]
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
  all_goals first | fin_script | skip
  all_goals sgn_script

/-- FPAdd at 64 bits under FPCR 0x02000000 returns Talos's `f64Add` for every pair of words from
every state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| addMask a b`, and the
other registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fpAdd_eq_f64Add (a b : BitVec 64) (s : State) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPAdd a b fpcrV).run s =
        .ok (Wasm.f64Add (UInt64.ofBitVec a) (UInt64.ofBitVec b)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| addMask a b) ∧ Frame s s' :=
  fpAdd_run a b h rfl

end F7
