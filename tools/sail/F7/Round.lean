import F7.Base

/-!
The rounding of FPRoundBase__1 at 64 bits under FPCR 0x02000000, and the lemmas on binary64 words
that the proofs of the arithmetic functions share.

`fpRound_dy` states what FPRound__2 returns on the real number `±N · 2^-(1074 + X)` for every
positive natural `N` and every `X`: Talos's `roundDyadicMagnitude` of `N` with `X` fractional bits,
the two-stage rounder of `IEEE64.mul`, and the FPSR bits of `maskDy N X`.  The exact sum of FPAdd
is a multiple of 2^-1074 (`X = 0`), and FPMul's exact product a multiple of 2^-2148 (`X = 1074`).
The proof splits the normal results (`round_normalG`), where the loops give the exponent
`log2 N − 1074 − X` and the integer mantissa is the quotient of `N` by `2^(X + j)` with
`j = log2 N − 52 − X`, from the subnormal ones (`round_subG`), whose mantissa is the quotient of
`N` by `2^X`.  On the Talos side `tDy_normal` and `tDy_sub` state the two stages over the same
quotient and remainder: `roundShift` rounds `N / 2^(X + j)` to the nearest integer, ties to even,
and `roundScaledMagnitude` of that integer times `2^j` is exact (`rsm_exact`).  A subnormal
result that is inexact sets FPSR.UFC, since FPRoundBase__1 detects tininess before rounding.
`fpRound_run`, the case `X = 0`, gives Talos's `roundScaledMagnitude` of `N`.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

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

theorem floor_div_nat (N d : ℕ) : round_down ((N : ℝ) / (d : ℝ)) = ((N / d : ℕ) : ℤ) := by
  simp only [round_down]
  rw [Int.floor_div_natCast, Int.floor_natCast]
  push_cast; rfl

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
theorem or_masks (v : BitVec 64) :
    (v ||| 1#64 <<< 2) ||| 1#64 <<< 4 = v ||| 0x14#64 ∧ v ||| 1#64 <<< 4 = v ||| 0x10#64 ∧
      v ||| 1#64 <<< 0 = v ||| 1#64 ∧ (v ||| 1#64 <<< 3) ||| 1#64 <<< 4 = v ||| 0x18#64 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [BitVec.or_assoc]; congr 1
  · congr 1
  · congr 1
  · rw [BitVec.or_assoc]; congr 1

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

theorem sv_eq (x : BitVec 64) : Wasm.IEEE64.scaledValue (UInt64.ofBitVec x) =
    if sg x then -(Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) : ℤ)
    else (Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) : ℤ) := by
  simp only [Wasm.IEEE64.scaledValue, t_sign]

/-- Two finite operands, not both zeros, whose exact sum is zero are not both negative. -/
theorem val_zero (x : BitVec 64) (h : ty64 x = .FPType_Zero) : val64 x = 0 := by
  have hfin : ex x ≠ 2047 := ty_fin x (by rw [h]; exact fun h => FPType.noConfusion h) (by rw [h]; rfl)
  rw [val_fin x hfin, sv_eq, (ty_zero x hfin).mpr h]
  simp

theorem sv_zero (x : BitVec 64) (h : ty64 x = .FPType_Zero) :
    Wasm.IEEE64.scaledValue (UInt64.ofBitVec x) = 0 := by
  have hfin : ex x ≠ 2047 := ty_fin x (by rw [h]; exact fun h => FPType.noConfusion h) (by rw [h]; rfl)
  rw [sv_eq, (ty_zero x hfin).mpr h]
  simp

/-! ## Talos's two-stage rounder -/

/-- Talos's rounding of the magnitude `N` in units of `2^-(1074 + X)`, with the sign `neg`. -/
def tDy (neg : Bool) (N X : ℕ) : BitVec 64 :=
  (Wasm.IEEE64.roundDyadicMagnitude neg N X).toBitVec

/-- Talos's rounding of the magnitude `N` in units of 2^-1074, with the sign `neg`. -/
def tRound (neg : Bool) (N : ℕ) : BitVec 64 := (Wasm.IEEE64.roundScaledMagnitude neg N).toBitVec

theorem log2_eq (n m : ℕ) (h1 : 2 ^ m ≤ n) (h2 : n < 2 ^ (m + 1)) : Nat.log2 n = m := by
  have hn : n ≠ 0 := by have := Nat.one_le_two_pow (n := m); omega
  have a1 : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn
  have a2 : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have b1 : Nat.log2 n < m + 1 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt a1 h2)
  have b2 : m < Nat.log2 n + 1 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (lt_of_le_of_lt h1 a2)
  omega

theorem roundShift_eq (N k : ℕ) (hk : 1 ≤ k) :
    Wasm.IEEE32.roundShift N k =
      if (2 ^ k < 2 * (N % 2 ^ k) ∨ 2 * (N % 2 ^ k) = 2 ^ k ∧ (N / 2 ^ k) % 2 = 1)
      then N / 2 ^ k + 1 else N / 2 ^ k := by
  have hhalf : 2 ^ k / 2 = 2 ^ (k - 1) := by
    rw [show k = k - 1 + 1 by omega, pow_succ]; simp
  have hpk : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  simp only [Wasm.IEEE32.roundShift, hhalf]
  generalize N / 2 ^ k = q
  generalize N % 2 ^ k = r
  rw [hpk]
  generalize 2 ^ (k - 1) = h
  simp only [beq_iff_eq]
  split_ifs <;> omega

theorem rsm_exact (neg : Bool) (q j : ℕ) (h1 : 2 ^ 52 ≤ q) (h2 : q < 2 ^ 53) :
    Wasm.IEEE64.roundScaledMagnitude neg (q * 2 ^ j) =
      if 2047 ≤ j + 1 then Wasm.IEEE64.infinity neg
      else Wasm.IEEE64.encodeFinite neg (j + 1) (q - 2 ^ 52) := by
  unfold Wasm.IEEE64.roundScaledMagnitude
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [pow_zero, Nat.mul_one]
    rw [if_neg (by omega), if_pos h2, if_neg (by omega)]
  · have hp : 2 ^ 53 ≤ q * 2 ^ j := by
      have : 2 ≤ 2 ^ j := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      calc 2 ^ 53 = 2 ^ 52 * 2 := by norm_num
        _ ≤ q * 2 ^ j := Nat.mul_le_mul h1 this
    have hlog : Nat.log2 (q * 2 ^ j) = 52 + j := by
      apply log2_eq
      · rw [pow_add]; exact Nat.mul_le_mul_right _ h1
      · rw [show 52 + j + 1 = 53 + j by omega, pow_add]
        exact Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos j)
    have hrs : Wasm.IEEE32.roundShift (q * 2 ^ j) j = q := by
      rw [roundShift_eq _ _ hj, Nat.mul_mod_left, Nat.mul_div_cancel _ (Nat.two_pow_pos j)]
      rw [if_neg]
      have := Nat.two_pow_pos j
      omega
    simp only [show ¬ q * 2 ^ j < 2 ^ 52 by omega, show ¬ q * 2 ^ j < 2 ^ 53 by omega, if_false,
      hlog, show 52 + j - 52 = j by omega, hrs]
    have hq : (q == 2 ^ 53) = false := by simp only [beq_eq_false_iff_ne]; omega
    simp only [hq, Bool.false_eq_true, if_false]

theorem rsm_carry (neg : Bool) (j : ℕ) :
    Wasm.IEEE64.roundScaledMagnitude neg (2 ^ 53 * 2 ^ j) =
      if 2047 ≤ j + 2 then Wasm.IEEE64.infinity neg
      else Wasm.IEEE64.encodeFinite neg (j + 2) 0 := by
  rw [show 2 ^ 53 * 2 ^ j = 2 ^ 52 * 2 ^ (j + 1) by rw [← pow_add, ← pow_add]; congr 1; omega,
    rsm_exact neg _ _ (le_refl _) (by norm_num)]
  simp

/-- Talos's two stages for a normal result: the quotient `q` of `N` by `2^(X + j)` rounds to
nearest even, with a carry into the exponent and an overflow to infinity. -/
theorem tDy_normal (neg : Bool) (N X j q r : ℕ) (hk : Nat.log2 N = X + j + 52)
    (hq : N / 2 ^ (X + j) = q) (hr : N % 2 ^ (X + j) = r) :
    tDy neg N X =
      (if (2 ^ (X + j) < 2 * r ∨ 2 * r = 2 ^ (X + j) ∧ q % 2 = 1) then
        (if q + 1 = 2 ^ 53 then
          (if 2047 ≤ j + 2 then (Wasm.IEEE64.infinity neg).toBitVec
           else (Wasm.IEEE64.encodeFinite neg (j + 2) 0).toBitVec)
         else (if 2047 ≤ j + 1 then (Wasm.IEEE64.infinity neg).toBitVec
           else (Wasm.IEEE64.encodeFinite neg (j + 1) (q + 1 - 2 ^ 52)).toBitVec))
       else (if 2047 ≤ j + 1 then (Wasm.IEEE64.infinity neg).toBitVec
         else (Wasm.IEEE64.encodeFinite neg (j + 1) (q - 2 ^ 52)).toBitVec)) := by
  have hN0 : N ≠ 0 := by intro h0; rw [h0] at hk; simp at hk
  have hL1 : 2 ^ (X + j + 52) ≤ N := hk ▸ Nat.log2_self_le hN0
  have hL2 : N < 2 ^ (X + j + 52 + 1) := hk ▸ Nat.lt_log2_self
  have hq1 : 2 ^ 52 ≤ q := by
    rw [← hq, Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
    rw [show X + j + 52 = 52 + (X + j) by omega, pow_add] at hL1; exact hL1
  have hq2 : q < 2 ^ 53 := by
    rw [← hq, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [show X + j + 52 + 1 = 53 + (X + j) by omega, pow_add] at hL2; exact hL2
  have hcand : (if Nat.log2 N - (X + 52) == 0 then
        (if X == 0 then N else Wasm.IEEE32.roundShift N X)
      else Wasm.IEEE32.roundShift N (X + (Nat.log2 N - (X + 52))) * 2 ^ (Nat.log2 N - (X + 52))) =
      (if (2 ^ (X + j) < 2 * r ∨ 2 * r = 2 ^ (X + j) ∧ q % 2 = 1) then q + 1 else q) * 2 ^ j := by
    rw [hk, show X + j + 52 - (X + 52) = j by omega]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rcases Nat.eq_zero_or_pos X with rfl | hX
      · simp only [Nat.add_zero, pow_zero, Nat.div_one, Nat.mod_one] at hq hr
        subst hq hr
        simp
      · simp only [beq_self_eq_true, if_true, Nat.add_zero, pow_zero, Nat.mul_one]
        have hX' : (X == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
        rw [hX', if_neg (by simp), roundShift_eq _ _ hX]
        simp only [Nat.add_zero] at hq hr
        rw [hq, hr]
    · have hj' : (j == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
      rw [hj', if_neg (by simp), roundShift_eq _ _ (by omega), hq, hr]
  unfold tDy Wasm.IEEE64.roundDyadicMagnitude
  have hN0' : (N == 0) = false := by simp only [beq_eq_false_iff_ne]; exact hN0
  simp only [hN0', Bool.false_eq_true, if_false]
  rw [hcand]
  by_cases hup : (2 ^ (X + j) < 2 * r ∨ 2 * r = 2 ^ (X + j) ∧ q % 2 = 1)
  · rw [if_pos hup, if_pos hup]
    by_cases hc : q + 1 = 2 ^ 53
    · rw [if_pos hc, hc, rsm_carry]
      split_ifs <;> rfl
    · rw [if_neg hc, rsm_exact neg (q + 1) j (by omega) (by omega)]
      split_ifs <;> rfl
  · rw [if_neg hup, if_neg hup, rsm_exact neg q j hq1 hq2]
    split_ifs <;> rfl

/-- Talos's two stages for a subnormal result: the quotient `q` of `N` by `2^X` rounds to
nearest even, and a carry gives the smallest normal number. -/
theorem tDy_sub (neg : Bool) (N X q r : ℕ) (hN : 0 < N) (hL : Nat.log2 N < X + 52)
    (hq : N / 2 ^ X = q) (hr : N % 2 ^ X = r) :
    tDy neg N X =
      if (2 ^ X < 2 * r ∨ 2 * r = 2 ^ X ∧ q % 2 = 1) then
        (if q + 1 = 2 ^ 52 then (Wasm.IEEE64.encodeFinite neg 1 0).toBitVec
         else (Wasm.IEEE64.encodeFinite neg 0 (q + 1)).toBitVec)
      else (Wasm.IEEE64.encodeFinite neg 0 q).toBitVec := by
  have hN2 : N < 2 ^ (X + 52) := by
    have := Nat.lt_log2_self (n := N)
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hq2 : q < 2 ^ 52 := by
    rw [← hq, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [show X + 52 = 52 + X by omega, pow_add] at hN2; exact hN2
  have hcand : (if Nat.log2 N - (X + 52) == 0 then
        (if X == 0 then N else Wasm.IEEE32.roundShift N X)
      else Wasm.IEEE32.roundShift N (X + (Nat.log2 N - (X + 52))) * 2 ^ (Nat.log2 N - (X + 52))) =
      (if (2 ^ X < 2 * r ∨ 2 * r = 2 ^ X ∧ q % 2 = 1) then q + 1 else q) := by
    rw [show Nat.log2 N - (X + 52) = 0 by omega]
    simp only [beq_self_eq_true, if_true]
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · simp only [pow_zero, Nat.div_one, Nat.mod_one] at hq hr
      subst hq hr
      simp
    · have hX' : (X == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
      rw [hX', if_neg (by simp), roundShift_eq _ _ hX, hq, hr]
  unfold tDy Wasm.IEEE64.roundDyadicMagnitude
  have hN0' : (N == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  simp only [hN0', Bool.false_eq_true, if_false]
  rw [hcand]
  unfold Wasm.IEEE64.roundScaledMagnitude
  by_cases hup : (2 ^ X < 2 * r ∨ 2 * r = 2 ^ X ∧ q % 2 = 1)
  · rw [if_pos hup, if_pos hup]
    by_cases hc : q + 1 = 2 ^ 52
    · rw [if_pos hc, hc, if_neg (by norm_num), if_pos (by norm_num)]
      simp
    · rw [if_neg hc, if_pos (by omega)]
  · rw [if_neg hup, if_neg hup, if_pos hq2]

/-- The bits of FPSR that FPRoundBase__1 sets for the nonzero magnitude `N` in units of
`2^-(1074 + X)`, at 64 bits under FPCR 0x02000000: OFC and IXC on overflow, IXC on an inexact
result, and UFC with IXC on an inexact subnormal result. -/
def maskDy (N X : ℕ) : BitVec 64 :=
  let j := Nat.log2 N - (X + 52)
  let q := N / 2 ^ (X + j)
  let r := N % 2 ^ (X + j)
  if X + 52 ≤ Nat.log2 N then
    (if 2047 ≤ (if (2 ^ (X + j) < 2 * r ∨ 2 * r = 2 ^ (X + j) ∧ q % 2 = 1) ∧ q + 1 = 2 ^ 53
        then j + 2 else j + 1) then 0x14#64
     else if r = 0 then 0#64 else 0x10#64)
  else if r = 0 then 0#64 else 0x18#64

/-- The real number `±N · 2^-S`. -/
noncomputable def sop (neg : Bool) (N : ℕ) (S : ℤ) : ℝ :=
  if neg then -((N : ℝ) * (2 : ℝ) ^ (-S)) else (N : ℝ) * (2 : ℝ) ^ (-S)

theorem sop_facts (neg : Bool) (N : ℕ) (S : ℤ) (hN : 0 < N) :
    lt_real (sop neg N S) 0 = neg ∧ (sop neg N S == 0) = false ∧
      neg_real (-((N : ℝ) * (2 : ℝ) ^ (-S))) = (N : ℝ) * (2 : ℝ) ^ (-S) := by
  have hM : (0 : ℝ) < (N : ℝ) * (2 : ℝ) ^ (-S) :=
    mul_pos (by exact_mod_cast hN) (zpow_pos (by norm_num) _)
  have hp : (0 : ℝ) < (2 : ℝ) ^ S := zpow_pos (by norm_num) _
  refine ⟨?_, ?_, by simp [neg_real]⟩
  · cases neg <;> simp [sop, lt_real, hM, hM.le, hN, hp, hp.le]
  · cases neg <;> simp [sop, hM.ne', Nat.pos_iff_ne_zero.mp hN, hp.ne']

theorem exp_eqG (N : ℕ) (hN : 0 < N) (S e : ℤ)
    (h1 : 1 ≤ (N : ℝ) * (2 : ℝ) ^ (-S) * 2 ^ (-e))
    (h2 : (N : ℝ) * (2 : ℝ) ^ (-S) * 2 ^ (-e) < 2) :
    e = (Nat.log2 N : ℤ) - S := by
  have hL1 : 2 ^ Nat.log2 N ≤ N := Nat.log2_self_le (by omega)
  have hL2 : N < 2 ^ (Nat.log2 N + 1) := Nat.lt_log2_self
  have hr1 : ((2 : ℝ) ^ (Nat.log2 N : ℤ)) ≤ N := by
    rw [zpow_natCast]; exact_mod_cast hL1
  have hr2 : (N : ℝ) < (2 : ℝ) ^ ((Nat.log2 N : ℤ) + 1) := by
    rw [show ((Nat.log2 N : ℤ) + 1) = ((Nat.log2 N + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact_mod_cast hL2
  have ht : (N : ℝ) * (2 : ℝ) ^ (-S) * 2 ^ (-e) = N * 2 ^ (-S - e) := by
    rw [mul_assoc, ← zpow_add₀ two_ne_zero]; ring_nf
  rw [ht] at h1 h2
  have hpos : (0 : ℝ) < 2 ^ (-S - e) := zpow_pos (by norm_num) _
  have a1 : (2 : ℝ) ^ (0 : ℤ) < 2 ^ ((Nat.log2 N : ℤ) + 1 + (-S - e)) := by
    rw [zpow_add₀ two_ne_zero, zpow_zero]
    calc (1 : ℝ) ≤ N * 2 ^ (-S - e) := h1
      _ < 2 ^ ((Nat.log2 N : ℤ) + 1) * 2 ^ (-S - e) := by
        exact mul_lt_mul_of_pos_right hr2 hpos
  have a2 : (2 : ℝ) ^ ((Nat.log2 N : ℤ) + (-S - e)) < 2 ^ (1 : ℤ) := by
    rw [zpow_add₀ two_ne_zero, zpow_one]
    calc (2 : ℝ) ^ (Nat.log2 N : ℤ) * 2 ^ (-S - e) ≤ N * 2 ^ (-S - e) :=
          mul_le_mul_of_nonneg_right hr1 hpos.le
      _ < 2 := h2
  rw [zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)] at a1 a2
  omega

theorem man_normalG (N : ℕ) (S e : ℤ) (hE : e = (Nat.log2 N : ℤ) - S) (hL : 52 ≤ Nat.log2 N) :
    mult_real ((N : ℝ) * 2 ^ (-S) * 2 ^ (-e)) (real_power 2 52) =
      (N : ℝ) / ((2 ^ (Nat.log2 N - 52) : ℕ) : ℝ) := by
  simp only [mult_real, real_power]
  rw [mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero, div_eq_mul_inv]
  congr 1
  push_cast
  rw [← zpow_natCast, ← zpow_neg]
  congr 1
  omega

theorem man_subG (N X : ℕ) (S e : ℤ) (hS : S = 1074 + X) :
    mult_real (div_real ((N : ℝ) * 2 ^ (-S) * 2 ^ (-e)) (real_power 2 (-1022 - e)))
      (real_power 2 52) = (N : ℝ) / ((2 ^ X : ℕ) : ℝ) := by
  have h2 : ((2 ^ X : ℕ) : ℝ) = (2 : ℝ) ^ (X : ℤ) := by push_cast; rw [zpow_natCast]
  rw [h2, div_eq_mul_inv (N : ℝ), ← zpow_neg]
  simp only [mult_real, div_real, real_power]
  rw [div_eq_mul_inv, ← zpow_neg, mul_assoc, mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero,
    ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
  congr 1
  congr 1
  omega

theorem tDy_zero (neg : Bool) (N : ℕ) (hN : 0 < N) : tDy neg N 0 = tRound neg N := by
  by_cases hL : Nat.log2 N < 52
  · rw [tDy_sub neg N 0 N 0 hN (by omega) (by rw [pow_zero, Nat.div_one])
      (by rw [pow_zero, Nat.mod_one])]
    have hN52 : N < 2 ^ 52 := by
      have := Nat.lt_log2_self (n := N)
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
    simp [tRound, Wasm.IEEE64.roundScaledMagnitude, show N < 4503599627370496 from hN52]
  · obtain ⟨j, hj⟩ : ∃ j, Nat.log2 N = 0 + j + 52 := ⟨Nat.log2 N - 52, by omega⟩
    rw [tDy_normal neg N 0 j _ _ hj rfl rfl]
    have hL1 : 2 ^ (j + 52) ≤ N := by rw [← show 0 + j + 52 = j + 52 by omega, ← hj]; exact Nat.log2_self_le (by omega)
    have hL2 : N < 2 ^ (j + 52 + 1) := by rw [← show 0 + j + 52 = j + 52 by omega, ← hj]; exact Nat.lt_log2_self
    simp only [Nat.zero_add] at hL1 hL2 ⊢
    have hq1 : 2 ^ 52 ≤ N / 2 ^ j := by
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
      rw [show j + 52 = 52 + j by omega, pow_add] at hL1; exact hL1
    have hq2 : N / 2 ^ j < 2 ^ 53 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      rw [show j + 52 + 1 = 53 + j by omega, pow_add] at hL2; exact hL2
    unfold tRound Wasm.IEEE64.roundScaledMagnitude
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [pow_zero, Nat.div_one, Nat.mod_one] at hq1 hq2 ⊢
      simp only [show ¬ N < 4503599627370496 by omega, show N < 9007199254740992 by omega,
        if_false, if_true]
      split_ifs <;> simp_all
    · have hN53 : ¬ N < 2 ^ 53 := by
        have : 2 ^ 53 ≤ 2 ^ (j + 52) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      simp only [show ¬ N < 2 ^ 52 by omega, hN53, if_false, hj, Nat.zero_add,
        show j + 52 - 52 = j by omega, roundShift_eq N j hj0]
      split_ifs <;> simp_all

/-! ## FPRoundBase__1 -/

set_option maxHeartbeats 1300000 in
theorem round_normalG (neg : Bool) (N X j : ℕ) (S : ℤ) (hS : S = 1074 + X) (hN : 0 < N)
    (hL : Nat.log2 N = X + j + 52) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (sop neg N S) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (tDy neg N X) s' ∧ s'.regs = R.insert .FPSR (fpsr ||| maskDy N X) ∧ Frame s s' := by
  subst hs
  have hM : (0 : ℝ) < (N : ℝ) * (2 : ℝ) ^ (-S) :=
    mul_pos (by exact_mod_cast hN) (zpow_pos (by norm_num) _)
  obtain ⟨e, he, h1, h2⟩ := loops_eq' _ hM
  have hE := exp_eqG N hN S e h1 h2
  obtain ⟨hlt, hne, hneg⟩ := sop_facts neg N S hN
  have hman : mult_real ((N : ℝ) * 2 ^ (-S) * 2 ^ (-e)) (real_power 2 52) =
      (N : ℝ) / ((2 ^ (X + j) : ℕ) : ℝ) := by
    rw [man_normalG N S e hE (by omega), hL, show X + j + 52 - 52 = X + j by omega]
  have hb : max (e - -1022 + 1) 0 = (j : ℤ) + 1 := by omega
  have hb0 : ((j : ℤ) + 1 == 0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  have hd : 0 < 2 ^ (X + j) := Nat.two_pow_pos _
  have hmask : maskDy N X = (let q := N / 2 ^ (X + j); let r := N % 2 ^ (X + j)
      if 2047 ≤ (if (2 ^ (X + j) < 2 * r ∨ 2 * r = 2 ^ (X + j) ∧ q % 2 = 1) ∧ q + 1 = 2 ^ 53
        then j + 2 else j + 1) then 0x14#64 else if r = 0 then 0#64 else 0x10#64) := by
    simp only [maskDy, hL, show X + 52 ≤ X + j + 52 by omega, if_true,
      show X + j + 52 - (X + 52) = j by omega]
  rw [hmask, tDy_normal neg N X j _ _ hL rfl rfl]
  have hL1 : 2 ^ (X + j + 52) ≤ N := hL ▸ Nat.log2_self_le (by omega)
  have hL2 : N < 2 ^ (X + j + 52 + 1) := hL ▸ Nat.lt_log2_self
  have hq1 : 2 ^ 52 ≤ N / 2 ^ (X + j) := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
    rw [show X + j + 52 = 52 + (X + j) by omega, pow_add] at hL1; exact hL1
  have hq2 : N / 2 ^ (X + j) < 2 ^ 53 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [show X + j + 52 + 1 = 53 + (X + j) by omega, pow_add] at hL2; exact hL2
  have hr : N % 2 ^ (X + j) < 2 ^ (X + j) := Nat.mod_lt _ hd
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, sop] at hlt hne ⊢
  all_goals (
    sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self,
      whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt, hneg]
    rw [he]
    sail_simp [↓join1_beq, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self, hne, bne, hlt, hb,
      hb0, hman, floor_div_nat, err_div _ _ hd, gt_half _ _ hd, eq_half _ _ hd,
      beq_zero_div _ _ hd, int_access]
    generalize hq : N / 2 ^ (X + j) = q at *
    generalize hrr : N % 2 ^ (X + j) = r at *
    clear he h1 h2 hlt hne hb hb0 hmask hE hman
    simp only [ipow, Int.reduceToNat, Int.reducePow, Int.reduceSub, Int.reduceAdd, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ge_iff_le]
    have hfd : fdiv_int ((q : ℤ) + 1) 2 = ((q : ℤ) + 1) / 2 := fdiv_two _ (by omega)
    have c2 : ((q : ℤ) + 1 = 4503599627370496) = False := by simp; omega
    have o1 : (2047 ≤ (j : ℤ) + 1 + 1) = (2047 ≤ j + 2) := by
      apply propext; constructor <;> intro <;> omega
    have o2 : (2047 ≤ (j : ℤ) + 1) = (2047 ≤ j + 1) := by
      apply propext; constructor <;> intro <;> omega
    simp only [c2, o1, o2, ↓reduceIte]
    by_cases hup : (2 ^ (X + j) < 2 * r ∨ 2 * r = 2 ^ (X + j) ∧ q % 2 = 1) <;>
    by_cases hc : q + 1 = 2 ^ 53 <;> by_cases hv1 : 2047 ≤ j + 1 <;> by_cases hv2 : 2047 ≤ j + 2 <;>
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
      · simp only [setReg_regs, bump_regs, faS_regs, insert_insert,
          upd_or _ _ (by norm_num : 2 < 64), upd_or _ _ (by norm_num : 4 < 64), (or_masks _).1,
          (or_masks _).2.1, BitVec.or_zero, cast_eq] <;>
          first | rfl | exact (insert_self _ _ _ h.hfpsr).symm
      · exact ⟨rfl, rfl, rfl, rfl⟩))

set_option maxHeartbeats 400000 in
theorem round_subG (neg : Bool) (N X : ℕ) (S : ℤ) (hS : S = 1074 + X) (hN : 0 < N)
    (hL : Nat.log2 N < X + 52) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (sop neg N S) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (tDy neg N X) s' ∧ s'.regs = R.insert .FPSR (fpsr ||| maskDy N X) ∧ Frame s s' := by
  subst hs
  have hM : (0 : ℝ) < (N : ℝ) * (2 : ℝ) ^ (-S) :=
    mul_pos (by exact_mod_cast hN) (zpow_pos (by norm_num) _)
  obtain ⟨e, he, h1, h2⟩ := loops_eq' _ hM
  have hE := exp_eqG N hN S e h1 h2
  obtain ⟨hlt, hne, hneg⟩ := sop_facts neg N S hN
  have hb : max (e - -1022 + 1) 0 = 0 := by omega
  have hd : 0 < 2 ^ X := Nat.two_pow_pos _
  have hmask : maskDy N X = (if N % 2 ^ X = 0 then 0#64 else 0x18#64) := by
    simp only [maskDy, show ¬ X + 52 ≤ Nat.log2 N by omega, if_false,
      show Nat.log2 N - (X + 52) = 0 by omega, Nat.add_zero]
  rw [hmask, tDy_sub neg N X _ _ hN hL rfl rfl]
  have hN2 : N < 2 ^ (X + 52) := by
    have := Nat.lt_log2_self (n := N)
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hq2 : N / 2 ^ X < 2 ^ 52 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [show X + 52 = 52 + X by omega, pow_add] at hN2; exact hN2
  have hr : N % 2 ^ X < 2 ^ X := Nat.mod_lt _ hd
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, sop] at hlt hne ⊢
  all_goals (
    sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self,
      whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt, hneg]
    rw [he]
    sail_simp [↓join1_beq, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self, hne, bne, hlt, hb,
      man_subG N X S e hS, floor_div_nat, err_div _ _ hd, gt_half _ _ hd, eq_half _ _ hd,
      beq_zero_div _ _ hd, int_access]
    generalize hq : N / 2 ^ X = q at *
    generalize hrr : N % 2 ^ X = r at *
    clear he h1 h2 hlt hne hb hmask hE
    simp only [ipow, Int.reduceToNat, Int.reducePow, Int.reduceSub, Int.reduceAdd, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ge_iff_le]
    have c1 : ((q : ℤ) + 1 = 9007199254740992) = False := by simp; omega
    have c2 : ((q : ℤ) + 1 = 4503599627370496) = (q + 1 = 2 ^ 52) := by
      apply propext; constructor <;> intro <;> omega
    simp only [c1, c2, ↓reduceIte]
    by_cases hup : (2 ^ X < 2 * r ∨ 2 * r = 2 ^ X ∧ q % 2 = 1) <;>
    by_cases hc : q + 1 = 2 ^ 52 <;> by_cases hr0 : r = 0
    all_goals first | (exfalso; omega) | skip
    all_goals (
      have e1 := by first | exact eq_false hup | exact eq_true hup
      have e2 := by first | exact eq_false hc | exact eq_true hc
      have e5 := by first | exact eq_false hr0 | exact eq_true hr0
      simp only [e1, e2, e5, true_and, and_true, false_and, and_false, ↓reduceIte, decide_true,
        decide_false, Bool.not_true, Bool.not_false]
      apply exists_of_run'
      · sail_simp [FPZero, FPProcessException, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr,
          ite_self, toBV_encode, one_beq_zero, beq_zero_div _ _ hd, cast_eq, e5]
        refine ok_congr ?_
        first
        | decide
        | (rw [bits_sub]
           · apply congrArg (BitVec.ofNat 64)
             simp only [BitVec.toNat_ofNat, Nat.zero_mod, zero_mul, zero_add, Nat.reducePow]
             omega
           all_goals first | decide | omega)
        | (rw [bits_eq]
           · apply congrArg (BitVec.ofNat 64)
             simp only [BitVec.toNat_ofNat, Nat.zero_mod, zero_mul, zero_add, Nat.reducePow]
             have hq1 : ((q : ℤ) + 1).toNat = 4503599627370496 := by
               have : ((q : ℤ) + 1) = ((q + 1 : ℕ) : ℤ) := by push_cast; rfl
               rw [this, Int.toNat_natCast, hc]; rfl
             rw [hq1]
             first | rfl | decide | norm_num
           all_goals first | decide | (clear * - hc; omega))
      · simp only [setReg_regs, bump_regs, faS_regs, insert_insert,
          upd_or _ _ (by norm_num : 3 < 64), upd_or _ _ (by norm_num : 4 < 64), (or_masks _).2.2.2,
          BitVec.or_zero, cast_eq] <;>
          first | rfl | exact (insert_self _ _ _ h.hfpsr).symm
      · exact ⟨rfl, rfl, rfl, rfl⟩))

/-- FPRound__2 at 64 bits under FPCR 0x02000000, rounding to nearest even, on `±N · 2^-S` with
`S = 1074 + X`, returns Talos's `roundDyadicMagnitude` and sets the FPSR bits of `maskDy N X`. -/
theorem fpRound_dy (neg : Bool) (N X : ℕ) (S : ℤ) (hS : S = 1074 + X) (hN : 0 < N)
    {R : Std.ExtDHashMap Register RegisterType} (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (sop neg N S) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (tDy neg N X) s' ∧ s'.regs = R.insert .FPSR (fpsr ||| maskDy N X) ∧ Frame s s' := by
  by_cases hL : X + 52 ≤ Nat.log2 N
  · exact round_normalG neg N X (Nat.log2 N - (X + 52)) S hS hN (by omega) h hs
  · exact round_subG neg N X S hS hN (by omega) h hs

/-- The FPSR bits of rounding the magnitude `N` in units of 2^-1074. -/
def roundMask (N : ℕ) : BitVec 64 := maskDy N 0

/-- FPRound__2 on `±N · 2^-1074`, the case of an exact sum: Talos's `roundScaledMagnitude`. -/
theorem fpRound_run (neg : Bool) (N : ℕ) (hN : 0 < N) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (sop neg N 1074) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (tRound neg N) s' ∧ s'.regs = R.insert .FPSR (fpsr ||| roundMask N) ∧ Frame s s' := by
  rw [← tDy_zero neg N hN]
  exact fpRound_dy neg N 0 1074 (by norm_num) hN h hs

end F7
