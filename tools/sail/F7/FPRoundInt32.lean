import F7.FPSqrt32
import F7.FPToFixed32

/-!
FPRoundInt of Sail's Lean translation of the Armv9.4-A model, as FRINTN Sd, Sn calls it,
`FPRoundInt(op, FPCR, FPRounding_TIEEVEN, FALSE)` on a 32-bit operand under FPCR 0x02000000,
returns Talos's `f32Nearest` of its operand for every word and sets in FPSR the bits of
`rintMask32`, IOC for a signaling NaN, from every state that satisfies `Hyp`.

For a finite nonzero operand FPRoundInt takes the floor of the value and the error between the
value and its floor, adds 1 to the floor when the error exceeds 1/2 or equals 1/2 at an odd floor,
returns a zero with the operand's sign when the integer is 0, and otherwise rounds the integer with
FPRound__1 and `FPRounding_ZERO`.  For a word whose magnitude is `m` in units of 2^-149, the
integer is `±n` with `n = roundShift m 149`, the integer of Talos's `roundIntegralFinite`
(`rint_eq`): for a positive value the floor is the quotient `q` of `m` by 2^149 and the error the
remainder `r` over 2^149, and for a negative one the floor is `−q` or `−q − 1` as `r` is 0 or not,
with the error `0` or `(2^149 − r) / 2^149`, and `int_accessZ` gives bit 0 of the floor `−q − 1`.
The integer `n · 2^149` in units of 2^-149 has at most 24 significant bits and an exponent field
below 255 (`rep_nearest`), so `round_zeroQ32` rounds it exactly: FPRoundBase__1's normal case with
the rounding toward zero and a zero error returns Talos's `roundRationalMagnitude` and sets no bit
of FPSR.  The statements write Talos's word without a definition in between, for the reason that
`F7/RoundQ.lean` gives.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

/-! ## FPRoundBase__1 at 32 bits on an exact normal value, rounding toward zero -/

set_option maxHeartbeats 80000 in
/-- FPRound__2 at 32 bits under FPCR 0x02000000, rounding toward zero, on `±(P/Q) · 2^-149` whose
quotient by `Q · 2^j` is exact and normal returns Talos's `IEEE32.roundRationalMagnitude neg P Q`
and changes no register. -/
theorem round_zeroQ32 (neg : Bool) (P Q j : ℕ) (S : ℤ) (hS : S = 149) (hP : 0 < P)
    (hQ : 0 < Q) (hL : Nat.log2 (P / Q) = j + 23) (hr0 : P % (Q * 2 ^ j) = 0) (hj : j + 1 < 255)
    {R : Std.ExtDHashMap Register RegisterType} (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (qop neg P Q S) fpcrV .FPRounding_ZERO true 32).run s =
      .ok (Wasm.IEEE32.roundRationalMagnitude neg P Q).toBitVec s' ∧ s'.regs = R ∧
        Frame s s' := by
  subst hs
  have hM : (0 : ℝ) < (P : ℝ) / (Q : ℝ) * (2 : ℝ) ^ (-S) :=
    mul_pos (div_pos (by exact_mod_cast hP) (by exact_mod_cast hQ)) (zpow_pos (by norm_num) _)
  obtain ⟨e, he, h1, h2⟩ := loops_eq' _ hM
  have hI0 : P / Q ≠ 0 := by intro h0; rw [h0, Nat.log2_zero] at hL; omega
  obtain ⟨hx1, hx2⟩ := div_bounds P Q (j + 23) hQ (by rw [← hL]; exact Nat.log2_self_le hI0)
    (by rw [← hL]; exact Nat.lt_log2_self)
  have hE0 := exp_eqR _ (j + 23) S e hx1 hx2 h1 h2
  have hE : e = (j : ℤ) - 126 := by omega
  obtain ⟨hlt, hne, hneg⟩ := qop_facts neg P Q S hP hQ
  have hman := man_normalQ32 P Q j S e hS hE
  have hb : max (e - -126 + 1) 0 = (j : ℤ) + 1 := by omega
  have hb0 : ((j : ℤ) + 1 == 0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  have hd : 0 < Q * 2 ^ j := Nat.mul_pos hQ (Nat.two_pow_pos _)
  rw [rq_normal32 neg P Q j _ _ hP hQ hL rfl rfl, hr0]
  obtain ⟨hq1, hq2⟩ := q_bounds32 P Q j hL
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, qop] at hlt hne ⊢
  all_goals (
    sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self,
      whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt, hneg]
    rw [he]
    sail_simp [h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self, hne, bne, hlt, hb, hb0, hman,
      floor_div_nat, err_div _ _ hd, beq_zero_div _ _ hd, hr0]
    generalize hq : P / (Q * 2 ^ j) = q at *
    clear he h1 h2 hlt hne hb hb0 hE hE0 hman hx1 hx2
    simp only [ipow, Int.reduceToNat, Int.reducePow, Int.reduceSub, ge_iff_le]
    have o2 : (255 ≤ (j : ℤ) + 1) = False := eq_false (by omega)
    simp only [o2, decide_false, Bool.false_eq_true, ↓reduceIte]
    apply exists_of_run'
    · sail_simp [FPProcessException, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self,
        toBV_encode32, Nat.cast_zero, zero_div, cast_eq]
      refine ok_congr ?_
      rw [bits_eq32]
      · apply congrArg (BitVec.ofNat 32)
        simp only [BitVec.toNat_ofNat, Nat.reducePow]
        omega
      all_goals first | decide | omega
    · simp only [bump_regs, faS_regs]
    · exact ⟨rfl, rfl, rfl, rfl⟩)

/-! ## The integer of FPRoundInt -/

/-- Bit 0 of an integer, negative ones included. -/
theorem int_accessZ (z : ℤ) : (integer_access z 0 == 1#1) = decide (z % 2 = 1) := by
  have hb : integer_access z 0 = BitVec.ofBool (decide (z % 2 = 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [integer_access, integer_subrange, get_slice_int, BitVec.access]
    rw [BitVec.toNat_ofBool, BitVec.toNat_ofBool]
    congr 1
    rw [getElem!_pos _ 0 (by decide), BitVec.getElem_eq_testBit_toNat,
      Nat.testBit_eq_decide_div_mod_eq]
    apply decide_eq_decide.mpr
    simp only [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
      Int.reduceSub, Int.reduceAdd, Int.reduceToNat, Nat.reduceAdd, Nat.reduceSub,
      Nat.shiftRight_zero, pow_zero, Nat.div_one, Nat.reducePow, Nat.cast_ofNat]
    omega
  rw [hb]
  by_cases hz : z % 2 = 1 <;> simp [hz]

/-- The value of a nonnegative finite binary32 word: its floor and its error. -/
theorem rint_pos (m : ℕ) :
    round_down ((m : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) = ((m / 2 ^ 149 : ℕ) : ℤ) ∧
      sub_real ((m : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) (to_real ((m / 2 ^ 149 : ℕ) : ℤ)) =
        ((m % 2 ^ 149 : ℕ) : ℝ) / ((2 ^ 149 : ℕ) : ℝ) := by
  rw [scale_149]
  exact ⟨floor_div_nat _ _, err_div _ _ (Nat.two_pow_pos 149)⟩

/-- The value of a negative finite binary32 word whose magnitude is a multiple of 2^149. -/
theorem rint_neg0 (m : ℕ) (hr : m % 2 ^ 149 = 0) :
    round_down (-(m : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) = -((m / 2 ^ 149 : ℕ) : ℤ) ∧
      sub_real (-(m : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) (to_real (-((m / 2 ^ 149 : ℕ) : ℤ))) = 0 := by
  refine ⟨(fix32_neg0 m hr).1, ?_⟩
  rw [neg_mul, scale_149, nat_div_exact m _ (Nat.two_pow_pos 149) hr]
  simp only [sub_real, to_real, Int.cast_neg, Int.cast_natCast, sub_self]

/-- The value of a negative finite binary32 word whose magnitude is not a multiple of 2^149. -/
theorem rint_neg1 (m : ℕ) (hr : m % 2 ^ 149 ≠ 0) :
    round_down (-(m : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) = -((m / 2 ^ 149 : ℕ) : ℤ) - 1 ∧
      sub_real (-(m : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) (to_real (-((m / 2 ^ 149 : ℕ) : ℤ) - 1)) =
        ((2 ^ 149 - m % 2 ^ 149 : ℕ) : ℝ) / ((2 ^ 149 : ℕ) : ℝ) := by
  refine ⟨(fix32_neg1 m hr).1, ?_⟩
  rw [neg_mul, scale_149]
  have hd : 0 < 2 ^ 149 := Nat.two_pow_pos 149
  obtain ⟨hx, -, -⟩ := nat_div_parts m _ hd
  have hlt : m % 2 ^ 149 < 2 ^ 149 := Nat.mod_lt _ hd
  have hd' : ((2 ^ 149 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [sub_real, to_real, Int.cast_sub, Int.cast_neg, Int.cast_one, Int.cast_natCast, hx,
    Nat.cast_sub hlt.le]
  field_simp
  ring

/-- FPRoundInt's integer for the value of a finite binary32 word with the sign `g` and the
magnitude `m`, rounding with ties to even, is `±(roundShift m 149)`. -/
theorem rint_eq (g : Bool) (m : ℕ) (v : ℝ)
    (hv : v = ((if g then -(m : ℤ) else (m : ℤ) : ℤ) : ℝ) * (2 : ℝ) ^ (-149 : ℤ)) :
    (if (gt_real (sub_real v (to_real (round_down v))) (1 / 2) ||
        eq_real (sub_real v (to_real (round_down v))) (1 / 2) &&
          BitVec.join1 [integer_access (round_down v) 0] == 1#1) = true then round_down v + 1
      else round_down v) =
      if g then -((Wasm.IEEE32.roundShift m 149 : ℕ) : ℤ)
      else ((Wasm.IEEE32.roundShift m 149 : ℕ) : ℤ) := by
  subst hv
  have hd : 0 < 2 ^ 149 := Nat.two_pow_pos 149
  have hlt : m % 2 ^ 149 < 2 ^ 149 := Nat.mod_lt _ hd
  rw [roundShift_eq m 149 (by norm_num), join1_beq]
  cases g
  · simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_natCast]
    rw [(rint_pos m).1, (rint_pos m).2, gt_half _ _ hd, eq_half _ _ hd, int_access]
    generalize m / 2 ^ 149 = q
    generalize m % 2 ^ 149 = r at hlt ⊢
    generalize 2 ^ 149 = d at hd hlt ⊢
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    split_ifs <;> push_cast <;> omega
  · simp only [↓reduceIte, Int.cast_neg, Int.cast_natCast]
    by_cases hr0 : m % 2 ^ 149 = 0
    · rw [(rint_neg0 m hr0).1, (rint_neg0 m hr0).2, hr0]
      have g0 : gt_real (0 : ℝ) (1 / 2) = false := by simp [gt_real]
      have e0 : eq_real (0 : ℝ) (1 / 2) = false := by simp [eq_real]
      simp only [g0, e0, Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      generalize m / 2 ^ 149 = q
      generalize 2 ^ 149 = d at hd ⊢
      split_ifs <;> push_cast <;> omega
    · rw [(rint_neg1 m hr0).1, (rint_neg1 m hr0).2, gt_half _ _ hd, eq_half _ _ hd, int_accessZ]
      generalize m / 2 ^ 149 = q
      generalize m % 2 ^ 149 = r at hlt hr0 ⊢
      generalize 2 ^ 149 = d at hd hlt ⊢
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      split_ifs <;> push_cast <;> omega

/-! ## The exactness of the integer -/

/-- `n · 2^149` is 0 or has at most 24 significant bits and an exponent field below 255. -/
def Rep32 (n : ℕ) : Prop :=
  n = 0 ∨ ∃ q j : ℕ, n * 2 ^ 149 = q * 2 ^ j ∧ 2 ^ 23 ≤ q ∧ q < 2 ^ 24 ∧ j + 1 < 255

theorem rep_small (n : ℕ) (hn : n ≤ 2 ^ 23) : Rep32 n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact .inl h0
  have hl : Nat.log2 n ≤ 23 := by
    have := (Nat.log2_lt hpos.ne').mpr (show n < 2 ^ 24 by omega)
    omega
  refine .inr ⟨n * 2 ^ (23 - Nat.log2 n), Nat.log2 n + 126, ?_, ?_, ?_, by omega⟩
  · rw [Nat.mul_assoc, ← pow_add]
    congr 2
    omega
  · calc 2 ^ 23 = 2 ^ Nat.log2 n * 2 ^ (23 - Nat.log2 n) := by rw [← pow_add]; congr 1; omega
      _ ≤ n * 2 ^ (23 - Nat.log2 n) := Nat.mul_le_mul_right _ (Nat.log2_self_le hpos.ne')
  · calc n * 2 ^ (23 - Nat.log2 n) < 2 ^ (Nat.log2 n + 1) * 2 ^ (23 - Nat.log2 n) :=
          Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (Nat.two_pow_pos _)
      _ = 2 ^ 24 := by rw [← pow_add]; congr 1; omega

/-- The magnitude of a binary32 word in units of 2^-149, with Mathlib's instance of `Pow`. -/
theorem mag32_eq (x : BitVec 32) : Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec x) =
    if ex32 x = 0 then fr32 x else (2 ^ 23 + fr32 x) * 2 ^ (ex32 x - 1) := by
  simp only [Wasm.IEEE32.scaledMagnitude, t_exp32, t_frac32, beq_iff_eq]

/-- The integer to which FPRoundInt and Talos's `nearest` round a finite binary32 word is exact. -/
theorem rep_nearest (x : BitVec 32) (hf : ex32 x ≠ 255) :
    Rep32 (Wasm.IEEE32.roundShift (Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec x)) 149) := by
  have he : ex32 x < 256 := Nat.mod_lt _ (by decide)
  have hfr : fr32 x < 2 ^ 23 := Nat.mod_lt _ (by decide)
  have hd : 0 < 2 ^ 149 := Nat.two_pow_pos 149
  rw [roundShift_eq _ 149 (by norm_num), mag32_eq]
  generalize ex32 x = e at he hf
  generalize fr32 x = f at hfr
  by_cases h150 : 150 ≤ e
  · have hm : (2 ^ 23 + f) * 2 ^ (e - 1) = (2 ^ 23 + f) * 2 ^ (e - 150) * 2 ^ 149 := by
      rw [Nat.mul_assoc, ← pow_add]; congr 2; omega
    simp only [show e ≠ 0 by omega, ↓reduceIte, hm, Nat.mul_mod_left,
      Nat.mul_div_cancel _ hd]
    rw [ite_eq_right (by omega)]
    refine .inr ⟨2 ^ 23 + f, e - 1, ?_, by omega, by omega, by omega⟩
    rw [Nat.mul_assoc, ← pow_add]
    congr 2
    omega
  · apply rep_small
    have hm : (if e = 0 then f else (2 ^ 23 + f) * 2 ^ (e - 1)) < 2 ^ 172 := by
      split
      · exact lt_of_lt_of_le hfr (Nat.pow_le_pow_right (by norm_num) (by norm_num))
      · calc (2 ^ 23 + f) * 2 ^ (e - 1) < 2 ^ 24 * 2 ^ (e - 1) :=
              Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
          _ = 2 ^ (24 + (e - 1)) := (pow_add _ _ _).symm
          _ ≤ 2 ^ 172 := Nat.pow_le_pow_right (by norm_num) (by omega)
    generalize (if e = 0 then f else (2 ^ 23 + f) * 2 ^ (e - 1)) = m at hm
    have hq : m / 2 ^ 149 < 2 ^ 23 := by
      rw [Nat.div_lt_iff_lt_mul hd, ← pow_add]; exact hm
    split_ifs <;> omega

/-! ## Talos's side -/

/-- Talos's rounding of a finite nonzero binary32 word to an integral value, ties to even.  The
two sides elaborate `2 ^ 149 : ℕ` with different instances of `Pow`, as in `fromInt32_nat`. -/
theorem nearest_fin (neg : Bool) (m : ℕ) :
    Wasm.IEEE32.roundIntegralFinite .nearest neg m =
      Wasm.IEEE32.roundScaledMagnitude neg (Wasm.IEEE32.roundShift m 149 * 2 ^ 149) := by
  rfl

/-- The real of a signed integer `±n` as the rational of `round_zeroQ32`. -/
theorem rint_val (g : Bool) (n : ℕ) :
    to_real (if g then -((n : ℕ) : ℤ) else ((n : ℕ) : ℤ)) = qop g (n * 2 ^ 149) 1 149 := by
  have e : ((n * 2 ^ 149 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) * (2 : ℝ) ^ (-(149 : ℤ)) = (n : ℝ) := by
    rw [Nat.cast_one, div_one, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc,
      ← zpow_natCast (2 : ℝ) 149, ← zpow_add₀ two_ne_zero]
    norm_num
  unfold qop
  rw [e]
  cases g <;> simp [to_real]

theorem rint_zero (g : Bool) (n : ℕ) :
    eq_real (to_real (if g then -((n : ℕ) : ℤ) else ((n : ℕ) : ℤ))) 0 = decide (n = 0) := by
  cases g <;> simp [eq_real, to_real]

/-- The bits of FPSR that FPRoundInt sets for a binary32 operand under FPCR 0x02000000, rounding
with ties to even and without the inexact exception: IOC for a signaling NaN. -/
def rintMask32 (a : BitVec 32) : BitVec 64 := if ty32 a == .FPType_SNaN then 1#64 else 0#64

set_option maxHeartbeats 75000 in
theorem fpRoundInt32_run (a : BitVec 32) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRoundInt a fpcrV .FPRounding_TIEEVEN false).run s =
        .ok (Wasm.f32Nearest (.ofBitVec a)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| rintMask32 a) ∧ Frame s s' := by
  subst hs
  simp only [FPRoundInt]
  sail_simp [bne, h.hfi, h.hps, h.nrw, h.aa64]
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run32 a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  simp only [Wasm.f32Nearest, Wasm.IEEE32.nearest, Wasm.IEEE32.roundIntegral, t_isNaN32,
    t_isInf32, mag32_beq_zero, rintMask32]
  cases ha : ty32 a <;> simp only [isNaNT] <;> sail_simp []
  -- The finite nonzero operands.
  case FPType_Denormal | FPType_Nonzero =>
       have hfa : ex32 a ≠ 255 :=
         ty32_fin a (by rw [ha]; exact fun h => FPType.noConfusion h) (by rw [ha]; rfl)
       have hrep := rep_nearest a hfa
       rw [val32_fin a hfa, sv32_eq, t_sign32, nearest_fin]
       unfold sgBit32
       generalize Wasm.IEEE32.scaledMagnitude (UInt32.ofBitVec a) = m at hrep ⊢
       generalize sg32 a = g
       rw [rint_eq g m _ rfl]
       generalize Wasm.IEEE32.roundShift m 149 = n at hrep ⊢
       sail_simp [rint_zero, bind_pure]
       rcases hrep with rfl | ⟨q, j, hn, hq1, hq2, hj⟩
       · sail_simp [FPZero]
         refine ⟨_, ok_congr ?_, ?_, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
         · rw [Nat.zero_mul]
           cases g <;> decide
         · rw [BitVec.or_zero, bump_regs, bump_regs, hr1]
           exact (insert_self _ _ _ h.hfpsr).symm
       · have hn0 : n ≠ 0 := by
           intro h0; subst h0
           rw [Nat.zero_mul] at hn
           have := Nat.mul_pos (show 0 < q by omega) (Nat.two_pow_pos j)
           omega
         have hP : 0 < n * 2 ^ 149 := Nat.mul_pos (Nat.pos_of_ne_zero hn0) (Nat.two_pow_pos _)
         have hL : Nat.log2 (n * 2 ^ 149 / 1) = j + 23 := by
           rw [Nat.div_one, hn]
           apply log2_eq
           · rw [pow_add, Nat.mul_comm (2 ^ j)]; exact Nat.mul_le_mul_right _ hq1
           · rw [show j + 23 + 1 = 24 + j by omega, pow_add]
             exact Nat.mul_lt_mul_of_pos_right hq2 (Nat.two_pow_pos j)
         have hr0 : n * 2 ^ 149 % (1 * 2 ^ j) = 0 := by
           rw [Nat.one_mul, hn, Nat.mul_mod_left]
         simp only [hn0, decide_false, Bool.false_eq_true, ↓reduceIte, FPRound__1, rint_val]
         rw [rsm_eq_rrm32 _ _ hP]
         obtain ⟨s', e1, e2, e3⟩ := round_zeroQ32 g (n * 2 ^ 149) 1 j 149 rfl hP Nat.one_pos hL hr0
           hj h (s := bump .bool (bump (.bitvector 32) σ1)) hr1
         refine ⟨s', e1, ?_, hf1.trans ⟨e3.mem, e3.tags, e3.cyc, e3.out⟩⟩
         rw [e2, BitVec.or_zero]
         exact (insert_self _ _ _ h.hfpsr).symm
  -- The NaNs, the infinities, and the zeros.
  all_goals (
    try simp only [FPProcessNaN, FPProcessNaN__1]
    try dsimp only [Sail.BitVec.length]
    try sail_simp [FPDefaultNaN__1, FPProcessException, FPZero, FPInfinity, hr1, h.hfi, h.hps,
      h.nrw, h.aa64, h.fa, h.hfpsr, setReg_regs, cast_eq, ite_self]
    try rw [zero_word32 a (by assumption)]
    try rw [inf_word32 a (by assumption)]
    try unfold sgBit32
    try simp only [canonicalNaN32_bv]
    refine ⟨_, ok_congr ?v, ?r, ⟨hf1.mem, hf1.tags, hf1.cyc, hf1.out⟩⟩
    case v => cases sg32 a <;> decide
    case r =>
      try simp only [setReg_regs, bump_regs, faS_regs, hr1]
      first
      | (rw [BitVec.or_zero]; exact (insert_self _ _ _ h.hfpsr).symm)
      | simp only [upd_or _ _ (by norm_num : 0 < 64), (or_masks _).2.2.1])

/-- FPRoundInt of a binary32 word under FPCR 0x02000000, rounding with ties to even and without the
inexact exception, returns Talos's `f32Nearest` for every word from every state that satisfies the
state hypothesis.  FPSR becomes `fpsr ||| rintMask32 a`, and the other registers, the memory, the
tags, the cycle count, and the output do not change. -/
theorem fpRoundInt32_eq_f32Nearest (a : BitVec 32) (s : State) (fi : Vector Bool 259)
    (ps : ProcState) (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPRoundInt a fpcrV .FPRounding_TIEEVEN false).run s =
        .ok (Wasm.f32Nearest (UInt32.ofBitVec a)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| rintMask32 a) ∧ Frame s s' :=
  fpRoundInt32_run a h rfl

end F7
