import F7.Round

/-!
The rounding of FPRoundBase__1 at 64 bits under FPCR 0x02000000 on a rational number
`±(P/Q) · 2^-1074`, the form of FPDiv's exact quotient.

`fpRound_q` states what FPRound__2 returns on `±(P/Q) · 2^-1074` for all positive naturals `P` and
`Q`: Talos's `roundRationalMagnitude neg P Q`, the two-stage rounder of `IEEE64.div`, and the FPSR
bits of `maskQ P Q`.  The proof splits the normal results, `2^52 ≤ ⌊P/Q⌋` (`round_normalQ`), from
the subnormal ones (`round_subQ`).  For a normal result with `log2 ⌊P/Q⌋ = 52 + j`, the loops give
the exponent `j − 1022` (`exp_eqR`), FPRoundBase__1's integer mantissa is the quotient of `P` by
`Q · 2^j`, and its error is the remainder over `Q · 2^j` (`man_normalQ`).  For a subnormal one
the divisor is `Q` (`man_subQ`).  `rq_normal` and `rq_sub` state Talos's two stages over the same
quotient and remainder: `roundQuotient` rounds `P` over the divisor to the nearest integer, ties to
even, and `roundScaledMagnitude` of that integer times `2^j` is exact (`rsm_exact`, `rsm_carry`).
A subnormal result that is inexact sets FPSR.UFC, since FPRoundBase__1 detects tininess before
rounding.

The statements write Talos's word as `(roundRationalMagnitude neg P Q).toBitVec`, where
`F7/Round.lean` names the dyadic rounder's word through the definition `tDy`.  With such a
definition, the kernel's check that it equals the word of `f64Div` at `P = A · 2^1074` ran past
60 s and 2 GB, even on identical arguments.  With `roundRationalMagnitude` on both sides the
check takes under 2 s.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

/-! ## Talos's rounder of a quotient -/

theorem roundQuotient_eq (n d : ℕ) (hd : 0 < d) :
    Wasm.IEEE32.roundQuotient n d =
      if (d < 2 * (n % d) ∨ 2 * (n % d) = d ∧ (n / d) % 2 = 1) then n / d + 1 else n / d := by
  have hd' : (d == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  simp only [Wasm.IEEE32.roundQuotient, hd', Bool.false_eq_true, ↓reduceIte]
  generalize n / d = q
  generalize n % d = r
  simp only [beq_iff_eq]
  split_ifs <;> omega

/-- The quotient of `P` by `Q · 2^j` has 53 bits when `log2 ⌊P/Q⌋ = j + 52`. -/
theorem q_bounds (P Q j : ℕ) (hk : Nat.log2 (P / Q) = j + 52) :
    2 ^ 52 ≤ P / (Q * 2 ^ j) ∧ P / (Q * 2 ^ j) < 2 ^ 53 := by
  have hI0 : P / Q ≠ 0 := by intro h0; rw [h0, Nat.log2_zero] at hk; omega
  have hL1 : 2 ^ (j + 52) ≤ P / Q := by rw [← hk]; exact Nat.log2_self_le hI0
  have hL2 : P / Q < 2 ^ (j + 52 + 1) := by rw [← hk]; exact Nat.lt_log2_self
  rw [← Nat.div_div_eq_div_mul]
  constructor
  · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _)]
    rw [show j + 52 = 52 + j by omega, pow_add] at hL1; exact hL1
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    rw [show j + 52 + 1 = 53 + j by omega, pow_add] at hL2; exact hL2

/-- Talos's two stages for a normal result: the quotient `q` of `P` by `Q · 2^j` rounds to
nearest even, with a carry into the exponent and an overflow to infinity. -/
theorem rq_normal (neg : Bool) (P Q j q r : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    (hk : Nat.log2 (P / Q) = j + 52) (hq : P / (Q * 2 ^ j) = q) (hr : P % (Q * 2 ^ j) = r) :
    (Wasm.IEEE64.roundRationalMagnitude neg P Q).toBitVec =
      (if (Q * 2 ^ j < 2 * r ∨ 2 * r = Q * 2 ^ j ∧ q % 2 = 1) then
        (if q + 1 = 2 ^ 53 then
          (if 2047 ≤ j + 2 then (Wasm.IEEE64.infinity neg).toBitVec
           else (Wasm.IEEE64.encodeFinite neg (j + 2) 0).toBitVec)
         else (if 2047 ≤ j + 1 then (Wasm.IEEE64.infinity neg).toBitVec
           else (Wasm.IEEE64.encodeFinite neg (j + 1) (q + 1 - 2 ^ 52)).toBitVec))
       else (if 2047 ≤ j + 1 then (Wasm.IEEE64.infinity neg).toBitVec
         else (Wasm.IEEE64.encodeFinite neg (j + 1) (q - 2 ^ 52)).toBitVec)) := by
  obtain ⟨hq1, hq2⟩ := q_bounds P Q j hk
  rw [hq] at hq1 hq2
  have hd : 0 < Q * 2 ^ j := Nat.mul_pos hQ (Nat.two_pow_pos _)
  have hcand : (if Nat.log2 (P / Q) - 52 == 0 then Wasm.IEEE32.roundQuotient P Q
      else Wasm.IEEE32.roundQuotient P (Q * 2 ^ (Nat.log2 (P / Q) - 52)) *
        2 ^ (Nat.log2 (P / Q) - 52)) =
      (if (Q * 2 ^ j < 2 * r ∨ 2 * r = Q * 2 ^ j ∧ q % 2 = 1) then q + 1 else q) * 2 ^ j := by
    rw [hk, show j + 52 - 52 = j by omega]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp only [pow_zero, Nat.mul_one, beq_self_eq_true, ite_true] at hq hr ⊢
      rw [roundQuotient_eq _ _ hQ, hq, hr]
    · have hj' : (j == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
      rw [hj', ite_eq_right (by simp), roundQuotient_eq _ _ hd, hq, hr]
  unfold Wasm.IEEE64.roundRationalMagnitude
  have hP0 : (P == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  have hQ0 : (Q == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  simp only [hP0, hQ0, Bool.false_eq_true, ite_false]
  rw [hcand]
  by_cases hup : (Q * 2 ^ j < 2 * r ∨ 2 * r = Q * 2 ^ j ∧ q % 2 = 1)
  · rw [ite_eq_left hup, ite_eq_left hup]
    by_cases hc : q + 1 = 2 ^ 53
    · rw [ite_eq_left hc, hc, rsm_carry]
      split_ifs <;> rfl
    · rw [ite_eq_right hc, rsm_exact neg (q + 1) j (by omega) (by omega)]
      split_ifs <;> rfl
  · rw [ite_eq_right hup, ite_eq_right hup, rsm_exact neg q j hq1 hq2]
    split_ifs <;> rfl

/-- Talos's two stages for a subnormal result: the quotient `q` of `P` by `Q` rounds to nearest
even, and a carry gives the smallest normal number. -/
theorem rq_sub (neg : Bool) (P Q q r : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hL : P / Q < 2 ^ 52)
    (hq : P / Q = q) (hr : P % Q = r) :
    (Wasm.IEEE64.roundRationalMagnitude neg P Q).toBitVec =
      if (Q < 2 * r ∨ 2 * r = Q ∧ q % 2 = 1) then
        (if q + 1 = 2 ^ 52 then (Wasm.IEEE64.encodeFinite neg 1 0).toBitVec
         else (Wasm.IEEE64.encodeFinite neg 0 (q + 1)).toBitVec)
      else (Wasm.IEEE64.encodeFinite neg 0 q).toBitVec := by
  have hlog : Nat.log2 (P / Q) - 52 = 0 := by
    rcases Nat.eq_zero_or_pos (P / Q) with h0 | h0
    · rw [h0, Nat.log2_zero]
    · have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp h0)).mpr hL
      omega
  have hq2 : q < 2 ^ 52 := hq ▸ hL
  unfold Wasm.IEEE64.roundRationalMagnitude
  have hP0 : (P == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  have hQ0 : (Q == 0) = false := by simp only [beq_eq_false_iff_ne]; omega
  simp only [hP0, hQ0, Bool.false_eq_true, ite_false, hlog, beq_self_eq_true, ite_true]
  rw [roundQuotient_eq _ _ hQ, hq, hr]
  unfold Wasm.IEEE64.roundScaledMagnitude
  by_cases hup : (Q < 2 * r ∨ 2 * r = Q ∧ q % 2 = 1)
  · rw [ite_eq_left hup, ite_eq_left hup]
    by_cases hc : q + 1 = 2 ^ 52
    · rw [ite_eq_left hc, hc, ite_eq_right (by norm_num), ite_eq_left (by norm_num)]
      simp
    · rw [ite_eq_right hc, ite_eq_left (by omega)]
  · rw [ite_eq_right hup, ite_eq_right hup, ite_eq_left hq2]

/-- The bits of FPSR that FPRoundBase__1 sets for the magnitude `P / Q` in units of 2^-1074, at
64 bits under FPCR 0x02000000: OFC and IXC on overflow, IXC on an inexact result, and UFC with IXC
on an inexact subnormal result. -/
def maskQ (P Q : ℕ) : BitVec 64 :=
  let j := Nat.log2 (P / Q) - 52
  let q := P / (Q * 2 ^ j)
  let r := P % (Q * 2 ^ j)
  if 2 ^ 52 ≤ P / Q then
    (if 2047 ≤ (if (Q * 2 ^ j < 2 * r ∨ 2 * r = Q * 2 ^ j ∧ q % 2 = 1) ∧ q + 1 = 2 ^ 53
        then j + 2 else j + 1) then 0x14#64
     else if r = 0 then 0#64 else 0x10#64)
  else if r = 0 then 0#64 else 0x18#64

/-! ## The real number and FPRoundBase__1's exponent and mantissa -/

/-- The real number `±(P/Q) · 2^-S`. -/
noncomputable def qop (neg : Bool) (P Q : ℕ) (S : ℤ) : ℝ :=
  if neg then -((P : ℝ) / (Q : ℝ) * (2 : ℝ) ^ (-S)) else (P : ℝ) / (Q : ℝ) * (2 : ℝ) ^ (-S)

theorem qop_facts (neg : Bool) (P Q : ℕ) (S : ℤ) (hP : 0 < P) (hQ : 0 < Q) :
    lt_real (qop neg P Q S) 0 = neg ∧ (qop neg P Q S == 0) = false ∧
      neg_real (-((P : ℝ) / (Q : ℝ) * (2 : ℝ) ^ (-S))) = (P : ℝ) / (Q : ℝ) * (2 : ℝ) ^ (-S) := by
  have hM : (0 : ℝ) < (P : ℝ) / (Q : ℝ) * (2 : ℝ) ^ (-S) :=
    mul_pos (div_pos (by exact_mod_cast hP) (by exact_mod_cast hQ)) (zpow_pos (by norm_num) _)
  unfold qop
  generalize (P : ℝ) / (Q : ℝ) * (2 : ℝ) ^ (-S) = M at hM ⊢
  refine ⟨?_, ?_, by simp [neg_real]⟩
  · cases neg <;> simp [lt_real, hM, hM.le]
  · cases neg <;> simp [hM.ne']

theorem div_bounds (P Q L : ℕ) (hQ : 0 < Q) (h1 : 2 ^ L ≤ P / Q) (h2 : P / Q < 2 ^ (L + 1)) :
    (2 : ℝ) ^ L ≤ (P : ℝ) / (Q : ℝ) ∧ (P : ℝ) / (Q : ℝ) < 2 ^ (L + 1) := by
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have e1 : 2 ^ L * Q ≤ P := (Nat.le_div_iff_mul_le hQ).mp h1
  have e2 : P < 2 ^ (L + 1) * Q := (Nat.div_lt_iff_lt_mul hQ).mp h2
  constructor
  · rw [le_div_iff₀ hQ']; exact_mod_cast e1
  · rw [div_lt_iff₀ hQ']; exact_mod_cast e2

/-- The exponent that FPRoundBase__1's loops give for `x · 2^-S` with `2^L ≤ x < 2^(L+1)`. -/
theorem exp_eqR (x : ℝ) (L : ℕ) (S e : ℤ) (hx1 : (2 : ℝ) ^ L ≤ x) (hx2 : x < 2 ^ (L + 1))
    (h1 : 1 ≤ x * (2 : ℝ) ^ (-S) * 2 ^ (-e)) (h2 : x * (2 : ℝ) ^ (-S) * 2 ^ (-e) < 2) :
    e = (L : ℤ) - S := by
  have hr1 : ((2 : ℝ) ^ (L : ℤ)) ≤ x := by rw [zpow_natCast]; exact hx1
  have hr2 : x < (2 : ℝ) ^ ((L : ℤ) + 1) := by
    rw [show ((L : ℤ) + 1) = ((L + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]; exact hx2
  have ht : x * (2 : ℝ) ^ (-S) * 2 ^ (-e) = x * 2 ^ (-S - e) := by
    rw [mul_assoc, ← zpow_add₀ two_ne_zero]; ring_nf
  rw [ht] at h1 h2
  have hpos : (0 : ℝ) < 2 ^ (-S - e) := zpow_pos (by norm_num) _
  have a1 : (2 : ℝ) ^ (0 : ℤ) < 2 ^ ((L : ℤ) + 1 + (-S - e)) := by
    rw [zpow_add₀ two_ne_zero, zpow_zero]
    calc (1 : ℝ) ≤ x * 2 ^ (-S - e) := h1
      _ < 2 ^ ((L : ℤ) + 1) * 2 ^ (-S - e) := mul_lt_mul_of_pos_right hr2 hpos
  have a2 : (2 : ℝ) ^ ((L : ℤ) + (-S - e)) < 2 ^ (1 : ℤ) := by
    rw [zpow_add₀ two_ne_zero, zpow_one]
    calc (2 : ℝ) ^ (L : ℤ) * 2 ^ (-S - e) ≤ x * 2 ^ (-S - e) :=
          mul_le_mul_of_nonneg_right hr1 hpos.le
      _ < 2 := h2
  rw [zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)] at a1 a2
  omega

/-- The exponent of `x · 2^-1074` with `x < 2^52` lies below the minimum normal exponent. -/
theorem exp_subR (x : ℝ) (S e : ℤ) (hS : S = 1074) (hx : x < 2 ^ 52)
    (h1 : 1 ≤ x * (2 : ℝ) ^ (-S) * 2 ^ (-e)) : e < -1022 := by
  have ht : x * (2 : ℝ) ^ (-S) * 2 ^ (-e) = x * 2 ^ (-S - e) := by
    rw [mul_assoc, ← zpow_add₀ two_ne_zero]; ring_nf
  rw [ht] at h1
  have hpos : (0 : ℝ) < 2 ^ (-S - e) := zpow_pos (by norm_num) _
  have hx' : x < (2 : ℝ) ^ (52 : ℤ) := by rw [zpow_ofNat]; exact hx
  have a1 : (2 : ℝ) ^ (0 : ℤ) < 2 ^ ((52 : ℤ) + (-S - e)) := by
    rw [zpow_add₀ two_ne_zero, zpow_zero]
    calc (1 : ℝ) ≤ x * 2 ^ (-S - e) := h1
      _ < 2 ^ (52 : ℤ) * 2 ^ (-S - e) := mul_lt_mul_of_pos_right hx' hpos
  rw [zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)] at a1
  omega

theorem man_normalQ (P Q j : ℕ) (S e : ℤ) (hS : S = 1074) (hE : e = (j : ℤ) - 1022) :
    mult_real ((P : ℝ) / (Q : ℝ) * 2 ^ (-S) * 2 ^ (-e)) (real_power 2 52) =
      (P : ℝ) / ((Q * 2 ^ j : ℕ) : ℝ) := by
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp only [mult_real, real_power]
  rw [mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero,
    show -S + (-e + 52) = -(j : ℤ) by omega, zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_div]

theorem man_subQ (x : ℝ) (S e : ℤ) (hS : S = 1074) :
    mult_real (div_real (x * 2 ^ (-S) * 2 ^ (-e)) (real_power 2 (-1022 - e)))
      (real_power 2 52) = x := by
  simp only [mult_real, div_real, real_power]
  rw [div_eq_mul_inv, ← zpow_neg, mul_assoc, mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero,
    ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero,
    show -S + (-e + (-(-1022 - e) + 52)) = 0 by omega, zpow_zero, mul_one]

/-! ## FPRoundBase__1 -/

set_option maxHeartbeats 1300000 in
theorem round_normalQ (neg : Bool) (P Q j : ℕ) (S : ℤ) (hS : S = 1074) (hP : 0 < P) (hQ : 0 < Q)
    (hL : Nat.log2 (P / Q) = j + 52) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (qop neg P Q S) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (Wasm.IEEE64.roundRationalMagnitude neg P Q).toBitVec s' ∧
        s'.regs = R.insert .FPSR (fpsr ||| maskQ P Q) ∧ Frame s s' := by
  subst hs
  have hM : (0 : ℝ) < (P : ℝ) / (Q : ℝ) * (2 : ℝ) ^ (-S) :=
    mul_pos (div_pos (by exact_mod_cast hP) (by exact_mod_cast hQ)) (zpow_pos (by norm_num) _)
  obtain ⟨e, he, h1, h2⟩ := loops_eq' _ hM
  have hI0 : P / Q ≠ 0 := by intro h0; rw [h0, Nat.log2_zero] at hL; omega
  obtain ⟨hx1, hx2⟩ := div_bounds P Q (j + 52) hQ (by rw [← hL]; exact Nat.log2_self_le hI0)
    (by rw [← hL]; exact Nat.lt_log2_self)
  have hE0 := exp_eqR _ (j + 52) S e hx1 hx2 h1 h2
  have hE : e = (j : ℤ) - 1022 := by omega
  obtain ⟨hlt, hne, hneg⟩ := qop_facts neg P Q S hP hQ
  have hman := man_normalQ P Q j S e hS hE
  have hb : max (e - -1022 + 1) 0 = (j : ℤ) + 1 := by omega
  have hb0 : ((j : ℤ) + 1 == 0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  have hd : 0 < Q * 2 ^ j := Nat.mul_pos hQ (Nat.two_pow_pos _)
  have hmask : maskQ P Q = (let q := P / (Q * 2 ^ j); let r := P % (Q * 2 ^ j)
      if 2047 ≤ (if (Q * 2 ^ j < 2 * r ∨ 2 * r = Q * 2 ^ j ∧ q % 2 = 1) ∧ q + 1 = 2 ^ 53
        then j + 2 else j + 1) then 0x14#64 else if r = 0 then 0#64 else 0x10#64) := by
    have h52 : 2 ^ 52 ≤ P / Q := (Nat.le_log2 hI0).mp (by omega)
    simp only [maskQ, hL, h52, ite_true, show j + 52 - 52 = j by omega]
  rw [hmask, rq_normal neg P Q j _ _ hP hQ hL rfl rfl]
  obtain ⟨hq1, hq2⟩ := q_bounds P Q j hL
  have hr : P % (Q * 2 ^ j) < Q * 2 ^ j := Nat.mod_lt _ hd
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, qop] at hlt hne ⊢
  all_goals (
    sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self,
      whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt, hneg]
    rw [he]
    sail_simp [↓join1_beq, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self, hne, bne, hlt, hb,
      hb0, hman, floor_div_nat, err_div _ _ hd, gt_half _ _ hd, eq_half _ _ hd,
      beq_zero_div _ _ hd, int_access]
    generalize hq : P / (Q * 2 ^ j) = q at *
    generalize hrr : P % (Q * 2 ^ j) = r at *
    generalize hdd : Q * 2 ^ j = d at *
    clear he h1 h2 hlt hne hb hb0 hmask hE hE0 hman hx1 hx2
    simp only [ipow, Int.reduceToNat, Int.reducePow, Int.reduceSub, Int.reduceAdd, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ge_iff_le]
    have hfd : fdiv_int ((q : ℤ) + 1) 2 = ((q : ℤ) + 1) / 2 := fdiv_two _ (by omega)
    have c2 : ((q : ℤ) + 1 = 4503599627370496) = False := by simp; omega
    have o1 : (2047 ≤ (j : ℤ) + 1 + 1) = (2047 ≤ j + 2) := by
      apply propext; constructor <;> intro <;> omega
    have o2 : (2047 ≤ (j : ℤ) + 1) = (2047 ≤ j + 1) := by
      apply propext; constructor <;> intro <;> omega
    simp only [c2, ↓reduceIte]
    by_cases hup : (d < 2 * r ∨ 2 * r = d ∧ q % 2 = 1) <;>
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
      simp only [hcI, e1, e2, e3, e4, e5, and_true, and_false, ↓reduceIte]
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
           all_goals first | decide | omega)
      · simp only [setReg_regs, bump_regs, faS_regs, insert_insert,
          upd_or _ _ (by norm_num : 2 < 64), upd_or _ _ (by norm_num : 4 < 64), (or_masks _).1,
          (or_masks _).2.1, BitVec.or_zero] <;>
          first | rfl | exact (insert_self _ _ _ h.hfpsr).symm
      · exact ⟨rfl, rfl, rfl, rfl⟩))

set_option maxHeartbeats 400000 in
theorem round_subQ (neg : Bool) (P Q : ℕ) (S : ℤ) (hS : S = 1074) (hP : 0 < P) (hQ : 0 < Q)
    (hL : P / Q < 2 ^ 52) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (qop neg P Q S) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (Wasm.IEEE64.roundRationalMagnitude neg P Q).toBitVec s' ∧
        s'.regs = R.insert .FPSR (fpsr ||| maskQ P Q) ∧ Frame s s' := by
  subst hs
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hM : (0 : ℝ) < (P : ℝ) / (Q : ℝ) * (2 : ℝ) ^ (-S) :=
    mul_pos (div_pos (by exact_mod_cast hP) hQ') (zpow_pos (by norm_num) _)
  obtain ⟨e, he, h1, h2⟩ := loops_eq' _ hM
  have hx : (P : ℝ) / (Q : ℝ) < 2 ^ 52 := by
    rw [div_lt_iff₀ hQ']
    have : P < 2 ^ 52 * Q := (Nat.div_lt_iff_lt_mul hQ).mp hL
    exact_mod_cast this
  have hE := exp_subR _ S e hS hx h1
  obtain ⟨hlt, hne, hneg⟩ := qop_facts neg P Q S hP hQ
  have hb : max (e - -1022 + 1) 0 = 0 := by omega
  have hmask : maskQ P Q = (if P % Q = 0 then 0#64 else 0x18#64) := by
    have hlog : Nat.log2 (P / Q) - 52 = 0 := by
      rcases Nat.eq_zero_or_pos (P / Q) with h0 | h0
      · rw [h0, Nat.log2_zero]
      · have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp h0)).mpr hL
        omega
    simp only [maskQ, show ¬ 2 ^ 52 ≤ P / Q by omega, ite_false, hlog, pow_zero, Nat.mul_one]
  rw [hmask, rq_sub neg P Q _ _ hP hQ hL rfl rfl]
  have hr : P % Q < Q := Nat.mod_lt _ hQ
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, qop] at hlt hne ⊢
  all_goals (
    sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self,
      whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt, hneg]
    rw [he]
    sail_simp [↓join1_beq, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self, hne, bne, hlt, hb,
      man_subQ _ S e hS, floor_div_nat, err_div _ _ hQ, gt_half _ _ hQ, eq_half _ _ hQ,
      beq_zero_div _ _ hQ, int_access]
    generalize hq : P / Q = q at *
    generalize hrr : P % Q = r at *
    clear he h1 h2 hlt hne hb hmask hE hx
    simp only [ipow, Int.reduceToNat, Int.reducePow, Int.reduceSub, Int.reduceAdd, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ge_iff_le]
    have c1 : ((q : ℤ) + 1 = 9007199254740992) = False := by simp; omega
    have c2 : ((q : ℤ) + 1 = 4503599627370496) = (q + 1 = 2 ^ 52) := by
      apply propext; constructor <;> intro <;> omega
    simp only [c1, c2, ↓reduceIte]
    by_cases hup : (Q < 2 * r ∨ 2 * r = Q ∧ q % 2 = 1) <;>
    by_cases hc : q + 1 = 2 ^ 52 <;> by_cases hr0 : r = 0
    all_goals first | (exfalso; omega) | skip
    all_goals (
      have e1 := by first | exact eq_false hup | exact eq_true hup
      have e2 := by first | exact eq_false hc | exact eq_true hc
      have e5 := by first | exact eq_false hr0 | exact eq_true hr0
      simp only [e1, e2, e5, ↓reduceIte, decide_true, decide_false, Bool.not_true, Bool.not_false]
      apply exists_of_run'
      · sail_simp [FPZero, FPProcessException, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr,
          ite_self, toBV_encode, one_beq_zero, beq_zero_div _ _ hQ, cast_eq, e5]
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
             rfl
           all_goals first | decide | (clear * - hc; omega))
      · simp only [setReg_regs, bump_regs, faS_regs, insert_insert,
          upd_or _ _ (by norm_num : 3 < 64), upd_or _ _ (by norm_num : 4 < 64), (or_masks _).2.2.2,
          BitVec.or_zero] <;>
          first | rfl | exact (insert_self _ _ _ h.hfpsr).symm
      · exact ⟨rfl, rfl, rfl, rfl⟩))

/-- FPRound__2 at 64 bits under FPCR 0x02000000, rounding to nearest even, on `±(P/Q) · 2^-1074`
returns Talos's `roundRationalMagnitude` and sets the FPSR bits of `maskQ P Q`. -/
theorem fpRound_q (neg : Bool) (P Q : ℕ) (hP : 0 < P) (hQ : 0 < Q)
    {R : Std.ExtDHashMap Register RegisterType} (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (qop neg P Q 1074) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (Wasm.IEEE64.roundRationalMagnitude neg P Q).toBitVec s' ∧
        s'.regs = R.insert .FPSR (fpsr ||| maskQ P Q) ∧ Frame s s' := by
  by_cases hL : 2 ^ 52 ≤ P / Q
  · have hI0 : P / Q ≠ 0 := by omega
    have h52 : 52 ≤ Nat.log2 (P / Q) := (Nat.le_log2 hI0).mpr hL
    exact round_normalQ neg P Q (Nat.log2 (P / Q) - 52) 1074 rfl hP hQ (by omega) h hs
  · exact round_subQ neg P Q 1074 rfl hP hQ (by omega) h hs

end F7
