import F7.Round

/-!
The rounding of FPRoundBase__1 at 64 bits under FPCR 0x02000000 for a positive real number `M`
whose result is normal, stated over the scaled mantissa rather than over a quotient of naturals.
`round_normalR` takes the exponent `E = j − 1022` of `M` (`1 ≤ M · 2^-E < 2`), the scaled mantissa
`x = M · 2^-E · 2^52`, its floor `q`, its error `x − q`, and the three comparisons of the error
with 1/2 and 0 as decisions of the propositions `Pu`, `Pt`, and `Pz`.  It gives Talos's
`roundScaledMagnitude` of the rounded mantissa times `2^j` and the FPSR bits of `maskN`.  The
proof follows `round_normalG` (`F7/Round.lean`), whose quotient and remainder it replaces by these
hypotheses, so that FPSqrt, whose scaled mantissa is a square root, can use it.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

/-- The exponent of a positive real in `[2^e, 2^(e+1))` is unique. -/
theorem exp_unique (M : ℝ) (e e' : ℤ) (h1 : 1 ≤ M * 2 ^ (-e)) (h2 : M * 2 ^ (-e) < 2)
    (h1' : 1 ≤ M * 2 ^ (-e')) (h2' : M * 2 ^ (-e') < 2) : e = e' := by
  have key : ∀ u v : ℤ, 1 ≤ M * 2 ^ (-u) → M * 2 ^ (-v) < 2 → ¬ v < u := by
    intro u v hu hv hlt
    have hM : M * 2 ^ (-v) = M * 2 ^ (-u) * 2 ^ (u - v) := by
      rw [mul_assoc, ← zpow_add₀ two_ne_zero]; ring_nf
    have hp : (2 : ℝ) ≤ 2 ^ (u - v) := by
      calc (2 : ℝ) = 2 ^ (1 : ℤ) := by norm_num
        _ ≤ 2 ^ (u - v) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    nlinarith
  have a := key e e' h1 h2'
  have b := key e' e h1' h2
  omega

/-- Talos's packing of the rounded integer mantissa `q` or `q + 1` times `2^j`, for
`2^52 ≤ q < 2^53`. -/
theorem tRound_normal (q j : ℕ) (up : Prop) [Decidable up] (hq1 : 2 ^ 52 ≤ q) (hq2 : q < 2 ^ 53) :
    tRound false ((if up then q + 1 else q) * 2 ^ j) =
      (if up then
        (if q + 1 = 2 ^ 53 then
          (if 2047 ≤ j + 2 then (Wasm.IEEE64.infinity false).toBitVec
           else (Wasm.IEEE64.encodeFinite false (j + 2) 0).toBitVec)
         else (if 2047 ≤ j + 1 then (Wasm.IEEE64.infinity false).toBitVec
           else (Wasm.IEEE64.encodeFinite false (j + 1) (q + 1 - 2 ^ 52)).toBitVec))
       else (if 2047 ≤ j + 1 then (Wasm.IEEE64.infinity false).toBitVec
         else (Wasm.IEEE64.encodeFinite false (j + 1) (q - 2 ^ 52)).toBitVec)) := by
  unfold tRound
  by_cases hup : up
  · rw [if_pos hup, if_pos hup]
    by_cases hc : q + 1 = 2 ^ 53
    · rw [if_pos hc, hc, rsm_carry]
      split_ifs <;> rfl
    · rw [if_neg hc, rsm_exact false (q + 1) j (by omega) (by omega)]
      split_ifs <;> rfl
  · rw [if_neg hup, if_neg hup, rsm_exact false q j hq1 hq2]
    split_ifs <;> rfl

/-- The bits of FPSR that FPRoundBase__1 sets for a positive normal result with the integer
mantissa `q`, the exponent field `j + 1`, the direction `up`, and the exactness `exact`: OFC and
IXC on overflow, and IXC on an inexact result. -/
def maskN (q j : ℕ) (up exact : Prop) [Decidable up] [Decidable exact] : BitVec 64 :=
  if 2047 ≤ (if up ∧ q + 1 = 2 ^ 53 then j + 2 else j + 1) then 0x14#64
  else if exact then 0#64 else 0x10#64

set_option maxHeartbeats 800000 in
/-- FPRound__2 at 64 bits under FPCR 0x02000000, rounding to nearest even, on a positive real `M`
with a normal result. -/
theorem round_normalR (M x err : ℝ) (E : ℤ) (q j : ℕ) (Pu Pt Pz : Prop) [Decidable Pu]
    [Decidable Pt] [Decidable Pz] (hM : 0 < M) (h1 : 1 ≤ M * 2 ^ (-E)) (h2 : M * 2 ^ (-E) < 2)
    (hj : E = (j : ℤ) - 1022) (hman : mult_real (M * 2 ^ (-E)) (real_power 2 52) = x)
    (hfl : round_down x = (q : ℤ)) (hq1 : 2 ^ 52 ≤ q) (hq2 : q < 2 ^ 53)
    (herr : sub_real x (to_real (q : ℤ)) = err) (hU : gt_real err (1 / 2) = decide Pu)
    (hT : eq_real err (1 / 2) = decide Pt) (hZ : (err == 0) = decide Pz)
    {R : Std.ExtDHashMap Register RegisterType} (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 M fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (tRound false ((if Pu ∨ Pt ∧ q % 2 = 1 then q + 1 else q) * 2 ^ j)) s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| maskN q j (Pu ∨ Pt ∧ q % 2 = 1) Pz) ∧ Frame s s' := by
  subst hs
  obtain ⟨e, he, he1, he2⟩ := loops_eq' _ hM
  have hE : e = E := exp_unique M e E he1 he2 h1 h2
  subst hE
  have hlt : lt_real M 0 = false := by simp [lt_real, hM.le]
  have hne : (M == 0) = false := by simp [hM.ne']
  have hb : max (e - -1022 + 1) 0 = (j : ℤ) + 1 := by omega
  have hb0 : ((j : ℤ) + 1 == 0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
  rw [tRound_normal q j _ hq1 hq2]
  simp only [maskN]
  sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self,
    whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt]
  rw [he]
  sail_simp [↓join1_beq, h.hfi, h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, ite_self, hne, bne, hlt, hb,
    hb0, hman, hfl, herr, hU, hT, hZ, int_access]
  clear he he1 he2 hlt hne hb hb0 hman hfl herr hU hT h1 h2
  simp only [ipow, Int.reduceToNat, Int.reducePow, Int.reduceSub, Int.reduceAdd, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ge_iff_le]
  have hfd : fdiv_int ((q : ℤ) + 1) 2 = ((q : ℤ) + 1) / 2 := fdiv_two _ (by omega)
  have c2 : ((q : ℤ) + 1 = 4503599627370496) = False := by simp; omega
  have o1 : (2047 ≤ (j : ℤ) + 1 + 1) = (2047 ≤ j + 2) := by
    apply propext; constructor <;> intro <;> omega
  have o2 : (2047 ≤ (j : ℤ) + 1) = (2047 ≤ j + 1) := by
    apply propext; constructor <;> intro <;> omega
  simp only [c2, ↓reduceIte]
  by_cases hup : (Pu ∨ Pt ∧ q % 2 = 1) <;>
  by_cases hc : q + 1 = 2 ^ 53 <;> by_cases hv1 : 2047 ≤ j + 1 <;> by_cases hv2 : 2047 ≤ j + 2 <;>
  by_cases hr0 : Pz
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
        h.hfpsr, ite_self, toBV_inf, toBV_encode, one_beq_zero, cast_eq, hZ, e5]
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
        (or_masks _).2.1, BitVec.or_zero, cast_eq] <;>
        first | rfl | exact (insert_self _ _ _ h.hfpsr).symm
    · exact ⟨rfl, rfl, rfl, rfl⟩)

end F7
