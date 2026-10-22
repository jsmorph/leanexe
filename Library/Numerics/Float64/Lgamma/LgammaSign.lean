import Library.Numerics.Float64.Lgamma.LgammaSpecial
import LeanExe.ProofKit.F64Convert
import LeanExe.ProofKit.F64TwoSum
import LeanExe.ProofKit.GammaBasic

/-!
The second result of `Lgamma.lgammaR` is the sign of `Γ x` at every finite input other than zero
and the negative integers (`lgammaR_sign`).  `sign_code` reads the sign from the code of
`lgammaWith` without evaluating the fast path: below `1/2` in magnitude it is the sign of `x`, and
from `1/2` on it is `+1` for a positive `x` and `(-1)^m` with `m = -⌊x⌋` for a negative one, from the
parity of the word `(-floorF x).toUInt64`.  `lgamma_sign` compares that with the sign of
`Real.Gamma` from `GammaBasic.gamma_pos_of_even` and `gamma_neg_of_odd` for arbitrary tables, with
the first border `0x1ff0000` of `Lgamma.mainTable` as a hypothesis, and `lgammaR_sign` adds the
inputs from `0x1.754d9278b51a6p+1014` on through `LgammaSpecial`.  `toUInt64_nat` and `parity`
repeat `Library.Numerics.Float64.Sinpi.SinpiFloor.toUInt64_int` and `Library.Numerics.Float64.Sinpi.SinpiFloor.parity`, whose module imports the sine and tangent
modules.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaSign
open CodeLib.IEEE64 LeanExe.ProofKit Lgamma LgammaBranches LgammaSpecial Library.Numerics.Float64.Tgamma.TgammaFloor
open Library.Numerics.Float64.Tgamma (floorF)

set_option exponentiation.threshold 4096

/-- `toUInt64` of a float with a positive integer value. -/
theorem toUInt64_nat (x : Float) (N : Nat) (hf : Finite x.toBits) (hv : value x.toBits = N)
    (h1 : 1 ≤ N) (h2 : N < 2 ^ 63) : x.toUInt64 = UInt64.ofNat N := by
  rw [F64Convert.toUInt64_eq]
  have hpos : 0 < value x.toBits := by rw [hv]; exact_mod_cast h1
  have hsg := F64Exact.sign_of_pos x.toBits hpos
  have hm : Wasm.IEEE64.scaledMagnitude x.toBits = N * 2 ^ 1074 := by
    have h := F64Exact.value_of_sign x.toBits hsg
    rw [hv, eq_div_iff (by positivity)] at h
    exact_mod_cast h.symm
  have hfin : Wasm.IEEE64.isFinite x.toBits = true := hf
  have hnan : Wasm.IEEE64.isNaN x.toBits = false := not_nan_of_finite hf
  have htr : Wasm.IEEE64.truncatedInt x.toBits = some (N : Int) := by
    unfold Wasm.IEEE64.truncatedInt
    simp only [hfin, ite_true, hm, hsg, Bool.false_eq_true, ite_false,
      Nat.mul_div_cancel _ (show 0 < 2 ^ 1074 by positivity)]
  unfold Wasm.IEEE64.truncSatI64U
  simp only [hnan, Bool.false_eq_true, ite_false, htr]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  unfold Wasm.IEEE64.intToUInt64
  rw [ite_eq_right (by omega)]
  rfl

theorem parity (N : Nat) (h : N < 2 ^ 64) : (UInt64.ofNat N &&& 1 == 1) = decide (N % 2 = 1) := by
  have hn : (UInt64.ofNat N).toNat = N :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have h1 : (UInt64.ofNat N &&& 1).toNat = N % 2 := by
    rw [UInt64.toNat_and, hn]
    exact Nat.and_two_pow_sub_one_eq_mod N 1
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← h1]
  constructor
  · intro h'; rw [h']; rfl
  · intro h'; exact UInt64.toNat_inj.mp (by rw [h']; rfl)

theorem au_test (w : UInt64) :
    w <<< 1 >>> 38 < 0x1FF0000 ↔ w.toNat % 2 ^ 63 < 0x3FE0000000000000 := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.reducePow]
  have := w.toNat_lt
  omega

theorem half_word : value (0x3FE0000000000000 : UInt64) = 1 / 2 := by
  rw [Library.Numerics.Float64.Tgamma.TgammaSpecial.lit_value _ (1 / 2) (by decide +kernel)]
  norm_num

theorem abs_lt_half (w : UInt64) (hw : w.toNat % 2 ^ 63 < 0x3FE0000000000000) :
    |value w| < 1 / 2 := by
  rw [← F64UpperWord.value_abs, ← half_word]
  exact F64PositiveOrder.value_strict (by decide) (by rw [F64UpperWord.abs_toNat]; exact hw)

theorem half_le_abs (w : UInt64) (hw : 0x3FE0000000000000 ≤ w.toNat % 2 ^ 63) :
    1 / 2 ≤ |value w| := by
  rw [← F64UpperWord.value_abs, ← half_word]
  exact (F64PositiveOrder.value_le_iff (by decide)
    (by rw [F64UpperWord.abs_toNat]; exact Nat.mod_lt _ (by norm_num))).mpr
    (by rw [F64UpperWord.abs_toNat]; exact hw)

/-! ### The last component of the fast path's block

The fast path's block is a tree of `if`, `have`, and `match` on pairs (`Lgamma.polyDD.match_1`) and
triples (`Lgamma.asLgammaAsymAccurate.match_3`).  These lemmas read the block's last component
`sgnOf` from its leaves without reducing any discriminant.  `sgnOf` is a regular definition, so the
kernel compares `sgnOf a` with `sgnOf b` through `a` and `b`: on `r.2.2.2` it unfolds the projection,
evaluates the block with `whnf`, and runs out of memory on calls such as `piecePoly tab j z`.  The
lemmas name the code's matchers, which `linter.auxLemma` flags because a change of `Lgamma` can
rename them, and such a change breaks these proofs at build time. -/

set_option linter.auxLemma false

/-- The last component of a block's result. -/
def sgnOf (r : Float × Float × Float × Float) : Float := r.2.2.2

theorem m1_sgn (p : Float × Float) (f : Float → Float → Float × Float × Float × Float) (s : Float)
    (h : ∀ a b, sgnOf (f a b) = s) :
    sgnOf (polyDD.match_1 (fun _ => Float × Float × Float × Float) p f) = s := by
  obtain ⟨a, b⟩ := p
  exact h a b

theorem m3_sgn (p : Float × Float × Float)
    (f : Float → Float → Float → Float × Float × Float × Float) (s : Float)
    (h : ∀ a b c, sgnOf (f a b c) = s) :
    sgnOf (asLgammaAsymAccurate.match_3 (fun _ => Float × Float × Float × Float) p f) = s := by
  obtain ⟨a, b, c⟩ := p
  exact h a b c

theorem ite_sgn {c : Prop} [Decidable c] (A B : Float × Float × Float × Float) (s : Float)
    (hA : c → sgnOf A = s) (hB : ¬ c → sgnOf B = s) : sgnOf (if c then A else B) = s := by
  by_cases h : c
  · rw [ite_eq_left h]; exact hA h
  · rw [ite_eq_right h]; exact hB h

open Lean Elab Tactic Meta in
/-- `sgn_step` takes one step into the goal `sgnOf r = s`.  For a pair or triple `match` of `Lgamma`
it applies `m1_sgn` or `m3_sgn`, instantiated with the goal's own discriminant, alternative, and
`s`: `apply` with metavariables unfolds the matcher by structure eta and fails.  For
`have y := v; b y` it leaves `∀ y, sgnOf (b y) = s` and closes the goal with that statement at
`v`. -/
elab "sgn_step" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := t.eq? | throwError "sgn_step: the goal is not an equation"
    let lhs := lhs.consumeMData
    unless lhs.isAppOfArity ``sgnOf 1 do throwError "sgn_step: the left side is not `sgnOf r`"
    let e := lhs.appArg!.consumeMData
    if let .letE n ty val body _ := e then
      let g2Type ← withLocalDeclD n ty fun y => do
        mkForallFVars #[y] (← mkEq (mkApp (mkConst ``sgnOf) (body.instantiate1 y)) rhs)
      let g2 ← mkFreshExprSyntheticOpaqueMVar g2Type
      g.assign (mkApp g2 val)
      replaceMainGoal [g2.mvarId!]
    else
      let lem :=
        if e.isAppOfArity ``polyDD.match_1 3 then some ``m1_sgn
        else if e.isAppOfArity ``asLgammaAsymAccurate.match_3 3 then some ``m3_sgn
        else none
      let some name := lem | throwError "sgn_step: no pair or triple matcher and no `have`"
      let args := e.getAppArgs
      replaceMainGoal (← g.apply (mkAppN (mkConst name) #[args[1]!, args[2]!, rhs]))

section
variable (logTab hTab sinTab asymTab accTab dbTab tab : Array UInt64) (x : Float)

/-- **The sign that the code returns** below the magnitude `0x1.754d9278b51a6p+1014`, other than at
the poles and at 1 and 2. -/
theorem sign_code (h1 : ¬ x.toBits <<< 1 ≥ 0xFEAEA9B24F16A34C)
    (h2 : ¬ (floorF x == x && x ≤ 0.0) = true)
    (h3 : ¬ (floorF x == x && (x == 1.0 || x == 2.0)) = true) :
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).2 =
      if x.toBits <<< 1 >>> 38 < tab[(0 : UInt64).toNat]! then
        (if x.toBits >>> 63 == 1 then -1.0 else 1.0)
      else if x.toBits >>> 63 == 1 then
        (if (-floorF x).toUInt64 &&& 1 == 1 then -1.0 else 1.0)
      else 1.0 := by
  by_cases hc : x.toBits <<< 1 >>> 38 < tab[(0 : UInt64).toNat]!
  · rewrite [ite_eq_left hc]
    rewrite [lgammaWith.eq_1, ite_eq_right h1]
    extract_lets fx au sgn
    have h2' : ¬ (fx == x && x ≤ 0.0) = true := h2
    have h3' : ¬ (fx == x && (x == 1.0 || x == 2.0)) = true := h3
    rewrite [ite_eq_right h2', ite_eq_right h3']
    split
    next fh fl eps sign heq =>
    extract_lets ub lb
    have hr : (if (ub != lb) = true then (accurate logTab hTab sinTab asymTab accTab dbTab x, sign)
        else (ub, sign)).2 = sign := by split <;> rfl
    rewrite [hr]
    have hs : sign = sgnOf _ := congrArg sgnOf heq.symm
    rewrite [hs]
    apply ite_sgn
    · intro _
      sgn_step; intro lh ll
      apply ite_sgn
      · intro _; rfl
      · intro _
        apply ite_sgn
        · intro _
          sgn_step; intro _ _
          sgn_step; intro _ _
          sgn_step; intro _ _
          rfl
        · intro _
          sgn_step; intro t xl
          sgn_step; intro au2
          sgn_step; intro j
          sgn_step; intro z
          sgn_step; intro _ _
          sgn_step; intro _ _
          sgn_step; intro eps2
          sgn_step; intro _ _
          rfl
    · intro h; exact absurd hc h
  · rewrite [ite_eq_right hc]
    by_cases hn : (x.toBits >>> 63 == 1) = true
    · rewrite [ite_eq_left hn]
      rewrite [lgammaWith.eq_1, ite_eq_right h1]
      extract_lets fx au sgn
      have h2' : ¬ (fx == x && x ≤ 0.0) = true := h2
      have h3' : ¬ (fx == x && (x == 1.0 || x == 2.0)) = true := h3
      rewrite [ite_eq_right h2', ite_eq_right h3']
      split
      next fh fl eps sign heq =>
      extract_lets ub lb
      have hr : (if (ub != lb) = true then (accurate logTab hTab sinTab asymTab accTab dbTab x, sign)
          else (ub, sign)).2 = sign := by split <;> rfl
      rewrite [hr]
      have hs : sign = sgnOf _ := congrArg sgnOf heq.symm
      rewrite [hs]
      apply ite_sgn
      · intro h; exact absurd h hc
      · intro _
        sgn_step; intro _ _ _
        apply ite_sgn
        · intro _
          sgn_step; intro _ _
          sgn_step; intro _ _
          sgn_step; intro _ _
          sgn_step; intro _ _
          rfl
        · intro h; exact absurd hn h
    · rewrite [ite_eq_right hn]
      rewrite [lgammaWith.eq_1, ite_eq_right h1]
      extract_lets fx au sgn
      have h2' : ¬ (fx == x && x ≤ 0.0) = true := h2
      have h3' : ¬ (fx == x && (x == 1.0 || x == 2.0)) = true := h3
      rewrite [ite_eq_right h2', ite_eq_right h3']
      split
      next fh fl eps sign heq =>
      extract_lets ub lb
      have hr : (if (ub != lb) = true then (accurate logTab hTab sinTab asymTab accTab dbTab x, sign)
          else (ub, sign)).2 = sign := by split <;> rfl
      rewrite [hr]
      have hs : sign = sgnOf _ := congrArg sgnOf heq.symm
      rewrite [hs]
      apply ite_sgn
      · intro h; exact absurd h hc
      · intro _
        sgn_step; intro _ _ _
        apply ite_sgn
        · intro h; exact absurd h hn
        · intro _; rfl

/-- **The second result is the sign of `Γ x`** at every finite input below the magnitude
`0x1.754d9278b51a6p+1014` other than zero and the negative integers. -/
theorem lgamma_sign (h0 : tab[(0 : UInt64).toNat]! = 0x1FF0000) (hf : Finite x.toBits)
    (hlim : x.toBits.toNat % 2 ^ 63 < 0x7F5754D9278B51A6)
    (hp : ∀ n : ℤ, value x.toBits = n → 0 < n) :
    (lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x).2 =
      if Real.Gamma (value x.toBits) < 0 then -1.0 else 1.0 := by
  have h1 : ¬ x.toBits <<< 1 ≥ 0xFEAEA9B24F16A34C := fun h => by
    have := (big_test _).mp h; omega
  have hv0 : value x.toBits ≠ 0 := fun h => by
    have := hp 0 (by rw [h]; simp)
    omega
  have hlarge : |value x.toBits| < 2 ^ 52 ∨ 0 < value x.toBits := by
    by_cases hl : 2 ^ 52 ≤ |value x.toBits|
    · obtain ⟨N, hN⟩ := int_of_large x.toBits hf hl
      have := hp N hN
      right; rw [hN]; exact_mod_cast this
    · left; exact lt_of_not_ge hl
  have h2 : ¬ (floorF x == x && x ≤ 0.0) = true := by
    rw [Bool.and_eq_true, decide_eq_true_iff, float_le_iff _ _ hf zero_finite,
      Library.Numerics.Float64.Tgamma.TgammaSpecial.zero_bits, F64Magnitude.value_zero]
    rintro ⟨hb, hle⟩
    rcases hlarge with hl | hl
    · obtain ⟨hff, hfv⟩ := floorF_spec x hf hl
      rw [F64UpperWord.float_beq_iff _ _ hff hf, hfv] at hb
      have hk := hp _ hb.symm
      have : ((⌊value x.toBits⌋ : ℤ) : ℝ) ≤ 0 := by rw [hb]; exact hle
      have : ⌊value x.toBits⌋ ≤ 0 := by exact_mod_cast this
      omega
    · exact absurd hle (not_le.mpr hl)
  by_cases h3 : (floorF x == x && (x == 1.0 || x == 2.0)) = true
  · have hu : value x.toBits = 1 ∨ value x.toBits = 2 := by
      rw [Bool.and_eq_true, Bool.or_eq_true, F64UpperWord.float_beq_iff _ _ hf one_finite,
        F64UpperWord.float_beq_iff _ _ hf two_finite, one_value, two_value] at h3
      exact h3.2
    rw [lgamma_unit _ _ _ _ _ _ _ x h1 h2 h3]
    have hg : 0 < Real.Gamma (value x.toBits) :=
      Real.Gamma_pos_of_pos (by rcases hu with h | h <;> rw [h] <;> norm_num)
    rw [ite_eq_right (not_lt.mpr hg.le)]
  rw [sign_code _ _ _ _ _ _ _ x h1 h2 h3, h0]
  by_cases hn : (x.toBits >>> 63 == 1) = true
  · have hneg : value x.toBits < 0 := by
      rcases lt_or_gt_of_ne hv0 with h | h
      · exact h
      · have hs := F64Exact.sign_of_pos x.toBits h
        simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not] at hs
        exact absurd ((sign_test _).mp hn) hs
    have hni : ∀ n : ℤ, value x.toBits ≠ n := fun n h => by
      have := hp n h
      have : (n : ℝ) < 0 := by rw [← h]; exact hneg
      have : n < 0 := by exact_mod_cast this
      omega
    by_cases hc : x.toBits <<< 1 >>> 38 < 0x1FF0000
    · rw [ite_eq_left hc, ite_eq_left hn]
      have hh := abs_lt_half _ ((au_test _).mp hc)
      rw [abs_of_neg hneg] at hh
      have hfl : ⌊value x.toBits⌋ = -1 := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      have hg := GammaBasic.gamma_neg_of_odd (by linarith) hni
        (by rw [hfl]; exact ⟨-1, by norm_num⟩)
      rw [ite_eq_left hg]
    · rw [ite_eq_right hc, ite_eq_left hn]
      have hl : |value x.toBits| < 2 ^ 52 := by
        rcases hlarge with hl | hl
        · exact hl
        · linarith
      obtain ⟨hff, hfv⟩ := floorF_spec x hf hl
      obtain ⟨hnf, hnv⟩ := neg_float (floorF x) hff
      have hk : ⌊value x.toBits⌋ ≤ -1 := by
        have : ⌊value x.toBits⌋ < 0 := Int.floor_lt.mpr (by push_cast; exact hneg)
        omega
      have hkl : -(2 : ℝ) ^ 52 - 1 ≤ ⌊value x.toBits⌋ := by
        have := Int.lt_floor_add_one (value x.toBits)
        rw [abs_lt] at hl
        linarith
      have hkl' : -2 ^ 52 - 1 ≤ ⌊value x.toBits⌋ := by exact_mod_cast hkl
      obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -⌊value x.toBits⌋ :=
        ⟨(-⌊value x.toBits⌋).toNat, Int.toNat_of_nonneg (by omega)⟩
      have hmv : value (-floorF x).toBits = m := by
        rw [hnv, hfv, ← Int.cast_natCast, hm, Int.cast_neg]
      rw [toUInt64_nat _ m hnf hmv (by omega) (by omega), parity m (by omega)]
      by_cases ho : Odd ⌊value x.toBits⌋
      · have hg := GammaBasic.gamma_neg_of_odd (by linarith) hni ho
        have hm2 : m % 2 = 1 := by rw [Int.odd_iff] at ho; omega
        rw [ite_eq_left (decide_eq_true hm2), ite_eq_left hg]
      · have he : Even ⌊value x.toBits⌋ := Int.not_odd_iff_even.mp ho
        have hg := GammaBasic.gamma_pos_of_even (by linarith) hni he
        have hm2 : ¬ m % 2 = 1 := by rw [Int.even_iff] at he; omega
        rw [ite_eq_right (by simp only [decide_eq_true_iff]; exact hm2), ite_eq_right (not_lt.mpr hg.le)]
  · have hpos : 0 < value x.toBits := by
      have hs : Wasm.IEEE64.sign x.toBits = false := by
        simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
        intro h; exact hn ((sign_test _).mpr h)
      exact lt_of_le_of_ne (F64TwoSum.value_nonneg_of_sign _ hs) (Ne.symm hv0)
    have hg := Real.Gamma_pos_of_pos hpos
    rw [ite_eq_right (not_lt.mpr hg.le)]
    by_cases hc : x.toBits <<< 1 >>> 38 < 0x1FF0000
    · rw [ite_eq_left hc, ite_eq_right hn]
    · rw [ite_eq_right hc, ite_eq_right hn]

end

theorem two52_le_abs (w : UInt64) (hw : 0x4330000000000000 ≤ w.toNat % 2 ^ 63) :
    (2 : ℝ) ^ 52 ≤ |value w| := by
  have h52 : value (0x4330000000000000 : UInt64) = 2 ^ 52 := by
    rw [Library.Numerics.Float64.Tgamma.TgammaSpecial.lit_value _ (2 ^ 52) (by decide +kernel)]
    norm_num
  rw [← F64UpperWord.value_abs, ← h52]
  exact (F64PositiveOrder.value_le_iff (by decide)
    (by rw [F64UpperWord.abs_toNat]; exact Nat.mod_lt _ (by norm_num))).mpr
    (by rw [F64UpperWord.abs_toNat]; exact hw)

/-- **The second result of `lgammaR` is the sign of `Γ x`** at every finite input other than zero
and the negative integers. -/
theorem lgammaR_sign (x : Float) (hf : Finite x.toBits) (hp : ∀ n : ℤ, value x.toBits = n → 0 < n) :
    (lgammaR x).2 = if Real.Gamma (value x.toBits) < 0 then -1.0 else 1.0 := by
  have h0 : mainTable[(0 : UInt64).toNat]! = 0x1FF0000 := by decide +kernel
  by_cases hlim : x.toBits.toNat % 2 ^ 63 < 0x7F5754D9278B51A6
  · exact lgamma_sign _ _ _ _ _ _ _ x h0 hf hlim hp
  · obtain ⟨N, hN⟩ := int_of_large x.toBits hf (two52_le_abs _ (by omega))
    have hv : 0 < value x.toBits := by rw [hN]; exact_mod_cast hp N hN
    have hs : x.toBits.toNat < 2 ^ 63 := by
      have hsg := F64Exact.sign_of_pos _ hv
      simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not] at hsg
      omega
    rw [ite_eq_right (not_lt.mpr (Real.Gamma_pos_of_pos hv).le)]
    have hm : x.toBits.toNat % 2 ^ 63 = x.toBits.toNat := Nat.mod_eq_of_lt hs
    rcases (show x.toBits.toNat = 0x7F5754D9278B51A6 ∨ x.toBits.toNat = 0x7F5754D9278B51A7 ∨
        0x7F5754D9278B51A8 ≤ x.toBits.toNat by omega) with h | h | h
    · exact (LgammaSpecial.lgamma_x1 _ _ _ _ _ _ _ x (UInt64.toNat_inj.mp (by rw [h]; rfl))).2
    · exact (LgammaSpecial.lgamma_x2 _ _ _ _ _ _ _ x (UInt64.toNat_inj.mp (by rw [h]; rfl))).2
    · exact (LgammaSpecial.lgamma_overflow _ _ _ _ _ _ _ x hf h hs).2

#print axioms sign_code
#print axioms lgamma_sign
#print axioms lgammaR_sign

end Library.Numerics.Float64.Lgamma.LgammaSign
