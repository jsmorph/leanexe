import Library.Numerics.Float64.Tgamma.TgammaEdge
import Library.Numerics.Float64.Tgamma.TgammaPoly

/-!
**The positive integers** of `tgammaWith`: `(n - 1)!` within one step of `Γ n` for `1 ≤ n ≤ 171`.
The code multiplies the double-double `t0h + t0l`, from 1, by the exact doubles `1, 2, …, n - 1`
with `mulDDD`.  `mulDDD_big` is `TgammaDD.mulDDD_spec` for products up to `2 ^ 1020`, since
`170!` lies near `2 ^ 1019.4`.  After `k` steps the pair lies within `k 2 ^ -93 k!` of `k!`, and
its low part below `k 2 ^ -50 k!` (`iloop_inv`), so the rounded sum is within one step of
`Γ n = (n - 1)!` (`intPath_within`).
-/

namespace Library.Numerics.Float64.Tgamma.TgammaInt
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaPoly TgammaMainRed TgammaRecip
  TgammaFloor

set_option exponentiation.threshold 4096

/-- `TgammaDD.mulDDD_spec` for products up to `2 ^ 1020`. -/
theorem mulDDD_big (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (x ch cl : Float) (hx : Finite x.toBits)
    (hch : Finite ch.toBits) (hcl : Finite cl.toBits) (H Lw : ℝ)
    (hH : |value ch.toBits| * |value x.toBits| ≤ H)
    (hL : |value cl.toBits| * |value x.toBits| ≤ Lw) (hHmax : H ≤ 2 ^ 1020)
    (hLmax : Lw ≤ 2 ^ 1020) :
    Finite (mulDDD x ch cl).1.toBits ∧ Finite (mulDDD x ch cl).2.toBits ∧
      |value (mulDDD x ch cl).1.toBits + value (mulDDD x ch cl).2.toBits -
          value x.toBits * (value ch.toBits + value cl.toBits)| ≤
        (3 * Lw + H / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1072 ∧
      |value (mulDDD x ch cl).2.toBits| ≤ Lw * (1 + 1 / 2 ^ 51) + H / 2 ^ 52 + 1 / 2 ^ 1071 := by
  have hH0 : 0 ≤ H := le_trans (by positivity) hH
  have hL0 : 0 ≤ Lw := le_trans (by positivity) hL
  have hp1022 : H < 2 ^ 1022 := by linarith [(by norm_num : (2 : ℝ) ^ 1020 < 2 ^ 1022)]
  have hp1022' : Lw < 2 ^ 1022 := by linarith [(by norm_num : (2 : ℝ) ^ 1020 < 2 ^ 1022)]
  set vx := value x.toBits
  set vh := value ch.toBits
  set vl := value cl.toBits
  have ha0 := fapprox_mul (fapprox_self ch hch) (fapprox_self x hx) |vh| |vx| le_rfl le_rfl H
    (by simpa using hH) hp1022
  have ha : FApprox (ch * x) (vh * vx) (H / 2 ^ 53 + 1 / 2 ^ 1075) :=
    Approx.mono ha0 (le_of_eq (by ring))
  set va := value (ch * x).toBits with hva
  have hna := fapprox_neg (fapprox_self (ch * x) ha.1)
  have hnaf : Finite (-(ch * x)).toBits := hna.1
  have hnav : value (-(ch * x)).toBits = -va := by
    have h0 := abs_nonpos_iff.mp hna.2
    linarith
  have hSb : |vh * vx + value (-(ch * x)).toBits| ≤ 2 ^ 1000 := by
    rw [hnav, ← sub_eq_add_neg, abs_sub_comm]
    have h1 := ha.2
    have : H / 2 ^ 53 ≤ 2 ^ 967 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [(by norm_num : (2 : ℝ) ^ 1020 ≤ 2 ^ 967 * 2 ^ 53)]
    linarith [(by norm_num : (2 : ℝ) ^ 967 + 1 / 2 ^ 1075 ≤ 2 ^ 1000)]
  have hf := fma_approx hF ch x (-(ch * x)) hch hx hnaf hSb
  rw [hnav, ← sub_eq_add_neg] at hf
  have hf' : FApprox (Library.Numerics.Arithmetic.Fma.Fma.fma ch x (-(ch * x))) (vh * vx - va)
      ((H / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 + 1 / 2 ^ 1075) := by
    refine Approx.mono hf ?_
    have : |vh * vx - va| ≤ H / 2 ^ 53 + 1 / 2 ^ 1075 := by rw [abs_sub_comm]; exact ha.2
    gcongr
  have hp0 := fapprox_mul (fapprox_self cl hcl) (fapprox_self x hx) |vl| |vx| le_rfl le_rfl Lw
    (by simpa using hL) hp1022'
  have hp : FApprox (cl * x) (vl * vx) (Lw / 2 ^ 53 + 1 / 2 ^ 1075) :=
    Approx.mono hp0 (le_of_eq (by ring))
  set B := Lw * (1 + 1 / 2 ^ 52) + H / 2 ^ 52 + 1 / 2 ^ 1072 with hB
  have hS : |vh * vx - va| ≤ H / 2 ^ 53 + 1 / 2 ^ 1075 := by rw [abs_sub_comm]; exact ha.2
  have hBb : |vl * vx + (vh * vx - va)| +
      (Lw / 2 ^ 53 + 1 / 2 ^ 1075 + ((H / 2 ^ 53 + 1 / 2 ^ 1075) / 2 ^ 53 + 1 / 2 ^ 1075)) ≤ B := by
    have h1 := abs_add_le (vl * vx) (vh * vx - va)
    have h2 : |vl * vx| ≤ Lw := by rw [abs_mul]; exact hL
    rw [hB]
    have : Lw / 2 ^ 53 ≤ Lw * (1 / 2 ^ 53) := le_of_eq (by ring)
    nlinarith
  have hlow := fapprox_add hp hf' B hBb (by
    rw [hB]; linarith [(by norm_num : (2 : ℝ) ^ 1020 * (1 + 1 / 2 ^ 52) + 2 ^ 1020 / 2 ^ 52 + 1 <
      2 ^ 1023), div_le_div_of_nonneg_right hHmax (by norm_num : (0 : ℝ) ≤ 2 ^ 52)])
  have hdef : mulDDD x ch cl = (ch * x, cl * x + Library.Numerics.Arithmetic.Fma.Fma.fma ch x (-(ch * x))) := rfl
  rw [hdef]
  refine ⟨ha.1, hlow.1, ?_, ?_⟩
  · have h := hlow.2
    rw [show va + value (cl * x + Library.Numerics.Arithmetic.Fma.Fma.fma ch x (-(ch * x))).toBits - vx * (vh + vl) =
      value (cl * x + Library.Numerics.Arithmetic.Fma.Fma.fma ch x (-(ch * x))).toBits - (vl * vx + (vh * vx - va)) by ring]
    rw [hB] at h
    nlinarith
  · have h := hlow.2
    have h2 := abs_sub_abs_le_abs_sub (value (cl * x + Library.Numerics.Arithmetic.Fma.Fma.fma ch x (-(ch * x))).toBits)
      (vl * vx + (vh * vx - va))
    have h3 := abs_add_le (vl * vx) (vh * vx - va)
    have h4 : |vl * vx| ≤ Lw := by rw [abs_mul]; exact hL
    rw [hB] at h
    nlinarith

/-- The loop body of the integer path. -/
def ibody (s : Float × Float × Float) : Float × Float × Float :=
  let (t0h, t0l, x0) := s
  let (t0h, t0l) := mulDDD x0 t0h t0l
  (t0h, t0l, x0 + 1.0)

theorem ibody_eq (h l x0 : Float) :
    ibody (h, l, x0) = ((mulDDD x0 h l).1, (mulDDD x0 h l).2, x0 + 1.0) := rfl

theorem intPath_eq (x : Float) :
    TgammaBranches.intPath x =
      (let fx := floorF x
       if x == 0.0 then 1.0 / x
       else if x < 0.0 then 0.0 / 0.0
       else
         let (t0h, t0l, _) := LeanExe.loop (fx - 1.0).toUInt64
           ((1.0 : Float), (0.0 : Float), (1.0 : Float)) fun _ s => ibody s
         t0h + t0l) := rfl

theorem fact_le (k : ℕ) (hk : k ≤ 170) : ((k.factorial : ℕ) : ℝ) ≤ 2 ^ 1020 * (1 - 1 / 2 ^ 30) := by
  have h1 : k.factorial ≤ (170 : ℕ).factorial := Nat.factorial_le hk
  have h2 : ((170 : ℕ).factorial : ℝ) ≤ 2 ^ 1020 * (1 - 1 / 2 ^ 30) := by
    obtain ⟨N, hN⟩ : ∃ N, N = (170 : ℕ).factorial := ⟨_, rfl⟩
    rw [← hN]
    have : N * 2 ^ 30 + 2 ^ 1020 ≤ 2 ^ 1050 := by rw [hN]; decide +kernel
    have h3 : (N : ℝ) * 2 ^ 30 + 2 ^ 1020 ≤ 2 ^ 1050 := by exact_mod_cast this
    rw [show (2 : ℝ) ^ 1020 * (1 - 1 / 2 ^ 30) = (2 ^ 1050 - 2 ^ 1020) / 2 ^ 30 by ring,
      le_div_iff₀ (by positivity)]
    linarith
  calc ((k.factorial : ℕ) : ℝ) ≤ ((170 : ℕ).factorial : ℝ) := by exact_mod_cast h1
    _ ≤ _ := h2

/-- **The integer loop** after `k ≤ 170` steps. -/
theorem iloop_inv (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (k : ℕ) (hk : k ≤ 170) :
    Finite (LeanExe.loop (UInt64.ofNat k) ((1.0 : Float), (0.0 : Float), (1.0 : Float))
        fun _ s => ibody s).1.toBits ∧
      Finite (LeanExe.loop (UInt64.ofNat k) ((1.0 : Float), (0.0 : Float), (1.0 : Float))
        fun _ s => ibody s).2.1.toBits ∧
      Finite (LeanExe.loop (UInt64.ofNat k) ((1.0 : Float), (0.0 : Float), (1.0 : Float))
        fun _ s => ibody s).2.2.toBits ∧
      value (LeanExe.loop (UInt64.ofNat k) ((1.0 : Float), (0.0 : Float), (1.0 : Float))
        fun _ s => ibody s).2.2.toBits = k + 1 ∧
      |value (LeanExe.loop (UInt64.ofNat k) ((1.0 : Float), (0.0 : Float), (1.0 : Float))
          fun _ s => ibody s).1.toBits +
        value (LeanExe.loop (UInt64.ofNat k) ((1.0 : Float), (0.0 : Float), (1.0 : Float))
          fun _ s => ibody s).2.1.toBits - k.factorial| ≤ k / 2 ^ 93 * k.factorial ∧
      |value (LeanExe.loop (UInt64.ofNat k) ((1.0 : Float), (0.0 : Float), (1.0 : Float))
          fun _ s => ibody s).2.1.toBits| ≤ k / 2 ^ 50 * k.factorial := by
  induction k with
  | zero =>
    rw [show UInt64.ofNat 0 = 0 from rfl, loop_zero]
    dsimp only
    refine ⟨one_finite, zero_finite, one_finite, ?_, ?_, ?_⟩
    · rw [one_value]; norm_num
    · rw [one_value, zero_value]; norm_num
    · rw [zero_value]; norm_num
  | succ m ih =>
    obtain ⟨hhf, hlf, hxf, hxv, he, hl⟩ := ih (by omega)
    rw [loop_succ m (by omega)]
    obtain ⟨S, hS⟩ : ∃ S, S = LeanExe.loop (UInt64.ofNat m) ((1.0 : Float), (0.0 : Float),
        (1.0 : Float)) fun _ s => ibody s := ⟨_, rfl⟩
    rw [← hS] at hhf hlf hxf hxv he hl ⊢
    obtain ⟨h, l, x0⟩ := S
    dsimp only at hhf hlf hxf hxv he hl ⊢
    rw [ibody_eq]
    dsimp only
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hm170 : (m : ℝ) ≤ 169 := by exact_mod_cast (show m ≤ 169 by omega)
    set F := ((m.factorial : ℕ) : ℝ) with hFdef
    have hF1 : 1 ≤ F := by rw [hFdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hFs : (((m + 1).factorial : ℕ) : ℝ) = (m + 1) * F := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hFmax := fact_le (m + 1) (by omega)
    rw [hFs] at hFmax
    -- magnitudes
    have hhb : |value h.toBits| ≤ F * (1 + 1 / 2 ^ 40) := by
      have h1 := abs_sub_abs_le_abs_sub (value h.toBits + value l.toBits) F
      have h2 := abs_add_le (value h.toBits + value l.toBits) (-value l.toBits)
      rw [add_neg_cancel_right, abs_neg] at h2
      rw [abs_of_pos (by linarith : (0 : ℝ) < F)] at h1
      have h3 : (m : ℝ) / 2 ^ 93 * F + m / 2 ^ 50 * F ≤ F / 2 ^ 40 := by
        have : (m : ℝ) / 2 ^ 93 + m / 2 ^ 50 ≤ 1 / 2 ^ 40 := by
          rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
            (by positivity)]
          nlinarith
        have := mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ F)
        linarith
      linarith
    have hxa : |value x0.toBits| = m + 1 := by rw [hxv, abs_of_pos (by linarith)]
    have hH : |value h.toBits| * |value x0.toBits| ≤ (m + 1) * F * (1 + 1 / 2 ^ 40) := by
      rw [hxa]
      have := mul_le_mul_of_nonneg_right hhb (by linarith : (0 : ℝ) ≤ m + 1)
      linarith
    have hL : |value l.toBits| * |value x0.toBits| ≤ (m + 1) * (m / 2 ^ 50 * F) := by
      rw [hxa, mul_comm]
      exact mul_le_mul_of_nonneg_left hl (by linarith)
    have hHmax : (m + 1) * F * (1 + 1 / 2 ^ 40) ≤ 2 ^ 1020 := by linarith
    have hLmax : (m + 1) * (m / 2 ^ 50 * F) ≤ 2 ^ 1020 := by
      have : (m : ℝ) / 2 ^ 50 ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (m + 1) * F)
      linarith
    obtain ⟨hp1, hp2, hpe, hpl⟩ := mulDDD_big hF x0 h l hxf hhf hlf _ _ hH hL hHmax hLmax
    -- `x0 + 1`
    have hx1 := add_exact x0 1.0 hxf one_finite (m + 2) 1074 (by norm_num)
      (by rw [hxv, one_value]; push_cast; ring)
      (by push_cast; rw [abs_of_pos (by linarith)]; linarith)
    rw [hxv, one_value] at hx1
    refine ⟨hp1, hp2, hx1.1, ?_, ?_, ?_⟩
    · rw [hx1.2]; push_cast; ring
    · -- the error
      push_cast
      rw [hFs]
      have hs : value (mulDDD x0 h l).1.toBits + value (mulDDD x0 h l).2.toBits - (m + 1) * F =
          (value (mulDDD x0 h l).1.toBits + value (mulDDD x0 h l).2.toBits -
            (m + 1) * (value h.toBits + value l.toBits)) +
          (m + 1) * (value h.toBits + value l.toBits - F) := by ring
      rw [hs]
      have h1 := abs_add_le (value (mulDDD x0 h l).1.toBits + value (mulDDD x0 h l).2.toBits -
            (m + 1) * (value h.toBits + value l.toBits))
          ((m + 1) * (value h.toBits + value l.toBits - F))
      rw [hxv] at hpe
      have h2 : |(↑m + 1) * (value h.toBits + value l.toBits - F)| ≤ (m + 1) * (m / 2 ^ 93 * F) := by
        rw [abs_mul, abs_of_pos (by linarith)]
        exact mul_le_mul_of_nonneg_left he (by linarith)
      have h3 : (3 * ((m + 1) * (m / 2 ^ 50 * F)) + (m + 1) * F * (1 + 1 / 2 ^ 40) / 2 ^ 51) / 2 ^ 53 +
          1 / 2 ^ 1072 ≤ (m + 1) * F / 2 ^ 93 := by
        have h4 : (3 * ((m : ℝ) / 2 ^ 50) + (1 + 1 / 2 ^ 40) / 2 ^ 51) / 2 ^ 53 ≤ 1 / 2 ^ 94 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have h5 : (1 : ℝ) / 2 ^ 1072 ≤ (m + 1) * F / 2 ^ 94 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have h6 : (3 * ((m + 1) * (m / 2 ^ 50 * F)) + (m + 1) * F * (1 + 1 / 2 ^ 40) / 2 ^ 51) /
            2 ^ 53 = (m + 1) * F * ((3 * (m / 2 ^ 50) + (1 + 1 / 2 ^ 40) / 2 ^ 51) / 2 ^ 53) := by
          ring
        rw [h6]
        have h7 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ (m + 1) * F)
        linarith
      have : (m + 1) * F / 2 ^ 93 + (m + 1) * (m / 2 ^ 93 * F) = (m + 1) / 2 ^ 93 * ((m + 1) * F) := by
        ring
      linarith
    · -- the low part
      push_cast
      rw [hFs]
      have h4 : (m + 1) * (m / 2 ^ 50 * F) * (1 + 1 / 2 ^ 51) + (m + 1) * F * (1 + 1 / 2 ^ 40) / 2 ^ 52 +
          1 / 2 ^ 1071 ≤ (m + 1) / 2 ^ 50 * ((m + 1) * F) := by
        have h5 : (1 : ℝ) / 2 ^ 1071 ≤ (m + 1) * F / 2 ^ 60 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have h6 : (m / 2 ^ 50 * (1 + 1 / 2 ^ 51) + (1 + 1 / 2 ^ 40) / 2 ^ 52 + 1 / 2 ^ 60 : ℝ) ≤
            (m + 1) / 2 ^ 50 := by
          linarith
        have h7 := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ (m + 1) * F)
        linarith
      linarith

/-- **The positive integers** `1 ≤ n ≤ 171`: within one step of `Γ n = (n - 1)!`. -/
theorem intPath_within (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (x : Float) (hx : Finite x.toBits) (n : ℕ)
    (hn1 : 1 ≤ n) (hn : n ≤ 171) (hv : value x.toBits = n) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (TgammaBranches.intPath x).toBits := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  rw [intPath_eq]
  dsimp only
  have hz : ¬ ((x == 0.0) = true) := by
    rw [TgammaSpecial.zero_test x hx, hv]; linarith
  have hlt : ¬ x < 0.0 := by
    rw [F64UpperWord.float_lt_iff _ _ hx zero_finite, zero_value, hv]; linarith
  rw [ite_eq_right hz, ite_eq_right hlt]
  -- the loop count
  obtain ⟨hff, hfv⟩ := floorF_spec x hx (by rw [hv, abs_of_pos (by linarith)]; norm_cast; omega)
  rw [hv, show ⌊(n : ℝ)⌋ = (n : ℤ) from Int.floor_natCast n] at hfv
  have hs := sub_exact (floorF x) 1.0 hff one_finite ((n : ℤ) - 1) 1074 (by norm_num)
    (by rw [hfv, one_value]; push_cast; ring)
    (by push_cast; rw [abs_of_nonneg (by linarith)]; norm_cast; omega)
  rw [hfv, one_value] at hs
  have hcount : (floorF x - 1.0).toUInt64 = UInt64.ofNat (n - 1) := by
    apply toUInt64_nat _ _ hs.1 _ (by omega)
    rw [hs.2]
    push_cast [Nat.cast_sub hn1]
    ring
  rw [hcount]
  obtain ⟨hhf, hlf, -, -, he, -⟩ := iloop_inv hF (n - 1) (by omega)
  generalize LeanExe.loop (UInt64.ofNat (n - 1)) ((1.0 : Float), (0.0 : Float), (1.0 : Float))
    (fun _ s => ibody s) = S at hhf hlf he ⊢
  obtain ⟨h, l, x0⟩ := S
  dsimp only at hhf hlf he ⊢
  -- `Γ n = (n - 1)!`
  have hG : Real.Gamma (value x.toBits) = ((n - 1).factorial : ℝ) := by
    rw [hv, ← Real.Gamma_nat_eq_factorial, Nat.cast_sub hn1]
    push_cast
    ring_nf
  rw [hG]
  set F := (((n - 1).factorial : ℕ) : ℝ) with hFdef
  have hF1 : 1 ≤ F := by rw [hFdef]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hFmax : F ≤ 2 ^ 1020 * (1 - 1 / 2 ^ 30) := fact_le (n - 1) (by omega)
  have hk : (((n - 1 : ℕ)) : ℝ) ≤ 170 := by exact_mod_cast (show n - 1 ≤ 170 by omega)
  have hk0 : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hFa : |F| = F := abs_of_pos (by linarith)
  have hrel : |value h.toBits + value l.toBits - F| ≤ 1 / 2 ^ 80 * |F| := by
    rw [hFa]
    have : ((n - 1 : ℕ) : ℝ) / 2 ^ 93 ≤ 1 / 2 ^ 80 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have := mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ F)
    linarith
  have hS0 : value h.toBits + value l.toBits ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg, hFa] at hrel
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 80 < 1)]
  have hSmax : |value h.toBits + value l.toBits| < 2 ^ 1023 := by
    have := abs_sub_abs_le_abs_sub (value h.toBits + value l.toBits) F
    rw [hFa] at this hrel
    linarith [(by norm_num : (2 : ℝ) ^ 1020 * (1 + 1 / 2 ^ 80) < 2 ^ 1023)]
  have hround := F64RoundNearest.add_rounded h.toBits l.toBits hhf hlf hS0 hSmax
  rw [← F64Bits.toBits_add] at hround
  exact F64RoundNearest.within_one_of_rounded_rel _ _ F hround (1 / 2 ^ 80) (by positivity)
    (by norm_num) hrel (by rw [hFa]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 1021 ≤ 1)])
    (by rw [hFa]; linarith [(by norm_num : (2 : ℝ) ^ 1020 < 2 ^ 1022)])

#print axioms mulDDD_big
#print axioms iloop_inv
#print axioms intPath_within

end Library.Numerics.Float64.Tgamma.TgammaInt
