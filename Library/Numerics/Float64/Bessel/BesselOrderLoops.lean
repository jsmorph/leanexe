import Library.Numerics.Float64.Bessel.BesselStepF
import Library.Numerics.Float64.Bessel.BesselJ1Large

/-!
The loops of `jn` and `yn` for `4 ≤ x ≤ 2^302` and `2 n ≤ x`.  `jn` runs
`LeanExe.loop (n - 1)` on the pair `(j0 x, j1 x)` with the body `jbody`; its states are `jseq`
(`loop_eq`), and the first components satisfy the recurrence with the step of `step_bt`.  `yn` runs
`LeanExe.repeatWhile` on `(1, y0 x, y1 x)` with the step `ystep`, whose iterates are
`(i + 1, ya i, ya (i + 1))` (`ystep_iter`); the condition holds while `i + 1 < n` because the values
are finite, so the loop stops after `n - 1` steps (`yn_loop_eq`).  With the starting errors of
`j0_large`, `j1_large`, `y0_large`, and `y1_large`, `BesselForward.forward` gives the error
`(17 + 12 n) u M_n` (`jn_forward`, `yn_forward`).
-/

namespace Library.Numerics.Float64.Bessel.BesselOrderLoops
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx BesselPQEval BesselOrderN BesselRecur
  BesselOrderEnergy BesselForward BesselStepF
open LeanExe.ProofKit.Bessel (J0 J1 Y0 Y1)

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- The body of `jn`'s forward loop. -/
def jbody (x : Float) (k : UInt64) (s : Float × Float) : Float × Float :=
  (s.2, s.2 * ((2 * (k + 1)).toFloat / x) - s.1)

/-- The states of `jn`'s forward loop. -/
def jseq (x : Float) (init : Float × Float) : ℕ → Float × Float
  | 0 => init
  | i + 1 => jbody x (UInt64.ofNat i) (jseq x init i)

theorem loop_eq (x : Float) (init : Float × Float) (n : UInt64) :
    LeanExe.loop n init (jbody x) = jseq x init n.toNat := by
  unfold LeanExe.loop
  induction n.toNat with
  | zero => rfl
  | succ k ih => rw [Nat.fold_succ, ih]; rfl

theorem loop_result (x : Float) (init : Float × Float) (n : UInt64) (hn : 1 ≤ n.toNat) :
    (LeanExe.loop (n - 1) init (jbody x)).2 = (jseq x init n.toNat).1 := by
  rw [loop_eq]
  have h : (n - 1).toNat + 1 = n.toNat := by
    rw [UInt64.toNat_sub]
    have := n.toNat_lt
    simp only [UInt64.reduceToNat, Nat.reducePow] at this ⊢
    omega
  rw [← h]
  rfl

theorem two_mul_word (i : ℕ) (hi : i < 2 ^ 40) : (2 * (UInt64.ofNat i + 1)).toNat = 2 * (i + 1) := by
  rw [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat']
  simp only [UInt64.reduceToNat, Nat.reducePow]
  omega

theorem two_mul_word' (i : ℕ) (hi : i < 2 ^ 40) : (2 * UInt64.ofNat (i + 1)).toNat = 2 * (i + 1) := by
  rw [UInt64.toNat_mul, UInt64.toNat_ofNat']
  simp only [UInt64.reduceToNat, Nat.reducePow]
  omega

/-- The value `2 (k + 1)` of the word and `λ_(k+1)`. -/
theorem lam_word {t : Float} {w : ℝ} (k : ℕ) (hk : k < 2 ^ 40) (W : UInt64) (hW : W.toNat = 2 * (k + 1))
    (ht : t = W.toFloat) :
    FApprox t ((2 * (k + 1) : ℕ) : ℝ) 0 ∧ ((2 * (k + 1) : ℕ) : ℝ) / w = lam w (k + 1) := by
  refine ⟨?_, by unfold lam; push_cast <;> ring⟩
  rw [ht, ← hW]
  exact toFloat_exact W (by rw [hW]; omega)

/-- The facts about `x ≥ 4` that both loops use. -/
theorem big_facts (xa : Float) (hxf : Finite xa.toBits) (hpos : xa.toBits.toNat < 2 ^ 63)
    (hw4 : 4 ≤ value xa.toBits) :
    0x4000000000000000 ≤ xa.toBits.toNat ∧ 0x4000000000000000 ≤ xa.toBits.toNat % 2 ^ 63 := by
  have h := (F64PositiveOrder.value_le_iff (left := (0x4000000000000000 : UInt64))
    (right := xa.toBits) (by decide) hpos).mp (by rw [BesselJ0Large.value_two]; linarith)
  exact ⟨h, by rw [Nat.mod_eq_of_lt hpos]; exact h⟩

/-- `|F_k| ≤ M_k` for `J` and `Y`. -/
theorem J_le_modn (w : ℝ) (k : ℕ) : |Jn k w| ≤ modn w k := by
  unfold modn
  exact Real.abs_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))

theorem Y_le_modn (w : ℝ) (k : ℕ) : |Yn w k| ≤ modn w k := by
  unfold modn
  exact Real.abs_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))

/-- A start within `c u M` of a value at most `M ≤ 0.92` is finite and at most 1. -/
theorem start_facts {f : Float} {F M c : ℝ} (h : |value f.toBits - F| ≤ c * 𝐮 * M) (hF : |F| ≤ M)
    (hM : M ≤ 92 / 100) (hc : 0 ≤ c) (hc' : c ≤ 12) (hM0 : 0 ≤ M) : Finite f.toBits := by
  apply finite_of_abs_lt
  have h1 : c * 𝐮 * M ≤ 1 := by
    have : c * 𝐮 ≤ 1 := by rw [show 𝐮 = 1 / 2 ^ 53 from rfl]; nlinarith
    nlinarith
  have := abs_sub_abs_le_abs_sub (value f.toBits) F
  have : (2 : ℝ) < 2 ^ 1024 := by norm_num
  linarith

/-- The start of `jn`'s forward loop. -/
def jinit (x : Float) : Float × Float :=
  (Bessel.j0With Trig.invPi Trig.halfPi Bessel.j0Table x,
    Bessel.j1With Trig.invPi Trig.halfPi Bessel.j1Table x)

/-- `jn`'s forward loop for `4 ≤ x ≤ 2^302` and `2 n ≤ x`, with `w` the value of `x`. -/
theorem jn_forward_w (xa : Float) (w : ℝ) (hwx : value xa.toBits = w) (n : ℕ)
    (hxf : Finite xa.toBits) (hpos : xa.toBits.toNat < 2 ^ 63) (hw4 : 4 ≤ w) (hwb : w ≤ 2 ^ 302)
    (hn : 2 * (n : ℝ) ≤ w) (hn2 : n ≤ 2 ^ 31) :
    Finite (jseq xa (jinit xa) n).1.toBits ∧
      |value (jseq xa (jinit xa) n).1.toBits - Jn n w| ≤ (17 + 12 * (n : ℝ)) * 𝐮 * modn w n := by
  have hw0 : 0 < w := by linarith
  obtain ⟨-, h2⟩ := big_facts xa hxf hpos (by rw [hwx]; exact hw4)
  have hM0 := modn_le w hw4 0 (by norm_num; linarith)
  have hM1 := modn_le w hw4 1 (by norm_num; linarith)
  have hj0 := BesselJ0Large.j0_large xa hxf h2
  have hj1 := BesselJ1Large.j1_large xa hxf h2
  rw [hwx, abs_of_pos hw0] at hj0 hj1
  have hx : FApprox xa w 0 := by rw [← hwx]; exact fapprox_exact xa hxf
  have e0 : modn w 0 = √(J0 w ^ 2 + Y0 w ^ 2) := by unfold modn; rw [Jn_zero, Yn_zero]
  have e1 : modn w 1 = √(J1 w ^ 2 + Y1 w ^ 2) := by unfold modn; rw [Jn_one, Yn_one]
  have h0 : Finite (jseq xa (jinit xa) 0).1.toBits ∧
      |value (jseq xa (jinit xa) 0).1.toBits - Jn 0 w| ≤ 10 * 𝐮 * modn w 0 := by
    have hv : |value (jseq xa (jinit xa) 0).1.toBits - Jn 0 w| ≤ 10 * 𝐮 * modn w 0 := by
      rw [Jn_zero, e0]; exact hj0
    exact ⟨start_facts hv (J_le_modn w 0) hM0 (by norm_num) (by norm_num) (Real.sqrt_nonneg _), hv⟩
  have h1 : Finite (jseq xa (jinit xa) 1).1.toBits ∧
      |value (jseq xa (jinit xa) 1).1.toBits - Jn 1 w| ≤ 12 * 𝐮 * modn w 1 := by
    have hv : |value (jseq xa (jinit xa) 1).1.toBits - Jn 1 w| ≤ 12 * 𝐮 * modn w 1 := by
      rw [Jn_one, e1]; exact hj1
    exact ⟨start_facts hv (J_le_modn w 1) hM1 (by norm_num) (by norm_num) (Real.sqrt_nonneg _), hv⟩
  have hstep : ∀ k, k + 2 ≤ n → Finite (jseq xa (jinit xa) k).1.toBits →
      Finite (jseq xa (jinit xa) (k + 1)).1.toBits →
      |value (jseq xa (jinit xa) k).1.toBits| ≤ 1 →
      |value (jseq xa (jinit xa) (k + 1)).1.toBits| ≤ 1 →
      Finite (jseq xa (jinit xa) (k + 2)).1.toBits ∧
        |value (jseq xa (jinit xa) (k + 2)).1.toBits -
            (lam w (k + 1) * value (jseq xa (jinit xa) (k + 1)).1.toBits -
              value (jseq xa (jinit xa) k).1.toBits)| ≤
          𝐮 * (301 / 100 * lam w (k + 1) * |value (jseq xa (jinit xa) (k + 1)).1.toBits| +
            |value (jseq xa (jinit xa) k).1.toBits|) + 1 / 2 ^ 1070 := by
    intro k hk fa fb ma mb
    have hk40 : k < 2 ^ 40 := by omega
    obtain ⟨ht, hl⟩ := lam_word (w := w) k hk40 (2 * (UInt64.ofNat k + 1)) (two_mul_word k hk40) rfl
    have hTw : ((2 * (k + 1) : ℕ) : ℝ) / w ≤ 2 ^ 40 := by
      rw [div_le_iff₀ hw0]
      have : ((2 * (k + 1) : ℕ) : ℝ) ≤ 2 ^ 33 := by exact_mod_cast (show 2 * (k + 1) ≤ 2 ^ 33 by omega)
      nlinarith
    have h := step_bt fa fb ht hx (Nat.cast_nonneg _) (by linarith) hTw ma mb
    rw [hl] at h
    have e2 : (jseq xa (jinit xa) (k + 2)).1 = (jseq xa (jinit xa) (k + 1)).1 *
        ((2 * (UInt64.ofNat k + 1)).toFloat / xa) - (jseq xa (jinit xa) k).1 := rfl
    rw [e2]
    exact h
  exact forward w hw4 hwb (fun k => Jn k w) (J_solution w hw0.ne') (J_le_modn w)
    (fun k => (jseq xa (jinit xa) k).1) n hn hn2 h0 h1 hstep n le_rfl

/-- `jn`'s forward loop for `4 ≤ x ≤ 2^302` and `2 n ≤ x`. -/
theorem jn_forward (xa : Float) (n : UInt64) (hxf : Finite xa.toBits)
    (hpos : xa.toBits.toNat < 2 ^ 63) (hw4 : 4 ≤ value xa.toBits) (hwb : value xa.toBits ≤ 2 ^ 302)
    (hn1 : 1 ≤ n.toNat) (hn : 2 * (n.toNat : ℝ) ≤ value xa.toBits) (hn2 : n.toNat ≤ 2 ^ 31) :
    Finite (LeanExe.loop (n - 1) (jinit xa) (jbody xa)).2.toBits ∧
      |value (LeanExe.loop (n - 1) (jinit xa) (jbody xa)).2.toBits - Jn n.toNat (value xa.toBits)| ≤
        (17 + 12 * (n.toNat : ℝ)) * 𝐮 * modn (value xa.toBits) n.toNat := by
  rw [loop_result _ _ n hn1]
  exact jn_forward_w xa _ rfl n.toNat hxf hpos hw4 hwb hn hn2

/-- The step of `yn`'s loop. -/
def ystep (x : Float) (s : UInt64 × Float × Float) : UInt64 × Float × Float :=
  (s.1 + 1, s.2.2, ((2 * s.1).toFloat / x) * s.2.2 - s.2.1)

/-- The condition of `yn`'s loop. -/
def ycond (n : UInt64) (s : UInt64 × Float × Float) : Bool :=
  s.1 < n && s.2.2.toBits >>> 32 != 0xFFF00000

/-- The values of `yn`'s loop. -/
def ya (x a0 a1 : Float) : ℕ → Float
  | 0 => a0
  | 1 => a1
  | j + 2 => ((2 * UInt64.ofNat (j + 1)).toFloat / x) * ya x a0 a1 (j + 1) - ya x a0 a1 j

theorem ofNat_succ (j : ℕ) : UInt64.ofNat (j + 1) + 1 = UInt64.ofNat (j + 1 + 1) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  simp only [UInt64.reduceToNat, Nat.reducePow]
  omega

theorem ystep_iter (x a0 a1 : Float) : ∀ j : ℕ,
    (ystep x)^[j] ((1 : UInt64), a0, a1) = (UInt64.ofNat (j + 1), ya x a0 a1 j, ya x a0 a1 (j + 1))
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', ystep_iter x a0 a1 j]
    show (UInt64.ofNat (j + 1) + 1, ya x a0 a1 (j + 1),
        ((2 * UInt64.ofNat (j + 1)).toFloat / x) * ya x a0 a1 (j + 1) - ya x a0 a1 j) = _
    rw [ofNat_succ]
    rfl

theorem high_ne_of_finite (w : UInt64) (hw : Finite w) : (w >>> 32 != 0xFFF00000) = true := by
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite Wasm.IEEE64.exponent at hw
  simp only [bne_iff_ne, ne_eq] at hw ⊢
  rw [← UInt64.toNat_inj, UInt64.toNat_shiftRight]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow] at hw ⊢
  omega

/-- `yn`'s loop stops after `n - 1` steps when the values stay finite. -/
theorem yn_loop_eq (x a0 a1 : Float) (n : UInt64) (hn1 : 1 ≤ n.toNat) (hn2 : n.toNat ≤ 2 ^ 31)
    (hfin : ∀ j, 1 ≤ j → j < n.toNat → Finite (ya x a0 a1 j).toBits) :
    LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), a0, a1) (ycond n) (ystep x) =
      (UInt64.ofNat n.toNat, ya x a0 a1 (n.toNat - 1), ya x a0 a1 n.toNat) := by
  unfold LeanExe.repeatWhile
  rw [go_iterate (ycond n) (ystep x) (n.toNat - 1) _ _ (by simp only [UInt64.reduceToNat]; omega)]
  · rw [ystep_iter, show n.toNat - 1 + 1 = n.toNat by omega]
  · intro j hj
    rw [ystep_iter]
    simp only [ycond, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, high_ne_of_finite _ (hfin (j + 1) (by omega) (by omega))⟩
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega
  · rw [ystep_iter]
    simp only [ycond, Bool.and_eq_false_iff]
    left
    rw [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']
    simp only [Nat.reducePow]
    omega

/-- The values of `yn`'s loop from `y0 x` and `y1 x`. -/
def yf (x : Float) : ℕ → Float := ya x (Bessel.y0 x) (Bessel.y1 x)

/-- `yn`'s forward values for `4 ≤ x ≤ 2^302` and `2 n ≤ x`, with `w` the value of `x`. -/
theorem yn_forward_w (xa : Float) (w : ℝ) (hwx : value xa.toBits = w) (n : ℕ)
    (hxf : Finite xa.toBits) (hpos : xa.toBits.toNat < 2 ^ 63) (hw4 : 4 ≤ w) (hwb : w ≤ 2 ^ 302)
    (hn : 2 * (n : ℝ) ≤ w) (hn2 : n ≤ 2 ^ 31) :
    ∀ m, m ≤ n → Finite (yf xa m).toBits ∧
      |value (yf xa m).toBits - Yn w m| ≤ (17 + 12 * (m : ℝ)) * 𝐮 * modn w m := by
  have hw0 : 0 < w := by linarith
  obtain ⟨h2, -⟩ := big_facts xa hxf hpos (by rw [hwx]; exact hw4)
  have hM0 := modn_le w hw4 0 (by norm_num; linarith)
  have hM1 := modn_le w hw4 1 (by norm_num; linarith)
  have hy0 := BesselY0Large.y0_large xa hxf hpos h2
  have hy1 := BesselY1Large.y1_large xa hxf hpos h2
  rw [hwx] at hy0 hy1
  have hx : FApprox xa w 0 := by rw [← hwx]; exact fapprox_exact xa hxf
  have e0 : modn w 0 = √(J0 w ^ 2 + Y0 w ^ 2) := by unfold modn; rw [Jn_zero, Yn_zero]
  have e1 : modn w 1 = √(J1 w ^ 2 + Y1 w ^ 2) := by unfold modn; rw [Jn_one, Yn_one]
  have h0 : Finite (yf xa 0).toBits ∧ |value (yf xa 0).toBits - Yn w 0| ≤ 10 * 𝐮 * modn w 0 := by
    have hv : |value (yf xa 0).toBits - Yn w 0| ≤ 10 * 𝐮 * modn w 0 := by
      rw [Yn_zero, e0]; exact hy0
    exact ⟨start_facts hv (Y_le_modn w 0) hM0 (by norm_num) (by norm_num) (Real.sqrt_nonneg _), hv⟩
  have h1 : Finite (yf xa 1).toBits ∧ |value (yf xa 1).toBits - Yn w 1| ≤ 12 * 𝐮 * modn w 1 := by
    have hv : |value (yf xa 1).toBits - Yn w 1| ≤ 12 * 𝐮 * modn w 1 := by
      rw [Yn_one, e1]; exact hy1
    exact ⟨start_facts hv (Y_le_modn w 1) hM1 (by norm_num) (by norm_num) (Real.sqrt_nonneg _), hv⟩
  have hstep : ∀ k, k + 2 ≤ n → Finite (yf xa k).toBits → Finite (yf xa (k + 1)).toBits →
      |value (yf xa k).toBits| ≤ 1 → |value (yf xa (k + 1)).toBits| ≤ 1 →
      Finite (yf xa (k + 2)).toBits ∧
        |value (yf xa (k + 2)).toBits -
            (lam w (k + 1) * value (yf xa (k + 1)).toBits - value (yf xa k).toBits)| ≤
          𝐮 * (301 / 100 * lam w (k + 1) * |value (yf xa (k + 1)).toBits| +
            |value (yf xa k).toBits|) + 1 / 2 ^ 1070 := by
    intro k hk fa fb ma mb
    have hk40 : k < 2 ^ 40 := by omega
    obtain ⟨ht, hl⟩ := lam_word (w := w) k hk40 (2 * UInt64.ofNat (k + 1)) (two_mul_word' k hk40) rfl
    have hTw : ((2 * (k + 1) : ℕ) : ℝ) / w ≤ 2 ^ 40 := by
      rw [div_le_iff₀ hw0]
      have : ((2 * (k + 1) : ℕ) : ℝ) ≤ 2 ^ 33 := by exact_mod_cast (show 2 * (k + 1) ≤ 2 ^ 33 by omega)
      nlinarith
    have h := step_tb fa fb ht hx (Nat.cast_nonneg _) (by linarith) hTw ma mb
    rw [hl] at h
    have e2 : yf xa (k + 2) = ((2 * UInt64.ofNat (k + 1)).toFloat / xa) * yf xa (k + 1) - yf xa k :=
      rfl
    rw [e2]
    exact h
  exact forward w hw4 hwb (Yn w) (Y_solution w) (Y_le_modn w) (yf xa) n hn hn2 h0 h1 hstep

/-- `yn`'s forward loop for `4 ≤ x ≤ 2^302` and `2 n ≤ x`. -/
theorem yn_forward (xa : Float) (n : UInt64) (hxf : Finite xa.toBits)
    (hpos : xa.toBits.toNat < 2 ^ 63) (hw4 : 4 ≤ value xa.toBits) (hwb : value xa.toBits ≤ 2 ^ 302)
    (hn1 : 1 ≤ n.toNat) (hn : 2 * (n.toNat : ℝ) ≤ value xa.toBits) (hn2 : n.toNat ≤ 2 ^ 31) :
    Finite (LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 xa, Bessel.y1 xa) (ycond n)
        (ystep xa)).2.2.toBits ∧
      |value (LeanExe.repeatWhile 0xFFFFFFFF ((1 : UInt64), Bessel.y0 xa, Bessel.y1 xa) (ycond n)
        (ystep xa)).2.2.toBits - Yn (value xa.toBits) n.toNat| ≤
        (17 + 12 * (n.toNat : ℝ)) * 𝐮 * modn (value xa.toBits) n.toNat := by
  have hall := yn_forward_w xa _ rfl n.toNat hxf hpos hw4 hwb hn hn2
  rw [yn_loop_eq xa _ _ n hn1 hn2 (fun j _ hj => (hall j hj.le).1)]
  exact hall n.toNat le_rfl

#print axioms jn_forward
#print axioms yn_forward

end Library.Numerics.Float64.Bessel.BesselOrderLoops
