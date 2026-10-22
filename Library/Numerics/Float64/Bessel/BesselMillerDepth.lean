import Library.Numerics.Float64.Bessel.BesselMillerCF
import Library.Numerics.Float64.Bessel.BesselOrderLoops

/-!
The depth loop of `jn`'s backward recurrence as a whole.  The start `(w, w (w + h) - 1, w + h, 1)`
satisfies `Good 0` (`good_zero`), each step keeps `Good` while `q₁ < 10^9` (`good_step`), and
since `Q 13 > 1.2 · 10^10` the condition fails within 12 steps (`exists_stop`).  The loop
therefore returns a depth `k ≤ 13` with `Q k = kern (n - 1) (n + k + 1) ≥ 9 · 10^8`
(`cf_depth`).
-/

namespace Library.Numerics.Float64.Bessel.BesselMillerDepth
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselOrderN BesselRecur
  BesselMillerReal BesselMillerCF BesselStepF

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

theorem value_two_f : FApprox (2.0 : Float) 2 0 := by
  unfold FApprox Approx
  have hb : (2.0 : Float).toBits = 0x4000000000000000 := rfl
  rw [hb, BesselJ0Large.value_two]
  exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by norm_num⟩

/-- The facts about `w = 2n/x` and `h = 2/x`. -/
theorem wh_facts (xa : Float) (n : UInt64) (hxf : Finite xa.toBits) (hw : 1 / 2 ^ 30 ≤ value xa.toBits)
    (hw2 : value xa.toBits < 2) (hn : 2 ≤ n.toNat) (hn2 : n.toNat ≤ 2 ^ 31) :
    FApprox ((n + n).toFloat / xa) (lam (value xa.toBits) n.toNat)
        (2 * 𝐮 * lam (value xa.toBits) n.toNat) ∧
      FApprox (2.0 / xa) (2 / value xa.toBits) (2 * 𝐮 * (2 / value xa.toBits)) := by
  set w := value xa.toBits with hwdef
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hnn : (n + n).toNat = 2 * n.toNat := by
    rw [UInt64.toNat_add]; have := n.toNat_lt; simp only [Nat.reducePow] at this ⊢; omega
  have ht := toFloat_exact (n + n) (by rw [hnn]; omega)
  rw [hnn] at ht
  have hx : FApprox xa w 0 := by rw [hwdef]; exact fapprox_exact xa hxf
  have hl : lam w n.toNat = ((2 * n.toNat : ℕ) : ℝ) / w := by unfold lam; push_cast; ring
  have hl2 : 2 ≤ lam w n.toNat := by
    have := lam_gt w hw0 hw2 n.toNat (by omega)
    have : (2 : ℝ) ≤ n.toNat := by exact_mod_cast hn
    linarith
  have hlb : lam w n.toNat ≤ 2 ^ 63 := lam_le w hw n.toNat (by omega)
  have hd := fapprox_div ht hx ((2 * n.toNat : ℕ) : ℝ) w (by rw [abs_of_nonneg (by positivity)])
    (le_abs_self w) (by linarith) (lam w n.toNat) (by rw [add_zero, sub_zero, hl])
    (by linarith [show (2 : ℝ) ^ 63 < 2 ^ 1022 by norm_num])
  rw [← hl] at hd
  have h2w : 1 ≤ 2 / w := by rw [le_div_iff₀ hw0]; linarith
  have h2wb : 2 / w ≤ 2 ^ 31 := by
    rw [div_le_iff₀ hw0]; nlinarith
  have hh := fapprox_div value_two_f hx 2 w (by norm_num) (le_abs_self w) (by linarith) (2 / w)
    (by simp) (by linarith [show (2 : ℝ) ^ 31 < 2 ^ 1022 by norm_num])
  constructor
  · refine fmono hd ?_
    rw [hu]
    have : (0 + ((2 * n.toNat : ℕ) : ℝ) * 0 / w) / (w - 0) = 0 := by simp
    rw [this]
    nlinarith
  · refine fmono hh ?_
    rw [hu]
    have : (0 + 2 * 0 / w) / (w - 0) = 0 := by simp
    rw [this]
    nlinarith

/-- The start of the depth loop. -/
def cinit (W H : Float) : Float × Float × Float × UInt64 := (W, W * (W + H) - 1.0, W + H, 1)

theorem c1e9_facts : Finite (Float.ofBits 0x41CDCD6500000000).toBits ∧
    value (Float.ofBits 0x41CDCD6500000000).toBits = 1000000000 := by
  have h := fapprox_ofBits _ finite_1e9
  refine ⟨h.1, ?_⟩
  have := abs_nonpos_iff.mp h.2
  rw [value_1e9] at this
  linarith

/-- The condition in terms of values. -/
theorem ccond_iff (s : Float × Float × Float × UInt64) (hf : Finite s.2.1.toBits) :
    ccond s = true ↔ value s.2.1.toBits < 1000000000 := by
  unfold ccond
  rw [decide_eq_true_iff, BesselSmallJ0.flt_iff _ _ hf c1e9_facts.1, c1e9_facts.2]

theorem good_zero {W H : Float} {w : ℝ} {n : ℕ} (hw : 1 / 2 ^ 30 ≤ w) (hw2 : w < 2) (hn : 2 ≤ n)
    (hn2 : n ≤ 2 ^ 31) (hW : FApprox W (lam w n) (2 * 𝐮 * lam w n))
    (hH : FApprox H (2 / w) (2 * 𝐮 * (2 / w))) : Good w n 0 (cinit W H) := by
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hl := lam_gt w hw0 hw2 n (by omega)
  have hl1 := lam_gt w hw0 hw2 (n + 1) (by omega)
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at hl1
  have hL := lam_le w hw (n + 1) (by omega)
  have hL0 := lam_le w hw n (by omega)
  have hsum : lam w n + 2 / w = lam w (n + 0 + 1) := by unfold lam; push_cast; ring
  have hd : 0 ≤ 2 / w := by positivity
  -- `w + h`
  have hz : FApprox (W + H) (lam w (n + 0 + 1)) (Zb 0 * lam w (n + 0 + 1)) := by
    have hs := fapprox_add hW hH (lam w (n + 0 + 1) * (1 + 1 / 2 ^ 40)) (by
      rw [hsum, abs_of_nonneg (by linarith)]
      rw [← hsum, hu]
      nlinarith) (by rw [← hsum]; nlinarith [show (2 : ℝ) ^ 63 * 2 < 2 ^ 1023 by norm_num])
    rw [hsum] at hs
    refine fmono hs ?_
    unfold Zb
    rw [← hsum, hu]
    push_cast
    nlinarith
  refine ⟨rfl, ?_, ?_, hz⟩
  · show FApprox W (Q w n 0) (Eb 0 * Q w n 0)
    rw [Q_zero w hw0 n (by omega)]
    refine fmono hW ?_
    unfold Eb
    rw [hu]
    norm_num
    nlinarith
  · show FApprox (W * (W + H) - 1.0) (Q w n (0 + 1)) (Eb 0 * Q w n (0 + 1))
    have hone : FApprox (1.0 : Float) 1 (2 * 𝐮 * 1) := fmono fapprox_one (by rw [hu]; norm_num)
    have hz' : FApprox (W + H) (lam w (n + 1)) (4 * 𝐮 * lam w (n + 1)) := by
      have := hz
      unfold Zb at this
      simpa using this
    have hr := rec_step' hone hW hz' (by norm_num) (by linarith) (by linarith) (by nlinarith)
      (by nlinarith) (by nlinarith) (by nlinarith [show (2 : ℝ) ^ 63 * 2 ^ 63 ≤ 2 ^ 200 by norm_num])
      (by rw [hu]; norm_num) (by rw [hu]; norm_num) (by rw [hu]; norm_num) (by rw [hu]; norm_num)
    rw [show (0 + 1 : ℕ) = 1 from rfl, Q_one w hw0 n (by omega)]
    refine fmono hr ?_
    unfold Eb
    have hq : 0 ≤ lam w (n + 1) * lam w n - 1 := by nlinarith
    rw [hu]
    norm_num
    nlinarith

theorem Eb_mono (j : ℕ) : Eb j ≤ Eb (j + 1) := by
  unfold Eb
  have : (3 : ℝ) ^ j ≤ 3 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have : (0 : ℝ) ≤ 𝐮 := by norm_num [unitRoundoff64]
  nlinarith

theorem good_step {H : Float} {w : ℝ} {n : ℕ} (hw : 1 / 2 ^ 30 ≤ w) (hw2 : w < 2) (hn : 2 ≤ n)
    (hn2 : n ≤ 2 ^ 31) (hH : FApprox H (2 / w) (2 * 𝐮 * (2 / w))) (j : ℕ) (hj : j < 12)
    (s : Float × Float × Float × UInt64) (hs : Good w n j s)
    (hc : value s.2.1.toBits < 1000000000) : Good w n (j + 1) (cstep H s) := by
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  obtain ⟨hk, h0, h1, hz⟩ := hs
  obtain ⟨g1, g2, g3, g4⟩ := Q_grow w hw0 hw2 n hn j
  obtain ⟨g1', g2', g3', g4'⟩ := Q_grow w hw0 hw2 n hn (j + 1)
  obtain ⟨hE50, hE⟩ := Eb_small j (by omega)
  obtain ⟨hZ0, hZ⟩ := Zb_small (j + 1) (by omega)
  have hE0 : 0 ≤ Eb j := le_trans (by rw [hu]; norm_num) hE50
  have hz' := z_step n j hw (by omega) hz hH (by omega)
  have hlam := lam_gt w hw0 hw2 (n + j + 2) (by omega)
  have hL := lam_le w hw (n + j + 2) (by omega)
  have hjr : (0 : ℝ) ≤ (n + j + 2 : ℕ) := Nat.cast_nonneg _
  have hl2 : 2 ≤ lam w (n + j + 2) := by
    have : (2 : ℝ) ≤ ((n + j + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n + j + 2 by omega)
    linarith
  -- `Q (j + 1) ≤ 2^31` from the condition
  have hQb : Q w n (j + 1) ≤ 2 ^ 31 := by
    have := (abs_le.mp h1.2).1
    have : Eb j * Q w n (j + 1) ≤ 1 / 2 ^ 25 * Q w n (j + 1) :=
      mul_le_mul_of_nonneg_right hE (by linarith)
    nlinarith
  have hQs := Q_succ w hw0 n j
  have hr := rec_step h0 h1 hz' (by linarith) (by linarith) (by linarith) (by rw [← hQs]; linarith)
    (by rw [← hQs]; linarith) (by rw [← hQs]; nlinarith)
    (by nlinarith [show (2 : ℝ) ^ 63 * 2 ^ 31 ≤ 2 ^ 200 by norm_num]) hE hZ hE0 hZ0
  rw [← hQs] at hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · show s.2.2.2 + 1 = UInt64.ofNat (j + 1 + 1)
    rw [hk]; exact BesselOrderLoops.ofNat_succ j
  · show FApprox s.2.1 (Q w n (j + 1)) (Eb (j + 1) * Q w n (j + 1))
    exact fmono h1 (mul_le_mul_of_nonneg_right (Eb_mono j) (by linarith))
  · show FApprox ((s.2.2.1 + H) * s.2.1 - s.1) (Q w n (j + 1 + 1)) (Eb (j + 1) * Q w n (j + 1 + 1))
    refine fmono hr (mul_le_mul_of_nonneg_right ?_ (by linarith))
    unfold Eb Zb
    have h3 : (3 : ℝ) ^ (j + 1) = 3 * 3 ^ j := by rw [pow_succ]; ring
    rw [h3]
    have hj' : (j : ℝ) ≤ 11 := by exact_mod_cast (show j ≤ 11 by omega)
    have : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
    push_cast
    nlinarith
  · show FApprox (s.2.2.1 + H) (lam w (n + (j + 1) + 1)) (Zb (j + 1) * lam w (n + (j + 1) + 1))
    rw [show n + (j + 1) + 1 = n + j + 2 by ring]
    exact hz'

/-- The iterates keep `Good` while the condition holds. -/
theorem good_iter {W H : Float} {w : ℝ} {n : ℕ} (hw : 1 / 2 ^ 30 ≤ w) (hw2 : w < 2) (hn : 2 ≤ n)
    (hn2 : n ≤ 2 ^ 31) (hW : FApprox W (lam w n) (2 * 𝐮 * lam w n))
    (hH : FApprox H (2 / w) (2 * 𝐮 * (2 / w))) :
    ∀ j, j ≤ 12 → (∀ i < j, value ((cstep H)^[i] (cinit W H)).2.1.toBits < 1000000000) →
      Good w n j ((cstep H)^[j] (cinit W H)) := by
  intro j
  induction j with
  | zero => intro _ _; exact good_zero hw hw2 hn hn2 hW hH
  | succ j ih =>
    intro hj hc
    have hg := ih (by omega) (fun i hi => hc i (by omega))
    rw [Function.iterate_succ_apply']
    exact good_step hw hw2 hn hn2 hH j (by omega) _ hg (hc j (by omega))

/-- The loop stops within 12 steps. -/
theorem exists_stop {W H : Float} {w : ℝ} {n : ℕ} (hw : 1 / 2 ^ 30 ≤ w) (hw2 : w < 2) (hn : 2 ≤ n)
    (hn2 : n ≤ 2 ^ 31) (hW : FApprox W (lam w n) (2 * 𝐮 * lam w n))
    (hH : FApprox H (2 / w) (2 * 𝐮 * (2 / w))) :
    ∃ j, ¬ value ((cstep H)^[j] (cinit W H)).2.1.toBits < 1000000000 ∧ j ≤ 12 := by
  by_contra hne
  push Not at hne
  have hall : ∀ i < 12, value ((cstep H)^[i] (cinit W H)).2.1.toBits < 1000000000 :=
    fun i hi => by
      by_contra h
      exact absurd (hne i (not_lt.mp h)) (by omega)
  have hg := good_iter hw hw2 hn hn2 hW hH 12 le_rfl hall
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hq := Q_twelve w hw0 hw2 n hn
  obtain ⟨-, g2, -, -⟩ := Q_grow w hw0 hw2 n hn 12
  obtain ⟨-, hE⟩ := Eb_small 12 le_rfl
  have hv := (abs_le.mp hg.2.2.1.2).1
  have : Eb 12 * Q w n (12 + 1) ≤ 1 / 2 ^ 25 * Q w n (12 + 1) :=
    mul_le_mul_of_nonneg_right hE (by linarith)
  have h12 := hne 12 (by
    by_contra hlt
    push_neg at hlt
    nlinarith)
  omega

/-- The depth loop returns a depth `K ≤ 13` with `Q K ≥ 9 · 10^8`. -/
theorem cf_depth {W H : Float} {w : ℝ} {n : ℕ} (hw : 1 / 2 ^ 30 ≤ w) (hw2 : w < 2) (hn : 2 ≤ n)
    (hn2 : n ≤ 2 ^ 31) (hW : FApprox W (lam w n) (2 * 𝐮 * lam w n))
    (hH : FApprox H (2 / w) (2 * 𝐮 * (2 / w))) :
    ∃ K : ℕ, 1 ≤ K ∧ K ≤ 13 ∧
      (LeanExe.repeatWhile 0xFFFFFFFF (cinit W H) ccond (cstep H)).2.2.2 = UInt64.ofNat K ∧
      900000000 ≤ Q w n K := by
  classical
  have hex := exists_stop hw hw2 hn hn2 hW hH
  let J := Nat.find hex
  have hJ : ¬ value ((cstep H)^[J] (cinit W H)).2.1.toBits < 1000000000 ∧ J ≤ 12 := Nat.find_spec hex
  have hmin : ∀ i < J, value ((cstep H)^[i] (cinit W H)).2.1.toBits < 1000000000 := by
    intro i hi
    by_contra h
    exact Nat.find_min hex hi ⟨h, by omega⟩
  have hg := good_iter hw hw2 hn hn2 hW hH J hJ.2 hmin
  have hgi : ∀ i < J, Good w n i ((cstep H)^[i] (cinit W H)) := fun i hi =>
    good_iter hw hw2 hn hn2 hW hH i (by omega) (fun i' hi' => hmin i' (by omega))
  have hrep : LeanExe.repeatWhile 0xFFFFFFFF (cinit W H) ccond (cstep H) = (cstep H)^[J] (cinit W H) := by
    unfold LeanExe.repeatWhile
    apply go_iterate ccond (cstep H) J _ _ (by simp only [UInt64.reduceToNat]; omega)
    · intro i hi
      exact (ccond_iff _ (hgi i hi).2.2.1.1).mpr (hmin i hi)
    · rw [Bool.eq_false_iff]
      intro h
      exact hJ.1 ((ccond_iff _ hg.2.2.1.1).mp h)
  refine ⟨J + 1, by omega, by omega, by rw [hrep]; exact hg.1, ?_⟩
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  obtain ⟨g1, -, -, -⟩ := Q_grow w hw0 hw2 n hn (J + 1)
  obtain ⟨-, hE⟩ := Eb_small J hJ.2
  have hv := (abs_le.mp hg.2.2.1.2).2
  have : Eb J * Q w n (J + 1) ≤ 1 / 2 ^ 25 * Q w n (J + 1) :=
    mul_le_mul_of_nonneg_right hE (by linarith)
  have := hJ.1
  push Not at this
  nlinarith

#print axioms wh_facts
#print axioms cf_depth

end Library.Numerics.Float64.Bessel.BesselMillerDepth
