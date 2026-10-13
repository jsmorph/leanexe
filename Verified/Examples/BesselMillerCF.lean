import Verified.Examples.BesselMillerReal
import Verified.Examples.BesselStepF
import Verified.Examples.BesselSmallJ0

/-!
The loop of `jn`'s backward recurrence that chooses the depth `k` of the continued fraction, for
`2^-30 ≤ x < 2` and `2 ≤ n ≤ 2^31`.  From `q₀ = w = 2n/x`, `q₁ = w (w + h) - 1` with `h = 2/x`, it
runs `z ← z + h`, `(q₀, q₁) ← (q₁, z q₁ - q₀)` while `q₁ < 10^9`.  In exact arithmetic the `q`
are the continuants `Q j = kern (n - 1) (n + j + 1)`, which satisfy the same recurrence
(`Q_succ`), grow by at least `j + 2` per step (`Q_grow`), and reach `2 · 13!` by `j = 12`.  One
step of the recurrence multiplies a relative error by at most 3 and adds `2 Z + 7 u`
(`rec_step`).  The module defines the loop's step `cstep`, its condition `ccond`, and the error
bounds `Eb j = (100 · 3^j - 50) u` and `Zb j = (3 j + 4) u` with which `BesselMillerDepth` shows that
the loop stops after at most 12 steps with `Q k ≥ 9 · 10^8`.
-/

namespace Verified.Examples.BesselMillerCF
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselOrderN BesselRecur
  BesselMillerReal BesselStepF

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- The subtraction of a growing three-term recurrence, from the product's error. -/
theorem rec_core {p a : Float} {A B L E Z ep : ℝ} (hp : FApprox p (L * B) ep)
    (hepb : ep ≤ L * B * (Z + E + 2 * 𝐮) + 1 / 2 ^ 1075) (ha : FApprox a A (E * A))
    (hA : 0 ≤ A) (hR1 : 1 ≤ L * B - A) (hAR : A ≤ L * B - A)
    (hLB : L * B ≤ 2 * (L * B - A)) (hmag : L * B ≤ 2 ^ 200)
    (hE : E ≤ 1 / 2 ^ 25) (hZ : Z ≤ 1 / 2 ^ 40) (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z) :
    FApprox (p - a) (L * B - A) ((3 * E + 2 * Z + 7 * 𝐮) * (L * B - A)) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hLB0 : 0 ≤ L * B := by linarith
  have hep0 : ep ≤ 2 ^ 200 + 1 := by
    have h5 : Z + E + 2 * 𝐮 ≤ 1 := by
      rw [hu]; linarith [show (1 : ℝ) / 2 ^ 40 + 1 / 2 ^ 25 + 2 * (1 / 2 ^ 53) ≤ 1 by norm_num]
    have := mul_le_mul hmag h5 (by rw [hu]; positivity) (by positivity)
    linarith [show (1 : ℝ) / 2 ^ 1075 ≤ 1 by norm_num]
  have hr := fapprox_sub hp ha (|L * B - A| + (ep + E * A)) le_rfl (by
    rw [abs_of_nonneg (by linarith)]
    have : E * A ≤ 2 ^ 200 := by nlinarith
    linarith [show (2 : ℝ) ^ 200 + 2 ^ 200 + 1 + 2 ^ 200 < 2 ^ 1023 by norm_num])
  refine fmono hr ?_
  rw [abs_of_nonneg (by linarith)]
  have hEA : E * A ≤ E * (L * B - A) := mul_le_mul_of_nonneg_left hAR hE0
  have hep2 : ep ≤ 2 * (L * B - A) * (Z + E + 2 * 𝐮) + 1 / 2 ^ 1075 := by
    have : L * B * (Z + E + 2 * 𝐮) ≤ 2 * (L * B - A) * (Z + E + 2 * 𝐮) :=
      mul_le_mul_of_nonneg_right hLB (by rw [hu]; positivity)
    linarith
  rw [hu] at hep2 ⊢
  have hη : 1 / 2 ^ 1075 ≤ (L * B - A) * (1 / 2 ^ 60) := by nlinarith
  have hsum : 2 * (Z + E + 2 * (1 / 2 ^ 53)) + 1 / 2 ^ 60 + E ≤ 1 := by
    linarith [show (2 : ℝ) * (1 / 2 ^ 40 + 1 / 2 ^ 25 + 2 * (1 / 2 ^ 53)) + 1 / 2 ^ 60 + 1 / 2 ^ 25 ≤ 1 by
      norm_num]
  have hsm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ L * B - A by linarith)
  nlinarith

/-- The product's error for `z ⊗ b`. -/
theorem prod_err {b z : Float} {B L E Z : ℝ} (hb : FApprox b B (E * B)) (hz : FApprox z L (Z * L))
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hmag : L * B ≤ 2 ^ 200)
    (hE : E ≤ 1 / 2 ^ 25) (hZ : Z ≤ 1 / 2 ^ 40) (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z) :
    ∃ ep, FApprox (z * b) (L * B) ep ∧ ep ≤ L * B * (Z + E + 2 * 𝐮) + 1 / 2 ^ 1075 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hLB0 : 0 ≤ L * B := mul_nonneg hL hB
  have hZE : Z * E ≤ 1 / 2 ^ 60 := by
    calc Z * E ≤ 1 / 2 ^ 40 * (1 / 2 ^ 25) := mul_le_mul hZ hE hE0 (by norm_num)
      _ ≤ 1 / 2 ^ 60 := by norm_num
  have h3 : (1 + Z) * (1 + E) ≤ 1 + 1 / 2 ^ 24 := by nlinarith
  have hp := fapprox_mul hz hb L B (by rw [abs_of_nonneg hL]) (by rw [abs_of_nonneg hB])
    ((L + Z * L) * (B + E * B)) le_rfl (by
      have h1 : (L + Z * L) * (B + E * B) = L * B * ((1 + Z) * (1 + E)) := by ring
      have h2 : (1 + Z) * (1 + E) ≤ 2 := by linarith [show (1 : ℝ) + 1 / 2 ^ 24 ≤ 2 by norm_num]
      rw [h1]
      have := mul_le_mul_of_nonneg_left h2 hLB0
      linarith [show (2 : ℝ) ^ 200 * 2 < 2 ^ 1022 by norm_num])
  refine ⟨_, hp, ?_⟩
  rw [hu]
  have e1 : Z * L * B + L * (E * B) + Z * L * (E * B) + (L + Z * L) * (B + E * B) / 2 ^ 53 =
      L * B * (Z + E + Z * E + (1 + Z) * (1 + E) / 2 ^ 53) := by ring
  have h4 : Z + E + Z * E + (1 + Z) * (1 + E) / 2 ^ 53 ≤ Z + E + 2 * (1 / 2 ^ 53) := by
    have : (1 + Z) * (1 + E) / 2 ^ 53 ≤ (1 + 1 / 2 ^ 24) / 2 ^ 53 :=
      div_le_div_of_nonneg_right h3 (by positivity)
    have : (1 + 1 / 2 ^ 24 : ℝ) / 2 ^ 53 + 1 / 2 ^ 60 ≤ 2 * (1 / 2 ^ 53) := by norm_num
    linarith
  have := mul_le_mul_of_nonneg_left h4 hLB0
  linarith

/-- The product's error for `b ⊗ z`. -/
theorem prod_err' {b z : Float} {B L E Z : ℝ} (hb : FApprox b B (E * B)) (hz : FApprox z L (Z * L))
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hmag : L * B ≤ 2 ^ 200)
    (hE : E ≤ 1 / 2 ^ 25) (hZ : Z ≤ 1 / 2 ^ 40) (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z) :
    ∃ ep, FApprox (b * z) (L * B) ep ∧ ep ≤ L * B * (Z + E + 2 * 𝐮) + 1 / 2 ^ 1075 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hLB0 : 0 ≤ L * B := mul_nonneg hL hB
  have hZE : Z * E ≤ 1 / 2 ^ 60 := by
    calc Z * E ≤ 1 / 2 ^ 40 * (1 / 2 ^ 25) := mul_le_mul hZ hE hE0 (by norm_num)
      _ ≤ 1 / 2 ^ 60 := by norm_num
  have h3 : (1 + Z) * (1 + E) ≤ 1 + 1 / 2 ^ 24 := by nlinarith
  have hp := fapprox_mul hb hz B L (by rw [abs_of_nonneg hB]) (by rw [abs_of_nonneg hL])
    ((B + E * B) * (L + Z * L)) le_rfl (by
      have h1 : (B + E * B) * (L + Z * L) = L * B * ((1 + Z) * (1 + E)) := by ring
      have h2 : (1 + Z) * (1 + E) ≤ 2 := by linarith [show (1 : ℝ) + 1 / 2 ^ 24 ≤ 2 by norm_num]
      rw [h1]
      have := mul_le_mul_of_nonneg_left h2 hLB0
      linarith [show (2 : ℝ) ^ 200 * 2 < 2 ^ 1022 by norm_num])
  rw [mul_comm B L] at hp
  refine ⟨_, hp, ?_⟩
  rw [hu]
  have e1 : E * B * L + B * (Z * L) + E * B * (Z * L) + (B + E * B) * (L + Z * L) / 2 ^ 53 =
      L * B * (Z + E + Z * E + (1 + Z) * (1 + E) / 2 ^ 53) := by ring
  have h4 : Z + E + Z * E + (1 + Z) * (1 + E) / 2 ^ 53 ≤ Z + E + 2 * (1 / 2 ^ 53) := by
    have : (1 + Z) * (1 + E) / 2 ^ 53 ≤ (1 + 1 / 2 ^ 24) / 2 ^ 53 :=
      div_le_div_of_nonneg_right h3 (by positivity)
    have : (1 + 1 / 2 ^ 24 : ℝ) / 2 ^ 53 + 1 / 2 ^ 60 ≤ 2 * (1 / 2 ^ 53) := by norm_num
    linarith
  have := mul_le_mul_of_nonneg_left h4 hLB0
  linarith

/-- One step `z ⊗ b ⊖ a` of a growing three-term recurrence, with relative errors. -/
theorem rec_step {a b z : Float} {A B L E Z : ℝ}
    (ha : FApprox a A (E * A)) (hb : FApprox b B (E * B)) (hz : FApprox z L (Z * L))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hR1 : 1 ≤ L * B - A) (hAR : A ≤ L * B - A)
    (hLB : L * B ≤ 2 * (L * B - A)) (hmag : L * B ≤ 2 ^ 200)
    (hE : E ≤ 1 / 2 ^ 25) (hZ : Z ≤ 1 / 2 ^ 40) (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z) :
    FApprox (z * b - a) (L * B - A) ((3 * E + 2 * Z + 7 * 𝐮) * (L * B - A)) := by
  obtain ⟨ep, hp, hepb⟩ := prod_err hb hz hB hL hmag hE hZ hE0 hZ0
  exact rec_core hp hepb ha hA hR1 hAR hLB hmag hE hZ hE0 hZ0

/-- One step `b ⊗ z ⊖ a`. -/
theorem rec_step' {a b z : Float} {A B L E Z : ℝ}
    (ha : FApprox a A (E * A)) (hb : FApprox b B (E * B)) (hz : FApprox z L (Z * L))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hR1 : 1 ≤ L * B - A) (hAR : A ≤ L * B - A)
    (hLB : L * B ≤ 2 * (L * B - A)) (hmag : L * B ≤ 2 ^ 200)
    (hE : E ≤ 1 / 2 ^ 25) (hZ : Z ≤ 1 / 2 ^ 40) (hE0 : 0 ≤ E) (hZ0 : 0 ≤ Z) :
    FApprox (b * z - a) (L * B - A) ((3 * E + 2 * Z + 7 * 𝐮) * (L * B - A)) := by
  obtain ⟨ep, hp, hepb⟩ := prod_err' hb hz hB hL hmag hE hZ hE0 hZ0
  exact rec_core hp hepb ha hA hR1 hAR hLB hmag hE hZ hE0 hZ0

/-- The continuants of the fraction. -/
noncomputable def Q (w : ℝ) (n : ℕ) (j : ℕ) : ℝ := kern w (n - 1) (n + j + 1)

theorem Q_zero (w : ℝ) (hw : 0 < w) (n : ℕ) (hn : 1 ≤ n) : Q w n 0 = lam w n := by
  have h0 : kern w (n - 1) n = 1 := by
    have := kern_succ w hw.ne' (n - 1); rwa [show n - 1 + 1 = n by omega] at this
  have := kern_recur w hw.ne' (n - 1) (n - 1)
  rw [show n - 1 + 2 = n + 1 by omega, show n - 1 + 1 = n by omega, kern_self, h0] at this
  unfold Q
  rw [show n + 0 + 1 = n + 1 by ring]
  linarith

theorem Q_succ (w : ℝ) (hw : 0 < w) (n j : ℕ) :
    Q w n (j + 2) = lam w (n + j + 2) * Q w n (j + 1) - Q w n j := by
  unfold Q
  have := kern_recur w hw.ne' (n - 1) (n + j + 1)
  rw [show n + j + 1 + 2 = n + (j + 2) + 1 by ring, show n + j + 1 + 1 = n + (j + 1) + 1 by ring,
    show n + (j + 1) + 1 = n + j + 2 by ring] at this
  rw [show n + (j + 1) + 1 = n + j + 2 by ring]
  exact this

theorem Q_one (w : ℝ) (hw : 0 < w) (n : ℕ) (hn : 1 ≤ n) :
    Q w n 1 = lam w (n + 1) * lam w n - 1 := by
  have h0 : kern w (n - 1) n = 1 := by
    have := kern_succ w hw.ne' (n - 1); rwa [show n - 1 + 1 = n by omega] at this
  have := kern_recur w hw.ne' (n - 1) n
  rw [show n + 2 = n + 1 + 1 by ring, show n + 1 = n + 0 + 1 by ring, h0] at this
  have hq0 := Q_zero w hw n hn
  unfold Q at hq0 ⊢
  rw [hq0] at this
  rw [show n + 1 + 1 = n + 0 + 1 + 1 by ring]
  linarith

/-- `λ_m > m` below 2. -/
theorem lam_gt (w : ℝ) (hw : 0 < w) (hw2 : w < 2) (m : ℕ) (hm : 1 ≤ m) : (m : ℝ) < lam w m := by
  unfold lam
  rw [lt_div_iff₀ hw]
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

/-- The continuants are positive, nondecreasing, and grow by `j + 2` at step `j + 1`. -/
theorem Q_grow (w : ℝ) (hw : 0 < w) (hw2 : w < 2) (n : ℕ) (hn : 2 ≤ n) : ∀ j : ℕ,
    1 ≤ Q w n j ∧ Q w n j ≤ Q w n (j + 1) ∧ ((j : ℝ) + 2) * Q w n j ≤ Q w n (j + 1) ∧
      2 * Q w n j ≤ lam w (n + j + 1) * Q w n (j + 1) := by
  intro j
  induction j with
  | zero =>
    rw [Q_one w hw n (by omega), Q_zero w hw n (by omega)]
    have h1 := lam_gt w hw hw2 n (by omega)
    have h2 := lam_gt w hw hw2 (n + 1) (by omega)
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2 ⊢
    refine ⟨by linarith, by nlinarith, by nlinarith, ?_⟩
    rw [show n + 0 + 1 = n + 1 from rfl]
    have hb : (3 : ℝ) < lam w (n + 1) := by linarith
    have ha : (2 : ℝ) < lam w n := by linarith
    have hab : 0 ≤ lam w (n + 1) * lam w n - 1 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.le) hab,
      mul_nonneg (sub_nonneg.mpr hb.le) (show (0 : ℝ) ≤ lam w n by linarith)]
  | succ j ih =>
    obtain ⟨a1, a2, a3, a4⟩ := ih
    have hs := Q_succ w hw n j
    have hl := lam_gt w hw hw2 (n + j + 2) (by omega)
    have hl' := lam_gt w hw hw2 (n + j + 1 + 1 + 1) (by omega)
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hs2 := Q_succ w hw n (j + 1)
    rw [show j + 1 + 2 = j + 3 by ring, show n + (j + 1) + 2 = n + j + 1 + 1 + 1 by ring,
      show j + 1 + 1 = j + 2 by ring] at hs2
    push_cast at hl hl' ⊢
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    rw [show j + 1 + 1 = j + 2 by ring, show n + (j + 1) + 1 = n + j + 2 by ring]
    have hq2 : Q w n (j + 2) = lam w (n + j + 2) * Q w n (j + 1) - Q w n j := hs
    refine ⟨by linarith, ?_, ?_, ?_⟩
    · rw [hq2]; nlinarith
    · rw [hq2]; nlinarith
    · rw [hq2]
      have hL : (4 : ℝ) ≤ lam w (n + j + 2) := by linarith
      have hLQ := mul_le_mul_of_nonneg_right hL (show (0 : ℝ) ≤ Q w n (j + 1) by linarith)
      have h1 : 3 * Q w n (j + 1) ≤ lam w (n + j + 2) * Q w n (j + 1) - Q w n j := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ lam w (n + j + 2) by linarith)]

/-- `Q 12 ≥ 2 · 13!`. -/
theorem Q_twelve (w : ℝ) (hw : 0 < w) (hw2 : w < 2) (n : ℕ) (hn : 2 ≤ n) :
    12454041600 ≤ Q w n 12 := by
  have hg := Q_grow w hw hw2 n hn
  have h0 : 2 ≤ Q w n 0 := by
    rw [Q_zero w hw n (by omega)]
    have := lam_gt w hw hw2 n (by omega)
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have s : ∀ j : ℕ, ((j : ℝ) + 2) * Q w n j ≤ Q w n (j + 1) := fun j => (hg j).2.2.1
  have q1 := s 0; have q2 := s 1; have q3 := s 2; have q4 := s 3; have q5 := s 4; have q6 := s 5
  have q7 := s 6; have q8 := s 7; have q9 := s 8; have q10 := s 9; have q11 := s 10
  have q12 := s 11
  norm_num at q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12
  linarith

/-- The step of the loop. -/
def cstep (h : Float) (s : Float × Float × Float × UInt64) : Float × Float × Float × UInt64 :=
  (s.2.1, (s.2.2.1 + h) * s.2.1 - s.1, s.2.2.1 + h, s.2.2.2 + 1)

/-- The condition of the loop. -/
def ccond (s : Float × Float × Float × UInt64) : Bool :=
  s.2.1 < Float.ofBits 0x41CDCD6500000000

/-- The error bound after `j` steps. -/
noncomputable def Eb (j : ℕ) : ℝ := (100 * 3 ^ j - 50) * 𝐮

noncomputable def Zb (j : ℕ) : ℝ := (3 * j + 4) * 𝐮

/-- The invariant after `j` steps. -/
def Good (w : ℝ) (n j : ℕ) (s : Float × Float × Float × UInt64) : Prop :=
  s.2.2.2 = UInt64.ofNat (j + 1) ∧ FApprox s.1 (Q w n j) (Eb j * Q w n j) ∧
    FApprox s.2.1 (Q w n (j + 1)) (Eb j * Q w n (j + 1)) ∧
    FApprox s.2.2.1 (lam w (n + j + 1)) (Zb j * lam w (n + j + 1))

theorem Eb_small (j : ℕ) (hj : j ≤ 12) : 50 * 𝐮 ≤ Eb j ∧ Eb j ≤ 1 / 2 ^ 25 := by
  unfold Eb
  have h1 : (1 : ℝ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
  have h2 : (3 : ℝ) ^ j ≤ 3 ^ 12 := pow_le_pow_right₀ (by norm_num) hj
  constructor
  · have : (0 : ℝ) ≤ 𝐮 := by norm_num [unitRoundoff64]
    nlinarith
  · rw [show 𝐮 = 1 / 2 ^ 53 from rfl]
    have : (100 * 3 ^ j - 50 : ℝ) ≤ 100 * 3 ^ 12 := by linarith
    calc (100 * 3 ^ j - 50) * (1 / 2 ^ 53 : ℝ) ≤ 100 * 3 ^ 12 * (1 / 2 ^ 53) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ 1 / 2 ^ 25 := by norm_num

theorem Zb_small (j : ℕ) (hj : j ≤ 12) : 0 ≤ Zb j ∧ Zb j ≤ 1 / 2 ^ 40 := by
  unfold Zb
  have hj' : (j : ℝ) ≤ 12 := by exact_mod_cast hj
  constructor
  · have : (0 : ℝ) ≤ 𝐮 := by norm_num [unitRoundoff64]
    positivity
  · rw [show 𝐮 = 1 / 2 ^ 53 from rfl]
    calc (3 * (j : ℝ) + 4) * (1 / 2 ^ 53) ≤ (3 * 12 + 4) * (1 / 2 ^ 53) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 1 / 2 ^ 40 := by norm_num

theorem value_1e9 : value (0x41CDCD6500000000 : UInt64) = 1000000000 := by
  rw [← ratOfWord_cast]
  have : ratOfWord 0x41CDCD6500000000 = 1000000000 := by decide +kernel
  rw [this]
  norm_num

theorem finite_1e9 : Finite (0x41CDCD6500000000 : UInt64) := by
  unfold CodeLib.IEEE64.Finite; decide

/-- `λ ≤ 2^63` for the indices of the loop. -/
theorem lam_le (w : ℝ) (hw : 1 / 2 ^ 30 ≤ w) (m : ℕ) (hm : m ≤ 2 ^ 32) : lam w m ≤ 2 ^ 63 := by
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  unfold lam
  rw [div_le_iff₀ hw0]
  have : (m : ℝ) ≤ 2 ^ 32 := by exact_mod_cast hm
  nlinarith

/-- The `z` update `z ⊕ h`. -/
theorem z_step {z h : Float} {w : ℝ} (n j : ℕ) (hw : 1 / 2 ^ 30 ≤ w) (hn : n + j + 2 ≤ 2 ^ 32)
    (hz : FApprox z (lam w (n + j + 1)) (Zb j * lam w (n + j + 1)))
    (hh : FApprox h (2 / w) (2 * 𝐮 * (2 / w))) (hj : j ≤ 12) :
    FApprox (z + h) (lam w (n + j + 2)) (Zb (j + 1) * lam w (n + j + 2)) := by
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hl : lam w (n + j + 1) + 2 / w = lam w (n + j + 2) := by
    unfold lam; push_cast; ring
  have hl0 : 0 ≤ lam w (n + j + 1) := by unfold lam; positivity
  have hd : 0 ≤ 2 / w := by positivity
  have hL := lam_le w hw (n + j + 2) hn
  obtain ⟨hZ0, hZ1⟩ := Zb_small j hj
  have hZ4 : 2 * 𝐮 ≤ Zb j := by
    unfold Zb
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
    nlinarith
  have hsmall : Zb j * lam w (n + j + 1) + 2 * 𝐮 * (2 / w) ≤ Zb j * lam w (n + j + 2) := by
    rw [← hl]
    have := mul_le_mul_of_nonneg_right hZ4 hd
    nlinarith
  have hs := fapprox_add hz hh (lam w (n + j + 2) * (1 + 1 / 2 ^ 39)) (by
    rw [abs_of_nonneg (by linarith), hl]
    have : Zb j * lam w (n + j + 2) ≤ 1 / 2 ^ 40 * lam w (n + j + 2) :=
      mul_le_mul_of_nonneg_right hZ1 (by linarith)
    nlinarith) (by nlinarith [show (2 : ℝ) ^ 63 * (1 + 1 / 2 ^ 39) < 2 ^ 1023 by norm_num])
  rw [hl] at hs
  refine fmono hs ?_
  have e : Zb (j + 1) = Zb j + 3 * 𝐮 := by unfold Zb; push_cast; ring
  rw [e]
  have hL0 : 0 ≤ lam w (n + j + 2) := by linarith
  have : lam w (n + j + 2) * (1 + 1 / 2 ^ 39) / 2 ^ 53 ≤ 3 * 𝐮 * lam w (n + j + 2) := by
    rw [hu]; nlinarith
  nlinarith

#print axioms rec_step
#print axioms Q_grow
#print axioms Q_twelve

end Verified.Examples.BesselMillerCF
