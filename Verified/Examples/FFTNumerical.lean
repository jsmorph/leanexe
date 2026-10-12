import Verified.Examples.FFTSpec
import Verified.Examples.FFTLoop
import Verified.Examples.FFTMath

namespace Verified.Examples.FFTNumerical

open CodeLib.IEEE64 LeanExe.ProofKit F64Approx FFTArithmetic FFTSpec

def direction (inverse : Bool) : Float := if inverse then 1.0 else -1.0

def pairAt (ys : Array Float) (k : Nat) : Float × Float := (ys[2 * k]!, ys[2 * k + 1]!)

def twiddles (n : UInt64) : Array (Float × Float) :=
  LeanExe.build (n / 2) fun m => Fourier.twiddle n m

def StageNear (xs : Array Float) (inverse : Bool) (p s : Nat) (ys : Array Float) : Prop :=
  ys.size = 2 * (xs.size / 2) ∧
    ∀ b k, b < 2 ^ (p - s) → k < 2 ^ s →
      PairFinite (pairAt ys (b * 2 ^ s + k)) ∧
      ‖pairValue (pairAt ys (b * 2 ^ s + k))‖ ≤ radixMagnitude s (FFTMath.stageMass xs p s b) ∧
      ‖pairValue (pairAt ys (b * 2 ^ s + k)) - FFTMath.stageValue xs inverse p s b k‖ ≤
        radixError s (FFTMath.stageMass xs p s b)

theorem signed_factor_near (inverse : Bool) (s : Float) (v e : ℝ) (hs : FApprox s v e) :
    FApprox ((if inverse then (1.0 : Float) else -1.0) * s)
      ((if inverse then (1 : ℝ) else -1) * v) e := by
  cases inverse with
  | false =>
    have h : FApprox ((-1.0 : Float) * s) (-v) e := by
      obtain ⟨hf, hv⟩ := FourierTwiddle.negOne_mul_exact s hs.1
      refine ⟨hf, ?_⟩
      rw [hv]
      simpa only [neg_sub_neg, abs_sub_comm] using hs.2
    simpa only [Bool.false_eq_true, ite_false, neg_one_mul] using h
  | true => simpa only [ite_true, one_mul] using FourierPositive.one_mul_near hs

theorem underflow_nonneg (s : Nat) : 0 ≤ underflow s := by
  induction s with
  | zero => exact le_rfl
  | succ s ih =>
    change 0 ≤ 2 * r * underflow s + nu
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (zero_le_one.trans r_ge_one)) ih) nu_nonneg

theorem underflow_monotone : Monotone underflow := by
  apply monotone_nat_of_le_succ
  intro s
  change underflow s ≤ 2 * r * underflow s + nu
  have hK := underflow_nonneg s
  have hR := r_ge_one
  have hN := nu_nonneg
  nlinarith [mul_nonneg (sub_nonneg.mpr hR) hK]

theorem radixMagnitude_nonneg (s : Nat) (A : ℝ) (hA : 0 ≤ A) :
    0 ≤ radixMagnitude s A :=
  add_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans r_ge_one) _) hA)
    (underflow_nonneg _)

theorem radixError_nonneg (s : Nat) (A : ℝ) (hA : 0 ≤ A) :
    0 ≤ radixError s A :=
  add_nonneg (mul_nonneg (sub_nonneg.mpr (one_le_pow₀ r_ge_one)) hA)
    (underflow_nonneg _)

theorem radixMagnitude_mono (s p : Nat) (A B : ℝ) (hs : s ≤ p)
    (hA : 0 ≤ A) (hAB : A ≤ B) : radixMagnitude s A ≤ radixMagnitude p B := by
  exact add_le_add (mul_le_mul (pow_le_pow_right₀ r_ge_one hs) hAB hA
    (pow_nonneg (zero_le_one.trans r_ge_one) _)) (underflow_monotone hs)

theorem stage_pair_near (p s : Nat) (A Aa Ab : ℝ) (hs : s ≤ p)
    (hAa : 0 ≤ Aa) (hAb : 0 ≤ Ab) (hAaA : Aa ≤ A) (hAbA : Ab ≤ A)
    (a b factor : Float × Float) (w a0 b0 : ℂ)
    (ha : PairFinite a) (hb : PairFinite b)
    (hc : FApprox factor.1 w.re (32 * unitRoundoff64))
    (hd : FApprox factor.2 w.im (32 * unitRoundoff64)) (hw : ‖w‖ = 1)
    (hnorma : ‖pairValue a‖ ≤ radixMagnitude s Aa)
    (hnormb : ‖pairValue b‖ ≤ radixMagnitude s Ab)
    (ha0 : ‖pairValue a - a0‖ ≤ radixError s Aa)
    (hb0 : ‖pairValue b - b0‖ ≤ radixError s Ab)
    (hsafe : radixSafety p A < (2 : ℝ) ^ 1022) :
    PairFinite (butterfly a b factor).1 ∧ PairFinite (butterfly a b factor).2 ∧
      ‖pairValue (butterfly a b factor).1‖ ≤ radixMagnitude (s + 1) (Aa + Ab) ∧
      ‖pairValue (butterfly a b factor).2‖ ≤ radixMagnitude (s + 1) (Aa + Ab) ∧
      ‖pairValue (butterfly a b factor).1 - (a0 + b0 * w)‖ ≤
        radixError (s + 1) (Aa + Ab) ∧
      ‖pairValue (butterfly a b factor).2 - (a0 - b0 * w)‖ ≤
        radixError (s + 1) (Aa + Ab) := by
  have haB := hnorma.trans (radixMagnitude_mono s p Aa A hs hAa hAaA)
  have hbB := hnormb.trans (radixMagnitude_mono s p Ab A hs hAb hAbA)
  have h := butterfly_near a b factor w a0 b0 (radixError s Aa) (radixError s Ab)
    (radixMagnitude p A) ha hb hc hd hw haB hbB hsafe ha0 hb0
  have hmag := next_stage_magnitude s Aa Ab (underflow s) (‖pairValue a‖) (‖pairValue b‖)
    hnorma hnormb
  have herr := next_stage_error s Aa Ab (underflow s) (‖pairValue a‖) (‖pairValue b‖)
    (radixError s Aa) (radixError s Ab) hnorma hnormb le_rfl le_rfl
  refine ⟨h.1, h.2.1, ?_, ?_, ?_, ?_⟩
  · exact h.2.2.1.trans hmag
  · exact h.2.2.2.1.trans hmag
  · exact h.2.2.2.2.1.trans herr
  · exact h.2.2.2.2.2.trans herr

theorem twiddle_factors_near (inverse : Bool) (n : UInt64) (p s j : Nat)
    (hn : n.toNat = 2 ^ p) (hp : p ≤ 32) (hs : s < p) (hj : j < 2 ^ s) :
    FApprox (twiddles n)[j * 2 ^ (p - s - 1)]!.1
      (FFTMath.root inverse (2 ^ (s + 1)) j).re (32 * unitRoundoff64) ∧
    FApprox (direction inverse * (twiddles n)[j * 2 ^ (p - s - 1)]!.2)
      (FFTMath.root inverse (2 ^ (s + 1)) j).im (32 * unitRoundoff64) := by
  let h : Nat := 2 ^ s
  let blocks : Nat := 2 ^ (p - s - 1)
  have hfull : n.toNat = 2 * (h * blocks) := by
    rw [hn]
    dsimp only [h, blocks]
    calc
      (2 : Nat) ^ p = 2 ^ ((s + 1) + (p - s - 1)) := by congr 1; omega
      _ = 2 ^ (s + 1) * 2 ^ (p - s - 1) := pow_add _ _ _
      _ = _ := by rw [pow_succ']; ring
  have hh : 0 < h := by dsimp only [h]; positivity
  have hblocks : 0 < blocks := by dsimp only [blocks]; positivity
  have hmhalf : j * blocks < (n / 2).toNat := by
    rw [UInt64.toNat_div]
    simp only [UInt64.reduceToNat]
    rw [hfull, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    exact Nat.mul_lt_mul_of_pos_right hj hblocks
  have hnmax : n.toNat ≤ 2 ^ 32 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by norm_num) hp
  have hm : j * blocks < n.toNat := by
    have hdiv := Nat.div_le_self n.toNat 2
    have hhalf : (n / 2).toNat = n.toNat / 2 := by simp only [UInt64.toNat_div, UInt64.reduceToNat]
    omega
  have hmi : (UInt64.ofNat (j * blocks)).toNat = j * blocks :=
    UInt64.toNat_ofNat_of_lt' (hm.trans (hnmax.trans_lt (by norm_num [UInt64.size])))
  have hfactor := FourierTwiddle.twiddle_near n (UInt64.ofNat (j * blocks))
    (by rw [hn]; positivity) (by rw [hmi]; exact hm)
    (hnmax.trans (by norm_num : (2 : Nat) ^ 32 ≤ 2 ^ 53))
  unfold twiddles
  rw [LeanExe.IR.build_get hmhalf]
  rw [← FFTMath.root_stage_succ inverse p s j hs]
  constructor
  · simpa only [FFTMath.root_re, FourierSpec.phase, hn, hmi, blocks] using hfactor.1
  · have hd := signed_factor_near inverse (Fourier.twiddle n (UInt64.ofNat (j * blocks))).2
      (Real.sin (2 * Real.pi * (UInt64.ofNat (j * blocks)).toNat / n.toNat))
      (32 * unitRoundoff64) hfactor.2
    simpa only [FFTMath.root_im, FFTMath.sign, FourierSpec.phase, hn, hmi, blocks, direction] using hd

theorem copy_near (xs : Array Float) (inverse : Bool) (p : Nat)
    (h : Radix2Admissible xs p) :
    StageNear xs inverse p 0
      (FFTLoop.copyReversed (FourierLoop.nWord xs) (UInt64.ofNat p) xs) := by
  have hn32 : FourierLoop.nSamples xs ≤ 2 ^ 32 := by
    change xs.size / 2 ≤ 2 ^ 32
    rw [h.1]
    exact Nat.pow_le_pow_right (by norm_num) h.2.1
  have hn := FourierLoop.nWord_toNat xs hn32
  have hpword : (UInt64.ofNat p).toNat = p := UInt64.toNat_ofNat_of_lt' (by
    have hp32 := h.2.1
    norm_num [UInt64.size]
    omega)
  have hnword : (FourierLoop.nWord xs).toNat = 2 ^ (UInt64.ofNat p).toNat := by
    rw [hn, hpword]
    exact h.1
  refine ⟨?_, ?_⟩
  · rw [FFTLoop.copyReversed_size _ _ _ (FourierLoop.nWord_le xs hn32), hn]
    rfl
  · intro b k hb hk
    have hk0 : k = 0 := by simpa using hk
    subst k
    simp only [pow_zero, mul_one, add_zero]
    have hb' : b < (FourierLoop.nWord xs).toNat := by
      rw [hn]
      change b < xs.size / 2
      rw [h.1]
      simpa only [Nat.sub_zero] using hb
    have hre := FFTLoop.copyReversed_get_real (FourierLoop.nWord xs) (UInt64.ofNat p) xs
      (by rw [hpword]; exact h.2.1) hnword b hb'
    have him := FFTLoop.copyReversed_get_imag (FourierLoop.nWord xs) (UInt64.ofNat p) xs
      (by rw [hpword]; exact h.2.1) hnword b hb'
    rw [hpword] at hre him
    have heq : pairValue (pairAt
        (FFTLoop.copyReversed (FourierLoop.nWord xs) (UInt64.ofNat p) xs) b) =
        FFTMath.inputValue xs (FFTBits.reverseNat p b) := by
      unfold pairAt pairValue
      rw [hre, him]
      rfl
    have hrev : FFTBits.reverseNat p b < xs.size / 2 := by
      rw [h.1]
      exact FFTBits.reverseNat_lt p b
    refine ⟨?_, ?_, ?_⟩
    · unfold PairFinite pairAt
      rw [hre, him]
      exact ⟨h.2.2.1 _ (by omega), h.2.2.1 _ (by omega)⟩
    · rw [heq, FFTMath.stageMass_zero]
      simpa only [radixMagnitude, pow_zero, one_mul, underflow, add_zero] using
        Complex.norm_le_abs_re_add_abs_im (FFTMath.inputValue xs (FFTBits.reverseNat p b))
    · rw [heq, FFTMath.stageValue_zero]
      simp only [sub_self, norm_zero, radixError, pow_zero, sub_self, zero_mul,
        underflow, add_zero, le_refl]

theorem stage_rows_near (xs : Array Float) (inverse : Bool) (p s : Nat)
    (h : Radix2Admissible xs p) (hs : s < p) (ys : Array Float)
    (hy : StageNear xs inverse p s ys) (b j : Nat)
    (hb : b < 2 ^ (p - s - 1)) (hj : j < 2 ^ s) :
    let half := 2 ^ s
    let zs := FFTLoop.stageWith (FourierLoop.nWord xs) (UInt64.ofNat (2 ^ (s + 1)))
      (twiddles (FourierLoop.nWord xs)) (direction inverse) ys
    (PairFinite (pairAt zs (b * (2 * half) + j)) ∧
      ‖pairValue (pairAt zs (b * (2 * half) + j))‖ ≤
        radixMagnitude (s + 1) (FFTMath.stageMass xs p (s + 1) b) ∧
      ‖pairValue (pairAt zs (b * (2 * half) + j)) -
        FFTMath.stageValue xs inverse p (s + 1) b j‖ ≤
        radixError (s + 1) (FFTMath.stageMass xs p (s + 1) b)) ∧
    (PairFinite (pairAt zs (b * (2 * half) + j + half)) ∧
      ‖pairValue (pairAt zs (b * (2 * half) + j + half))‖ ≤
        radixMagnitude (s + 1) (FFTMath.stageMass xs p (s + 1) b) ∧
      ‖pairValue (pairAt zs (b * (2 * half) + j + half)) -
        FFTMath.stageValue xs inverse p (s + 1) b (j + half)‖ ≤
        radixError (s + 1) (FFTMath.stageMass xs p (s + 1) b)) := by
  let n := FourierLoop.nWord xs
  let half : Nat := 2 ^ s
  let blocks : Nat := 2 ^ (p - s - 1)
  let width := UInt64.ofNat (2 ^ (s + 1))
  let zs := FFTLoop.stageWith n width (twiddles n) (direction inverse) ys
  have hn32 : FourierLoop.nSamples xs ≤ 2 ^ 32 := by
    change xs.size / 2 ≤ 2 ^ 32
    rw [h.1]
    exact Nat.pow_le_pow_right (by norm_num) h.2.1
  have hn : n.toNat = xs.size / 2 := FourierLoop.nWord_toNat xs hn32
  have hnp : n.toNat = 2 ^ p := hn.trans h.1
  have hnmax : n.toNat ≤ 2 ^ 32 := FourierLoop.nWord_le xs hn32
  have hhalf : 0 < half := by dsimp only [half]; positivity
  have hwidthNat : (2 : Nat) ^ (s + 1) = 2 * half := pow_succ' _ _
  have hspan : n.toNat = 2 * half * blocks := by
    rw [hnp]
    calc
      (2 : Nat) ^ p = 2 ^ ((s + 1) + (p - s - 1)) := by congr 1; omega
      _ = 2 ^ (s + 1) * 2 ^ (p - s - 1) := pow_add _ _ _
      _ = _ := by rw [hwidthNat]
  have hwidth : width.toNat = 2 * half := by
    change (UInt64.ofNat (2 ^ (s + 1))).toNat = 2 * half
    rw [UInt64.toNat_ofNat_of_lt', hwidthNat]
    have hp32 := h.2.1
    exact (Nat.pow_le_pow_right (by norm_num : (1 : Nat) ≤ 2)
      (show s + 1 ≤ 32 by omega)).trans_lt (by norm_num [UInt64.size])
  have hchildren : (2 : Nat) ^ (p - s) = 2 * blocks := by
    calc
      (2 : Nat) ^ (p - s) = 2 ^ ((p - s - 1) + 1) := by congr 1; omega
      _ = 2 * blocks := pow_succ' _ _
  have hsize : ys.size = 2 * n.toNat := by rw [hy.1, hn]
  let low := pairAt ys ((2 * b) * half + j)
  let high := pairAt ys ((2 * b + 1) * half + j)
  let factor := ((twiddles n)[j * blocks]!.1,
    direction inverse * (twiddles n)[j * blocks]!.2)
  have hlow := hy.2 (2 * b) j (by rw [hchildren]; omega) hj
  have hhigh := hy.2 (2 * b + 1) j (by rw [hchildren]; omega) hj
  have hf := twiddle_factors_near inverse n p s j hnp h.2.1 hs hj
  have hnear := stage_pair_near p s (FourierSpec.inputNorm xs)
    (FFTMath.stageMass xs p s (2 * b)) (FFTMath.stageMass xs p s (2 * b + 1)) hs.le
    (FFTMath.stageMass_nonneg _ _ _ _) (FFTMath.stageMass_nonneg _ _ _ _)
    (FFTMath.stageMass_le_inputNorm xs p s _ h.1 hs.le)
    (FFTMath.stageMass_le_inputNorm xs p s _ h.1 hs.le)
    low high factor (FFTMath.root inverse (2 ^ (s + 1)) j)
    (FFTMath.stageValue xs inverse p s (2 * b) j)
    (FFTMath.stageValue xs inverse p s (2 * b + 1) j)
    hlow.1 hhigh.1 hf.1 hf.2 (FFTMath.root_norm _ _ _)
    hlow.2.1 hhigh.2.1 hlow.2.2 hhigh.2.2 h.2.2.2
  have hi : b * half + j < half * blocks := by
    calc
      b * half + j < b * half + half := Nat.add_lt_add_left hj _
      _ = (b + 1) * half := by ring
      _ ≤ blocks * half := Nat.mul_le_mul_right _ (by omega)
      _ = half * blocks := Nat.mul_comm _ _
  have heq := FFTLoop.stageWith_entries n width (twiddles n) (direction inverse) ys
    half blocks hhalf hspan hwidth hnmax hsize (b * half + j) hi
  have hm : (b * half + j) % half = j := by
    rw [Nat.mul_comm b half, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  rw [FFTIndex.lower_flattened half b j hhalf hj,
    FFTIndex.upper_flattened half b j hhalf hj, hm] at heq
  have hlo : b * (2 * half) + j = (2 * b) * half + j := by ring
  have hhi : b * (2 * half) + j + half = (2 * b + 1) * half + j := by ring
  have hhi' : (2 * b) * half + j + half = (2 * b + 1) * half + j := by ring
  rw [hlo, hhi'] at heq
  change (pairAt zs ((2 * b) * half + j), pairAt zs ((2 * b + 1) * half + j)) =
    butterfly low high factor at heq
  have heqlo : pairAt zs (b * (2 * half) + j) = (butterfly low high factor).1 := by
    rw [hlo]
    exact congrArg Prod.fst heq
  have heqhi : pairAt zs (b * (2 * half) + j + half) = (butterfly low high factor).2 := by
    rw [hhi]
    exact congrArg Prod.snd heq
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [heqlo]; exact hnear.1
  · rw [heqlo, FFTMath.stageMass_children xs p s b (by omega)]; exact hnear.2.2.1
  · rw [heqlo, FFTMath.stageValue_lower xs inverse p s b j (by omega),
      FFTMath.stageMass_children xs p s b (by omega)]
    exact hnear.2.2.2.2.1
  · rw [heqhi]; exact hnear.2.1
  · rw [heqhi, FFTMath.stageMass_children xs p s b (by omega)]; exact hnear.2.2.2.1
  · rw [heqhi, FFTMath.stageValue_upper xs inverse p s b j (by omega),
      FFTMath.stageMass_children xs p s b (by omega)]
    exact hnear.2.2.2.2.2

theorem stage_near (xs : Array Float) (inverse : Bool) (p s : Nat)
    (h : Radix2Admissible xs p) (hs : s < p) (ys : Array Float)
    (hy : StageNear xs inverse p s ys) :
    StageNear xs inverse p (s + 1)
      (FFTLoop.stageWith (FourierLoop.nWord xs) (UInt64.ofNat (2 ^ (s + 1)))
        (twiddles (FourierLoop.nWord xs)) (direction inverse) ys) := by
  let half : Nat := 2 ^ s
  have hwidthNat : (2 : Nat) ^ (s + 1) = 2 * half := pow_succ' _ _
  refine ⟨by rw [FFTLoop.stageWith_size]; exact hy.1, ?_⟩
  intro b k hb hk
  have hb' : b < 2 ^ (p - s - 1) := by
    simpa only [Nat.sub_sub] using hb
  rw [hwidthNat] at hk
  by_cases hkh : k < half
  · have hrow := (stage_rows_near xs inverse p s h hs ys hy b k hb' hkh).1
    have hindex : b * (2 * half) + k = b * 2 ^ (s + 1) + k := by rw [hwidthNat]
    rw [hindex] at hrow
    exact hrow
  · let j := k - half
    have hj : j < half := by dsimp only [j]; omega
    have hjk : j + half = k := by dsimp only [j]; omega
    have hrow := (stage_rows_near xs inverse p s h hs ys hy b j hb' hj).2
    have hindex : b * (2 * half) + j + half = b * 2 ^ (s + 1) + k := by
      rw [hwidthNat, Nat.add_assoc, hjk]
    rw [hindex, hjk] at hrow
    exact hrow

theorem radix2_near (xs : Array Float) (inverse : Bool) (p : Nat)
    (h : Radix2Admissible xs p) :
    let ys := FFT.radix2With Trig.invPi Trig.halfPi (direction inverse) xs
    ys.size = 2 * (xs.size / 2) ∧ ∀ k, k < xs.size / 2 →
      PairFinite (pairAt ys k) ∧
      ‖pairValue (pairAt ys k)‖ ≤ radixMagnitude p (FourierSpec.inputNorm xs) ∧
      ‖pairValue (pairAt ys k) - FFTMath.stageValue xs inverse p p 0 k‖ ≤
        radixError p (FourierSpec.inputNorm xs) := by
  have hn32 : FourierLoop.nSamples xs ≤ 2 ^ 32 := by
    change xs.size / 2 ≤ 2 ^ 32
    rw [h.1]
    exact Nat.pow_le_pow_right (by norm_num) h.2.1
  have hn : (FourierLoop.nWord xs).toNat = 2 ^ p :=
    (FourierLoop.nWord_toNat xs hn32).trans h.1
  have hpword : (UInt64.ofNat p).toNat = p := UInt64.toNat_ofNat_of_lt' (by
    have hp32 := h.2.1
    norm_num [UInt64.size]
    omega)
  have hpcount : FFT.stageCount (FourierLoop.nWord xs) = UInt64.ofNat p := by
    have hpNat := FFTBits.stageCount_toNat (FourierLoop.nWord xs) p hn h.2.1
    rw [← hpNat, UInt64.ofNat_toNat]
  have hloop := FFTLoop.stage_loop_induction (UInt64.ofNat p) (FourierLoop.nWord xs)
    (twiddles (FourierLoop.nWord xs)) (direction inverse)
    (FFTLoop.copyReversed (FourierLoop.nWord xs) (UInt64.ofNat p) xs)
    (by rw [hpword]; exact h.2.1)
    (fun s ys => StageNear xs inverse p s ys) (copy_near xs inverse p h)
    (by
      intro s ys hs hy
      rw [hpword] at hs
      exact stage_near xs inverse p s h hs ys hy)
  rw [hpword] at hloop
  have hfinal : StageNear xs inverse p p
      (FFT.radix2With Trig.invPi Trig.halfPi (direction inverse) xs) := by
    rw [FFTLoop.radix2With_eq]
    change StageNear xs inverse p p
      (LeanExe.loop (FFT.stageCount (FourierLoop.nWord xs))
        (FFTLoop.copyReversed (FourierLoop.nWord xs) (FFT.stageCount (FourierLoop.nWord xs)) xs,
          (2 : UInt64))
        (fun _ state => (FFTLoop.stageWith (FourierLoop.nWord xs) state.2
          (twiddles (FourierLoop.nWord xs)) (direction inverse) state.1, 2 * state.2))).1
    rw [hpcount]
    exact hloop
  refine ⟨hfinal.1, ?_⟩
  intro k hk
  have hkpow : k < 2 ^ p := by rw [← h.1]; exact hk
  have hrow := hfinal.2 0 k (by simp) hkpow
  simp only [zero_mul, zero_add] at hrow
  rw [FFTMath.stageMass_final xs p 0 h.1] at hrow
  exact hrow

theorem radix2_accuracy (xs : Array Float) (inverse : Bool) (p : Nat)
    (h : Radix2Admissible xs p) :
    let ys := FFT.radix2With Trig.invPi Trig.halfPi (direction inverse) xs
    ys.size = 2 * (xs.size / 2) ∧ ∀ k, k < xs.size / 2 →
      FApprox ys[2 * k]!
        (if inverse then FourierPositive.realReference xs k else FourierSpec.realDFT xs k)
        (radixError p (FourierSpec.inputNorm xs)) ∧
      FApprox ys[2 * k + 1]!
        (if inverse then FourierPositive.imagReference xs k else FourierSpec.imagDFT xs k)
        (radixError p (FourierSpec.inputNorm xs)) ∧
      |value ys[2 * k]!.toBits| ≤ radixMagnitude p (FourierSpec.inputNorm xs) ∧
      |value ys[2 * k + 1]!.toBits| ≤ radixMagnitude p (FourierSpec.inputNorm xs) := by
  have hn := radix2_near xs inverse p h
  refine ⟨hn.1, ?_⟩
  intro k hk
  have hrow := hn.2 k hk
  have hre := (Complex.abs_re_le_norm
    (pairValue (pairAt (FFT.radix2With Trig.invPi Trig.halfPi (direction inverse) xs) k) -
      FFTMath.stageValue xs inverse p p 0 k)).trans hrow.2.2
  have him := (Complex.abs_im_le_norm
    (pairValue (pairAt (FFT.radix2With Trig.invPi Trig.halfPi (direction inverse) xs) k) -
      FFTMath.stageValue xs inverse p p 0 k)).trans hrow.2.2
  rw [Complex.sub_re, FFTMath.stageValue_final_re xs inverse p 0 k h.1] at hre
  rw [Complex.sub_im, FFTMath.stageValue_final_im xs inverse p 0 k h.1] at him
  exact ⟨⟨hrow.1.1, hre⟩, ⟨hrow.1.2, him⟩,
    (Complex.abs_re_le_norm _).trans hrow.2.1,
    (Complex.abs_im_le_norm _).trans hrow.2.1⟩

#print axioms underflow_nonneg
#print axioms signed_factor_near
#print axioms underflow_monotone
#print axioms radixMagnitude_mono
#print axioms stage_pair_near
#print axioms twiddle_factors_near
#print axioms copy_near
#print axioms stage_rows_near
#print axioms stage_near
#print axioms radix2_near
#print axioms radix2_accuracy

end Verified.Examples.FFTNumerical
